/*
    Copyright(c)  2023   Alessandro Improta, Luca Sani, Catchpoint Systems, Inc.
    
    This software was updated by Catchpoint Systems, Inc. to incorporate
    InSession algorithm functionality.
    
    Copyright(c)  2006, 2007        Dmitry Butskoy
                    <buc@citadel.stu.neva.ru>
    License:  GPL v2 or any later

    See COPYING for the status of this software.
*/

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/socket.h>
#include <poll.h>
#include <netinet/tcp.h>
#include <linux/types.h>
#include <sys/socket.h>
#include <netdb.h>
       
#include "common-tcp.h"
#include "flowlabel.h"

#define MAX_CONNECT_TIMEOUT_SEC 5

#ifndef IP_MTU
#define IP_MTU 14
#endif

static sockaddr_any dest_addr = {{ 0, }, };
static unsigned int dest_port = 0;

static int raw_icmp_sk = -1;
static int raw_sk = -1;
static int sk = -1;
static int last_ttl = 0;

static int mtu = 0;
static int af = 0;
static int header_len = 0;

static unsigned pseudo_IP_header_size = 0;
static uint8_t* counter_pointer = NULL;
static uint8_t* buf;        /*  enough, enough...  */
static uint8_t tmp_buf[1024];        /*  enough, enough...  */
static size_t* length_p;
static sockaddr_any src;
static uint32_t ts_value_offset = 0;
static struct tcphdr* th = NULL;
static uint16_t* lenp = NULL;
static unsigned mss_received = 0;
static int info = 0;

extern int use_additional_raw_icmp_socket;

uint32_t initial_seq_num = 0;
uint32_t seq_num = 0;
uint32_t ack_num = 0;
uint32_t ts_value = 0;
uint32_t ts_echo_reply = 0;

static CLIF_option tcp_options[] = {
    { 0, "info", 0, "Print tcp flags of final tcp replies when target host is reached. Useful to determine whether an application listens the port etc.", CLIF_set_flag, &info, 0, 0 },
    CLIF_END_OPTION
};

static int tcpinsession_init(const sockaddr_any* dest, unsigned int port_seq, size_t* packet_len_p) 
{
    initial_seq_num = rand();
    
    af = dest->sa.sa_family;

    if(!port_seq)  
        port_seq = DEF_TCP_PORT;
    dest_port = htons(port_seq);
    
    dest_addr = *dest;
    
    if(af == AF_INET)
        dest_addr.sin.sin_port = dest_port;
    else
        dest_addr.sin6.sin6_port = dest_port;
    
    raw_sk = socket(af, SOCK_RAW, IPPROTO_TCP);
    if(raw_sk < 0)
        error_or_perm("socket");

    tune_socket(raw_sk);
    
    double connect_starttime = get_time();
    
    if(connect(raw_sk, &dest_addr.sa, sizeof(dest_addr)) < 0)
        error("connect");
    
    sk = socket(af, SOCK_STREAM, 0);
    tune_socket(sk);    /*  common stuff  */
    
    if(connect(sk, &dest_addr.sa, sizeof(dest_addr)) < 0)
        if(errno != EINPROGRESS) // note that we don't need to wait the connect to be successful since the loop below will wait for the syn+ack.
            error("connect");

    socklen_t lenmtu = sizeof(mtu);
    if(getsockopt(raw_sk, af == AF_INET ? SOL_IP : SOL_IPV6, af == AF_INET ? IP_MTU : IPV6_MTU, &mtu, &lenmtu) < 0 || mtu < 576)
        mtu = 576;
        
    socklen_t src_len = sizeof(src);
    if(getsockname(sk, &src.sa, &src_len) < 0)
        error("getsockname");
     
    uint8_t ack_buf[1024];
    int found = 0;
    int received = 0;
    sockaddr_any response_src_addr;
    memset(&response_src_addr, 0, sizeof(response_src_addr));
    socklen_t src_addr_len = sizeof(response_src_addr);
    
    do {
        if((received = recvfrom(raw_sk, ack_buf, sizeof(ack_buf), 0, &response_src_addr.sa, &src_addr_len)) >= 0) {
            struct tcphdr* response_tcp_hdr = NULL;
            uint8_t* opt_ptr = NULL;
            uint16_t option_len = 0;
            
            if(af == AF_INET) {
                struct iphdr* response_iphdr = (struct iphdr*)ack_buf;
                response_tcp_hdr = (struct tcphdr*) (ack_buf + (response_iphdr->ihl << 2));
                if(response_tcp_hdr->dest == src.sin.sin_port) {
                    uint16_t response_flags = get_th_flags(response_tcp_hdr);
                    if((response_flags & SYN) && (response_flags & ACK)) { // paranoid
                        response_src_addr.sin.sin_port = response_tcp_hdr->source;
                        
                        if(equal_sockaddr(&dest_addr, &response_src_addr)) {
                            found = 1;
                            opt_ptr = ((uint8_t*)response_tcp_hdr)+sizeof(*response_tcp_hdr);
                            option_len = htons(response_iphdr->tot_len)-sizeof(*response_iphdr)-sizeof(*response_tcp_hdr);
                        }
                    }
                }
            } else if(af == AF_INET6) {
                response_tcp_hdr = (struct tcphdr*)ack_buf;
                if(response_tcp_hdr->dest == src.sin6.sin6_port) {
                    uint16_t response_flags = get_th_flags(response_tcp_hdr);
                    if((response_flags & SYN) && (response_flags & ACK)) { // paranoid
                        response_src_addr.sin6.sin6_port = response_tcp_hdr->source;
                        
                        if(equal_sockaddr(&dest_addr, &response_src_addr)) {
                            found = 1;
                            opt_ptr = ((uint8_t*)response_tcp_hdr)+sizeof(*response_tcp_hdr);
                            option_len = received-sizeof(*response_tcp_hdr);
                        }
                    }
                }
            }
                    
            if(found) {
                initial_seq_num = ntohl(response_tcp_hdr->ack_seq)+1;
                seq_num = initial_seq_num;
                ack_num = ntohl(response_tcp_hdr->seq)+1;
                
                int SACK_permitted = 0;
                for(uint16_t i = 0; i < option_len; i++) {
                    uint8_t opt_kind = *opt_ptr;
                    if(opt_kind == TCPOPT_EOL)
                        break;
                    
                    opt_ptr++;
                    if(opt_kind == TCPOPT_NOP)
                        continue;
                    
                    uint8_t opt_len = *opt_ptr;
                    opt_ptr++;
                    if(opt_kind == TCPOPT_SACK_PERMITTED) {
                        SACK_permitted = 1;
                        opt_ptr += opt_len;
                        opt_ptr -= 2; // opt kind and len are included in opt_len
                    } else if(opt_kind == TCPOPT_MAXSEG) {
                        mss_received = ntohs(*(uint16_t*)opt_ptr);
                        opt_ptr += opt_len;
                        opt_ptr -= 2; // opt kind and len are included in opt_len
                    } else if(opt_kind != TCPOPT_TIMESTAMP) {
                        opt_ptr += opt_len;
                        opt_ptr -= 2; // opt kind and len are included in opt_len
                    } else {
                        uint32_t timestamp_value = ntohl(*((uint32_t*)opt_ptr));
                        opt_ptr += sizeof(uint32_t);
                        uint32_t timestamp_echo_reply = ntohl(*((uint32_t*)opt_ptr));
                        
                        ts_value = htonl(timestamp_echo_reply+30);
                        ts_echo_reply = htonl(timestamp_value);
                        
                        options |= OPT_TSTAMP;
                        
                        break;
                    }
                }
                
                if(SACK_permitted == 0) {
                    close(sk);
                    close(raw_sk);
                    ex_error("TCP SACK not permitted from destination");
                }
            }
        } else {
            if(get_time() - connect_starttime > MAX_CONNECT_TIMEOUT_SEC)
                break;
            
            usleep(10000);
        }
    } while(!found);
    
    if(!found) {
        close(sk);
        close(raw_sk);
        ex_error("Cannot complete initial TCP handshake");
    }
    
    socklen_t len;
    uint8_t* ptr;

    use_recverr(raw_sk);
    add_poll(raw_sk, POLLIN | POLLERR);

    /*  Now create the sample packet.  */

    flags |= PSH;
    flags |= ACK;
    
    /*  For easy checksum computing:
        saddr
        daddr
        length
        protocol
        tcphdr
        tcpoptions
    */

    ptr = tmp_buf;

    if(af == AF_INET) {
        len = sizeof(src.sin.sin_addr);
        memcpy(ptr, &src.sin.sin_addr, len);
        ptr += len;
        memcpy(ptr, &dest_addr.sin.sin_addr, len);
        ptr += len;
    } else {
        len = sizeof(src.sin6.sin6_addr);
        memcpy(ptr, &src.sin6.sin6_addr, len);
        ptr += len;
        memcpy(ptr, &dest_addr.sin6.sin6_addr, len);
        ptr += len;
    }

    lenp = (uint16_t*)ptr;
    uint16_t delta_len_p = ptr - tmp_buf;
    ptr += sizeof(uint16_t);
    *((uint16_t*)ptr) = htons((uint16_t)IPPROTO_TCP);
    ptr += sizeof(uint16_t);

    /*  Construct TCP header   */

    th = (struct tcphdr*)ptr;
    
    pseudo_IP_header_size = ptr - tmp_buf;

    th->source = 0;
    th->dest = dest_port;
    th->seq = 0;
    th->ack_seq = htonl(ack_num);
    th->doff = 0;
    set_th_flags(th, flags);
    th->window = htons(4 * mtu);
    th->check = 0;
    th->urg_ptr = 0;

    ptr = (uint8_t*)(th + 1);

    // Send timestamp only if it was received into the initial SYN+ACK
    // Add also two bytes NOP for a total of 12 bytes to align the options space on 4 bytes.
    if(options & OPT_TSTAMP) {
        *ptr++ = TCPOPT_TIMESTAMP;    /*  8   */
        *ptr++ = TCPOLEN_TIMESTAMP;    /*  10  */
        ts_value_offset = ptr - (uint8_t*)th;
        *((uint32_t*)ptr) = ts_value;
        ptr += sizeof(uint32_t);
        *((uint32_t*)ptr) = ts_echo_reply;
        ptr += sizeof(uint32_t);
        *ptr++ = TCPOPT_NOP;    /*  1   */
        *ptr++ = TCPOPT_NOP;    /*  1   */
    }

    len = ptr - (uint8_t*)th;
    if(len & 0x03)
        ex_error("impossible");    /*  as >>2 ...  */

    th->doff = len >> 2;
    
    length_p = packet_len_p;
    *lenp = htons(*length_p);
    
    if(*length_p && !(buf = malloc(*length_p+pseudo_IP_header_size)))
        error("malloc");

    memcpy(buf, tmp_buf, pseudo_IP_header_size+len);
    th = (struct tcphdr*)(buf + pseudo_IP_header_size);

    counter_pointer = buf + pseudo_IP_header_size + len;

    for(int i = pseudo_IP_header_size + len; i < pseudo_IP_header_size + (*length_p); i++)
        buf[i] = 0x00;
    
    header_len = len;
    
    if(use_additional_raw_icmp_socket) {
        raw_icmp_sk = socket(dest_addr.sa.sa_family, SOCK_RAW, (dest_addr.sa.sa_family == AF_INET) ? IPPROTO_ICMP : IPPROTO_ICMPV6);
        
        if(raw_icmp_sk < 0)
            error_or_perm("raw icmp socket");
        
        lenp = (uint16_t*)(buf + delta_len_p); // Allow the length in the pseudo IP header to be changed when we send probes 
        
        add_poll(raw_icmp_sk, POLLIN | POLLERR);
    }
    
    return 0;
}

static void tcpinsession_send_probe(probe* pb, int ttl) 
{
    th->source = src.sin.sin_port;
    th->seq = htonl(seq_num);
    pb->seq_num = seq_num;
    
    if(counter_pointer == NULL)
        error("counter pointer uninitialized");
    
    (*counter_pointer)++;
    
    uint8_t* ts_ptr = ((uint8_t*)th)+ts_value_offset;
    uint32_t val = htonl(*((uint32_t*)ts_ptr));
    val++;
    *((uint32_t*)ts_ptr) = htonl(val);
    *lenp = htons(*length_p); 
    th->check = 0;
    th->check = in_csum(buf, (*length_p)+pseudo_IP_header_size);
    if(ttl != last_ttl) {
        set_ttl(raw_sk, ttl);
        last_ttl = ttl;
    }

    pb->sk = -1;
    pb->icmp_done = 0;
    pb->send_time = get_time();
    
    int res = do_send(raw_sk, th, *length_p, &dest_addr);
    if(res < 0) {
        error("so bad");
        pb->send_time = 0;
    } else if(res > 0) {
        seq_num += (*length_p - header_len);
    }
}

int compare_desc(const void* a, const void* b)
{
    sack_block* u_a = (sack_block*)a;
    sack_block* u_b = (sack_block*)b;

    if(u_b->sle < u_a->sle)
        return -1;

    if(u_b->sle > u_a->sle)
        return 1;

    return 0;
}

static probe* find_probe_from_sack(struct tcphdr* tcp)
{
    const uint8_t* ptr = (const uint8_t*)(tcp + 1);
    
    int opt_len = (tcp->doff * 4) - sizeof(struct tcphdr);
    
    sack_blocks curr_sack_blocks;
    memset(&curr_sack_blocks, 0, sizeof(curr_sack_blocks));
    
    uint8_t sack_block_i = 0;
    uint32_t interval = 0;
    int sack_found = 0;
    while(opt_len > 0) {
        int opcode = *ptr++;
        
        if(opcode == TCPOPT_EOL) // End of options (EOL)
            break;
            
        if(opcode == TCPOPT_NOP) { // NOP with no length
            opt_len--;
            continue;
        }
        
        uint8_t size = *ptr++;
        
        if(opcode != TCPOPT_SACK) {
            ptr += (size - 2);
            opt_len -= size;
            continue;
        }
        
        uint32_t sack_len = size-2;
        if(sack_len % 8 != 0 || sack_len > 24)
            ex_error("Malformed SACK option");
        
        sack_found = 1;
        
        while(sack_len > 0) {
            uint32_t sle = ntohl(*((uint32_t*)ptr));
            curr_sack_blocks.block[sack_block_i].sle = sle;
            
            ptr += sizeof(uint32_t);
            
            uint32_t sre = ntohl(*((uint32_t*)ptr));
            curr_sack_blocks.block[sack_block_i].sre = sre;
            sack_block_i++;
            
            ptr += sizeof(uint32_t);
            
            sack_len -= 2*sizeof(uint32_t);
            
            interval += sre-sle;
        }
        
        opt_len -= size;
    }
    
    if(interval == 0) {
        close(sk);
        close(raw_sk);
        if(sack_found == 0)
            ex_error("Missing SACK options");
        else
            ex_error("Unexpected overlap of SACK intervals");
    }
    
    // just order them decreasing
    qsort(curr_sack_blocks.block, 3, sizeof(sack_block), compare_desc);
    
    probe* first_avail_probe = NULL;
    
    for(int i = 0; i < num_probes; i++) {
        if(((probes[i].seq_num >= curr_sack_blocks.block[0].sle && probes[i].seq_num < curr_sack_blocks.block[0].sre) || (probes[i].seq_num >= curr_sack_blocks.block[1].sle && probes[i].seq_num < curr_sack_blocks.block[1].sre) || (probes[i].seq_num >= curr_sack_blocks.block[2].sle && probes[i].seq_num < curr_sack_blocks.block[2].sre)) && (probes[i].seq_num > 0)) {
            probes[i].tcpinsession_destination_reply = 1;
                
            if(probes[i].done == 0 && probes[i].final == 0) {
                first_avail_probe = &probes[i];
                break;
            }
        }
    }
    
    return first_avail_probe;
}

static probe* tcpinsession_check_reply(int sk, int err, sockaddr_any* from, char* buf, size_t len) 
{
    if(len < 8)
        return NULL;        /*  too short   */

    if(!equal_addr(&dest_addr, from))
        return NULL;
        
    struct tcphdr* tcp = (struct tcphdr*)buf;
    uint32_t seq_num_returned = 0;
    
    if(err) { // got icmp, thus buf contains the TCP header of the offending probe
        uint16_t dport = tcp->dest; 
        if(dport != dest_port)
            return NULL;

        seq_num_returned = ntohl(tcp->seq);
        return probe_by_seq_num(seq_num_returned);
    }
    
    uint16_t dport = tcp->source;
    if(dport != dest_port)
        return NULL;
        
    uint16_t sport = tcp->dest;
    if(src.sa.sa_family == AF_INET6) {
        if(sport != src.sin6.sin6_port) 
            return NULL;
    } else if(src.sa.sa_family == AF_INET) {
        if(sport != src.sin.sin_port) 
            return NULL;
    } else {
        return NULL;
    }
    
    probe* pb = find_probe_from_sack(tcp);
    
    if(!pb)
        return NULL;
        
    pb->final = 1;
    
    if(info)
        pb->ext = names_by_flags(get_th_flags(tcp));
    
    // Note that here we cannot receive the MSS, because it is included only in the initial SYN+ACK
    
    return pb;
}

static void tcpinsession_recv_probe(int sk, int revents) 
{
    if(!(revents & (POLLIN | POLLERR)))
        return;

    recv_reply(sk, !!(revents & POLLERR), tcpinsession_check_reply);
}

static int tcpinsession_is_raw_icmp_sk(int sk)
{
    if(sk == raw_icmp_sk)
        return 1;

    return 0;
}

/*
    Here we need to slightly change the logic wrt the same function in other modules.
    Since in this module all the probes share the same five tuple, we recover the probe by looking at the sequence number of the offending probe and finding the probe with the same value (as in thethe check_reply). Furthermore, to be extrasure that this is a probe for us (since this is a RAW ICMP socket), once the probe is found, we check if the destination and source address of the offendng probe matches the ones that we are using to perform the traceroute
*/
static probe* tcpinsession_handle_raw_icmp_packet(char* bufp, uint16_t* overhead, struct msghdr* response_get, struct msghdr* ret)
{
    sockaddr_any offending_probe_dest;
    sockaddr_any offending_probe_src;
    struct tcphdr* offending_probe = NULL;
    int proto = 0;
    int returned_tos = 0;
    extract_ip_info(dest_addr.sa.sa_family, bufp, &proto, &offending_probe_src, &offending_probe_dest, (void **)&offending_probe, &returned_tos); 
    
    if(proto != IPPROTO_TCP)
        return NULL;
    
    offending_probe = (struct tcphdr*)offending_probe;
    
    uint32_t probe_seq_num = ntohl(offending_probe->seq);
    probe* pb = probe_by_seq_num(probe_seq_num);
    
    if(!pb)
        return NULL;
    
    offending_probe_dest.sin.sin_port = offending_probe->dest;
    offending_probe_src.sin.sin_port = offending_probe->source;
    
    if((loose_match || equal_sockaddr(&src, &offending_probe_src)) && equal_sockaddr(&dest_addr, &offending_probe_dest)) {
        pb->returned_tos = returned_tos;
        probe_done(pb, &pb->icmp_done);
        if(loose_match)
            *overhead = prepare_ancillary_data(dest_addr.sa.sa_family, bufp, sizeof(struct tcphdr), ret, response_get->msg_name);
    }
    
    return pb;
}

static void tcpinsession_close()
{
    tcpinsession_print_allowed = 1;
    int start = (first_hop - 1) * probes_per_hop;
    for(int i = start; i < last_probe; i++)
        print_probe(&probes[i]);
    
    close(sk);
    if(use_additional_raw_icmp_socket)
        close(raw_icmp_sk);
}

static tr_module tcpinsession_ops = {
    .name = "tcpinsession",
    .init = tcpinsession_init,
    .send_probe = tcpinsession_send_probe,
    .recv_probe = tcpinsession_recv_probe,
    .options = tcp_options,
    .is_raw_icmp_sk = tcpinsession_is_raw_icmp_sk,
    .handle_raw_icmp_packet = tcpinsession_handle_raw_icmp_packet,
    .close = tcpinsession_close
};

TR_MODULE(tcpinsession_ops);
