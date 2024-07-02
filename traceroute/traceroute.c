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
#include <stdarg.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/socket.h>
#include <poll.h>
#include <netinet/icmp6.h>
#include <netinet/ip_icmp.h>
#include <netinet/in.h>
#include <netinet/ip6.h>
#include <netdb.h>
#include <errno.h>
#include <locale.h>
#include <sys/utsname.h>

#ifdef __APPLE__
#define SO_BINDTODEVICE 25
#include <string.h>
#include "mac/errqueue.h" 
#include "mac/icmp.h"
#include "mac/ip.h" 
#include <dispatch/dispatch.h>
#else
#include <linux/errqueue.h>
#include <semaphore.h>
#endif

/*  XXX: Remove this when things will be defined properly in netinet/ ...  */
#include "flowlabel.h"

#include <clif.h>
#include "version.h"
#include "traceroute.h"

#include <pthread.h>

#ifndef ICMP6_DST_UNREACH_BEYONDSCOPE
#ifdef ICMP6_DST_UNREACH_NOTNEIGHBOR
#define ICMP6_DST_UNREACH_BEYONDSCOPE ICMP6_DST_UNREACH_NOTNEIGHBOR
#else
#define ICMP6_DST_UNREACH_BEYONDSCOPE 2
#endif
#endif

#ifndef IPV6_RECVHOPLIMIT
#define IPV6_RECVHOPLIMIT IPV6_HOPLIMIT
#endif

#ifndef IP_PMTUDISC_PROBE
#define IP_PMTUDISC_PROBE 3
#endif

#ifndef IPV6_PMTUDISC_PROBE
#define IPV6_PMTUDISC_PROBE 3
#endif

#ifndef AI_IDN
#define AI_IDN 0
#endif

#ifndef NI_IDN
#define NI_IDN 0
#endif

#define MAX_HOPS 255
#define MAX_HOP_FAILURES MAX_HOPS
#define MAX_PROBES 30
#define MAX_GATEWAYS_4 8
#define MAX_GATEWAYS_6 127
#define MAX_MTU_RETRIES 3
#define DEF_HOPS 30
#define DEF_SIM_PROBES 16    /*  including several hops   */
#define DEF_NUM_PROBES 3
#define DEF_WAIT_SECS 5.0
#define DEF_HERE_FACTOR 3
#define DEF_NEAR_FACTOR 10
#ifndef DEF_WAIT_PREC
#define DEF_WAIT_PREC 0.001    /*  +1 ms  to avoid precision issues   */
#endif
#define DEF_SEND_SECS 0
#define DEF_DATA_LEN 40    /*  all but IP header...  */
#define DEF_DATA_LEN_TCPINSESSION 33 // 20 TCP header + 12 options(NOP+NOP+TS) + 1 byte of payload(00)
#ifdef HAVE_OPENSSL3
#define DEF_DATA_LEN_QUIC 1200 // According to RFC9000 Client Initial QUIC packets must have at least 1200 bytes UDP payload https://www.rfc-editor.org/rfc/rfc9000.html#section-8.1-5
#endif
#define MAX_PACKET_LEN 65000
#ifndef DEF_AF
#define DEF_AF AF_INET
#endif

#define ttl2hops(X) (((X) <= 64 ? 65 :((X) <= 128 ? 129 : 256)) -(X))

static char version_string[] = "Modern traceroute for Linux, version " _TEXT(VERSION) "\n"
                               "Copyright(c)  2023   Alessandro Improta, Luca Sani, Catchpoint Systems, Inc.\n"
                               "This software was updated by Catchpoint Systems, Inc. to incorporate InSession algorithm functionality\n\n"
                               "Copyright(c) 2016  Dmitry Butskoy,   License: GPL v2 or any later";
static int debug = 0;
unsigned int first_hop = 1;

static unsigned int max_hops = DEF_HOPS;
static unsigned int sim_probes = DEF_SIM_PROBES;
unsigned int probes_per_hop = DEF_NUM_PROBES;
unsigned int num_probes = 0;
int last_probe = -1;
int tcpinsession_print_allowed = 0;
probe* probes = NULL;
probe* tcpinsession_destination_probes = NULL;

static char **gateways = NULL;
static int num_gateways = 0;
static unsigned char *rtbuf = NULL;
static size_t rtbuf_len = 0;
static unsigned int ipv6_rthdr_type = 2;    /*  IPV6_RTHDR_TYPE_2   */
static size_t header_len = 0;
static size_t data_len = 0;
static int dontfrag = 0;
static int noresolve = 0;
static int extension = 0;
static int as_lookups = 0;
static unsigned int dst_port_seq = 0;
static int tos_input_value = -1;
static int dscp_input_value = -1;
static unsigned int flow_label = 0;
static int noroute = 0;
static int packet_len = -1;
static double wait_secs = DEF_WAIT_SECS;
static double here_factor = DEF_HERE_FACTOR;
static double near_factor = DEF_NEAR_FACTOR;
static double send_secs = DEF_SEND_SECS;
static int overall_mtu = -1;
static int reliable_overall_mtu = 0;
static int backward = 0;
#ifdef SO_MARK
static unsigned int fwmark = 0;
#endif
static sockaddr_any dst_addr = {{ 0, }, };
static char* dst_name = NULL;
static char* device = NULL;
sockaddr_any src_addr = {{ 0, }, };
static unsigned int src_port = 0;
static unsigned int overall_timeout = 0;
static unsigned int timedout = 0;
static unsigned int destination_reached = 0;
static int consecutive_probe_failures = 0;
static int max_consecutive_hop_failures = MAX_HOPS;
static const char* module = "default";
static const tr_module *ops = NULL;
static char *opts[16] = { NULL, };    /*  assume enough   */
static unsigned int opts_idx = 1;    /*  first one reserved...   */
static int af = 0;
static int extra_ping_ongoing = 0;
static int last_hop_reached = 0;
static void print_trailer();

int use_additional_raw_icmp_socket = 0;
int tr_via_additional_raw_icmp_socket = 0;
int ecn_input_value = -1;
int loose_match = 0;
int mtudisc = 0;
int disable_extra_ping = 0;
unsigned int tos = 0;
int mtudisc_phase = 0;

static unsigned int saved_max_hops = -1;
static unsigned int saved_first_hop = -1;
static unsigned int saved_sim_probes = -1;

// The following tables are inspired from kernel 3.10 (net/ipv4/icmp.c and net/ipv6/icmp.c)
// RFC 1122: 3.2.2.1 States that NET_UNREACH, HOST_UNREACH and SR_FAILED MUST be considered 'transient errs'.

struct icmp4_err {
  int error;
  unsigned int fatal;
};

const struct icmp4_err icmp4_err_convert[] = {
    {
        .error = ENETUNREACH,    // ICMP_NET_UNREACH
        .fatal = 0,
    },
    {
        .error = EHOSTUNREACH,    // ICMP_HOST_UNREACH
        .fatal = 0,
    },
    {
        .error = ENOPROTOOPT,    // ICMP_PROT_UNREACH
        .fatal = 1,
    },
    {
        .error = ECONNREFUSED,    // ICMP_PORT_UNREACH
        .fatal = 1,
    },
    {
        .error = EMSGSIZE,    // ICMP_FRAG_NEEDED
        .fatal = 0,
    },
    {
        .error = EOPNOTSUPP,    // ICMP_SR_FAILED
        .fatal = 0,
    },
    {
        .error = ENETUNREACH,    // ICMP_NET_UNKNOWN
        .fatal = 1,
    },
    {
        .error = EHOSTDOWN,    // ICMP_HOST_UNKNOWN
        .fatal = 1,
    },
    {
    #ifdef __APPLE__
        .error = EHOSTDOWN,
    #else
        .error = ENONET,    // ICMP_HOST_ISOLATED
    #endif
        .fatal = 1,
    },
    {
        .error = ENETUNREACH,    // ICMP_NET_ANO
        .fatal = 1,
    },
    {
        .error = EHOSTUNREACH,    // ICMP_HOST_ANO
        .fatal = 1,
    },
    {
        .error = ENETUNREACH,    // ICMP_NET_UNR_TOS
        .fatal = 0,
    },
    {
        .error = EHOSTUNREACH,    // ICMP_HOST_UNR_TOS
        .fatal = 0,
    },
    {
        .error = EHOSTUNREACH,    // ICMP_PKT_FILTERED
        .fatal = 1,
    },
    {
        .error = EHOSTUNREACH,    // ICMP_PREC_VIOLATION
        .fatal = 1,
    },
    {
        .error = EHOSTUNREACH,    // ICMP_PREC_CUTOFF
        .fatal = 1,
    },
};

struct icmp6_err {
    int err;
    int fatal;
};

const struct icmp6_err icmp6_err_convert[] = {
    {    
        .err = ENETUNREACH,    // NOROUTE */
        .fatal = 0,
    },
    {    
        .err = EACCES,    // ADM_PROHIBITED */
        .fatal = 1,
    },
    {    
        .err = EHOSTUNREACH,    // Was NOT_NEIGHBOUR, now reserved
        .fatal = 0,
    },
    {    
        .err = EHOSTUNREACH,    // ADDR_UNREACH
        .fatal = 0,
    },
    {    
        .err = ECONNREFUSED,    // PORT_UNREACH
        .fatal = 1,
    },
    {    
        .err = EACCES,    // POLICY_FAIL
        .fatal = 1,
    },
    {    
        .err = EACCES,    // REJECT_ROUTE
        .fatal = 1,
    },
};

#ifdef HAVE_OPENSSL3
extern int quic_print_dest_rtt_mode;
#endif

unsigned int compute_data_len(int packet_len);

static void print_end(void) 
{
    printf("\n");
}

struct timeval starttime;

#ifdef __APPLE__
    dispatch_semaphore_t probe_semaphore;
#else
    sem_t probe_semaphore;
#endif

pthread_t printer_thr;

void ex_error(const char *format, ...) 
{
    va_list ap;

    va_start(ap, format);
    vfprintf(stderr, format, ap);
    va_end(ap);

    fprintf(stderr, "\n");

    exit(2);
}

void error(const char *str)
{
    fprintf(stderr, "\n");

    perror(str);

    exit(1);
}

void error_or_perm(const char *str) 
{
    if(errno == EPERM)
        fprintf(stderr, "You do not have enough privileges to use this traceroute method.");
    error(str);
}

#define SYSCTL_PREFIX "/proc/sys/net/ipv4/tcp_"
int check_sysctl(const char* name) 
{
    int fd;
    int res;
    char buf[sizeof(SYSCTL_PREFIX) + strlen(name) + 1];
    uint8_t ch;

    strcpy(buf, SYSCTL_PREFIX);
    strcat(buf, name);

    fd = open(buf, O_RDONLY, 0);
    if(fd < 0)
        return 0;

    res = read(fd, &ch, sizeof(ch));
    close(fd);

    if(res != sizeof(ch))
        return 0;

    /*  since kernel 2.6.31 "tcp_ecn" can have value of '2'...  */
    if(ch == '1')
        return 1;
    else if(ch == '3') // Experimental: AccECN experimentation for L4S allows the value to be 3 (https://github.com/L4STeam/linux)
        return 3;

    return 0;
}

static void check_expired(probe*);

static void poll_callback(int, int);

static void* printer(void* args)
{
    int start = (first_hop - 1) * probes_per_hop;
    int end = num_probes;
    
    int replace_idx = 0;
    
    for(int idx = start; idx < end; idx++) {
    #ifdef __APPLE__
        dispatch_semaphore_wait(probe_semaphore, DISPATCH_TIME_FOREVER);
    #else
        sem_wait(&probe_semaphore);
    #endif
        
        probe* pb = &probes[idx];

        if(pb->exit_please > 0) {
            if(idx > 0 && ((idx-1) % probes_per_hop) != probes_per_hop-1) { // Last valid probe was not in a triplet
                unsigned int n = idx-1;
                while(n % probes_per_hop != probes_per_hop-1) {
                    printf(" *"); // Add forced timeouts when overall timeout has been reached
                    pb = &probes[n];
                    probe_done(pb, NULL);
                    check_expired(pb);
                    n++;
                }
            }
            return NULL;
        }
        
        print_probe(pb);

        if(pb->done && pb->final) {
            end = (idx / probes_per_hop + 1) * probes_per_hop;
            last_hop_reached = end/probes_per_hop;
        }
    }

    if(strcmp(module, "tcpinsession") == 0) { // Only in tcpinsession we need to replace the destination with the initial ping. Please note that print_probe will not print the probe results if  tcpinsession_destination_reply is set, and the final print is required to be performed at the end of the run
        int destination_replies = 0;
        for(int i = last_probe-probes_per_hop; i < last_probe; i++)
            if(probes[i].tcpinsession_destination_reply == 1)
                destination_replies++;

        if(destination_replies > 0) {
            for(int i = last_probe-probes_per_hop; i < last_probe; i++, replace_idx++) {
                tcpinsession_destination_probes[replace_idx].mtu = probes[i].mtu;
                tcpinsession_destination_probes[replace_idx].mss = probes[i].mss;
                memcpy(&probes[i], &tcpinsession_destination_probes[replace_idx], sizeof(probe));
            }
        }
    }
    
    return NULL;
}

/*  Set initial parameters according to how we was called   */
static void check_progname(const char *name) 
{
    const char* p = strrchr(name, '/');
    if(p)
        p++;
    else
        p = name;

    int l = strlen(p);
    if(l <= 0)
        return;
    l--;

    if(p[l] == '6')
        af = AF_INET6;
    else if(p[l] == '4')
        af = AF_INET;

    if(!strncmp(p, "tcp", 3))
        module = "tcp";
    if(!strncmp(p, "tracert", 7))
        module = "icmp";
}

static int getaddr(const char *name, sockaddr_any *addr) 
{
    struct addrinfo hints;
    struct addrinfo* ai = NULL;
    struct addrinfo* res = NULL;

    memset(&hints, 0, sizeof(hints));
    hints.ai_family = af;
    hints.ai_flags = AI_IDN;

    int ret = getaddrinfo(name, NULL, &hints, &res);
    if(ret) {
        fprintf(stderr, "%s: %s\n", name, gai_strerror(ret));
        return -1;
    }

    for(ai = res; ai; ai = ai->ai_next) {
        if(ai->ai_family == af)
            break;
        /*  when af not specified, choose DEF_AF if present   */
        if(!af && ai->ai_family == DEF_AF)
            break;
    }
    if(!ai)
        ai = res;    /*  anything...  */

    if(ai->ai_addrlen > sizeof(*addr))
        return -1;    /*  paranoia   */
    memcpy(addr, ai->ai_addr, ai->ai_addrlen);

    freeaddrinfo(res);

    /*  No v4 mapped addresses in real network, interpret it as ipv4 anyway   */
    if(addr->sa.sa_family == AF_INET6 && IN6_IS_ADDR_V4MAPPED(&addr->sin6.sin6_addr)) {
        if(af == AF_INET6)  return -1;
        addr->sa.sa_family = AF_INET;
        addr->sin.sin_addr.s_addr = addr->sin6.sin6_addr.s6_addr32[3];
    }

    return 0;
}

static void make_fd_used(int fd) 
{
    if(fcntl(fd, F_GETFL) != -1)
        return;

    if(errno != EBADF)
        error("fcntl F_GETFL");

    int nfd = open("/dev/null", O_RDONLY);
    if(nfd < 0)
        error("open /dev/null");

    if(nfd != fd) {
        dup2(nfd, fd);
        close(nfd);
    }
}

static char addr2str_buf[INET6_ADDRSTRLEN];

static const char *addr2str(const sockaddr_any *addr) 
{
    getnameinfo(&addr->sa, sizeof(*addr), addr2str_buf, sizeof(addr2str_buf), 0, 0, NI_NUMERICHOST);
    return addr2str_buf;
}

/*    IP  options  stuff        */
static void init_ip_options(void) 
{
    sockaddr_any *gates;
    int i;
    int max;

    if(!num_gateways)
        return;

    /*  check for TYPE,ADDR,ADDR... form   */
    if(af == AF_INET6 && num_gateways > 1 && gateways[0]) {
        char* q;
        unsigned int value = strtoul(gateways[0], &q, 0);

        if(!*q) {
            ipv6_rthdr_type = value;
            num_gateways--;
            for(i = 0; i < num_gateways; i++)
                gateways[i] = gateways[i + 1];
        }
    }

    max = af == AF_INET ? MAX_GATEWAYS_4 : MAX_GATEWAYS_6;
    if(num_gateways > max)
        ex_error("Too many gateways specified. No more than %d", max);

    gates = alloca(num_gateways * sizeof(*gates));

    for(i = 0; i < num_gateways; i++) {
        if(!gateways[i])
            error("strdup");

        if(getaddr(gateways[i], &gates[i]) < 0)
            ex_error("");    /*  already reported   */
        if(gates[i].sa.sa_family != af)
            ex_error("IP versions mismatch in gateway addresses");

        free(gateways[i]);
    }

    free(gateways);
    gateways = NULL;

    if(af == AF_INET) {
        struct in_addr *in;

        rtbuf_len = 4 +(num_gateways + 1) * sizeof(*in);
        rtbuf = malloc(rtbuf_len);
        if(!rtbuf)  error("malloc");

        in = (struct in_addr *) &rtbuf[4];
        for(i = 0; i < num_gateways; i++)
            memcpy(&in[i], &gates[i].sin.sin_addr, sizeof(*in));
        /*  final hop   */
        memcpy(&in[i], &dst_addr.sin.sin_addr, sizeof(*in));
        i++;

        rtbuf[0] = IPOPT_NOP;
        rtbuf[1] = IPOPT_LSRR;
        rtbuf[2] = (i * sizeof(*in)) + 3;
        rtbuf[3] = IPOPT_MINOFF;
    } else if(af == AF_INET6) {
        struct in6_addr *in6;
        struct ip6_rthdr *rth;

        /*  IPV6_RTHDR_TYPE_0 length is 8   */
        rtbuf_len = 8 + num_gateways * sizeof(*in6);
        rtbuf = malloc(rtbuf_len);
        if(!rtbuf)  error("malloc");

        rth = (struct ip6_rthdr*)rtbuf;
        rth->ip6r_nxt = 0;
        rth->ip6r_len = 2 * num_gateways;
        rth->ip6r_type = ipv6_rthdr_type;
        rth->ip6r_segleft = num_gateways;

        *((uint32_t *)(rth + 1)) = 0;

        in6 = (struct in6_addr *)(rtbuf + 8);
        for(i = 0; i < num_gateways; i++)
            memcpy(&in6[i], &gates[i].sin6.sin6_addr, sizeof(*in6));
    }
}

/*    Command line stuff        */
static int set_af(CLIF_option* optn, char* arg) 
{
    int vers = (long) optn->data;

    if(vers == 4)
        af = AF_INET;
    else if(vers == 6)
        af = AF_INET6;
    else
        return -1;
    return 0;
}

static int add_gateway(CLIF_option *optn, char *arg) 
{
    if(num_gateways >= MAX_GATEWAYS_6) {    /*  127 > 8 ... :)   */
        fprintf(stderr, "Too many gateways specified.");
        return -1;
    }

    gateways = realloc(gateways,(num_gateways + 1) * sizeof(*gateways));
    if(!gateways)
        error("malloc");
    gateways[num_gateways++] = strdup(arg);

    return 0;
}

static int set_source(CLIF_option *optn, char *arg) 
{
    return getaddr(arg, &src_addr);
}

static int set_port(CLIF_option *optn, char *arg) 
{
    unsigned int *up = (unsigned int *)optn->data;
    char *q;

    *up = strtoul(arg, &q, 0);
    if(q == arg) {
        struct servent *s = getservbyname(arg, NULL);

        if(!s)
            return -1;
        *up = ntohs(s->s_port);
    }

    return 0;
}

static int set_module(CLIF_option *optn, char *arg) 
{
    module = (char *) optn->data;
    return 0;
}

static int set_mod_option(CLIF_option *optn, char *arg) 
{
    if(!strcmp(arg, "help")) {
        const tr_module *mod = tr_get_module(module);

        if(mod && mod->options) {
            /*  just to set common keyword flag...  */
            CLIF_parse(1, &arg, 0, 0, CLIF_KEYWORD);
            CLIF_print_options(NULL, mod->options);
        } else {
            fprintf(stderr, "No options for module `%s'\n", module);
        }

        exit(0);
    }

    if(opts_idx >= sizeof(opts) / sizeof(*opts))  {
        fprintf(stderr, "Too many module options\n");
        return -1;
    }

    opts[opts_idx] = strdup(arg);
    if(!opts[opts_idx])
        error("strdup");
    opts_idx++;

    return 0;
}

static int set_raw(CLIF_option *optn, char *arg) 
{
    char buf[1024];

    module = "raw";

    snprintf(buf, sizeof(buf), "protocol=%s", arg);
    return set_mod_option(optn, buf);
}

static int set_wait_specs(CLIF_option *optn, char *arg) 
{
    char *p, *q;

    here_factor = near_factor = 0;

    wait_secs = strtod(p = arg, &q);
    if(q == p)
        return -1;
    if(!*q++)
        return 0;

    here_factor = strtod(p = q, &q);
    if(q == p)
        return -1;
    if(!*q++)
        return 0;

    near_factor = strtod(p = q, &q);
    if(q == p || *q)
        return -1;

    return 0;
}

static int set_host(CLIF_argument *argm, char *arg, int index) 
{
    if(getaddr(arg, &dst_addr) < 0)
        return -1;

    dst_name = arg;

    /*  i.e., guess it by the addr in cmdline...  */
    if(!af)  
        af = dst_addr.sa.sa_family;

    return 0;
}

int allowed_icmp(char* bufp)
{
    if(af == AF_INET) {
        struct iphdr* outer_ip = (struct iphdr*)bufp;
        struct icmphdr* outer_icmp = (struct icmphdr*)(bufp + (outer_ip->ihl << 2));
        switch(outer_icmp->type)
        {
            case ICMP_TIME_EXCEEDED:
            case ICMP_DEST_UNREACH:
            {
                return 1;
            }
            default:
            {
                return 0;
            }
        }
    } else if(af == AF_INET6) {
        struct icmp6_hdr* outer_icmp = (struct icmp6_hdr*)bufp;
        switch(outer_icmp->icmp6_type)
        {
            case ICMP6_TIME_EXCEEDED:
            case ICMP6_DST_UNREACH:
            {
                return 1;
            }
            default:
            {
                return 0;
            }
        }
    } else {
        return 0;
    }
}

static CLIF_option option_list[] = {
    { "4", 0, 0, "Use IPv4", set_af, (void *) 4, 0, CLIF_EXTRA },
    { "6", 0, 0, "Use IPv6", set_af, (void *) 6, 0, 0 },
    { "d", "debug", 0, "Enable socket level debugging", CLIF_set_flag, &debug, 0, 0 },
    { "F", "dont-fragment", 0, "Do not fragment packets", CLIF_set_flag, &dontfrag, 0, CLIF_ABBREV },
    { "f", "first", "first_ttl", "Start from the %s hop (instead from 1)", CLIF_set_uint16, &first_hop, 0, 0 },
    { "g", "gateway", "gate", "Route packets through the specified gateway (maximum " _TEXT(MAX_GATEWAYS_4) " for IPv4 and " _TEXT(MAX_GATEWAYS_6) " for IPv6)", add_gateway, 0, 0, CLIF_SEVERAL },
    { "H", "failures", "hop failures", "Set a max number of hop not replying before exiting, max is "_TEXT(MAX_HOP_FAILURES), CLIF_set_uint16, &max_consecutive_hop_failures, 0, 0 },
    { "I", "icmp", 0, "Use ICMP ECHO for tracerouting", set_module, "icmp", 0, 0 },
    { "i", "interface", "device", "Specify a network interface to operate with", CLIF_set_string, &device, 0, 0 },
    { "m", "max-hops", "max_ttl", "Set the max number of hops (max TTL to be reached). Default is " _TEXT(DEF_HOPS) ,
            CLIF_set_uint16, &max_hops, 0, 0 },
    { "N", "sim-queries", "squeries", "Set the number of probes to be tried simultaneously (default is " _TEXT(DEF_SIM_PROBES) ")", CLIF_set_uint16, &sim_probes, 0, 0 },
    { "n", 0, 0, "Do not resolve IP addresses to their domain names", CLIF_set_flag, &noresolve, 0, 0 },
    { "p", "port", "port", "Set the destination port to use. It is either initial udp port value for \"default\" method(incremented by each probe, default is " _TEXT(DEF_START_PORT) "), or initial seq for \"icmp\"(incremented as well, default from 1), or some constant destination port for other methods(with default of " _TEXT(DEF_TCP_PORT) " for \"tcp\", " _TEXT(DEF_UDP_PORT) " for \"udp\", etc.)", set_port, &dst_port_seq, 0, 0 },
    { "t", "tos", "num", "Set the TOS (IPv4 type of service) or TC (IPv6 traffic class) value for outgoing packets. This option excludes --dscp and --ecn. Allowed values are between 0 and 255", CLIF_set_uint16, &tos_input_value, 0, 0 },
    { "l", "flowlabel", "flow_label", "Use specified %s for IPv6 packets", CLIF_set_uint16, &flow_label, 0, 0 },
    { "w", "wait", "MAX,HERE,NEAR", "Wait for a probe no more than HERE (default " _TEXT(DEF_HERE_FACTOR) ") times longer than a response from the same hop, or no more than NEAR(default " _TEXT(DEF_NEAR_FACTOR) ") times than some next hop, or MAX(default " _TEXT(DEF_WAIT_SECS) ") seconds (float point values allowed too)", set_wait_specs, 0, 0, 0 },
    { "Q", "timeout", "timeout", "Set a max timeout for traceroute to be completed (max 65535 seconds)", CLIF_set_uint16, &overall_timeout, 0, 0 },
    { "q", "queries", "nqueries", "Set the number of probes per each hop. Default is " _TEXT(DEF_NUM_PROBES)", max is " _TEXT(MAX_PROBES), CLIF_set_uint16, &probes_per_hop, 0, 0 },
    { "r", 0, 0, "Bypass the normal routing and send directly to a host on an attached network", CLIF_set_flag, &noroute, 0, 0 },
    { "s", "source", "src_addr", "Use source %s for outgoing packets", set_source, 0, 0, 0 },
    { "T", "tcp", 0, "Use TCP SYN for tracerouting (default port is " _TEXT(DEF_TCP_PORT) ")", set_module, "tcp", 0, 0 },
    { "z", "sendwait", "sendwait", "Minimal time interval between probes (default " _TEXT(DEF_SEND_SECS) "). If the value is more than 10, then it specifies a number in milliseconds, else it is a number of seconds (float point values allowed too)", CLIF_set_double, &send_secs, 0, 0 },
    { "e", "extensions", 0, "Show ICMP extensions(if present), including MPLS", CLIF_set_flag, &extension, 0, CLIF_ABBREV },
    { "A", "as-path-lookups", 0, "Perform AS path lookups in routing registries and print results directly after the corresponding addresses", CLIF_set_flag, &as_lookups, 0, 0 },
    { "M", "module", "name", "Use specified module(either builtin or external) for traceroute operations. Most methods have their shortcuts(`-I' means `-M icmp' etc.)", CLIF_set_string, &module, 0, CLIF_EXTRA },
    { "O", "options", "OPTS", "Use module-specific option %s for the traceroute module. Several %s allowed, separated by comma. If %s is \"help\", print info about available options", set_mod_option, 0, 0, CLIF_SEVERAL | CLIF_EXTRA },
    { 0, "sport", "num", "Use source port %s for outgoing packets. Implies `-N 1'", set_port, &src_port, 0, CLIF_EXTRA },
#ifdef SO_MARK
    { 0, "fwmark", "num", "Set firewall mark for outgoing packets", CLIF_set_uint16, &fwmark, 0, 0 },
#endif
    { "U", "udp", 0, "Use UDP to particular port for tracerouting (instead of increasing the port per each probe), default port is " _TEXT(DEF_UDP_PORT), set_module, "udp", 0, CLIF_EXTRA },
    { 0, "UL", 0, "Use UDPLITE for tracerouting(default dest port is " _TEXT(DEF_UDP_PORT) ")", set_module, "udplite", 0, CLIF_ONEDASH|CLIF_EXTRA },
    { "D", "dccp", 0, "Use DCCP Request for tracerouting (default port is " _TEXT(DEF_DCCP_PORT) ")", set_module, "dccp", 0, CLIF_EXTRA },
    { "P", "protocol", "prot", "Use raw packet of protocol %s for tracerouting", set_raw, 0, 0, CLIF_EXTRA },
    { 0, "mtu", 0, "Discover MTU along the path being traced. Implies `-F -N 1'", CLIF_set_flag, &mtudisc, 0, CLIF_EXTRA },
    { 0, "back", 0, "Guess the number of hops in the backward path and print if it differs", CLIF_set_flag, &backward, 0, CLIF_EXTRA },
    { 0, "tcpinsession", 0, "Run in TCP InSession mode", set_module, "tcpinsession", 0, 0 },
    { 0, "dscp", "num", "Set the DSCP bits into the IP header. This option excludes -t (--tos) and might be used in conjunction with --ecn. Allowed values are between 0 and 63", CLIF_set_uint16, &dscp_input_value, 0, 0 },
    { 0, "ecn", "num", "Set the ECN bits into the IP header. This option excludes -t (--tos) and might be used in conjunction with --dscp. Allowed values are between 0 and 3", CLIF_set_uint16, &ecn_input_value, 0, 0 },
    { 0, "quic", 0, "Use QUIC to particular port for tracerouting, default port is " _TEXT(DEF_QUIC_PORT), set_module, "quic", 0, CLIF_EXTRA },
    { 0, "loose-match", 0, "Enable loose-match mode", CLIF_set_flag, &loose_match, 0, CLIF_EXTRA },
    { 0, "disable-extra-ping", 0, "Disable additional ping performed at the end (if any)", CLIF_set_flag, &disable_extra_ping, 0, CLIF_EXTRA },
    CLIF_VERSION_OPTION(version_string),
    CLIF_HELP_OPTION,
    CLIF_END_OPTION
};

static CLIF_argument arg_list[] = {
    { "host", "The host to traceroute to", set_host, 0, CLIF_STRICT },
    { "packetlen", "The full packet length(default is the length of an IP header plus " _TEXT(DEF_DATA_LEN) "). Can be ignored or increased to a minimal allowed value", CLIF_arg_int, &packet_len, 0 },
    CLIF_END_ARGUMENT
};

unsigned int compute_data_len(int packet_len)
{
    int data_len = 0;
    
    if(packet_len < 0) {
     #ifdef HAVE_OPENSSL3
        if(strcmp(module, "quic") == 0) {
            data_len = DEF_DATA_LEN_QUIC;
        } else if(strcmp(module, "tcpinsession") == 0) {
            data_len = DEF_DATA_LEN_TCPINSESSION;
        } else {
            if(DEF_DATA_LEN >= ops->header_len)
                data_len = DEF_DATA_LEN - ops->header_len;
        }
    #else
        if(strcmp(module, "tcpinsession") == 0) {
            data_len = DEF_DATA_LEN_TCPINSESSION;
        } else {
            if(DEF_DATA_LEN >= ops->header_len)
                data_len = DEF_DATA_LEN - ops->header_len;
        }
    #endif
    } else {
        if(packet_len >= header_len)
            data_len = packet_len - header_len;
        else
            data_len = packet_len;
    }
    
    return data_len;
}

/*    PRINT  STUFF        */
static void print_header(void) 
{
    /*  Note, without ending new-line!  */
    printf("traceroute to %s(%s), %u hops max, %zu byte packets, ", dst_name, addr2str(&dst_addr), max_hops, header_len + data_len);
    
    if(overall_timeout > 0)
        printf("%us overall timeout", overall_timeout);
    else
        printf("overall timeout not set");
        
    fflush(stdout);
}

static void do_it(void);

static void poll_callback(int fd, int revents) 
{
    ops->recv_probe(fd, revents);
}

int main(int argc, char *argv[]) 
{
    setlocale(LC_ALL, "");
    setlocale(LC_NUMERIC, "C");    /*  avoid commas in msec printed  */

    check_progname(argv[0]);

    if(CLIF_parse(argc, argv, option_list, arg_list, CLIF_MAY_JOIN_ARG | CLIF_HELP_EMPTY) < 0)
        exit(2);

#ifndef HAVE_OPENSSL3
    if(strcmp(module, "quic") == 0) {
        printf("Traceroute QUIC is not available as this binary was compiled without openssl3 linking.\n");
        exit(1);
    }
#endif

#ifdef __APPLE__
    if(strcmp(module, "tcpinsession") == 0) {
        printf("Traceroute TCP InSession is not yet available on MacOS.\n");
        exit(1);
    }
    
    if(strcmp(module, "tcp") == 0) {
        printf("Traceroute TCP is not yet available on MacOS.\n");
        exit(1);
    }
    
    if(mtudisc) {
        printf("Path MTU discovery is not yet available on MacOS.\n");
        exit(1);
    }
#endif

    ops = tr_get_module(module);
    if(!ops)
        ex_error("Unknown traceroute module %s", module);

    if(!first_hop || first_hop > max_hops)
        ex_error("first hop out of range");
    if(max_hops > MAX_HOPS)
        ex_error("max hops cannot be more than " _TEXT(MAX_HOPS));
    if(probes_per_hop > MAX_PROBES)
        ex_error("no more than " _TEXT(MAX_PROBES) " probes per hop");
    if(!probes_per_hop)
       ex_error("Need to have at least 1 probe per hop");
    if(wait_secs < 0 || here_factor < 0 || near_factor < 0)
        ex_error("bad wait specifications `%g,%g,%g' used", wait_secs, here_factor, near_factor);
    if(packet_len > MAX_PACKET_LEN)
        ex_error("too big packetlen %d specified", packet_len);
    if(src_addr.sa.sa_family && src_addr.sa.sa_family != af)
        ex_error("IP version mismatch in addresses specified");
    if(send_secs < 0)
        ex_error("bad sendtime `%g' specified", send_secs);
    if(send_secs >= 10)    /*  it is milliseconds   */
        send_secs /= 1000;
    if(max_consecutive_hop_failures <= 0 || max_consecutive_hop_failures > MAX_HOP_FAILURES)
        ex_error("max consecutive hop failures cannot be more than " _TEXT(MAX_HOP_FAILURES));
    if(max_consecutive_hop_failures > 0)
        sim_probes =(sim_probes > max_consecutive_hop_failures*probes_per_hop) ? max_consecutive_hop_failures*probes_per_hop : sim_probes; // This to avoid to exceed the hard limit set with -failures

    if(tos_input_value != -1 && (dscp_input_value != -1 || ecn_input_value != -1)) {
        ex_error("tos cannot be used in conjunction with dscp and ecn");
    } else if(dscp_input_value != -1 || ecn_input_value != -1) {
        if(dscp_input_value != -1)
            tos = dscp_input_value;
        else
            tos = 0;

        tos <<= 2;
            
        if(ecn_input_value >= 0 && ecn_input_value <= 3)
            tos += ecn_input_value;
        else if(ecn_input_value != -1) // If a value of ECN is provided and is not in acceptable range do error
            ex_error("ECN supplied value is not in range [0-3]");
            
        tos_input_value = tos;
        use_additional_raw_icmp_socket = 1;
    } else if(tos_input_value != -1) {
        tos = tos_input_value;
        use_additional_raw_icmp_socket = 1;
    }
    
    if(loose_match)
        use_additional_raw_icmp_socket = 1;
    
    if(af == AF_INET6 && (tos || flow_label))
        dst_addr.sin6.sin6_flowinfo = htonl(((tos & 0xff) << 20) |(flow_label & 0x000fffff));

    if(src_port) {
        src_addr.sin.sin_port = htons((uint16_t) src_port);
        src_addr.sa.sa_family = af;
    }

    if(src_port || ops->one_per_time) {
        sim_probes = 1;
        here_factor = near_factor = 0;
    }

    /*  make sure we don't std{in,out,err} to open sockets  */
    make_fd_used(0);
    make_fd_used(1);
    make_fd_used(2);

    init_ip_options();

    header_len = (af == AF_INET ? sizeof(struct iphdr) : sizeof(struct ip6_hdr)) + rtbuf_len + ops->header_len;

    data_len = compute_data_len(packet_len);

    saved_max_hops = max_hops;
    saved_first_hop = first_hop;
    saved_sim_probes = sim_probes;
    
    if(mtudisc) {
        mtudisc_phase = 1;
        dontfrag = 1;
        sim_probes = 1;
        data_len = compute_data_len(MAX_PACKET_LEN);
    }

#ifdef __APPLE__
    tr_via_additional_raw_icmp_socket = 1;
    use_additional_raw_icmp_socket = 1;
#endif

    if(strcmp(module, "tcpinsession") == 0) {
        max_hops = 255;
        first_hop = 255;
        sim_probes = 1;
        tcpinsession_print_allowed = 0;
        
        tcpinsession_destination_probes = calloc(probes_per_hop, sizeof(probe));
        if(!tcpinsession_destination_probes)
            error("calloc");
    }

    num_probes = max_hops * probes_per_hop;
    probes = calloc(num_probes, sizeof(*probes));
    if(!probes)
        error("calloc");

#ifdef __APPLE__
    probe_semaphore = dispatch_semaphore_create(0);
#else
    sem_init(&probe_semaphore, 0, 0);
#endif

    if(ops->options && opts_idx > 1) {
        opts[0] = strdup(module);        /*  aka argv[0] ...  */
        if(CLIF_parse(opts_idx, opts, ops->options, 0, CLIF_KEYWORD) < 0)
            exit(2);
    }
    
    print_header();

    if(ops->init(&dst_addr, dst_port_seq, &data_len) < 0)
        ex_error("trace method's init failed");
        
    if(strcmp(module, "tcpinsession") == 0) { // Only in this module we need to run an initial ping in the very same TCP session
        data_len = DEF_DATA_LEN_TCPINSESSION;
        do_it();
        
        int start = 254 * probes_per_hop;
        for(int idx = 0; idx < probes_per_hop; idx++)
            memcpy(tcpinsession_destination_probes+idx, &probes[start+idx], sizeof(probe));
        
        if(last_probe == -1) // The destination did not reply with any TCP message back to our gaps
            tcpinsession_print_allowed = 1;
        
        memset(probes, 0x0, sizeof(*probes)*num_probes); // Reset the content of all probes used so far

        if(!mtudisc)
            sim_probes = saved_sim_probes; // In case of mtudisc we still need to use 1 probe for the initial part of the algorithm

        data_len = compute_data_len(packet_len); // After the pre-send, restore the probe size to whatever the user decided (or the default)
        last_probe = -1;
        max_hops = saved_max_hops;
        first_hop = saved_first_hop;

        num_probes = max_hops * probes_per_hop; // Recompute the max probes with the original value of "max_hops"

        destination_reached = 0;
      #ifdef __APPLE__
        probe_semaphore = dispatch_semaphore_create(0);
      #else
        sem_init(&probe_semaphore, 0, 0);  // Ignore the destination probes at the moment
      #endif
    }
    
    if(pthread_create(&printer_thr, NULL, printer, NULL) != 0)
        ex_error("printer thread creation failed");

    if(mtudisc) {
        data_len = compute_data_len(MAX_PACKET_LEN);
        
        int i = 0;
        while(!probes[0].final) {
            i++;
            ops->send_probe(&probes[0], 255);
            
            do_poll(wait_secs, poll_callback);
            
            if(probes[0].err_str[0] && strlen(probes[0].err_str) > 2) {
                overall_mtu = atoi(probes[0].err_str+2);
                memset(&probes[0], 0x0, sizeof(probe));
            } else if(!probes[0].done && i <= MAX_MTU_RETRIES) {
                probe_done(&probes[0], NULL);
                break;
            }
        }
        
        if(probes[0].final)
            reliable_overall_mtu = 1;

        memset(&probes[0], 0x0, sizeof(probe));
        
        data_len = compute_data_len(MAX_PACKET_LEN); // After the initial "MTU Discovery Pings" restart doing traceroute from the MAX_PACKET_LEN until the bootleneck is found
    }

    mtudisc_phase = 0;
    
    do_it();

    pthread_join(printer_thr, NULL);

    if(!disable_extra_ping && destination_reached && ops->need_extra_ping && ops->need_extra_ping()) {
        if(ops->setup_extra_ping() != 0)
            error("error while setting up extra_ping");
        
        free(probes);
        
        extra_ping_ongoing = 1;
        first_hop = 255;
        max_hops = 255;
        num_probes = max_hops * probes_per_hop;
        probes = calloc(num_probes, sizeof(*probes));
        
        do_it();
        
        int start = (first_hop - 1) * probes_per_hop;
        for(int i = start; i < num_probes; i++)
            print_probe(&probes[i]);
    }
    
    // Make extra-sure to not leave any FD open
    for(int i = 0; i < num_probes; i++)
        if(probes[i].sk > 0)
            close(probes[i].sk);

    print_trailer();
    
    return 0;
}

static void print_addr(sockaddr_any *res)
{
    const char *str;

    if(!res->sa.sa_family)
        return;

    str = addr2str(res);

    if(noresolve) {
        printf(" %s", str);
    } else {
        unsigned int do_not_resolve_due_to_timeout = 0;
        if(overall_timeout > 0) {
            struct timeval currtime;
            gettimeofday(&currtime, NULL);
            
            if(currtime.tv_sec-starttime.tv_sec >= overall_timeout)
                do_not_resolve_due_to_timeout = 1;
        }
        
        char buf[1024];

        buf[0] = '\0';

        if(do_not_resolve_due_to_timeout == 0)
            getnameinfo(&res->sa, sizeof(*res), buf, sizeof(buf), 0, 0, NI_IDN);
        printf(" %s (%s)", buf[0] ? buf : str, str);
    }

    if(as_lookups)
        printf(" [%s]", get_as_path(str));
}

void print_probe(probe *pb) 
{
    if(strcmp(module, "tcpinsession") == 0 && tcpinsession_print_allowed == 0)
        return;
        
    unsigned int idx = (pb - probes);
    unsigned int ttl = idx / probes_per_hop + 1;
    unsigned int np = idx % probes_per_hop;

    if(np == 0) {
        printf("\n");
        if(extra_ping_ongoing == 0)
            printf("%4u ", ttl);
        else
            printf("+%3u ", last_hop_reached);
    }

    if(!pb->res.sa.sa_family) {
        printf(" *");
    } else {
        int prn = !np;    /*  print if the first...  */
        if(np) {        /*  ...and if differs with previous   */
            probe *p;

            /*  skip expired   */
            for(p = pb - 1; np && !p->res.sa.sa_family; p--, np--);

            if(!np || !equal_addr(&p->res, &pb->res) || (p->ext != pb->ext && !(p->ext && pb->ext && !strcmp(p->ext, pb->ext))) || (backward && p->recv_ttl != pb->recv_ttl))
                prn = 1;
        }

        if(prn) {
            print_addr(&pb->res);
            if(pb->ext) {
                printf(" <%s>", pb->ext);
                free(pb->ext);
                pb->ext = NULL;
            }

            if(backward && pb->recv_ttl) {
                int hops = ttl2hops(pb->recv_ttl);
                if(hops != ttl)
                    printf(" '-%d'", hops);
            }
        }

        if(pb->proto_details != NULL) {
            printf(" <%s>", pb->proto_details);
            free(pb->proto_details);
            pb->proto_details = NULL;
        }

        if(tos_input_value >= 0 && !pb->final) {
            uint8_t ecn = pb->returned_tos & 3;
            uint8_t dscp = ((pb->returned_tos - ecn) >> 2);
            printf(" <TOS:%d,DSCP:%d,ECN:%d>", pb->returned_tos, dscp, ecn);
        }
    }

    if(pb->recv_time) {
        double diff = pb->recv_time - pb->send_time;
        #ifdef HAVE_OPENSSL3
            if(pb->retry_rtt) {
                switch(quic_print_dest_rtt_mode)
                {
                    case QUIC_PRINT_DEST_RTT_ALL:
                    {
                        printf("  %.3f+%.3f ms", diff * 1000, pb->retry_rtt*1000);
                        break;
                    }
                    case QUIC_PRINT_DEST_RTT_FIRST:
                    {
                        printf("  %.3f ms", pb->retry_rtt*1000);
                        break;
                    }
                    case QUIC_PRINT_DEST_RTT_LAST:
                    {
                        printf("  %.3f ms", diff * 1000);
                        break;
                    }
                    case QUIC_PRINT_DEST_RTT_SUM:
                    {
                        printf("  %.3f ms", (diff + pb->retry_rtt)* 1000);
                        break;
                    }
                    default:
                    {
                        printf("  %.3f+%.3f ms", diff * 1000, pb->retry_rtt*1000);
                        break;
                    }
                }
            } else {
                printf("  %.3f ms", diff * 1000);
            }
        #else
            printf("  %.3f ms", diff * 1000);
        #endif
    }

    if(pb->err_str[0])
        printf(" %s", pb->err_str);

    fflush(stdout);
}

/*    Compute timeout stuff   */
static double get_timeout(probe *pb) 
{
    double value;

    if(here_factor) {
        /*  check for already replied from the same hop   */
        int i, idx = (pb - probes);
        probe *p = &probes[idx - (idx % probes_per_hop)];

        for(i = 0; i < probes_per_hop; i++, p++) {
            /*   `p == pb' skipped since  !pb->done   */

            if(p->done && (value = p->recv_time - p->send_time) > 0) {
                value += DEF_WAIT_PREC;
                value *= here_factor;
                return value < wait_secs ? value : wait_secs;
            }
        }
    }

    if(near_factor) {
        /*  check forward for already replied   */
        probe *p, *endp = probes + num_probes;

        for(p = pb + 1; p < endp && p->send_time; p++) {
            if(p->done &&(value = p->recv_time - p->send_time) > 0) {
                value += DEF_WAIT_PREC;
                value *= near_factor;
                return value < wait_secs ? value : wait_secs;
            }
        }
    }

    return wait_secs;
}

/*    Check  expiration  stuff    */
static void check_expired(probe *pb) 
{
    int idx = (pb - probes);
    probe *p, *endp = probes + num_probes;
    probe *fp = NULL, *pfp = NULL;

    if(!pb->done)        /*  an ops method still not release it  */
        return;

    /*  check all the previous in the same hop   */
    for(p = &probes[idx -(idx % probes_per_hop)]; p < pb; p++) {
        if(!p->done || !p->final)       /*  too early to decide something OR already ttl-exceeded in the same hop  */
            return;

        pfp = p;    /*  some of the previous probes is final   */
    }

    /*  check forward all the sent probes   */
    for(p = pb + 1; p < endp && p->send_time; p++) {
        if(p->done) {    /*  some next probe already done...  */
            if(!p->final) {    /*  ...was ttl-exceeded. OK, we are expired.  */
                return;
            } else {
                fp = p;
                break;
            }
        }
    }

    if(!fp)    /*  no any final probe found. Assume expired.   */
        return;

    /*  Well. There is a situation "* (this) * * * * ... * * final"
       We cannot guarantee that "final" is in its right place.
       We've sent "sim_probes" simultaneously, and the final hop
       can drop some of them and answer only for latest ones.
       If we can detect/assume that it so, then just put "final"
       to the(pseudo-expired) "this" place.
    */

    /*  It seems that the case of "answers for latest ones only"
       occurs mostly with icmp_unreach error answers ("!H" etc.).
       Icmp_echoreply, tcp_reset and even icmp_port_unreach looks
       like going in the right order.
     */
    if(!fp->err_str[0])    /*  not an icmp_unreach error report...  */
        return;

    if(pfp || (idx % probes_per_hop) +(fp - pb) < probes_per_hop) {
        /*  Either some previous(pfp) or some next probe
        in this hop is final. It means that the whole hop is final.
        Do the replace(it also causes further "final"s to be shifted
        here too).
        */
        goto replace_by_final;
    }

    /*  If the final probe is an icmp_unreachable report
      (either in a case of some error, like "!H", or just port_unreach),
        it could follow the "time-exceed" report from the *same* hop.
    */
    for(p = pb - 1; p >= probes; p--) {
        if(equal_addr(&p->res, &fp->res)) {
            /*  ...Yes. Put "final" to the "this" place.  */
            goto replace_by_final;
        }
    }

    if(fp->recv_ttl) {
        /*  Consider the ttl value of the report packet and guess where
        the "final" should be. If it seems that it should be
        in the same hop as "this", then do replace.
        */
        int back_hops, ttl;

        /*  We assume that the reporting one has an initial ttl value
        of either 64, or 128, or 255. It is most widely used
        in the modern routers and computers.
        The idea comes from tracepath(1) routine.
        */
        back_hops = ttl2hops(fp->recv_ttl);

        /*  It is possible that the back path differs from the forward
        and therefore has different number of hops. To minimize
        such an influence, get the nearest previous time-exceeded
        probe and compare with it.
        */
        for(p = pb - 1; p >= probes; p--) {
            if(p->done && !p->final && p->recv_ttl) {
                int hops = ttl2hops(p->recv_ttl);

                if(hops < back_hops) {
                    ttl = (p - probes) / probes_per_hop + 1;
                    back_hops = (back_hops - hops) + ttl;
                    break;
                }
            }
        }

        ttl = idx / probes_per_hop + 1;
        if(back_hops == ttl) /*  Yes! It seems that "final" should be at "this" place   */
            goto replace_by_final;
        else if(back_hops < ttl) /*  Hmmm... Assume better to replace here too...  */
            goto replace_by_final;
    }

    /*  No idea what to do. Assume expired.  */

    return;

replace_by_final:

    *pb = *fp;

    memset(fp, 0, sizeof(*fp));
    /*  block extra re-send  */
    fp->send_time = 1.;
}

probe *probe_by_seq(int seq) 
{
    if(seq == 0)
        return NULL;

    for(int n = 0; n < num_probes; n++) {
        if(probes[n].seq == seq)
            return &probes[n];
    }

    return NULL;
}

probe* probe_by_seq_num(uint32_t seq_num) 
{
    for(int n = 0; n < num_probes; n++)
        if(probes[n].seq_num == seq_num)
            return &probes[n];

    return NULL;
}

probe *probe_by_sk(int sk) 
{
    int n;

    if(sk <= 0)
        return NULL;

    for(n = 0; n < num_probes; n++) {
        if(probes[n].sk == sk)
            return &probes[n];
    }

    return NULL;
}

int equal_port(const sockaddr_any* a, const sockaddr_any* b) 
{
    if(!a->sa.sa_family)
        return 0;

    if(a->sa.sa_family != b->sa.sa_family)
        return 0;

    if(a->sa.sa_family == AF_INET6)
        return (a->sin6.sin6_port == b->sin6.sin6_port);
    else
        return (a->sin.sin_port == b->sin.sin_port);
    return 0;    /*  not reached   */
}

// if check_source_addr is false, the source IP address is not compared, however the source port is still compared
// This is useful in those environment where for some reason the source IP of the offendig probe is not translated properly back.
probe* probe_by_src_and_dest(sockaddr_any* src, sockaddr_any* dest, int check_source_addr) 
{
    for(int n = 0; n < num_probes; n++) {
        if(!equal_sockaddr(dest, &probes[n].dest))
            continue;

        if(check_source_addr) {
            if(equal_sockaddr(src, &probes[n].src))
                return (probes[n].seq == 0) ? NULL : &probes[n];
        } else {
            if(equal_port(src, &probes[n].src))
                return (probes[n].seq == 0) ? NULL : &probes[n];
        }
    }
    
    return NULL;
}

static void do_it(void) 
{
    int start = (first_hop - 1) * probes_per_hop;
    int end = num_probes;
    double last_send = 0;
    
    gettimeofday(&starttime, NULL);

    while(start < end) {
        int n = 0;
        int num = 0;
        double next_time = 0;
        double now_time = get_time();
        
        int exit_please = 0;

        for(n = start; n < end && exit_please == 0; n++) {
            if(overall_timeout > 0) {
                struct timeval currtime;
                gettimeofday(&currtime, NULL);
                
                if(currtime.tv_sec-starttime.tv_sec >= overall_timeout) {
                    if(n < end) {
                        probes[n].exit_please = 1;
                        #ifdef __APPLE__
                            dispatch_semaphore_signal(probe_semaphore);
                        #else
                            sem_post(&probe_semaphore);
                        #endif
                    }
                    timedout = 1;
                    break;
                }
            }
            
            probe *pb = &probes[n];

            if(n == start && !pb->done && pb->send_time) { /*  probably time to print, but yet not replied   */
                double expire_time = pb->send_time + get_timeout(pb);
                if(expire_time > now_time) {
                    next_time = expire_time;
                } else {
                    probe_done(pb, NULL);
                    check_expired(pb);
                }
            }
            
            if(mtudisc && sim_probes == 1 && pb->err_str[0]) {
                destination_reached = 0; // Any unreachability means we didn't get to destination!
                int mtu_value = atoi(pb->err_str+2);
                if(strlen(pb->err_str) > 2 && overall_mtu >= mtu_value) {
                    if(overall_mtu > mtu_value)
                        overall_mtu = mtu_value;
                    dontfrag = 0;
                    sim_probes = saved_sim_probes;
                    data_len = compute_data_len(packet_len); // We found the bottleneck hop, we can restart doing simulatneous traceroute sending probes of the default size or the one provided in input
                }
            }

            if(pb->done) {
                if(n == start) {    /*  can print it now   */
                    if(pb->final && pb->res.sa.sa_family && equal_addr(&pb->res, &dst_addr))
                        destination_reached = 1;
                    
                    if(!pb->res.sa.sa_family)
                        consecutive_probe_failures++;
                    else
                        consecutive_probe_failures = 0;
                    
                #ifdef __APPLE__
                    dispatch_semaphore_signal(probe_semaphore);
                #else
                    sem_post(&probe_semaphore);
                #endif
                    
                    if(max_consecutive_hop_failures >= 0 && max_consecutive_hop_failures <= (consecutive_probe_failures/probes_per_hop)) {
                        if(n+1 < end) {
                            probes[n+1].exit_please = 1;
                        #ifdef __APPLE__
                            dispatch_semaphore_signal(probe_semaphore);
                        #else
                            sem_post(&probe_semaphore);
                        #endif
                        }
                        
                        if(strcmp(module, "tcpinsession") == 0)
                            destination_reached = 0;
                        
                        exit_please = 1;
                    }                    
                    
                    start++;
                }
                if(pb->final) {
                    end = (n / probes_per_hop + 1) * probes_per_hop;
                    last_probe = end;
                }

                continue;
            }

            if(!pb->send_time) {
                double next;

                if(send_secs &&(next = last_send + send_secs) > now_time) {
                    next_time = next;
                    break;
                }

                int ttl = n / probes_per_hop + 1;

                pb->mss = 0;
                pb->mtu = 0;

                ops->send_probe(pb, ttl);

                if(!pb->send_time) {
                    if(next_time)
                        break;    /*  have chances later   */
                    else 
                        error("send probe");
                }

                last_send = pb->send_time;
            }

            if(!next_time)
                next_time = pb->send_time + get_timeout(pb);

            num++;
            if(num >= sim_probes)
                break;
        }

        if(timedout > 0 || exit_please > 0)
            break;

        if(next_time) {
            double timeout = next_time - get_time();
            if(timeout < 0)
                timeout = 0;

            if(overall_timeout > 0) {
                struct timeval currtime;
                gettimeofday(&currtime, NULL);

                double missing_time = overall_timeout;
                missing_time -= currtime.tv_sec-starttime.tv_sec;
                double decimals = 0;
                if(currtime.tv_usec < starttime.tv_usec) {
                    missing_time -= 1;
                    decimals = starttime.tv_usec - currtime.tv_usec;
                } else {
                    decimals = currtime.tv_usec - starttime.tv_usec;
                }
                decimals /= 1000;
                decimals /= 1000;
                missing_time -= decimals;

                missing_time = (missing_time < 0) ? 0 : missing_time;
                do_poll((missing_time > timeout) ? timeout : missing_time, poll_callback);                
            } else {
                do_poll(timeout, poll_callback);
            }
        }
    }
}

static void print_trailer()
{
    struct timeval endtime;
    gettimeofday(&endtime, NULL);
    
    struct timeval elapsedtime;
    
    timersub(&endtime, &starttime, &elapsedtime);
    
    float msec_elapsed = elapsedtime.tv_usec % 1000;
    msec_elapsed /= 1000; // Move microseconds
    msec_elapsed += elapsedtime.tv_sec * 1000; // Add seconds
    msec_elapsed += elapsedtime.tv_usec / 1000; // Add milliseconds
    
    if(ops->close)
        ops->close();

    printf("\n   Timedout: %s", (timedout == 1) ? "true" : "false");
    printf("\n   Duration: %0.3f ms", msec_elapsed);
    printf("\n   DestinationReached: %s", (destination_reached == 1) ? "true" : "false");

    if(overall_mtu > 0) {
        if(reliable_overall_mtu > 0)
            printf("\n   Path MTU: %d", overall_mtu);
        else
            printf("\n   Path MTU: %d (Potentially overestimated)", overall_mtu);
    }
    
    print_end();

    fflush(stdout);
}

void tune_socket(int sk) 
{
    int i = 0;

    if(debug) {
        i = 1;
        if(setsockopt(sk, SOL_SOCKET, SO_DEBUG, &i, sizeof(i)) < 0)
            error("setsockopt SO_DEBUG");
    }

#ifdef SO_MARK
    if(fwmark) {
        if(setsockopt(sk, SOL_SOCKET, SO_MARK,
                    &fwmark, sizeof(fwmark)) < 0
        )  error("setsockopt SO_MARK");
    }
#endif

    if(rtbuf && rtbuf_len) {
        if(af == AF_INET) {
            if(setsockopt(sk, IPPROTO_IP, IP_OPTIONS, rtbuf, rtbuf_len) < 0)
                error("setsockopt IP_OPTIONS");
        } else if(af == AF_INET6) {
            if(setsockopt(sk, IPPROTO_IPV6, IPV6_RTHDR, rtbuf, rtbuf_len) < 0)
                error("setsockopt IPV6_RTHDR");
        }
    }

    bind_socket(sk);

    if(af == AF_INET) {
      #ifdef __APPLE__
        if(dontfrag && setsockopt(sk, IPPROTO_IP, IP_DONTFRAG, &i, sizeof(i)) < 0)
            error("setsockopt IP_DONTFRAG");
      #else
        i = dontfrag ? IP_PMTUDISC_PROBE : IP_PMTUDISC_DONT;
        if(setsockopt(sk, SOL_IP, IP_MTU_DISCOVER, &i, sizeof(i)) < 0 && (!dontfrag ||(i = IP_PMTUDISC_DO, setsockopt(sk, SOL_IP, IP_MTU_DISCOVER, &i, sizeof(i)) < 0)))
            error("setsockopt IP_MTU_DISCOVER");
      #endif
        if(tos) {
            i = tos;
            if(setsockopt(sk, SOL_IP, IP_TOS, &i, sizeof(i)) < 0)
                error("setsockopt IP_TOS");
        }
    } else if(af == AF_INET6) {
        i = dontfrag ? IPV6_PMTUDISC_PROBE : IPV6_PMTUDISC_DONT;
        if(setsockopt(sk, SOL_IPV6, IPV6_MTU_DISCOVER,&i,sizeof(i)) < 0 && (!dontfrag ||(i = IPV6_PMTUDISC_DO, setsockopt(sk, SOL_IPV6, IPV6_MTU_DISCOVER,&i,sizeof(i)) < 0)))
            error("setsockopt IPV6_MTU_DISCOVER");

        if(flow_label) {
            struct in6_flowlabel_req flr;

            memset(&flr, 0, sizeof(flr));
            flr.flr_label = htonl(flow_label & 0x000fffff);
            flr.flr_action = IPV6_FL_A_GET;
            flr.flr_flags = IPV6_FL_F_CREATE;
            flr.flr_share = IPV6_FL_S_ANY;
            memcpy(&flr.flr_dst, &dst_addr.sin6.sin6_addr, sizeof(flr.flr_dst));

            if(setsockopt(sk, IPPROTO_IPV6, IPV6_FLOWLABEL_MGR, &flr, sizeof(flr)) < 0)
                error("setsockopt IPV6_FLOWLABEL_MGR");
        }

        if(tos) {
            i = tos;
            if(setsockopt(sk, IPPROTO_IPV6, IPV6_TCLASS, &i, sizeof(i)) < 0)
                error("setsockopt IPV6_TCLASS");
        }

        if(tos || flow_label) {
            i = 1;
            if(setsockopt(sk, IPPROTO_IPV6, IPV6_FLOWINFO_SEND, &i, sizeof(i)) < 0) 
                error("setsockopt IPV6_FLOWINFO_SEND");
        }
    }

    if(noroute) {
        i = noroute;
        if(setsockopt(sk, SOL_SOCKET, SO_DONTROUTE, &i, sizeof(i)) < 0)
            error("setsockopt SO_DONTROUTE");
    }

    use_timestamp(sk);

    use_recv_ttl(sk);

    fcntl(sk, F_SETFL, O_NONBLOCK);
}

void parse_icmp_res(probe *pb, int type, int code, int info) 
{
    char *str = NULL;
    char buf[sizeof(pb->err_str)];

    if(af == AF_INET) {
        if(type == ICMP_TIME_EXCEEDED) {
            if(code == ICMP_EXC_TTL)
                return;
        }  else if(type == ICMP_DEST_UNREACH) {
            switch(code) {
                case ICMP_UNREACH_NET:
                case ICMP_UNREACH_NET_UNKNOWN:
                case ICMP_UNREACH_ISOLATED:
                case ICMP_UNREACH_TOSNET:
                {
                    str = "!N";
                    break;
                }
                case ICMP_UNREACH_HOST:
                case ICMP_UNREACH_HOST_UNKNOWN:
                case ICMP_UNREACH_TOSHOST:
                {
                    str = "!H";
                    break;
                }
                case ICMP_UNREACH_NET_PROHIB:
                case ICMP_UNREACH_HOST_PROHIB:
                case ICMP_UNREACH_FILTER_PROHIB:
                {
                    str = "!X";
                    break;
                }
                case ICMP_UNREACH_PORT:
                {
                    /*  dest host is reached   */
                    str = "";
                    break;
                }
                case ICMP_UNREACH_PROTOCOL:
                {
                    str = "!P";
                    break;
                }
                case ICMP_UNREACH_NEEDFRAG:
                {
                    snprintf(buf, sizeof(buf), "!F-%d", info);
                    str = buf;
                    break;
                }
                case ICMP_UNREACH_SRCFAIL:
                {
                    str = "!S";
                    break;
                }
                case ICMP_UNREACH_HOST_PRECEDENCE:
                {
                    str = "!V";
                    break;
                }
                case ICMP_UNREACH_PRECEDENCE_CUTOFF:
                {
                    str = "!C";
                    break;
                }
                default:
                {
                    snprintf(buf, sizeof(buf), "!<%u>", code);
                    str = buf;
                    break;
                }
            }
        }
    } else if(af == AF_INET6) {
        if(type == ICMP6_TIME_EXCEEDED) {
            if(code == ICMP6_TIME_EXCEED_TRANSIT)
                return;
        } else if(type == ICMP6_DST_UNREACH) {
            switch(code) 
            {
                case ICMP6_DST_UNREACH_NOROUTE:
                {
                    str = "!N";
                    break;
                }
                case ICMP6_DST_UNREACH_BEYONDSCOPE:
                case ICMP6_DST_UNREACH_ADDR:
                {
                    str = "!H";
                    break;
                }
                case ICMP6_DST_UNREACH_ADMIN:
                {
                    str = "!X";
                    break;
                }
                case ICMP6_DST_UNREACH_NOPORT:
                {
                    /*  dest host is reached   */
                    str = "";
                    break;
                }
                default:
                {
                    snprintf(buf, sizeof(buf), "!<%u>", code);
                    str = buf;
                    break;
                }
            }
        } else if(type == ICMP6_PACKET_TOO_BIG) {
            snprintf(buf, sizeof(buf), "!F-%d", info);
            str = buf;
        }
    }

    if(!str) {
        snprintf(buf, sizeof(buf), "!<%u-%u>", type, code);
        str = buf;
    }

    if(*str) {
        strncpy(pb->err_str, str, sizeof(pb->err_str));
        pb->err_str[sizeof(pb->err_str) - 1] = '\0';
    }

    pb->final = 1;
}

static void parse_local_res(probe *pb, int ee_errno, int info) 
{
    if(ee_errno == EMSGSIZE && info != 0) {
        snprintf(pb->err_str, sizeof(pb->err_str)-1, "!F-%d", info);
        pb->final = 1;
        return;
    }

    errno = ee_errno;
    error("local recverr");
}

void probe_done(probe* pb, int* what) 
{
    if(what != NULL)
        *what = 1;
        
    // Note that we are not interested in TOS for last hop, so if the probe is declared final, we skip it
    // Note also that what is NULL when probe is considered to be expired, thus we can proceed with closing the socket
    if(what == NULL || pb->final == 1 || (pb->proto_done == 1 && pb->icmp_done == 1)) {
        if(pb->sk) {
            del_poll(pb->sk);
            if(pb->sk != -1)
                close(pb->sk);
            pb->sk = 0;
        }

        pb->seq = 0;
        pb->done = 1;
    }
}

void extract_ip_info(int family, char* bufp, int* proto, sockaddr_any* src, sockaddr_any* dst, void** offending_probe, int* probe_tos)
{
    if(family == AF_INET) {
        struct iphdr* outer_ip = (struct iphdr*)bufp;
        struct iphdr* inner_ip = (struct iphdr*)(bufp + (outer_ip->ihl << 2) + sizeof(struct icmphdr));
        
        *proto = inner_ip->protocol;
        
        *offending_probe = (void *)(bufp + (outer_ip->ihl << 2) + sizeof(struct icmphdr) + (inner_ip->ihl << 2));
        
        memset(dst, 0, sizeof(sockaddr_any));
        dst->sin.sin_family = AF_INET;
        dst->sin.sin_addr.s_addr = inner_ip->daddr;
        
        memset(src, 0, sizeof(sockaddr_any));
        src->sin.sin_family = AF_INET;
        src->sin.sin_addr.s_addr = inner_ip->saddr;
        
        *probe_tos = inner_ip->tos;
    } else if(family == AF_INET6) {
        struct ip6_hdr* inner_ip = (struct ip6_hdr*) (bufp + sizeof(struct icmp6_hdr));
        *proto = inner_ip->ip6_ctlun.ip6_un1.ip6_un1_nxt;
        
        *offending_probe = (void *) (bufp + sizeof(struct icmp6_hdr) + sizeof(struct ip6_hdr));
        
        memset(dst, 0, sizeof(sockaddr_any));
        dst->sin6.sin6_family = AF_INET6;
        memcpy(&dst->sin6.sin6_addr, &inner_ip->ip6_dst, sizeof(dst->sin6.sin6_addr));
        
        memset(src, 0, sizeof(sockaddr_any));
        src->sin6.sin6_family = AF_INET6;
        memcpy(&src->sin6.sin6_addr, &inner_ip->ip6_src, sizeof(src->sin6.sin6_addr));
        
        uint32_t tmp = ntohl(inner_ip->ip6_ctlun.ip6_un1.ip6_un1_flow);
        tmp &= 0x0fffffff;
        tmp >>= 20; 
        
        *probe_tos = (uint8_t)tmp;
    }
}

uint16_t prepare_ancillary_data(int family, char* bufp, uint16_t inner_proto_hlen, struct msghdr* ret, sockaddr_any* offender)
{
    if(family == AF_INET) {
        struct iphdr* outer_ip = (struct iphdr*)bufp;
        struct icmphdr* outer_icmp = (struct icmphdr*)(bufp + (outer_ip->ihl << 2));
        
        // pre-alloc for all the errors that tr is handling, which are [SOL_SOCKET-SO_TIMESTAMP] + [SOL_IP-IP_TTL] + [SOL_IP-IP_RECVERR]
        // IP_RECVERR data is composed by a sock_extended_err followed by a sockaddr_in (the address of the offender), see ip_recv_error@ip_sockglue.c.
        // About the spaced occupied by IP_TTL: The cmsglen is 20, but the actual data is 24 bytes, (because CMSG_SPACE(sizeof(int)) = 24, while CMSG_LEN(sizeof(int)) = 20. See put_cmsg@net/core/scm.c
        // Also the global msg_controllen contains the computation with CMSG_SPACE, while the individual cmsg_len the actual data to read, which is the result of CMSG_LEN See put_cmsg@net/core/scm.c
        // In summary, CMSG_LEN is used to indicate the amount to read, while CMSG_SPACE is used to reserve the actual space 
        ret->msg_controllen = CMSG_SPACE(sizeof(struct timeval)) + CMSG_SPACE(sizeof(int)) + CMSG_SPACE(sizeof(struct sock_extended_err) + sizeof(struct sockaddr_in));

        // prepare the pointers to respective headers and data
        struct cmsghdr* cmsghdr_so_timestamp = (struct cmsghdr*)ret->msg_control;
        struct cmsghdr* cmsghdr_ip_ttl = (struct cmsghdr*)(((char *)cmsghdr_so_timestamp) + CMSG_SPACE(sizeof(struct timeval)));
        struct cmsghdr* cmsghdr_so_ip_recverr = (struct cmsghdr*)(((char *)cmsghdr_ip_ttl) + CMSG_SPACE(sizeof(int)));
        
        // data pointers
        struct timeval* data_so_timestamp = (struct timeval*)((char *)cmsghdr_so_timestamp + sizeof(struct cmsghdr));
        int* data_ip_ttl = (int *)((char *)cmsghdr_ip_ttl + sizeof(struct cmsghdr));
        struct sock_extended_err* data_ip_recv_err_serr = (struct sock_extended_err*)((char *)cmsghdr_so_ip_recverr + sizeof(struct cmsghdr));
        struct sockaddr_in* data_ip_recv_err_offender = (struct sockaddr_in*)(data_ip_recv_err_serr+1);
        
        // SO_TIMESTAMP
        // See __sock_recv_timestamp@socket.c
        cmsghdr_so_timestamp->cmsg_len = CMSG_LEN(sizeof(struct timeval));
        cmsghdr_so_timestamp->cmsg_level = SOL_SOCKET;
        cmsghdr_so_timestamp->cmsg_type = SO_TIMESTAMP;
        gettimeofday(data_so_timestamp, NULL);
        
        // IP_TTL
        cmsghdr_ip_ttl->cmsg_len = CMSG_LEN(sizeof(int));
        cmsghdr_ip_ttl->cmsg_level = SOL_IP;
        cmsghdr_ip_ttl->cmsg_type = IP_TTL;
        // In kernel this is done by ip_cmsg_recv_ttl @net/ipv4/ip_sockglue.c
        // The trace looks like this: SYS_recvmsg->inet_recvmsg->raw_recvmsg->ip_recv_error->ip_cmsg_recv_ttl (inferred as it is a static function)
        // Note that we need to put the outer_ip TTL (not the ojne of the encapsulated probe)
        *data_ip_ttl = outer_ip->ttl;
        
        // IP_RECVERR 
        cmsghdr_so_ip_recverr->cmsg_len = CMSG_LEN(sizeof(struct sock_extended_err) + sizeof(struct sockaddr_in));
        cmsghdr_so_ip_recverr->cmsg_level = SOL_IP;
        cmsghdr_so_ip_recverr->cmsg_type = IP_RECVERR;
        // In kernel this is filled by the ip_icmp_error @net/ipv4/ip_sockglue.c
        // NOTE: this is executed independently from the recvmsg.
        // The trace looks like this: ip_rcv->ip_rcv_finish->ip_local_deliver->ip_local_deliver_finish->icmp_rcv->icmp_unreach->icmp_socket_deliver->raw_icmp_error->raw_err->ip_icmp_error
        
        // Set data_ip_recv_err->ee_errno like raw_err@raw.c:232
        // Also, set `info` like icmp_unreach@icmp.c:801
        // Note that this info is propagated up to ip_icmp_error as argument
        int err = 0;
        uint32_t info = 0;
        int has_recv_err = 1;
        switch(outer_icmp->type)
        {
            case ICMP_ECHOREPLY:
            {
                // No IP_RECVERR in case of ECHO REPLY
                has_recv_err = 0;
                ret->msg_controllen -= CMSG_SPACE(sizeof(struct sock_extended_err) + sizeof(struct sockaddr_in)); // Do not return the ee if there is no error (this would be a mistake)
                break;
            }
            case ICMP_TIME_EXCEEDED:
            {
                err = EHOSTUNREACH;
                break;
            }
            case ICMP_SOURCE_QUENCH:
            {
                return 0; // TODO Thus reset the ret?
            }
            case ICMP_PARAMETERPROB:
            {
                err = EPROTO;
                info = ntohl(outer_icmp->un.gateway) >> 24; // See icmp_unreach@icmp.c
                break;
            }
            case ICMP_DEST_UNREACH:
            {
                // See icmp_unreach@icmp.c
                switch(outer_icmp->code & 15)
                {
                    case ICMP_NET_UNREACH:
                    case ICMP_HOST_UNREACH:
                    case ICMP_PROT_UNREACH:
                    case ICMP_PORT_UNREACH:
                    {
                        break;
                    }
                    case ICMP_FRAG_NEEDED: // This can be probably moved below, however moving it after the outer_icmp->code bound check is not equivalent to what is being done into the kernel, so leaving it here
                    {
                        // Always report mtu info
                        info = ntohs(outer_icmp->un.frag.mtu); 
                        break;
                    }
                }
                
                // See raw_err@raw.c
                err = EHOSTUNREACH;
                if(outer_icmp->code > sizeof(icmp4_err_convert) / sizeof(struct icmp4_err) - 1) // NR_ICMP_UNREACH is defined as 15 in include/net/icmp.
                    break;
                err = icmp4_err_convert[outer_icmp->code].error;
                if(outer_icmp->code == ICMP_FRAG_NEEDED)
                    err = EMSGSIZE;
                
                break;
            }
            default:
            {
                err = EHOSTUNREACH;
                break;
            }
        }
        
        if(has_recv_err) {
            // See ip_icmp_error@ip_sockglue.c
            data_ip_recv_err_serr->ee_errno = err;
            data_ip_recv_err_serr->ee_origin = SO_EE_ORIGIN_ICMP;
            data_ip_recv_err_serr->ee_type = outer_icmp->type;
            data_ip_recv_err_serr->ee_code = outer_icmp->code;
            data_ip_recv_err_serr->ee_pad = 0;
            data_ip_recv_err_serr->ee_info = info;
            data_ip_recv_err_serr->ee_data = 0;
        }
        
        // Now we have to do two things, see ip_recv_error@ip_sockglue.c
        // 1. Fill the ret msg_name
        // 2. Fill the offender address of the IP_RECVERR data
        
        struct sockaddr_in *sin = (struct sockaddr_in *)ret->msg_name;
        sin->sin_family = AF_INET;
        sin->sin_port = 0; // This is left to be zero, see the call to ip_icmp_error in raw_err@raw.c (This is the parameter after "err"). In any case it is not used by tr.
        // NOTE: in the ip_recv_error the address put in s_addr is what is found at the "addr_offset" which is set in ip_icmp_error@ip_sockglue.c. This offset is the offset of the destination address of the packet incapsulated into the ICMP payload.
        // NOTE: That this is equivalent to our dst_addr.sin.sin_addr.s_addr.
        // NOTE: This is not true fror ICMP_ECHOREPLY, in this case the from is the source address of the reply
        if(has_recv_err)
            sin->sin_addr.s_addr = ((struct iphdr*)(outer_icmp + 1))->daddr;
        else
            sin->sin_addr.s_addr = outer_ip->saddr;
        memset(&sin->sin_zero, 0, sizeof(sin->sin_zero));
        ret->msg_namelen = sizeof(*sin);
        
        // Fill the offender
        if(has_recv_err) {
            struct iphdr* inner_ip = (struct iphdr*)(bufp + (outer_ip->ihl << 2) + sizeof(struct icmphdr));
        
            data_ip_recv_err_offender->sin_family = AF_INET;
            data_ip_recv_err_offender->sin_addr.s_addr = outer_ip->saddr;
            
            // Return also the payload of the offending probe (and extensions, if present)
            uint16_t tot_len = ntohs(outer_ip->tot_len);
            uint16_t icmp_len = tot_len - (outer_ip->ihl << 2);
            uint16_t icmp_payload_len = icmp_len - sizeof(struct icmphdr);
            uint8_t* payload_ptr = ((uint8_t*)outer_icmp + sizeof(struct icmphdr));
            payload_ptr += (inner_ip->ihl << 2);
            payload_ptr += inner_proto_hlen;
            
            memcpy(ret->msg_iov->iov_base, payload_ptr, (icmp_payload_len > ret->msg_iov->iov_len) ? ret->msg_iov->iov_len : icmp_payload_len);
            
            return (outer_ip->ihl << 2) + sizeof(struct icmphdr) + (inner_ip->ihl << 2) + inner_proto_hlen;
        }
        
        return (outer_ip->ihl << 2) + sizeof(struct icmphdr);
    } else {
        struct icmp6_hdr* outer_icmp = (struct icmp6_hdr*)bufp;
        
        // pre-alloc for all the errors that tr is handling, which are [SOL_IPV6-IPV6_HOPLIMIT] + [SOL_IPV6-IPV6_RECVERR]
        // IPV6_RECVERR data is composed by a sock_extended_err followed by a sockaddr_in6 (the address of the offender), see ipv6_recv_error@ipv6/datagram.c.
        // About the spaced occupied by IPV6_HOPLIMIT: the cmsglen is 20, but the actual data is 24 bytes, (because CMSG_SPACE(sizeof(int)) = 24, while CMSG_LEN(sizeof(int)) = 20. See put_cmsg@net/core/scm.c
        // Also the global msg_controllen contains the computation with CMSG_SPACE, while the individual cmsg_len the actual data to read, so the result of CMS_LEN See put_cmsg@net/core/scm.c
        // So it appears that CMSG_LEN is used to indicate the amount to read, while CMSG_SPACE is used to reserve the actual space 
        ret->msg_controllen = CMSG_SPACE(sizeof(int)) + CMSG_SPACE(sizeof(struct sock_extended_err) + sizeof(struct sockaddr_in6));
        
        // prepare the pointers to respective headers and data
        struct cmsghdr* cmsghdr_ipv6_hoplimit = (struct cmsghdr*)ret->msg_control;
        struct cmsghdr* cmsghdr_ipv6_recverr = (struct cmsghdr*)(((char *)cmsghdr_ipv6_hoplimit) + CMSG_SPACE(sizeof(int)));
        
        int* data_ip_ttl = (int *)((char *)cmsghdr_ipv6_hoplimit + sizeof(struct cmsghdr));
        struct sock_extended_err* data_ip_recv_err_serr = (struct sock_extended_err*)((char *)cmsghdr_ipv6_recverr + sizeof(struct cmsghdr));
        struct sockaddr_in6* data_ip_recv_err_offender = (struct sockaddr_in6*)(data_ip_recv_err_serr+1);
        
        // IPV6_HOPLIMIT
        cmsghdr_ipv6_hoplimit->cmsg_len = CMSG_LEN(sizeof(int));
        cmsghdr_ipv6_hoplimit->cmsg_level = SOL_IPV6;
        cmsghdr_ipv6_hoplimit->cmsg_type = IPV6_HOPLIMIT;
        // In kernel this is done by ip_cmsg_recv_ttl @net/ipv6/ipv6_sockglue.c
        // Note that we need to put the OUTER IP TTL
        *data_ip_ttl = 0; // This would be outer_ip->ttl, but we cannot do that without the IP header. This means that we can't use "backward" tr option.
        
        // IPV6_RECVERR 
        cmsghdr_ipv6_recverr->cmsg_len = CMSG_LEN(sizeof(struct sock_extended_err) + sizeof(struct sockaddr_in6));
        cmsghdr_ipv6_recverr->cmsg_level = SOL_IPV6;
        cmsghdr_ipv6_recverr->cmsg_type = IPV6_RECVERR;
        // In kernel this is filled by the ipv6_recv_error@net/ipv6/datagram.c
        
        // Set data_ip_recv_err->ee_errno like icmpv6_err_convert@net/ipv6/icmp.c:232
        // (called by rawv6_err@net/ipv6/raw.c, called by raw6_icmp_error@net/ipv6/raw.c, raw6_icmp_error@net/ipv6/icmp.c, icmpv6_notify@icmpv6_notify.c)
        // Note that rawv6_err does a ntohl of info
        // Also, et info like icmpv6_rcv@net/ipv6/icmp.c:801
        // Note that this info is propagated up to ip_icmp_error as argument
        int err = 0;
        uint32_t info = 0;
        int has_recv_err = 1;
        switch(outer_icmp->icmp6_type)
        {
            case ICMP6_ECHO_REPLY:
            {
                // No IPV6_RECVERR in case of ECHO REPLY
                has_recv_err = 0;
                ret->msg_controllen -= CMSG_SPACE(sizeof(struct sock_extended_err) + sizeof(struct sockaddr_in6)); // Do not return the ee if there is no error (this would be a mistake)
                break;
            }
            case ICMP6_TIME_EXCEEDED:
            {
                err = EHOSTUNREACH;
                info = ntohl(outer_icmp->icmp6_mtu);
                break;
            }
            case ICMP6_PACKET_TOO_BIG:
            {
                err = EMSGSIZE;
                break;
            }
            case ICMP6_PARAM_PROB:
            {
                err = EPROTO;
                info = ntohl(outer_icmp->icmp6_mtu);
                break;
            }
            case ICMP6_DST_UNREACH:
            {
                info = ntohl(outer_icmp->icmp6_mtu);
                // See icmpv6_err_convert@net/ipv6/icmp.c
                err = EPROTO;
                if(outer_icmp->icmp6_code > sizeof(icmp6_err_convert)/sizeof(struct icmp6_err)) 
                    break;
                err = icmp6_err_convert[outer_icmp->icmp6_code].err;
                
                break;
            }
            default:
            {
                err = EPROTO;
                break;
            }
        }
        
        if(has_recv_err) {
        // See ipv6_icmp_error@net/ipv6/datagram.c
            data_ip_recv_err_serr->ee_errno = err;
            data_ip_recv_err_serr->ee_origin = SO_EE_ORIGIN_ICMP6;
            data_ip_recv_err_serr->ee_type = outer_icmp->icmp6_type;
            data_ip_recv_err_serr->ee_code = outer_icmp->icmp6_code;
            data_ip_recv_err_serr->ee_pad = 0;
            data_ip_recv_err_serr->ee_info = info;
            data_ip_recv_err_serr->ee_data = 0;
        }
        
        // Now we have to do two things, see ip_recv_error@ip_sockglue.c
        
        // 1. Fill the offender address of the IP_RECVERR data
        // Since we do not have the IP header, we need to rely on the offender given in input.
        // Note that the "offender" given in input is contained into ret->msg_name, so we need to use it before overwriting ret->msg_name at point 2.
        struct ip6_hdr* inner_ip = NULL;
        if(has_recv_err) {
            data_ip_recv_err_offender->sin6_family = AF_INET6; 
            memcpy(data_ip_recv_err_offender->sin6_addr.s6_addr, ((struct sockaddr_in6*)offender)->sin6_addr.s6_addr, sizeof((data_ip_recv_err_offender->sin6_addr.s6_addr)));
            
            // Return the expected payload
            inner_ip = (struct ip6_hdr*) (bufp + sizeof(struct icmp6_hdr));
            uint8_t* payload_ptr = ((uint8_t*)inner_ip + sizeof(struct ip6_hdr) + inner_proto_hlen);
            memcpy(ret->msg_iov->iov_base, payload_ptr, ret->msg_iov->iov_len);
            
            return sizeof(struct ip6_hdr) + sizeof(struct icmp6_hdr) + inner_proto_hlen;
        }
        
        // 2. Fill the ret msg_name
        struct sockaddr_in6 *sin = (struct sockaddr_in6 *)ret->msg_name;
        sin->sin6_family = AF_INET6;
        sin->sin6_flowinfo = 0; // This seems to be zero, see the ipv6_recv_error@net/ipv6/datagram.c
        sin->sin6_port = 0; // This the destination port of the inner protocol header (if any).  See ipv6_recv_error@net/ipv6/datagram.c:425 and 293. This is not really useful here, so left zero.
        // NOTE: in the ip_recv_error the address put in s_addr is what is found at the "addr_offset" which is set in ipv6_icmp_error@datagram.c. This offset is the offset of the destination address of the packet incapsulated into the ICMP payload.
        // NOTE That this is equivalent to our dst_addr
        // NOTE this is not true fror ICMP_ECHOREPLY, in this case the from is the source address of the reply
        if(has_recv_err)
            memcpy(sin->sin6_addr.s6_addr, inner_ip->ip6_dst.s6_addr, sizeof(sin->sin6_addr.s6_addr));
        else
            memcpy(sin->sin6_addr.s6_addr, ((struct sockaddr_in6*)offender)->sin6_addr.s6_addr, sizeof(sin->sin6_addr.s6_addr));
        ret->msg_namelen = sizeof(*sin);
        
        return sizeof(struct ip6_hdr) + sizeof(struct icmp6_hdr) + inner_proto_hlen;
    }
    
    return 0;
}


void recv_reply(int sk, int err, check_reply_t check_reply) 
{
    struct msghdr msg;
    sockaddr_any from;
    struct iovec iov;
    int n;
    probe *pb;
    char buf[1280];        /*  min mtu for ipv6( >= 576 for ipv4)  */
    char *bufp = buf;
    char control[1024];
    struct cmsghdr *cm;
    double recv_time = 0;
    int recv_ttl = 0;
    struct sock_extended_err *ee = NULL;

    memset(&msg, 0, sizeof(msg));
    msg.msg_name = &from;
    msg.msg_namelen = sizeof(from);
    msg.msg_control = control;
    msg.msg_controllen = sizeof(control);
    iov.iov_base = buf;
    iov.iov_len = sizeof(buf);
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;

    n = recvmsg(sk, &msg, err ? MSG_ERRQUEUE : 0);
    if(n < 0)
        return;

    if(ops->is_raw_icmp_sk(sk) == 1) {
        struct msghdr cust_msg;
        memset(&cust_msg, 0, sizeof(cust_msg));
        
        cust_msg.msg_name = &from;
        cust_msg.msg_namelen = sizeof(from);
        
        char buf[1280];
        memset(&buf, 0, sizeof(buf));
        
        char cust_control[1024];
        memset(cust_control, 0, sizeof(cust_control));
        
        struct iovec iov;
        iov.iov_base = buf;
        iov.iov_len = sizeof(buf);
        
        cust_msg.msg_iov = &iov;
        cust_msg.msg_iovlen = 1;
        cust_msg.msg_control = &cust_control;
        cust_msg.msg_controllen = sizeof(cust_control);
        
        uint16_t overhead = 0; // from where the payload of the returned messages is supposed to start
        
        if(allowed_icmp(bufp) == 0)
            return;
        
        pb = ops->handle_raw_icmp_packet(bufp, &overhead, &msg, &cust_msg);
        if(!pb)
            return;
        
        // If we are not running in "Lose match mode" nor via re using the additional raw icmp socket to do traceroute, then the handle raw icmp is used only to assign the ToS to the probe, do not use it for anything more
        if(!loose_match && !tr_via_additional_raw_icmp_socket)
            return;
        
        msg = cust_msg;
        bufp = cust_msg.msg_iov->iov_base;
        n -= overhead;
    }
    
    /*  when not MSG_ERRQUEUE, AF_INET returns full ipv4 header
        on raw sockets...
    */

    if(!err && ops->is_raw_icmp_sk(sk) == 0 && af == AF_INET && ops->header_len == 0) { /*  XXX: Assume that the presence of an extra header means that it is not a raw socket... */
        struct iphdr *ip = (struct iphdr *) bufp;
        int hlen;

        if(n < sizeof(struct iphdr))
            return;

        hlen = ip->ihl << 2;
        if(n < hlen)
            return;

        bufp += hlen;
        n -= hlen;
    }

    if(ops->is_raw_icmp_sk(sk) == 0) {
        pb = check_reply(sk, err, &from, bufp, n);
        if(!pb) {
            /*  for `frag needed' case at the local host,
            kernel >= 3.13 sends local error(no more icmp)
            */
            if(!n && err && dontfrag) {
                pb = &probes[(first_hop - 1) * probes_per_hop];
                if(pb->done)
                    return;
            } else {
                return;
            }
        }
    }

    // Do not proceed for expired probes.
    // We could end up here even if the probe is expired when we are using the additional raw_icmp_socket because no del_poll is called on that socket when the probe expired, so a packet that comes after the timeout is still received and processed
    if(pb && pb->done)
        return;

    /*  Parse CMSG stuff   */

    for(cm = CMSG_FIRSTHDR(&msg); cm; cm = CMSG_NXTHDR(&msg, cm)) {
        void *ptr = CMSG_DATA(cm);

        if(cm->cmsg_level == SOL_SOCKET) {
            if(cm->cmsg_type == SO_TIMESTAMP) {
                struct timeval *tv = (struct timeval *) ptr;
                recv_time = tv->tv_sec + tv->tv_usec / 1000000.;
            }
        } else if(cm->cmsg_level == SOL_IP) {
            if(cm->cmsg_type == IP_TTL)
                recv_ttl = *((int *) ptr);
            else if(cm->cmsg_type == IP_RECVERR) {
                ee = (struct sock_extended_err *) ptr;

                if(ee->ee_origin != SO_EE_ORIGIN_ICMP && ee->ee_origin != SO_EE_ORIGIN_LOCAL) 
                    return;

                /*  dgram icmp sockets might return extra things...  */
                if(ee->ee_origin == SO_EE_ORIGIN_ICMP && (ee->ee_type == ICMP_SOURCE_QUENCH || ee->ee_type == ICMP_REDIRECT))
                    return;
            }
        } else if(cm->cmsg_level == SOL_IPV6) {
            if(cm->cmsg_type == IPV6_HOPLIMIT) {
                recv_ttl = *((int *) ptr);
            } else if(cm->cmsg_type == IPV6_RECVERR) {
                ee = (struct sock_extended_err *) ptr;

                if(ee->ee_origin != SO_EE_ORIGIN_ICMP6 && ee->ee_origin != SO_EE_ORIGIN_LOCAL)
                    return;
            }
        }
    }

    if(!recv_time)
        recv_time = get_time();

    if(!err)
        memcpy(&pb->res, &from, sizeof(pb->res));

    pb->recv_time = recv_time;
    pb->recv_ttl = recv_ttl;

    if(ee && ee->ee_origin != SO_EE_ORIGIN_LOCAL) {    /*  icmp or icmp6   */
        memcpy(&pb->res, SO_EE_OFFENDER(ee), sizeof(pb->res));
        parse_icmp_res(pb, ee->ee_type, ee->ee_code, ee->ee_info);
    }

    if(ee && ee->ee_origin == SO_EE_ORIGIN_LOCAL)
        parse_local_res(pb, ee->ee_errno, ee->ee_info);

    if(ee && mtudisc && ee->ee_info >= header_len && ee->ee_info < header_len + data_len) {
        data_len = ee->ee_info - header_len;

        probe_done(pb, &pb->proto_done);
        if(!use_additional_raw_icmp_socket)
            probe_done(pb, &pb->icmp_done);
            
        /*  clear this probe(as actually the previous hop answers here)
          but fill its `err_str' by the info obtained. Ugly, but easy...
        */
        memset(pb, 0, sizeof(*pb));
        snprintf(pb->err_str, sizeof(pb->err_str)-1, "F=%d", ee->ee_info);

        return;
    }

    /*  at least...(rfc4884)  */
    if(ee && extension && header_len + n >= (128 + 8) && header_len <= 128 && ((af == AF_INET &&(ee->ee_type == ICMP_TIME_EXCEEDED || ee->ee_type == ICMP_DEST_UNREACH || ee->ee_type == ICMP_PARAMETERPROB)) || (af == AF_INET6 &&(ee->ee_type == ICMP6_TIME_EXCEEDED || ee->ee_type == ICMP6_DST_UNREACH)))) {
        int step;
        int offs = 128 - header_len;

        if(n > data_len)
            step = 0;    /*  guaranteed at 128 ...  */
        else
            step = af == AF_INET ? 4 : 8;

        handle_extensions(pb, bufp + offs, n - offs, step);
    }

    probe_done(pb, &pb->proto_done);
    if(!use_additional_raw_icmp_socket)
        probe_done(pb, &pb->icmp_done);
}

int equal_addr(const sockaddr_any *a, const sockaddr_any *b) 
{
    if(!a->sa.sa_family)
        return 0;

    if(a->sa.sa_family != b->sa.sa_family)
        return 0;

    if(a->sa.sa_family == AF_INET6)
        return  !memcmp(&a->sin6.sin6_addr, &b->sin6.sin6_addr, sizeof(a->sin6.sin6_addr));
    else
        return  !memcmp(&a->sin.sin_addr, &b->sin.sin_addr, sizeof(a->sin.sin_addr));
    return 0;    /*  not reached   */
}

int equal_sockaddr(const sockaddr_any* a, const sockaddr_any* b) 
{
    if(!a->sa.sa_family)
        return 0;

    if(a->sa.sa_family != b->sa.sa_family)
        return 0;

    if(a->sa.sa_family == AF_INET6)
        return (!memcmp (&a->sin6.sin6_addr, &b->sin6.sin6_addr, sizeof(a->sin6.sin6_addr)) && (a->sin6.sin6_port == b->sin6.sin6_port));
    else
        return !memcmp (&a->sin, &b->sin, sizeof(a->sin));
    return 0;    /*  not reached   */
}

void bind_socket(int sk) 
{
    sockaddr_any *addr, tmp;

    if(device)
        if(setsockopt(sk, SOL_SOCKET, SO_BINDTODEVICE, device, strlen(device) + 1) < 0)
            error("setsockopt SO_BINDTODEVICE");

    if(!src_addr.sa.sa_family) {
        memset(&tmp, 0, sizeof(tmp));
        tmp.sa.sa_family = af;
        addr = &tmp;
    } else {
        addr = &src_addr;
    }

    if(bind(sk, &addr->sa, sizeof(struct sockaddr)) < 0)
        error("bind");
}

void use_timestamp(int sk) 
{
    int n = 1;

    setsockopt(sk, SOL_SOCKET, SO_TIMESTAMP, &n, sizeof(n));
    /*  foo on errors...  */
}

void use_recv_ttl(int sk) 
{
    int n = 1;

    if(af == AF_INET)
        setsockopt(sk, SOL_IP, IP_RECVTTL, &n, sizeof(n));
    else if(af == AF_INET6)
        setsockopt(sk, SOL_IPV6, IPV6_RECVHOPLIMIT, &n, sizeof(n));
    /*  foo on errors   */
}

void use_recverr(int sk) 
{
    int val = 1;

    if(af == AF_INET) {
        if(setsockopt(sk, SOL_IP, IP_RECVERR, &val, sizeof(val)) < 0)
            error("setsockopt IP_RECVERR");
    } else if(af == AF_INET6) {
        if(setsockopt(sk, SOL_IPV6, IPV6_RECVERR, &val, sizeof(val)) < 0)
            error("setsockopt IPV6_RECVERR");
    }
}

void set_ttl(int sk, int ttl) 
{
    if(af == AF_INET) {
        if(setsockopt(sk, SOL_IP, IP_TTL, &ttl, sizeof(ttl)) < 0)
            error("setsockopt IP_TTL");
    } else if(af == AF_INET6) {
        if(setsockopt(sk, SOL_IPV6, IPV6_UNICAST_HOPS, &ttl, sizeof(ttl)) < 0)
            error("setsockopt IPV6_UNICAST_HOPS");
    }
}

int do_send(int sk, const void *data, size_t len, const sockaddr_any *addr) 
{
    int res;

    if(!addr || raw_can_connect())
        res = send(sk, data, len, 0);
    else
        res = sendto(sk, data, len, 0, &addr->sa, sizeof(struct sockaddr));

    if(res < 0) {
        if(errno == ENOBUFS || errno == EAGAIN)
            return res;
        if(errno == EMSGSIZE || errno == EHOSTUNREACH)
            return 0;    /*  recverr will say more...  */
        error("send");    /*  not recoverable   */
    }

    return res;
}

/*  There is a bug in the kernel before 2.6.25, which prevents icmp errors
  to be obtained by MSG_ERRQUEUE for ipv6 connected raw sockets.
*/
static int can_connect = -1;

#define VER(A,B,C,D)    (((((((A) << 8) |(B)) << 8) |(C)) << 8) |(D))

int raw_can_connect(void) 
{
    if(can_connect < 0) {
        if(af == AF_INET)
            can_connect = 1;
        else {    /*  AF_INET6   */
            struct utsname uts;
            int n;
            unsigned int a, b, c, d = 0;

            if(uname(&uts) < 0)
                return 0;

            n = sscanf(uts.release, "%u.%u.%u.%u", &a, &b, &c, &d);
            can_connect = (n >= 3 && VER(a, b, c, d) >= VER(2, 6, 25, 0));
        }
    }

    return can_connect;
}

#ifdef __APPLE__

/*
 * Return the source address for the given destination address
 * Original: https://opensource.apple.com/source/network_cmds/network_cmds-606.140.1/traceroute.tproj/findsaddr-socket.c.auto.html
 */
const char* findsaddr(register const struct sockaddr_in *to, register struct sockaddr_in *from)
{
    struct sockaddr_in* ifa;
    struct sockaddr *sa;
    
    static char errbuf[512];

    int s = socket(PF_ROUTE, SOCK_RAW, AF_UNSPEC);
    if (s < 0) {
        snprintf(errbuf, sizeof(errbuf), "socket: %.128s", strerror(errno));
        return (errbuf);
    }

    pid_t pid = getpid();
    int seq = 0;
    
    struct rtmsg rtmsg;
    memset(&rtmsg, 0, sizeof(rtmsg));
    
    struct rt_msghdr* rp = &rtmsg.rtmsg; // Points to the header
    rp->rtm_type = RTM_GET;
    rp->rtm_version = RTM_VERSION;
    rp->rtm_flags = RTF_UP | RTF_GATEWAY | RTF_HOST | RTF_STATIC;
    rp->rtm_addrs = RTA_DST | RTA_IFA;
    rp->rtm_seq = ++seq;
    rp->rtm_pid = pid;
    
    uint8_t* cp = rtmsg.data;

    // Fill the data with the destination address
    struct sockaddr_in* sp = (struct sockaddr_in*)cp;
    *sp = *to;
    // align
    int l = roundup(SALEN((struct sockaddr *)sp), sizeof(uint32_t));
    cp += l;

    int size = cp - (uint8_t*)rp; // Size is the length of the header plus the data
    rp->rtm_msglen = size;

    int cc = write(s, (char *)rp, size);
    if(cc < 0) {
        snprintf(errbuf, sizeof(errbuf), "write: %.128s", strerror(errno));
        close(s);
        return (errbuf);
    }
    
    if(cc != size) {
        snprintf(errbuf, sizeof(errbuf), "short write (%d != %d)", cc, size);
        close(s);
        return (errbuf);
    }

    size = sizeof(rtmsg);
    
    // Read the answer
    do {
        memset(rp, 0, size);
        cc = read(s, (char *)rp, size);
        if(cc < 0) {
            snprintf(errbuf, sizeof(errbuf), "read: %.128s", strerror(errno));
            close(s);
            return (errbuf);
        }
    } while(rp->rtm_seq != seq || rp->rtm_pid != pid); // Read until we get the message for us
    
    close(s);

    if(rp->rtm_version != RTM_VERSION) {
        snprintf(errbuf, sizeof(errbuf), "bad version %d", rp->rtm_version);
        return (errbuf);
    }
    
    if(rp->rtm_msglen > cc) {
        snprintf(errbuf, sizeof(errbuf), "bad msglen %d > %d", rp->rtm_msglen, cc);
        return (errbuf);
    }
    
    if(rp->rtm_errno != 0) {
        snprintf(errbuf, sizeof(errbuf), "rtm_errno: %.128s", strerror(rp->rtm_errno));
        return (errbuf);
    }

    // Find the interface sockaddr
    cp = (uint8_t *)(rp + 1); // Points to the answer's data
    
    for(int i = 1; i != 0; i <<= 1) {
        if(i & rp->rtm_addrs) {
            sa = (struct sockaddr *)cp;
            switch(i) {
                case RTA_IFA:
                {
                    if (sa->sa_family == AF_INET) {
                        ifa = (struct sockaddr_in *)cp;
                        if (ifa->sin_addr.s_addr != 0) {
                            *from = *ifa;
                            return NULL;
                        }
                    }
                    break;
                }
                default:
                {
                    break;
                }
            }

            if (SALEN(sa) == 0)
                cp += sizeof (uint32_t);
            else
                cp += roundup(SALEN(sa), sizeof (uint32_t));
        }
    }

    return ("failed!");
}

#endif
