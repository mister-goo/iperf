/*
 * iperf, Copyright (c) 2014-2022, The Regents of the University of
 * California, through Lawrence Berkeley National Laboratory (subject
 * to receipt of any required approvals from the U.S. Dept. of
 * Energy).  All rights reserved.
 *
 * If you have questions about your rights to use or distribute this
 * software, please contact Berkeley Lab's Technology Transfer
 * Department at TTD@lbl.gov.
 *
 * NOTICE.  This software is owned by the U.S. Department of Energy.
 * As such, the U.S. Government has been granted for itself and others
 * acting on its behalf a paid-up, nonexclusive, irrevocable,
 * worldwide license in the Software to reproduce, prepare derivative
 * works, and perform publicly and display publicly.  Beginning five
 * (5) years after the date permission to assert copyright is obtained
 * from the U.S. Department of Energy, and subject to any subsequent
 * five (5) year renewals, the U.S. Government is granted for itself
 * and others acting on its behalf a paid-up, nonexclusive,
 * irrevocable, worldwide license in the Software to reproduce,
 * prepare derivative works, distribute copies to the public, perform
 * publicly and display publicly, and to permit others to do so.
 *
 * This code is distributed under a BSD style license, see the LICENSE
 * file for complete information.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <assert.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netdb.h>
#include <netinet/in.h>
#ifdef HAVE_STDINT_H
#include <stdint.h>
#endif
#include <sys/time.h>
#include <sys/select.h>

#include "iperf.h"
#include "iperf_api.h"
#include "iperf_util.h"
#include "iperf_udp.h"
#include "timer.h"
#include "net.h"
#include "cjson.h"
#include "portable_endian.h"

#if defined(HAVE_INTTYPES_H)
# include <inttypes.h>
#else
# ifndef PRIu64
#  if sizeof(long) == 8
#   define PRIu64		"lu"
#  else
#   define PRIu64		"llu"
#  endif
# endif
#endif


// +----+------+------+----------+----------+----------+
// |RSV | FRAG | ATYP | DST.ADDR | DST.PORT |   DATA   |
// +----+------+------+----------+----------+----------+
// | 2  |  1   |  1   | Variable |    2     | Variable |
// +----+------+------+----------+----------+----------+
static int
socks5_header_len(const uint8_t *pkt, size_t n) {
    if (n <= 6) {
        return -1;
    }
    if (pkt[0] != 0 || pkt[1] != 0 || pkt[2] != 0) {
        return -1;
    }
    size_t alen = 0;
    switch (pkt[3]) {
    case 1:
        alen = 4;
        break;
    case 4:
        alen = 16;
        break;
    case 3:
        alen = 1 + (size_t)pkt[4];
        break;
    default:
        return -1;
    }
    if (n < 4 + alen + 2) {
        return -1;
    }
    return 4 + alen + 2;
}


/* iperf_udp_recv
 *
 * receives the data for UDP
 */
int
iperf_udp_recv(struct iperf_stream *sp)
{
    uint32_t  sec, usec;
    uint64_t  pcount;
    int       r;
    int       size = sp->settings->blksize;
    int       first_packet = 0;
    double    transit = 0, d = 0;
    struct iperf_time sent_time, arrival_time, temp_time;

    r = read(sp->socket, sp->buffer, size);

    /*
     * If we got an error in the read, or if we didn't read anything
     * because the underlying read(2) got a EAGAIN, then skip packet
     * processing.
     */
    if (r <= 0)
        return r;

    /* Only count bytes received while we're in the correct state. */
    if (sp->test->state == TEST_RUNNING) {

	/*
	 * For jitter computation below, it's important to know if this
	 * packet is the first packet received.
	 */
	if (sp->result->bytes_received == 0) {
	    first_packet = 1;
	}

	sp->result->bytes_received += r;
	sp->result->bytes_received_this_interval += r;

    const char *data = sp->buffer;
    if (sp->test->socks5_proxy) {
        int n = socks5_header_len((const uint8_t *)sp->buffer, (size_t)r);
        if (n < 0) {
            return -1;
        }
        data += n;
    }

    // FIXME: need check the size of packet
    /* Dig the various counters out of the incoming UDP packet */
    memcpy(&sec, data, sizeof(sec));
    memcpy(&usec, data+4, sizeof(usec));
	if (sp->test->udp_counters_64bit) {
	    memcpy(&pcount, data+8, sizeof(pcount));
	    sec = ntohl(sec);
	    usec = ntohl(usec);
	    pcount = be64toh(pcount);
	    sent_time.secs = sec;
	    sent_time.usecs = usec;
	}
	else {
	    uint32_t pc;
	    memcpy(&pc, data+8, sizeof(pc));
	    sec = ntohl(sec);
	    usec = ntohl(usec);
	    pcount = ntohl(pc);
	    sent_time.secs = sec;
	    sent_time.usecs = usec;
	}

	if (sp->test->debug_level >= DEBUG_LEVEL_DEBUG)
	    fprintf(stderr, "pcount %" PRIu64 " packet_count %d\n", pcount, sp->packet_count);

	/*
	 * Try to handle out of order packets.  The way we do this
	 * uses a constant amount of storage but might not be
	 * correct in all cases.  In particular we seem to have the
	 * assumption that packets can't be duplicated in the network,
	 * because duplicate packets will possibly cause some problems here.
	 *
	 * First figure out if the sequence numbers are going forward.
	 * Note that pcount is the sequence number read from the packet,
	 * and sp->packet_count is the highest sequence number seen so
	 * far (so we're expecting to see the packet with sequence number
	 * sp->packet_count + 1 arrive next).
	 */
	if (pcount >= sp->packet_count + 1) {

	    /* Forward, but is there a gap in sequence numbers? */
	    if (pcount > sp->packet_count + 1) {
		/* There's a gap so count that as a loss. */
		sp->cnt_error += (pcount - 1) - sp->packet_count;
	    }
	    /* Update the highest sequence number seen so far. */
	    sp->packet_count = pcount;
	} else {

	    /*
	     * Sequence number went backward (or was stationary?!?).
	     * This counts as an out-of-order packet.
	     */
	    sp->outoforder_packets++;

	    /*
	     * If we have lost packets, then the fact that we are now
	     * seeing an out-of-order packet offsets a prior sequence
	     * number gap that was counted as a loss.  So we can take
	     * away a loss.
	     */
	    if (sp->cnt_error > 0)
		sp->cnt_error--;

	    /* Log the out-of-order packet */
	    if (sp->test->debug)
		fprintf(stderr, "OUT OF ORDER - incoming packet sequence %" PRIu64 " but expected sequence %d on stream %d", pcount, sp->packet_count + 1, sp->socket);
	}

	/*
	 * jitter measurement
	 *
	 * This computation is based on RFC 1889 (specifically
	 * sections 6.3.1 and A.8).
	 *
	 * Note that synchronized clocks are not required since
	 * the source packet delta times are known.  Also this
	 * computation does not require knowing the round-trip
	 * time.
	 */
	iperf_time_now(&arrival_time);

	iperf_time_diff(&arrival_time, &sent_time, &temp_time);
	transit = iperf_time_in_secs(&temp_time);

	/* Hack to handle the first packet by initializing prev_transit. */
	if (first_packet)
	    sp->prev_transit = transit;

	d = transit - sp->prev_transit;
	if (d < 0)
	    d = -d;
	sp->prev_transit = transit;
	sp->jitter += (d - sp->jitter) / 16.0;
    }
    else {
	if (sp->test->debug)
	    printf("Late receive, state = %d\n", sp->test->state);
    }

    return r;
}


/* iperf_udp_send
 *
 * sends the data for UDP
 */
int
iperf_udp_send(struct iperf_stream *sp)
{
    int r;
    int       size = sp->settings->blksize;
    struct iperf_time before;

    iperf_time_now(&before);

    ++sp->packet_count;

    size_t tssz = 4 + 4 + (sp->test->udp_counters_64bit ? 8 : 4);

    // +----+------+------+----------+----------+----------+
    // |RSV | FRAG | ATYP | DST.ADDR | DST.PORT |   DATA   |
    // +----+------+------+----------+----------+----------+
    // | 2  |  1   |  1   | Variable |    2     | Variable |
    // +----+------+------+----------+----------+----------+
    size_t hdrsz = 0;
    if (sp->test->socks5_proxy) {
        size_t alen = 0;
        const void *addr = NULL;
        if (sp->test->udp_server_addr.ss_family == AF_INET) {
            struct sockaddr_in *sa = (struct sockaddr_in *)&sp->test->udp_server_addr;
            alen = 4;
            addr = &sa->sin_addr.s_addr;
        } else {
            struct sockaddr_in6 *sa = (struct sockaddr_in6 *)&sp->test->udp_server_addr;
            alen = 16;
            addr = &sa->sin6_addr;
        }
        hdrsz = 4 + alen + 2;
        if (hdrsz + tssz > sp->settings->blksize) {
            // buffer too small
            return -1;
        }

        sp->buffer[0] = sp->buffer[1] = sp->buffer[2] = 0;
        sp->buffer[3] = (alen == 4) ? 1 : 4;
        memcpy(sp->buffer + 4, addr, alen);
        sp->buffer[4 + alen + 0] = (char)(uint8_t)(sp->test->server_port >> 8);
        sp->buffer[4 + alen + 1] = (char)(uint8_t)(sp->test->server_port >> 0);
    }

    char *data = sp->buffer + hdrsz;
    uint32_t sec = htonl(before.secs);
    uint32_t usec = htonl(before.usecs);
    memcpy(data + 0, &sec, sizeof(sec));
    memcpy(data + 4, &usec, sizeof(usec));
    if (sp->test->udp_counters_64bit) {
        uint64_t pcount = htobe64(sp->packet_count);
        memcpy(data + 8, &pcount, sizeof(pcount));
    } else {
        uint32_t pcount = htonl(sp->packet_count);
        memcpy(data + 8, &pcount, sizeof(pcount));
    }

    r = write(sp->socket, sp->buffer, size);

    if (r < 0)
	return r;

    sp->result->bytes_sent += r;
    sp->result->bytes_sent_this_interval += r;

    if (sp->test->debug_level >=  DEBUG_LEVEL_DEBUG)
	printf("sent %d bytes of %d, total %" PRIu64 "\n", r, sp->settings->blksize, sp->result->bytes_sent);

    return r;
}


/**************************************************************************/

/*
 * The following functions all have to do with managing UDP data sockets.
 * UDP of course is connectionless, so there isn't really a concept of
 * setting up a connection, although connect(2) can (and is) used to
 * bind the remote end of sockets.  We need to simulate some of the
 * connection management that is built-in to TCP so that each side of the
 * connection knows about each other before the real data transfers begin.
 */

/*
 * Set and verify socket buffer sizes.
 * Return 0 if no error, -1 if an error, +1 if socket buffers are
 * potentially too small to hold a message.
 */
int
iperf_udp_buffercheck(struct iperf_test *test, int s)
{
    int rc = 0;
    int sndbuf_actual, rcvbuf_actual;

    /*
     * Set socket buffer size if requested.  Do this for both sending and
     * receiving so that we can cover both normal and --reverse operation.
     */
    int opt;
    socklen_t optlen;

    if ((opt = test->settings->socket_bufsize)) {
        if (setsockopt(s, SOL_SOCKET, SO_RCVBUF, &opt, sizeof(opt)) < 0) {
            i_errno = IESETBUF;
            return -1;
        }
        if (setsockopt(s, SOL_SOCKET, SO_SNDBUF, &opt, sizeof(opt)) < 0) {
            i_errno = IESETBUF;
            return -1;
        }
    }

    /* Read back and verify the sender socket buffer size */
    optlen = sizeof(sndbuf_actual);
    if (getsockopt(s, SOL_SOCKET, SO_SNDBUF, &sndbuf_actual, &optlen) < 0) {
	i_errno = IESETBUF;
	return -1;
    }
    if (test->debug) {
	printf("SNDBUF is %u, expecting %u\n", sndbuf_actual, test->settings->socket_bufsize);
    }
    if (test->settings->socket_bufsize && test->settings->socket_bufsize > sndbuf_actual) {
	i_errno = IESETBUF2;
	return -1;
    }
    if (test->settings->blksize > sndbuf_actual) {
	char str[WARN_STR_LEN];
	snprintf(str, sizeof(str),
		 "Block size %d > sending socket buffer size %d",
		 test->settings->blksize, sndbuf_actual);
	warning(str);
	rc = 1;
    }

    /* Read back and verify the receiver socket buffer size */
    optlen = sizeof(rcvbuf_actual);
    if (getsockopt(s, SOL_SOCKET, SO_RCVBUF, &rcvbuf_actual, &optlen) < 0) {
	i_errno = IESETBUF;
	return -1;
    }
    if (test->debug) {
	printf("RCVBUF is %u, expecting %u\n", rcvbuf_actual, test->settings->socket_bufsize);
    }
    if (test->settings->socket_bufsize && test->settings->socket_bufsize > rcvbuf_actual) {
	i_errno = IESETBUF2;
	return -1;
    }
    if (test->settings->blksize > rcvbuf_actual) {
	char str[WARN_STR_LEN];
	snprintf(str, sizeof(str),
		 "Block size %d > receiving socket buffer size %d",
		 test->settings->blksize, rcvbuf_actual);
	warning(str);
	rc = 1;
    }

    if (test->json_output) {
	cJSON_AddNumberToObject(test->json_start, "sock_bufsize", test->settings->socket_bufsize);
	cJSON_AddNumberToObject(test->json_start, "sndbuf_actual", sndbuf_actual);
	cJSON_AddNumberToObject(test->json_start, "rcvbuf_actual", rcvbuf_actual);
    }

    return rc;
}

/*
 * iperf_udp_accept
 *
 * Accepts a new UDP "connection"
 */
int
iperf_udp_accept(struct iperf_test *test)
{
    struct sockaddr_storage sa_peer;
    unsigned int buf;
    socklen_t len;
    int       sz, s;
    int	      rc;

    /*
     * Get the current outstanding socket.  This socket will be used to handle
     * data transfers and a new "listening" socket will be created.
     */
    s = test->prot_listener;

    /*
     * Grab the UDP packet sent by the client.  From that we can extract the
     * client's address, and then use that information to bind the remote side
     * of the socket to the client.
     */
    len = sizeof(sa_peer);
    if ((sz = recvfrom(test->prot_listener, &buf, sizeof(buf), 0, (struct sockaddr *) &sa_peer, &len)) < 0) {
        i_errno = IESTREAMACCEPT;
        return -1;
    }

    if (connect(s, (struct sockaddr *) &sa_peer, len) < 0) {
        i_errno = IESTREAMACCEPT;
        return -1;
    }

    /* Check and set socket buffer sizes */
    rc = iperf_udp_buffercheck(test, s);
    if (rc < 0)
	/* error */
	return rc;
    /*
     * If the socket buffer was too small, but it was the default
     * size, then try explicitly setting it to something larger.
     */
    if (rc > 0) {
	if (test->settings->socket_bufsize == 0) {
            char str[WARN_STR_LEN];
	    int bufsize = test->settings->blksize + UDP_BUFFER_EXTRA;
	    snprintf(str, sizeof(str), "Increasing socket buffer size to %d",
	             bufsize);
	    warning(str);
	    test->settings->socket_bufsize = bufsize;
	    rc = iperf_udp_buffercheck(test, s);
	    if (rc < 0)
		return rc;
	}
    }

#if defined(HAVE_SO_MAX_PACING_RATE)
    /* If socket pacing is specified, try it. */
    if (test->settings->fqrate) {
	/* Convert bits per second to bytes per second */
	unsigned int fqrate = test->settings->fqrate / 8;
	if (fqrate > 0) {
	    if (test->debug) {
		printf("Setting fair-queue socket pacing to %u\n", fqrate);
	    }
	    if (setsockopt(s, SOL_SOCKET, SO_MAX_PACING_RATE, &fqrate, sizeof(fqrate)) < 0) {
		warning("Unable to set socket pacing");
	    }
	}
    }
#endif /* HAVE_SO_MAX_PACING_RATE */
    {
	unsigned int rate = test->settings->rate / 8;
	if (rate > 0) {
	    if (test->debug) {
		printf("Setting application pacing to %u\n", rate);
	    }
	}
    }

    /*
     * Create a new "listening" socket to replace the one we were using before.
     */
    test->prot_listener = netannounce(test->settings->domain, Pudp, test->bind_address, test->bind_dev, test->server_port);
    if (test->prot_listener < 0) {
        i_errno = IESTREAMLISTEN;
        return -1;
    }

    FD_SET(test->prot_listener, &test->read_set);
    test->max_fd = (test->max_fd < test->prot_listener) ? test->prot_listener : test->max_fd;

    /* Let the client know we're ready "accept" another UDP "stream" */
    buf = UDP_CONNECT_REPLY;
    if (write(s, &buf, sizeof(buf)) < 0) {
        i_errno = IESTREAMWRITE;
        return -1;
    }

    return s;
}


/*
 * iperf_udp_listen
 *
 * Start up a listener for UDP stream connections.  Unlike for TCP,
 * there is no listen(2) for UDP.  This socket will however accept
 * a UDP datagram from a client (indicating the client's presence).
 */
int
iperf_udp_listen(struct iperf_test *test)
{
    int s;

    if ((s = netannounce(test->settings->domain, Pudp, test->bind_address, test->bind_dev, test->server_port)) < 0) {
        i_errno = IESTREAMLISTEN;
        return -1;
    }

    /*
     * The caller will put this value into test->prot_listener.
     */
    return s;
}


static int
socks5_udp_handshake(int s, int *port_out) {
    char res[2 + 4 + 1 + 256 + 2];
    char req[3 + 4 + 256 + 2] = {
        5, 1, 0,
        5, 3, 0, 1,
    };
    size_t alen = 4;
    if (Nwrite(s, req, 3 + 4 + alen + 2, Ptcp) < 0) {
        return -1;
    }
    if (Nread(s, res, 2 + 4, Ptcp) != 2 + 4) {
        return -1;
    }
    if (0 != memcmp(res, "\x05\0" "\x05\0\0", 5)) {
        return -1;
    }
    switch (res[5]) {
    case 1:
        alen = 4;
        break;
    case 3:
        if (1 != read(s, &res[6], 1)) {
            return -1;
        }
        alen = (uint8_t)res[6];
        break;
    case 4:
        alen = 16;
        break;
    default:
        return -1;
    }
    if (Nread(s, res, alen + 2, Ptcp) != alen + 2) {
        return -1;
    }
    *port_out = (int)((((uint8_t)res[alen + 0]) << 8) | (uint8_t)res[alen + 1]);

    return 0;
}


/*
 * iperf_udp_connect
 *
 * "Connect" to a UDP stream listener.
 */
int
iperf_udp_connect(struct iperf_test *test)
{
    int s, sz;
#ifdef SO_RCVTIMEO
    struct timeval tv;
#endif
    int rc;
    int i, max_cnt_wait_for_reply;
    int connect_port = test->server_port;

    const char *connect_server = test->server_hostname;
    if (test->socks5_proxy) {
        connect_server = test->socks5_proxy;
        connect_port = 1080;    // FIXME: parse port from test->socks5_proxy

        int proxy_so = netdial(
            test->settings->domain, Ptcp, test->bind_address, test->bind_dev, 0,
            connect_server, connect_port, test->settings->connect_timeout
        );
        if (proxy_so < 0) {
            i_errno = IESTREAMCONNECT;
            return -1;
        }

        if (0 != socks5_udp_handshake(proxy_so, &connect_port)) {
            i_errno = IESTREAMCONNECT;
            return -1;
        }

        // resolve server locally
        struct addrinfo *server_res = NULL;
        char portstr[16] = {};
        snprintf(portstr, sizeof(portstr), "%d", test->server_port);
        (void)getaddrinfo(test->server_hostname, portstr, NULL, &server_res);
        if (!server_res) {
            i_errno = IESTREAMCONNECT;
            return -1;
        }
        freeaddrinfo(server_res);
        memcpy(&test->udp_server_addr, server_res->ai_addr, server_res->ai_addrlen);

        // FIXME: proxy_so leak
        ;
    }

    /* Create and bind our local socket. */
    if ((s = netdial(test->settings->domain, Pudp, test->bind_address, test->bind_dev, test->bind_port, connect_server, connect_port, -1)) < 0) {
        i_errno = IESTREAMCONNECT;
        return -1;
    }

    /* Check and set socket buffer sizes */
    rc = iperf_udp_buffercheck(test, s);
    if (rc < 0)
	/* error */
	return rc;
    /*
     * If the socket buffer was too small, but it was the default
     * size, then try explicitly setting it to something larger.
     */
    if (rc > 0) {
	if (test->settings->socket_bufsize == 0) {
            char str[WARN_STR_LEN];
	    int bufsize = test->settings->blksize + UDP_BUFFER_EXTRA;
	    snprintf(str, sizeof(str), "Increasing socket buffer size to %d",
	             bufsize);
	    warning(str);
	    test->settings->socket_bufsize = bufsize;
	    rc = iperf_udp_buffercheck(test, s);
	    if (rc < 0)
		return rc;
	}
    }

#if defined(HAVE_SO_MAX_PACING_RATE)
    /* If socket pacing is available and not disabled, try it. */
    if (test->settings->fqrate) {
	/* Convert bits per second to bytes per second */
	unsigned int fqrate = test->settings->fqrate / 8;
	if (fqrate > 0) {
	    if (test->debug) {
		printf("Setting fair-queue socket pacing to %u\n", fqrate);
	    }
	    if (setsockopt(s, SOL_SOCKET, SO_MAX_PACING_RATE, &fqrate, sizeof(fqrate)) < 0) {
		warning("Unable to set socket pacing");
	    }
	}
    }
#endif /* HAVE_SO_MAX_PACING_RATE */
    {
	unsigned int rate = test->settings->rate / 8;
	if (rate > 0) {
	    if (test->debug) {
		printf("Setting application pacing to %u\n", rate);
	    }
	}
    }

#ifdef SO_RCVTIMEO
    /* 30 sec timeout for a case when there is a network problem. */
    tv.tv_sec = 30;
    tv.tv_usec = 0;
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, (struct timeval *)&tv, sizeof(struct timeval));
#endif

    /*
     * Write a datagram to the UDP stream to let the server know we're here.
     * The server learns our address by obtaining its peer's address.
     */
    // +----+------+------+----------+----------+----------+
    // |RSV | FRAG | ATYP | DST.ADDR | DST.PORT |   DATA   |
    // +----+------+------+----------+----------+----------+
    // | 2  |  1   |  1   | Variable |    2     | Variable |
    // +----+------+------+----------+----------+----------+
    uint8_t buf[4 + 16 + 2 + 4] = {};
    size_t reqsz = 0;
    if (test->socks5_proxy) {
        size_t alen = 0;
        if (test->udp_server_addr.ss_family == AF_INET) {
            buf[3] = 1;
            struct sockaddr_in *addr = (struct sockaddr_in *)&test->udp_server_addr;
            memcpy(buf + 4, &addr->sin_addr.s_addr, 4);
            alen = 4;
        } else {
            buf[3] = 4;
            struct sockaddr_in6 *addr = (struct sockaddr_in6 *)&test->udp_server_addr;
            memcpy(buf + 4, &addr->sin6_addr, 16);
            alen = 16;
        }
        buf[4 + alen + 0] = (uint8_t)(test->server_port >> 8);
        buf[4 + alen + 1] = (uint8_t)test->server_port;
        reqsz = 4 + alen + 2;
    }
    uint32_t code = UDP_CONNECT_MSG;
    memcpy(buf + reqsz, &code, 4);
    reqsz += 4;
    if (test->debug) {
        printf("Sending Connect message to Sockt %d\n", s);
    }
    if (write(s, buf, reqsz) < 0) {
        // XXX: Should this be changed to IESTREAMCONNECT?
        i_errno = IESTREAMWRITE;
        return -1;
    }

    /*
     * Wait until the server replies back to us with the "accept" response.
     */
    i = 0;
    max_cnt_wait_for_reply = 1;
    if (test->reverse) /* In reverse mode allow few packets to have the "accept" response - to handle out of order packets */
        max_cnt_wait_for_reply += MAX_REVERSE_OUT_OF_ORDER_PACKETS;
    do {
        memset(buf, 0, sizeof(buf));
        if ((sz = recv(s, buf, sizeof(buf), 0)) < 0) {
            i_errno = IESTREAMREAD;
            return -1;
        }
        i += 1;

        int hdrlen = test->socks5_proxy ? socks5_header_len(buf, (size_t)sz) : 0;
        if (hdrlen < 0 || hdrlen + 4 < (size_t)sz) {
            continue;
        }
        memcpy(&code, buf + hdrlen, 4);

        if (test->debug) {
            printf("Connect received for Socket %d, sz=%d, buf=%x, i=%d, max_cnt_wait_for_reply=%d\n", s, sz, code, i, max_cnt_wait_for_reply);
        }
    } while (code != UDP_CONNECT_REPLY && code != LEGACY_UDP_CONNECT_REPLY && i < max_cnt_wait_for_reply);

    if (code != UDP_CONNECT_REPLY && code != LEGACY_UDP_CONNECT_REPLY) {
        i_errno = IESTREAMREAD;
        return -1;
    }

    return s;
}


/* iperf_udp_init
 *
 * initializer for UDP streams in TEST_START
 */
int
iperf_udp_init(struct iperf_test *test)
{
    return 0;
}
