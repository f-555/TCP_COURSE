/* TCP congestion control for UCAS network course
 * based on BBR congestion control
 * add reaction to packet losses and a new startup
 * Wu Wenhao and Fei Jiaqiang
 * wu_wenhao555@163.com
 */
#include <linux/module.h>
#include <net/tcp.h>
#include <linux/inet_diag.h>
#include <linux/inet.h>
#include <linux/random.h>
#include <linux/win_minmax.h>

/* Scale factor for rate in pkt/uSec unit to avoid truncation in bandwidth
 * estimation. The rate unit ~= (1500 bytes / 1 usec / 2^24) ~= 715 bps.
 * This handles bandwidths from 0.06pps (715bps) to 256Mpps (3Tbps) in a u32.
 * Since the minimum window is >=4 packets, the lower bound isn't
 * an issue. The upper bound isn't an issue with existing technologies.
 */
#define BW_SCALE 24
#define BW_UNIT (1 << BW_SCALE)
#define course_SCALE 8	/* scaling factor for fractions in course (e.g. gains) */
#define course_UNIT (1 << course_SCALE)

enum course_mode {
    course_SLOWSTART, /*using slow start to increase sending rate*/
	//course_STARTUP,	/* ramp up sending rate rapidly to fill pipe */
	course_DRAIN,	/* drain any queue created during startup */
	course_PROBE_BW,	/* discover, share bw: pace around estimated bw */
	course_PROBE_RTT,	/* cut inflight to min to probe min_rtt */
    course_PACKET_LOSS,
    course_PROTECTION,
};

struct course{
	u32	min_rtt_us;	        /* min RTT in min_rtt_win_sec window */
	u32	min_rtt_stamp;	        /* timestamp of min_rtt_us */
	u32	probe_rtt_done_stamp;   /* end time for course_PROBE_RTT mode */
	struct minmax bw;	/* Max recent delivery rate in pkts/uS << 24 */
	u32	rtt_cnt;	    /* count of packet-timed rounds elapsed */
	u32 next_rtt_delivered; /* scb->tx.delivered at end of round */
	u64	cycle_mstamp;	     /* time of this cycle phase start */
	u32 mode:3,		     /* current course_mode in state machine */
		prev_ca_state:3,     /* CA state on previous ACK */
		packet_conservation:1,  /* use packet conservation? */
		round_start:1,	     /* start of packet-timed tx->ack round? */
		tso_segs_goal:7,     /* segments we want in each skb we send */
		idle_restart:1,	     /* restarting after idle? */
		probe_rtt_round_done:1,  /* a course_PROBE_RTT round at 4 pkts? */
		down_count:3,
        rate_lock:3,
		lt_is_sampling:1,    /* taking long-term ("LT") samples now? */
		lt_rtt_cnt:7,	     /* round trips in long-term interval */
		lt_use_bw:1;	     /* use lt_bw as our bw estimate? */
	u32	lt_bw;		     /* LT est delivery rate in pkts/uS << 24 */
	u32	lt_last_delivered;   /* LT intvl start: tp->delivered */
	u32	lt_last_stamp;	     /* LT intvl start: tp->delivered_mstamp */
	u32	lt_last_lost;	     /* LT intvl start: tp->lost */
	u32	pacing_gain:10,	/* current gain for setting pacing rate */
		cwnd_gain:10,	/* current gain for setting cwnd */
		full_bw_reached:1,   /* reached full bw in Startup? */
		full_bw_cnt:2,	/* number of rounds without large bw gains */
		cycle_idx:3,	/* current index in pacing_gain cycle array */
		has_seen_rtt:1, /* have we seen an RTT sample yet? */
        loss_count:3,
        rtt_up_count:2;
	u32	prior_cwnd;	/* prior cwnd upon entering loss recovery */
	u32	full_bw;	/* recent bw, to estimate if pipe is full */
    u32	loss_packet_stamp1;	        /* timestamp of first time loss */
    u32	loss_packet_stamp2;	        /* timestamp of second time loss */
    u32 rtt_last;
    u32 loss_last_stamp;
};
#define CYCLE_LEN	8	/* number of phases in a pacing gain cycle */

/* Window length of bw filter (in rounds): */
static const int course_bw_rtts = CYCLE_LEN + 2;
/* Window length of min_rtt filter (in sec): */
static const u32 course_min_rtt_win_sec = 10;
/* Minimum time (in ms) spent at course_cwnd_min_target in course_PROBE_RTT mode: */
static const u32 course_probe_rtt_mode_ms = 200;
/* Skip TSO below the following bandwidth (bits/sec): */
static const int course_min_tso_rate = 1200000;

/* We use a high_gain value of 2/ln(2) because it's the smallest pacing gain
 * that will allow a smoothly increasing pacing rate that will double each RTT
 * and send the same number of packets per RTT that an un-paced, slow-starting
 * Reno or CUBIC flow would:
 */
static const int course_high_gain  = course_UNIT * 2885 / 1000 + 1;

/* The pacing gain of 1/high_gain in course_DRAIN is calculated to typically drain
 * the queue created in course_STARTUP in a single round:
 */
static const int course_drain_gain = course_UNIT * 1000 / 2885;

/* The gain for deriving steady-state cwnd tolerates delayed/stretched ACKs: */
static const int course_cwnd_gain  = course_UNIT * 2;

/* the pacing_gain values for the PACKET_LOSS mode */
static const int course_loss_gain  = course_UNIT * 950 / 1000;

/* quickly drop */
static const int course_drop_gain  = course_UNIT * 700 / 1000;

static const int course_lock_gain  = course_UNIT;

/* The pacing_gain values for the PROBE_BW gain cycle, to discover/share bw: */
static const int course_pacing_gain[] = {
	course_UNIT * 5 / 4,	
	course_UNIT * 4 / 5,	
	course_UNIT, 
    course_UNIT, 
    course_UNIT,	
	course_UNIT, 
    course_UNIT, 
    course_UNIT	
};
/* Randomize the starting gain cycling phase over N phases: */
static const u32 course_cycle_rand = 7;

/* Try to keep at least this many packets in flight, if things go smoothly. For
 * smooth functioning, a sliding window protocol ACKing every other packet
 * needs at least 4 packets in flight:
 */
static const u32 course_cwnd_min_target = 4;

/* To estimate if course_STARTUP mode (i.e. high_gain) has filled pipe... */
/* If bw has increased significantly (1.25x), there may be more bw available: */
static const u32 course_full_bw_thresh = course_UNIT * 5 / 4;
/* But after 3 rounds w/o significant bw growth, estimate pipe is full: */
static const u32 course_full_bw_cnt = 3;

/* "long-term" ("LT") bandwidth estimator parameters... */
/* The minimum number of rounds in an LT bw sampling interval: */
static const u32 course_lt_intvl_min_rtts = 4;
/* If lost/delivered ratio > 20%, interval is "lossy" and we may be policed: */
static const u32 course_lt_loss_thresh = 50;
/* If 2 intervals have a bw ratio <= 1/8, their bw is "consistent": */
static const u32 course_lt_bw_ratio = course_UNIT / 8;
/* If 2 intervals have a bw diff <= 4 Kbit/sec their bw is "consistent": */
static const u32 course_lt_bw_diff = 4000 / 8;
/* If we estimate we're policed, use lt_bw for this many round trips: */
static const u32 course_lt_bw_max_rtts = 48;

static const u32 loss_thereshold_ms = 10;

static const u32 lock_thereshold_ms = 100;

static void course_reset_slowstart_mode(struct sock *sk);
static void course_check_probe_rtt_done(struct sock *sk);
static void course_reset_probe_bw_mode(struct sock *sk);
static void course_reset_lt_bw_sampling_interval(struct sock *sk);
static void course_reset_lt_bw_sampling(struct sock *sk);
static void course_advance_cycle_phase(struct sock *sk);
static void course_lt_bw_sampling(struct sock *sk, const struct rate_sample *rs);
static void course_update_bw(struct sock *sk, const struct rate_sample *rs);
static u32 course_bw(const struct sock *sk);
static void course_update_cycle_phase(struct sock *sk,const struct rate_sample *rs);
static bool course_full_bw_reached(const struct sock *sk);
static void course_check_full_bw_reached(struct sock *sk,const struct rate_sample *rs);
static void course_slow_start(struct sock *sk, struct tcp_sock *tp, u32 acked);
static u32 course_quantization_budget(struct sock *sk, u32 cwnd, int gain);
static u32 course_bdp(struct sock *sk, u32 bw, int gain);
static u32 course_inflight(struct sock *sk, u32 bw, int gain);
static void course_check_drain(struct sock *sk, const struct rate_sample *rs);
static void course_save_cwnd(struct sock *sk);
static void course_reset_mode(struct sock *sk);
static void course_check_probe_rtt_done(struct sock *sk);
static void course_update_min_rtt(struct sock *sk, const struct rate_sample *rs);
static u64 course_rate_bytes_per_sec(struct sock *sk, u64 rate, int gain);
static u32 course_bw_to_pacing_rate(struct sock *sk, u32 bw, int gain);
static void course_init_pacing_rate_from_rtt(struct sock *sk);
static void course_set_pacing_rate(struct sock *sk, u32 bw, int gain);
static void course_set_tso_segs_goal(struct sock *sk);
static bool course_set_cwnd_to_recover_or_restore(struct sock *sk, const struct rate_sample *rs, u32 acked, u32 *new_cwnd);
static void course_set_cwnd(struct sock *sk, const struct rate_sample *rs,u32 acked, u32 bw, int gain);
static void course_advance_cycle_phase(struct sock *sk);
static u32 course_max_bw(const struct sock *sk);
static void course_lt_bw_interval_done(struct sock *sk, u32 bw);
static void course_init(struct sock *sk);
static void course_slow_start_rate_down(struct sock *sk);

/*
static void course_reset_startup_mode(struct sock *sk)
{
	struct course*course= inet_csk_ca(sk);

	course->mode = course_STARTUP;
	course->pacing_gain = course_high_gain;
	course->cwnd_gain	 = course_high_gain;
}
*/

static void course_rate_lock(struct sock *sk){
    struct course*course= inet_csk_ca(sk);
    if(course->rate_lock == 2 && course->mode==course_PACKET_LOSS){
        course->loss_packet_stamp1 = tcp_jiffies32;
        course->mode = course_PROTECTION;
        course->cwnd_gain = course_lock_gain;
        course->pacing_gain = course_lock_gain;
        return;
    }
    if(course->mode==course_PROTECTION){
        if(after(tcp_jiffies32 , course->loss_packet_stamp1 + msecs_to_jiffies(lock_thereshold_ms))){
            course->rate_lock =0;
            course->loss_packet_stamp1 = 0;
            course_reset_mode(sk);
            return;
        }
        return;
    }

}

static void course_slow_start_rate_down(struct sock *sk){
    struct course*course= inet_csk_ca(sk);
    course->down_count ++;
}

static void course_check_loss_out(struct sock *sk)
{
    struct course*course= inet_csk_ca(sk);
    if(course->mode != course_PACKET_LOSS)
        return;
    if(after(tcp_jiffies32 , course->loss_packet_stamp2 + msecs_to_jiffies(loss_thereshold_ms))){
        course->loss_packet_stamp1 = 0;
        course->loss_packet_stamp2 = 0;
        course->loss_count = 0;
    }
    course_reset_mode(sk);
}

static void course_reset_packet_loss_mode(struct sock *sk)
{
	struct course*course= inet_csk_ca(sk);

	course->mode = course_PACKET_LOSS;
	course->pacing_gain = course_loss_gain;
	course->cwnd_gain	= course_loss_gain;
    course->loss_packet_stamp2 = tcp_jiffies32;
}


static void course_reset_slowstart_mode(struct sock *sk)
{
	struct course*course= inet_csk_ca(sk);
	course->mode = course_SLOWSTART;
    course->down_count=1;
}

static void course_reset_probe_bw_mode(struct sock *sk)
{
	struct course*course= inet_csk_ca(sk);

	course->mode = course_PROBE_BW;
	course->pacing_gain = course_UNIT;
	course->cwnd_gain = course_cwnd_gain;
	course->cycle_idx = CYCLE_LEN - 1 - prandom_u32_max(course_cycle_rand);
	course_advance_cycle_phase(sk);	/* flip to next phase of gain cycle */
}

static void course_reset_lt_bw_sampling_interval(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);

	course->lt_last_stamp = div_u64(tp->delivered_mstamp, USEC_PER_MSEC);
	course->lt_last_delivered = tp->delivered;
	course->lt_last_lost = tp->lost;
	course->lt_rtt_cnt = 0;
}

static void course_reset_lt_bw_sampling(struct sock *sk)
{
	struct course*course= inet_csk_ca(sk);

	course->lt_bw = 0;
	course->lt_use_bw = 0;
	course->lt_is_sampling = false;
	course_reset_lt_bw_sampling_interval(sk);
}

/* Long-term bw sampling interval is done. Estimate whether we're policed. */
static void course_lt_bw_interval_done(struct sock *sk, u32 bw)
{
	struct course*course= inet_csk_ca(sk);
	u32 diff;

	if (course->lt_bw) {  /* do we have bw from a previous interval? */
		/* Is new bw close to the lt_bw from the previous interval? */
		diff = abs(bw - course->lt_bw);
		if ((diff * course_UNIT <= course_lt_bw_ratio * course->lt_bw) ||
		    (course_rate_bytes_per_sec(sk, diff, course_UNIT) <=
		     course_lt_bw_diff)) {
			/* All criteria are met; estimate we're policed. */
			course->lt_bw = (bw + course->lt_bw) >> 1;  /* avg 2 intvls */
			course->lt_use_bw = 1;
			course->pacing_gain = course_UNIT;  /* try to avoid drops */
			course->lt_rtt_cnt = 0;
			return;
		}
	}
	course->lt_bw = bw;
	course_reset_lt_bw_sampling_interval(sk);
}

static void course_lt_bw_sampling(struct sock *sk, const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	u32 lost, delivered;
	u64 bw;
	u32 t;

	if (course->lt_use_bw) {	/* already using long-term rate, lt_bw? */
		if (course->mode == course_PROBE_BW && course->round_start &&
		    ++course->lt_rtt_cnt >= course_lt_bw_max_rtts) {
			course_reset_lt_bw_sampling(sk);    /* stop using lt_bw */
			course_reset_probe_bw_mode(sk);  /* restart gain cycling */
		}
		return;
	}

	if (!course->lt_is_sampling && course->mode!= course_SLOWSTART && course->mode!=course_PACKET_LOSS) {
		if (!rs->losses)
			return;
		course_reset_lt_bw_sampling_interval(sk);
		course->lt_is_sampling = true;
	}

	if (rs->is_app_limited) {
		course_reset_lt_bw_sampling(sk);
		return;
	}

	if (course->round_start)
		course->lt_rtt_cnt++;	
	if (course->lt_rtt_cnt < course_lt_intvl_min_rtts)
		return;		
	if (course->lt_rtt_cnt > 4 * course_lt_intvl_min_rtts) {
		course_reset_lt_bw_sampling(sk);  
		return;
	}

	if (!rs->losses)
		return;

	lost = tp->lost - course->lt_last_lost;
	delivered = tp->delivered - course->lt_last_delivered;

	if (!delivered || (lost << course_SCALE) < course_lt_loss_thresh * delivered)
		return;

	t = div_u64(tp->delivered_mstamp, USEC_PER_MSEC) - course->lt_last_stamp;
	if ((s32)t < 1)
		return;		
	if (t >= ~0U / USEC_PER_MSEC) {
		course_reset_lt_bw_sampling(sk);  /* interval too long; reset */
		return;
	}
	t *= USEC_PER_MSEC;
	bw = (u64)delivered * BW_UNIT;
	do_div(bw, t);
	course_lt_bw_interval_done(sk, bw);
}

static void course_update_bw(struct sock *sk, const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	u64 bw;

	course->round_start = 0;
	if (rs->delivered < 0 || rs->interval_us <= 0)
		return; /* Not a valid observation */

	/* See if we've reached the next RTT */
	if (!before(rs->prior_delivered, course->next_rtt_delivered)) {
		course->next_rtt_delivered = tp->delivered;
		course->rtt_cnt++;
		course->round_start = 1;
		course->packet_conservation = 0;
	}
	course_lt_bw_sampling(sk, rs);
	bw = div64_long((u64)rs->delivered * BW_UNIT, rs->interval_us);
	if (!rs->is_app_limited || bw >= course_max_bw(sk)) {
		minmax_running_max(&course->bw, course_bw_rtts, course->rtt_cnt, bw);
	}
}

static u32 course_bw(const struct sock *sk)
{
	struct course*course= inet_csk_ca(sk);
	return course->lt_use_bw ? course->lt_bw : course_max_bw(sk);
}

static void course_advance_cycle_phase(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);

	course->cycle_idx = (course->cycle_idx + 1) & (CYCLE_LEN - 1);
	course->cycle_mstamp = tp->delivered_mstamp;
	course->pacing_gain = course->lt_use_bw ? course_UNIT :
					    course_pacing_gain[course->cycle_idx];
}

static bool course_is_next_cycle_phase(struct sock *sk,
				    const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	bool is_full_length =
		tcp_stamp_us_delta(tp->delivered_mstamp, course->cycle_mstamp) >
		course->min_rtt_us;
	u32 inflight, bw;

	if (course->pacing_gain == course_UNIT)
		return is_full_length;		/* just use wall clock time */

	inflight = rs->prior_in_flight;  /* what was in-flight before ACK? */
	bw = course_max_bw(sk);

	if (course->pacing_gain > course_UNIT)
		return is_full_length &&
			(rs->losses ||  /* perhaps pacing_gain*BDP won't fit */
			 inflight >= course_inflight(sk, bw, course->pacing_gain));

	return is_full_length ||
		inflight <= course_inflight(sk, bw, course_UNIT);
}

static void course_update_cycle_phase(struct sock *sk,
				   const struct rate_sample *rs)
{
	struct course*course= inet_csk_ca(sk);

	if (course->mode == course_PROBE_BW && course_is_next_cycle_phase(sk, rs))
		course_advance_cycle_phase(sk);
}

/* Do we estimate that STARTUP filled the pipe? */
static bool course_full_bw_reached(const struct sock *sk)
{
	const struct course*course= inet_csk_ca(sk);

	return course->full_bw_reached;
}

static void course_check_full_bw_reached(struct sock *sk,
				      const struct rate_sample *rs)
{
	struct course*course= inet_csk_ca(sk);
	u32 bw_thresh;

	if (course_full_bw_reached(sk) || !course->round_start || rs->is_app_limited)
		return;

	bw_thresh = (u64)course->full_bw * course_full_bw_thresh >> course_SCALE;
	if (course_max_bw(sk) >= bw_thresh) {
		course->full_bw = course_max_bw(sk);
		course->full_bw_cnt = 0;
		return;
	}
	++course->full_bw_cnt;
    if(course->mode == course_SLOWSTART)
	    course->full_bw_reached = course->full_bw_cnt >= 1;
    course->full_bw_reached = course->full_bw_cnt >= course_full_bw_cnt;
}

static void course_slow_start(struct sock *sk, struct tcp_sock *tp, u32 acked)
{
    struct course*course= inet_csk_ca(sk);
    if(course->mode != course_SLOWSTART){
        return;
    }
    if(course_full_bw_reached(sk)){
        course->mode=course_DRAIN;
        return;
    }
    u32 cwnd;
    /*
    if(tp->snd_ssthresh!=0)
        cwnd = tp->snd_cwnd_cnt;
        if (tp->snd_cwnd_cnt >= cwnd) {
            tp->snd_cwnd_cnt = 0;
            cwnd++;
        }
        tp->snd_cwnd_cnt += acked;
        if (tp->snd_cwnd_cnt >= cwnd) {
            u32 delta = tp->snd_cwnd_cnt / cwnd;

            tp->snd_cwnd_cnt -= delta * cwnd;
            cwnd += delta;
        }
    else*/
    course->cwnd_gain = (tp->snd_cwnd + 3 * acked / (2 * course->down_count))/tp->snd_cwnd;
    course->pacing_gain = (tp->snd_cwnd + 3 * acked / (2 * course->down_count))/tp->snd_cwnd;
	//tp->snd_cwnd = min(cwnd, tp->snd_cwnd_clamp); //Do not allow snd_cwnd to grow above this
}

static u32 course_quantization_budget(struct sock *sk, u32 cwnd, int gain)
{
	struct course*course= inet_csk_ca(sk);

	/* Allow enough full-sized skbs in flight to utilize end systems. */
	cwnd += 3 * course->tso_segs_goal;

	/* Reduce delayed ACKs by rounding up cwnd to the next even number. */
	cwnd = (cwnd + 1) & ~1U;

	/* Ensure gain cycling gets inflight above BDP even for small BDPs. */
	if (course->mode == course_PROBE_BW && gain > course_UNIT)
		cwnd += 2;

	return cwnd;
}

static u32 course_bdp(struct sock *sk, u32 bw, int gain)
{
	struct course*course= inet_csk_ca(sk);
	u32 bdp;
	u64 w;
	if (unlikely(course->min_rtt_us == ~0U))	 /* no valid RTT samples yet? */
		return TCP_INIT_CWND;  /* be safe: cap at default initial cwnd*/
	w = (u64)bw * course->min_rtt_us;
	bdp = (((w * gain) >> course_SCALE) + BW_UNIT - 1) / BW_UNIT;

	return bdp;
}

static u32 course_inflight(struct sock *sk, u32 bw, int gain)
{
	u32 inflight;

	inflight = course_bdp(sk, bw, gain);
	inflight = course_quantization_budget(sk, inflight, gain);

	return inflight;
}

static u32 course_max_bw(const struct sock *sk)
{
	struct course*course= inet_csk_ca(sk);

	return minmax_get(&course->bw);
}

static void course_check_drain(struct sock *sk, const struct rate_sample *rs)
{
	struct course*course= inet_csk_ca(sk);

	if (course->mode == course_SLOWSTART && course_full_bw_reached(sk)) {
		course->mode = course_DRAIN;	/* drain queue we created */
		course->pacing_gain = course_drain_gain;	/* pace slow to drain */
		course->cwnd_gain = course_high_gain;	/* maintain cwnd */
	}	/* fall through to check if in-flight is already small: */
	if (course->mode == course_DRAIN &&
	    tcp_packets_in_flight(tcp_sk(sk)) <=
	    course_inflight(sk, course_max_bw(sk), course_UNIT))
		course_reset_probe_bw_mode(sk);  /* we estimate queue is drained */
}

static void course_save_cwnd(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);

	if (course->prev_ca_state < TCP_CA_Recovery && course->mode != course_PROBE_RTT)
		course->prior_cwnd = tp->snd_cwnd;  /* this cwnd is good enough */
	else  /* loss recovery or course_PROBE_RTT have temporarily cut cwnd */
		course->prior_cwnd = max(course->prior_cwnd, tp->snd_cwnd);
}

static void course_reset_mode(struct sock *sk)
{
	if (!course_full_bw_reached(sk))
		course_reset_slowstart_mode(sk);
	else
		course_reset_probe_bw_mode(sk);
}

static void course_check_probe_rtt_done(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);

	if (!(course->probe_rtt_done_stamp &&
	      after(tcp_jiffies32, course->probe_rtt_done_stamp)))
		return;

	course->min_rtt_stamp = tcp_jiffies32;  /* wait a while until PROBE_RTT */
	tp->snd_cwnd = max(tp->snd_cwnd, course->prior_cwnd);
	course_reset_mode(sk);
}

static void course_update_min_rtt(struct sock *sk, const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	bool filter_expired;
    if(course->mode==course_SLOWSTART){
        if(course->rtt_last == 0)
            course->rtt_last = course->min_rtt_us;
        if(rs->rtt_us >= 0 && rs->rtt_us > (course->rtt_last * 7/5)){
            course->rtt_up_count++;
            course->rtt_last = rs->rtt_us;
        }
        if(course->rtt_up_count >= 2){
            course->rtt_up_count = 0;
            course->rtt_last = course->min_rtt_us;
            course_slow_start_rate_down(sk);
        }
    }
	/* Track min RTT seen in the min_rtt_win_sec filter window: */
	filter_expired = after(tcp_jiffies32,
			       course->min_rtt_stamp + course_min_rtt_win_sec * HZ);
	if (rs->rtt_us >= 0 &&
	    (rs->rtt_us < course->min_rtt_us || filter_expired)) {
		course->min_rtt_us = rs->rtt_us;
		course->min_rtt_stamp = tcp_jiffies32;
	}

	if (course_probe_rtt_mode_ms > 0 && filter_expired &&
	    !course->idle_restart && course->mode != course_PROBE_RTT) {
		course->mode = course_PROBE_RTT;  /* dip, drain queue */
		course->pacing_gain = course_UNIT;
		course->cwnd_gain = course_UNIT;
		course_save_cwnd(sk);  /* note cwnd so we can restore it */
		course->probe_rtt_done_stamp = 0;
	}

	if (course->mode == course_PROBE_RTT) {
		/* Ignore low rate samples during this mode. */
		tp->app_limited =
			(tp->delivered + tcp_packets_in_flight(tp)) ? : 1;
		/* Maintain min packets in flight for max(200 ms, 1 round). */
		if (!course->probe_rtt_done_stamp &&
		    tcp_packets_in_flight(tp) <= course_cwnd_min_target) {
			course->probe_rtt_done_stamp = tcp_jiffies32 +
				msecs_to_jiffies(course_probe_rtt_mode_ms);
			course->probe_rtt_round_done = 0;
			course->next_rtt_delivered = tp->delivered;
		} else if (course->probe_rtt_done_stamp) {
			if (course->round_start)
				course->probe_rtt_round_done = 1;
			if (course->probe_rtt_round_done)
				course_check_probe_rtt_done(sk);
		}
	}
	/* Restart after idle ends only once we process a new S/ACK for data */
	if (rs->delivered > 0)
		course->idle_restart = 0;
}

static u64 course_rate_bytes_per_sec(struct sock *sk, u64 rate, int gain)
{
    struct course*course= inet_csk_ca(sk);
	rate *= tcp_mss_to_mtu(sk, tcp_sk(sk)->mss_cache);
	rate *= gain;
    if(course->loss_packet_stamp2 != 0 && course->mode==course_PACKET_LOSS){
        rate = rate * (3 + (course->loss_packet_stamp2 - course->loss_packet_stamp1) * 1000 / HZ) / 3;
        course->rate_lock++;
    }
	rate >>= course_SCALE;
	rate *= USEC_PER_SEC;
	return rate >> BW_SCALE;
}

static u32 course_bw_to_pacing_rate(struct sock *sk, u32 bw, int gain)
{
	u64 rate = bw;

	rate = course_rate_bytes_per_sec(sk, rate, gain);
	rate = min_t(u64, rate, sk->sk_max_pacing_rate);
	return rate;
}

static void course_init_pacing_rate_from_rtt(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	u64 bw;
	u32 rtt_us;

	if (tp->srtt_us) {		/* any RTT sample yet? */
		rtt_us = max(tp->srtt_us >> 3, 1U);
		course->has_seen_rtt = 1;
	} else {			 /* no RTT sample yet */
		rtt_us = USEC_PER_MSEC;	 /* use nominal default RTT */
	}
	bw = (u64)tp->snd_cwnd * BW_UNIT;
	do_div(bw, rtt_us);
	sk->sk_pacing_rate = course_bw_to_pacing_rate(sk, bw, course_high_gain);
}

static void course_set_pacing_rate(struct sock *sk, u32 bw, int gain)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	u32 rate = course_bw_to_pacing_rate(sk, bw, gain);

	if (unlikely(!course->has_seen_rtt && tp->srtt_us))
		course_init_pacing_rate_from_rtt(sk);
	if (course_full_bw_reached(sk) || rate > sk->sk_pacing_rate)
		sk->sk_pacing_rate = rate;
    if (course->mode == course_PACKET_LOSS){
        sk->sk_pacing_rate = rate;
    }
}

static void course_set_tso_segs_goal(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	u32 min_segs;

	min_segs = sk->sk_pacing_rate < (course_min_tso_rate >> 3) ? 1 : 2;
	course->tso_segs_goal = min(tcp_tso_autosize(sk, tp->mss_cache, min_segs),
				 0x7FU);
}

static bool course_set_cwnd_to_recover_or_restore(
	struct sock *sk, const struct rate_sample *rs, u32 acked, u32 *new_cwnd)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	u8 prev_state = course->prev_ca_state, state = inet_csk(sk)->icsk_ca_state;
	u32 cwnd = tp->snd_cwnd;

	/* An ACK for P pkts should release at most 2*P packets. We do this
	 * in two steps. First, here we deduct the number of lost packets.
	 * Then, in course_set_cwnd() we slow start up toward the target cwnd.
	 */
	if (rs->losses > 0)
		cwnd = max_t(s32, cwnd - rs->losses, 1);

	if (state == TCP_CA_Recovery && prev_state != TCP_CA_Recovery) {
		/* Starting 1st round of Recovery, so do packet conservation. */
		course->packet_conservation = 1;
		course->next_rtt_delivered = tp->delivered;  /* start round now */
		/* Cut unused cwnd from app behavior, TSQ, or TSO deferral: */
		cwnd = tcp_packets_in_flight(tp) + acked;
	} else if (prev_state >= TCP_CA_Recovery && state < TCP_CA_Recovery) {
		/* Exiting loss recovery; restore cwnd saved before recovery. */
		cwnd = max(cwnd, course->prior_cwnd);
		course->packet_conservation = 0;
	}
	course->prev_ca_state = state;

	if (course->packet_conservation) {
		*new_cwnd = max(cwnd, tcp_packets_in_flight(tp) + acked);
		return true;	/* yes, using packet conservation */
	}
	*new_cwnd = cwnd;
	return false;
}

static void course_set_cwnd(struct sock *sk, const struct rate_sample *rs,
			 u32 acked, u32 bw, int gain)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);
	u32 cwnd = 0, target_cwnd = 0;

	if (!acked)
		return;

	if (course_set_cwnd_to_recover_or_restore(sk, rs, acked, &cwnd) && course->mode!=course_PACKET_LOSS)
		goto done;

    if(course->loss_packet_stamp2 != 0 && course->mode==course_PACKET_LOSS){
        gain = gain * (3 + (course->loss_packet_stamp2 - course->loss_packet_stamp1) * 1000 / HZ) / 3;
        course->rate_lock++;
    }
	target_cwnd = course_bdp(sk, bw, gain);
	target_cwnd = course_quantization_budget(sk, target_cwnd, gain);

	if (course_full_bw_reached(sk))  
		cwnd = min(cwnd + acked, target_cwnd);
	else if (cwnd < target_cwnd || tp->delivered < TCP_INIT_CWND)
		cwnd = cwnd + acked;
	cwnd = max(cwnd, course_cwnd_min_target);

done:
	tp->snd_cwnd = min(cwnd, tp->snd_cwnd_clamp);
	if (course->mode == course_PROBE_RTT)  
		tp->snd_cwnd = min(tp->snd_cwnd, course_cwnd_min_target);
    if (course->mode == course_PACKET_LOSS){
        target_cwnd = max(target_cwnd,course_cwnd_min_target);
    }
}

static void course_main(struct sock *sk, const struct rate_sample *rs)
{
	struct course*course= inet_csk_ca(sk);
    struct tcp_sock *tp = tcp_sk(sk);
	u32 bw;

    course_update_bw(sk, rs);
	course_update_cycle_phase(sk, rs);
	course_check_full_bw_reached(sk, rs);
    course_check_drain(sk, rs);
	course_update_min_rtt(sk, rs);
    course_check_loss_out(sk);
    course_rate_lock(sk);

    course_slow_start(sk,tp,rs->acked_sacked);
    /*if(course->mode == course_SLOWSTART){
        course_slow_start(sk,tp,rs->acked_sacked);
        u64 rate = (u64)tp->mss_cache * ((USEC_PER_SEC / 100) << 3);
        sk->sk_pacing_rate = min(rate, sk->sk_max_pacing_rate);
        return;
    }*/

	bw = course_bw(sk);
	course_set_pacing_rate(sk, bw, course->pacing_gain);
	course_set_tso_segs_goal(sk);
	course_set_cwnd(sk, rs, rs->acked_sacked, bw, course->cwnd_gain);
}

static void course_init(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct course*course= inet_csk_ca(sk);

	course->prior_cwnd = 0;
	course->tso_segs_goal = 0;
	course->rtt_cnt = 0;
	course->next_rtt_delivered = tp->delivered;
	course->prev_ca_state = TCP_CA_Open;
	course->packet_conservation = 0;
	course->probe_rtt_done_stamp = 0;
	course->probe_rtt_round_done = 0;
	course->min_rtt_us = tcp_min_rtt(tp);
	course->min_rtt_stamp = tcp_jiffies32;
	minmax_reset(&course->bw, course->rtt_cnt, 0);  /* init max bw to 0 */
	course->has_seen_rtt = 0;
	course_init_pacing_rate_from_rtt(sk);
	course->round_start = 0;
	course->idle_restart = 0;
	course->full_bw_reached = 0;
	course->full_bw = 0;
	course->full_bw_cnt = 0;
	course->cycle_mstamp = 0;
	course->cycle_idx = 0;
	course_reset_lt_bw_sampling(sk);
	course_reset_slowstart_mode(sk);
    course->loss_packet_stamp1 = 0;
    course->loss_packet_stamp2 = 0;
    course->loss_count = 0;
    course->rtt_up_count = 0;  
    course->loss_last_stamp =0;
	cmpxchg(&sk->sk_pacing_status, SK_PACING_NONE, SK_PACING_NEEDED);
    course->down_count=1;
    tp->snd_ssthresh=0;
    course->rate_lock=0;
}

static u32 course_ssthresh(struct sock *sk)
{
    return 0;
}

static u32 course_undo_cwnd(struct sock *sk)
{
	struct course*course= inet_csk_ca(sk);

	course->full_bw = 0;   /* spurious slow-down; reset full pipe detection */
	course->full_bw_cnt = 0;
	course_reset_lt_bw_sampling(sk);
	return tcp_sk(sk)->snd_cwnd;
}

static void course_set_state(struct sock *sk, u8 new_state)
{
	struct course*course= inet_csk_ca(sk);

    if(new_state == TCP_CA_Recovery || new_state == TCP_CA_Loss){
        if(course->loss_last_stamp==0 || after(tcp_jiffies32 , course->loss_last_stamp + msecs_to_jiffies(loss_thereshold_ms))){
            course->loss_count++;
            course->loss_last_stamp = tcp_jiffies32;
        }else{
            course->loss_count = 0;
        }
    }

	if((new_state == TCP_CA_Recovery || new_state == TCP_CA_Loss) && course->mode == course_SLOWSTART){
        course_slow_start_rate_down(sk);
        course->prev_ca_state = new_state;
        return;
    }

    if(course->loss_count <= 2)
        return;

    if((new_state == TCP_CA_Recovery || new_state == TCP_CA_Loss) && course->mode == course_DRAIN){
        return;
    }

    if ((new_state == TCP_CA_Recovery || new_state == TCP_CA_Loss) && course->loss_packet_stamp1 == 0){
        course->prev_ca_state = new_state;
        course->loss_packet_stamp1 = tcp_jiffies32;
        return;
    }

    if (new_state == TCP_CA_Recovery && course->loss_packet_stamp1 != 0){ //second recorvey
        if(after(tcp_jiffies32 , course->loss_packet_stamp1 + msecs_to_jiffies(loss_thereshold_ms))){
            course->prev_ca_state = new_state;
            course->loss_packet_stamp1 = tcp_jiffies32;
            return;
        }
        course_reset_packet_loss_mode(sk);
        course->prev_ca_state = new_state;
        return;
    }

	if (new_state == TCP_CA_Loss && course->loss_packet_stamp1 != 0) { //second loss
        if(after(tcp_jiffies32 , course->loss_packet_stamp1 + msecs_to_jiffies(loss_thereshold_ms))){
            course->prev_ca_state = new_state;
            course->loss_packet_stamp1 = tcp_jiffies32;
            return;
        }
        course_reset_packet_loss_mode(sk);
		course->prev_ca_state = new_state;
        return;
	}
    
	if ((new_state == TCP_CA_Recovery || new_state == TCP_CA_Loss) && course->mode == course_PACKET_LOSS) { //loss in state loss
        if(after(tcp_jiffies32 , course->loss_packet_stamp2 + msecs_to_jiffies(loss_thereshold_ms))){
            course->loss_packet_stamp1 = course->loss_packet_stamp2;
            course->loss_packet_stamp2 = tcp_jiffies32;
            course->cwnd_gain = course_drop_gain;
            course->pacing_gain =course_drop_gain;
            return;
        }
	}
}

static struct tcp_congestion_ops tcp_course_cong_ops __read_mostly = {
	.flags		= TCP_CONG_NON_RESTRICTED,
	.name		= "course",
	.owner		= THIS_MODULE,
	.init		= course_init,
	.cong_control	= course_main,
	.undo_cwnd	= course_undo_cwnd,
	.ssthresh	= course_ssthresh,
	.set_state	= course_set_state,
};

static int __init course_register(void)
{
	BUILD_BUG_ON(sizeof(struct course) > ICSK_CA_PRIV_SIZE);
	return tcp_register_congestion_control(&tcp_course_cong_ops);
}

static void __exit course_unregister(void)
{
	tcp_unregister_congestion_control(&tcp_course_cong_ops);
}

module_init(course_register);
module_exit(course_unregister);

MODULE_AUTHOR("Wu Wenhao <wu_wenhao555@163.com>");
MODULE_AUTHOR("Fei Jiaqiang <feijiaqiang22@mails.ucas.ac.cn>");
MODULE_LICENSE("Dual BSD/GPL");
MODULE_DESCRIPTION("TCP Course (A naive congestion control for homework)");