
/*--------- threads support ------------------------- g.f. -----*/
/*--------- lower half of the Oberon Threads module             */


#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <signal.h>
#include <semaphore.h>
#include <errno.h>
#include "Threads.h"


extern int suid_root;
extern int debug;

extern void SetSigaltstack();

static _thr_ mainthread = 0;

static int prio_high, prio_low;

static pthread_mutex_t prio_mutex;


void _thr_sleep(int ms) {

    struct timespec sltime, rem;

    sltime.tv_sec = ms/1000;
    sltime.tv_nsec = 1000000*(ms%1000);
    while (nanosleep( &sltime, &rem ) < 0 && errno == EINTR)
    	sltime = rem;
}


_mut_
_mtx_init( ) {
    _mut_ mtx;

    mtx = (_mut_)malloc( sizeof(pthread_mutex_t) );
    pthread_mutex_init( mtx, NULL );
    return mtx;
}



void _mtx_destroy(_mut_ mtx) {
    
    (void)pthread_mutex_destroy( mtx );
    free( mtx );
}



void _mtx_lock(_mut_ mtx) {
    
    (void)pthread_mutex_lock( mtx );
}



void _mtx_unlock(_mut_ mtx) {
    
    (void)pthread_mutex_unlock( mtx );
}


_con_ _con_init( ) {
    _con_	c;

    c = (_con_)malloc( sizeof(pthread_cond_t) );
    pthread_cond_init( c, NULL );
    return c;
}

void _con_destroy(_con_ c) {
    pthread_cond_destroy( c );
    free( c );
}

void _con_wait( _con_ c, _mut_ m ) {
    pthread_cond_wait( c, m );
}

void _con_signal( _con_ c ) {
    pthread_cond_signal( c );
}


static void *starter(void *p) {
    _thr_ me = pthread_self();
    oberon_proc proc = (oberon_proc)p;
    sigset_t old, new;
    struct sched_param param;

    SetSigaltstack();
    sigfillset( &new );
    sigdelset( &new, SIGILL );
    sigdelset( &new, SIGTRAP );
    sigdelset( &new, SIGFPE );
    sigdelset( &new, SIGBUS );
    sigdelset( &new, SIGSEGV );
    sigdelset( &new, SIGTERM );
    pthread_sigmask( SIG_SETMASK, &new, &old );

    pthread_setcancelstate( PTHREAD_CANCEL_ENABLE, NULL );
    pthread_setcanceltype( PTHREAD_CANCEL_ASYNCHRONOUS, NULL );
    if ( suid_root != 0) {
        param.sched_priority = 0;
        pthread_setschedparam( me, SCHED_OTHER, &param );
    }

    proc();
    pthread_exit( NULL );
    return NULL;
}



_thr_ 
_thr_start( oberon_proc p, int len ) {
    
    _thr_ id;
    pthread_attr_t attr;
     
    if (len < PTHREAD_STACK_MIN) len = PTHREAD_STACK_MIN;
    pthread_attr_init( &attr );
    pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);
    pthread_attr_setdetachstate( &attr, PTHREAD_CREATE_DETACHED );
    if ( suid_root ) {
        pthread_attr_setstacksize( &attr, len );
    }
    if (pthread_create( &id, &attr, starter, p ) != 0) {
        perror( "pthread_create" );
	return 0;
    }
    return id;
}



_thr_ _thr_this() {

    return pthread_self();
}



void _thr_pass( ) {

    _thr_sleep( 10 );
}



void _thr_exit( ) {
    
    pthread_exit( 0 );
}



void _thr_sendsig( _thr_ thr, int sig ) {

    pthread_kill( thr, sig );
}



void _thr_suspend(_thr_ thr) {
    mach_port_t mthread;

    mthread = pthread_mach_thread_np(thr);
    thread_suspend(mthread);
}



void _thr_resume(_thr_ thr) {
    mach_port_t mthread;

    mthread = pthread_mach_thread_np(thr);
    thread_resume(mthread);
}



void _thr_setprio(_thr_ thr, int prio) {

    struct sched_param param;
    int policy;

    if ( suid_root == 0) return;

    pthread_mutex_lock( &prio_mutex );
    seteuid(0);
    pthread_getschedparam( thr, &policy, &param );
    param.sched_priority = prio;
    if (pthread_setschedparam( thr, SCHED_FIFO, &param ) != 0)
    	perror("pthread_setschedparam");
    seteuid( getuid());
    pthread_mutex_unlock( &prio_mutex );
}



int _thr_getprio(_thr_ thr) {

    struct sched_param param;
    int policy;

    if ( suid_root == 0) return 0;

    pthread_mutex_lock( &prio_mutex );
    pthread_getschedparam( thr, &policy, &param );
    pthread_mutex_unlock( &prio_mutex );
    return ( param.sched_priority );
}



void _thr_kill(_thr_ thr) {

    if (thr != mainthread) {
    	pthread_detach( thr );
    	if (thr == pthread_self())
    	    pthread_exit( 0 );
    	else {
    	    pthread_cancel( thr );
        } 
    }
}


/* _thr_initialize returns 0 (FALSE) if no threads support is compiled in */

int _thr_initialize( int *low, int* high ) {
    struct sched_param param;
    
    mainthread = pthread_self();
    if ( suid_root == 0) {
    	prio_high = sched_get_priority_max(SCHED_RR);
    	prio_low = sched_get_priority_min(SCHED_RR);
    	*low = prio_low;
    	*high = prio_high;
        param.sched_priority = prio_high;
        pthread_setschedparam( mainthread, SCHED_RR, &param );
    }else{
    	prio_high = sched_get_priority_max(SCHED_FIFO);
    	prio_low = sched_get_priority_min(SCHED_FIFO);
    	*low = prio_low;
    	*high = prio_high;	

    	pthread_mutex_init( &prio_mutex, NULL );
    }
    return 1;
}



