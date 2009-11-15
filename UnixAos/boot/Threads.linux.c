
/*--------- threads support ------------------------- g.f. -----*/
/*--------- lower half of the Oberon Threads module             */
/*
 * The PowerPC Oberon compiler follows the old MacOS ABI which
 * is different from the ABI used in Linux and MacOS X. Because of
 * this the interfacing between C and Oberon is a little bit
 * tricky and this module has to be compiled with
 *	-DPowerPC_Oberon_Compiler
 */


#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <signal.h>
#include <semaphore.h>
#include <errno.h>
#include <bits/local_lim.h>
#include "Threads.h"


extern int suid_root;
extern int debug;

extern void SetSigaltstack();

static _thr_ mainthread = 0;

static int prio_high, prio_low;

static pthread_mutex_t prio_mutex;

static struct sched_param oldparam;
static int oldpolicy;

#ifdef PowerPC_Oberon_Compiler
    extern void CallOberon( int pc, int sb );
#endif

#define	T_SIGSUSPEND	SIGUSR1
#define	T_SIGRESUME	SIGUSR2

static struct sigaction sasuspend, saresume;
static pthread_mutex_t suspend_mutex;
static int suspend_done;
static int resume_done;


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

#ifdef SOLARIS
    c = (_con_)malloc( sizeof(cond_t) );
#else
    c = (_con_)malloc( sizeof(pthread_cond_t) );
#endif
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


static void suspend_handler(int sig) {
    sigset_t block;

    sigfillset( &block );
    sigdelset( &block, T_SIGRESUME );
    //if (debug&2) printf( "thread %8x suspended\n", pthread_self() );
    suspend_done = 1;

    sigsuspend( &block ); /* await T_SIGRESUME */

    //if (debug&2) printf( "thread %8x resuming\n", pthread_self() );
    resume_done = 1;
}



static  void resume_handler(int sig) {
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
    sigdelset( &new, T_SIGSUSPEND );
    //sigdelset( &new, T_SIGRESUME );
    pthread_sigmask( SIG_SETMASK, &new, &old );

    pthread_setcancelstate( PTHREAD_CANCEL_ENABLE, NULL );
    pthread_setcanceltype( PTHREAD_CANCEL_ASYNCHRONOUS, NULL );
    if ( suid_root != 0) {
        param.sched_priority = 0;
        pthread_setschedparam( me, SCHED_OTHER, &param );
    }

#ifdef PowerPC_Oberon_Compiler
    CallOberon( proc->pc, proc->sb );
#else
    proc();
#endif
    pthread_exit( NULL );
    return NULL;
}



#ifdef PowerPC_Oberon_Compiler
_thr_ 
_thr_start( int PC, int SB, int len ) {
    
    oberon_proc p = (oberon_proc)malloc(8);
    _thr_ id;
    pthread_attr_t attr;
    p->pc = PC; p->sb = SB;
#else
_thr_ 
_thr_start( oberon_proc p, int len ) {
    
    _thr_ id;
    pthread_attr_t attr;
#endif
     
    if (len < PTHREAD_STACK_MIN) len = PTHREAD_STACK_MIN;
    pthread_attr_init( &attr );
    pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);
    pthread_attr_setdetachstate( &attr, PTHREAD_CREATE_DETACHED );
    if ( suid_root ) {
        pthread_attr_setstacksize( &attr, len );
    }
    if (pthread_create( &id, &attr, starter, p ) != 0) return 0;
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

    pthread_mutex_lock( &suspend_mutex );
    suspend_done = 0;
    pthread_kill( thr, T_SIGSUSPEND );
    while (suspend_done != 1) _thr_sleep( 1 );
    pthread_mutex_unlock( &suspend_mutex );
}



void _thr_resume(_thr_ thr) {
    int n;

    pthread_mutex_lock( &suspend_mutex );
    resume_done = 0; n = 1;
    pthread_kill( thr, T_SIGRESUME ); 
    while (resume_done != 1 && n < 20) _thr_sleep( n++ );
    pthread_mutex_unlock( &suspend_mutex );
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
    
    pthread_mutex_init( &suspend_mutex, NULL );
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

    sigemptyset( &sasuspend.sa_mask );
    sigaddset( &sasuspend.sa_mask, T_SIGRESUME );
    sasuspend.sa_flags = 0;
    sasuspend.sa_handler = suspend_handler;
    sigaction( T_SIGSUSPEND, &sasuspend, NULL );

    sigemptyset( &saresume.sa_mask );
    saresume.sa_flags = 0;
    saresume.sa_handler = resume_handler;
    sigaction( T_SIGRESUME, &saresume, NULL );
    
    return 1;
}



