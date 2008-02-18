
/*--------- threads support ------------------------- g.f. -----*/
/*--------- lower half of the Oberon Threads module             */

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "Threads.h"

static int suid_root;
static _thr_ mainthread = 0;

extern void SetSigaltstack();

_mut_ _mtx_init( ) {
    _mut_ mtx;

    mtx = (_mut_)malloc( sizeof(mutex_t) );
    mutex_init( mtx, USYNC_THREAD, NULL );
    return mtx;
}

void _mtx_destroy(_mut_ mtx) {
    mutex_destroy( mtx );
    free( mtx );
}


void _mtx_lock(_mut_ mtx) {
    mutex_lock( mtx );
}


void _mtx_unlock(_mut_ mtx) {
    mutex_unlock( mtx );
}

_con_ _con_init( ) {
    _con_	c;

    c = (_con_)malloc( sizeof(cond_t) );
    cond_init( c, USYNC_THREAD, NULL );
    return c;
}

void _con_destroy(_con_ c) {
    cond_destroy( c );
    free( c );
}

void _con_wait( _con_ c, _mut_ m ) {
    cond_wait( c, m );
}

void _con_signal( _con_ c ) {
   cond_signal( c );
}

void starter( oberon_proc p ) {
    sigset_t orig, new;

    SetSigaltstack();
    sigfillset( &new );
    sigdelset( &new, SIGILL );
    sigdelset( &new, SIGTRAP );
    sigdelset( &new, SIGEMT );
    sigdelset( &new, SIGFPE );
    sigdelset( &new, SIGBUS );
    sigdelset( &new, SIGSEGV );
    sigdelset( &new, SIGSYS );
    sigdelset( &new, SIGPIPE );
    sigdelset( &new, SIGALRM );
    thr_sigsetmask( SIG_SETMASK, &new, &orig );
    pthread_setcancelstate( PTHREAD_CANCEL_ENABLE, NULL );
    pthread_setcanceltype( PTHREAD_CANCEL_ASYNCHRONOUS, NULL );
    p(NULL);
    thr_exit( 0 );
}


_thr_ _thr_start( oberon_proc p, int len ) {
    _thr_ id;
    int	err;

    if ((len != 0) && (len < 16*1024)) {
        len =  16*1024;
    }

    err = thr_create( NULL, len, starter, p, THR_BOUND|THR_DETACHED, &id );
    if (err != 0)
        return 0;
    return id;
}


_thr_ _thr_this() {
    return thr_self();
}


void _thr_sleep(int ms) {
    struct timespec sltime, rem;

    sltime.tv_sec = ms/1000;
    sltime.tv_nsec = 1000000*(ms%1000);
    nanosleep( &sltime, &rem );
}


void _thr_pass( ) {
    _thr_yield( 1 );
}

void _thr_exit() {
    thr_exit( 0 );
}


void _thr_suspend(_thr_ thr) {
    thr_suspend( thr );
}

void _thr_resume(_thr_ thr) {
    thr_continue( thr );
}


void _thr_setprio(_thr_ thr, int prio) {
    thr_setprio( thr, prio );
}

int _thr_getprio(_thr_ thr) {
    int prio;

    thr_getprio( thr, &prio );
    return ( prio );
}


void _thr_kill(_thr_ thr) {
    if (thr != mainthread) {
        if (thr == thr_self())
            thr_exit( 0 );
        else 
	    pthread_cancel( thr );
    }
}


/* thr_initialize returns 0 (FALSE) if the program has
   been compiled without threads suport. If the program
   has no suid root privilleges, priorities are disabled
   and low and high both return 0. */

int _thr_initialize( int *low, int* high ) {
    mainthread = thr_self();
    *low = 0;  *high = 100;
    return 1;
}

