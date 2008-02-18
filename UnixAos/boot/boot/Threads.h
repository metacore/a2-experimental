
#include <stdio.h>

#ifdef SOLARIS
# define _REENTRANT
# define __EXTENSIONS__  1
# include <thread.h>
# include <pthread.h>
# include <synch.h>
  typedef mutex_t *	_mut_;
  typedef cond_t *	_con_;
  typedef thread_t	_thr_;
  typedef void* (*oberon_proc)(void *);
#else
  /*** Linix | Darwin ***/
# include <pthread.h>
  typedef pthread_mutex_t *	_mut_;
  typedef pthread_cond_t *	_con_;
  typedef pthread_t		_thr_;
# ifdef PowerPC_Oberon_Compiler
	typedef struct { int pc, sb; } *oberon_proc;
# else
	typedef	int (*oberon_proc)();
# endif
#endif


extern _mut_	_mtx_init( );
extern void	_mtx_destroy( _mut_ mtx );
extern void	_mtx_lock(    _mut_ mtx );
extern void	_mtx_unlock(  _mut_ mtx );

extern _con_	_con_init( );
extern void	_con_destroy( _con_ con );
extern void	_con_wait ( _con_ con, _mut_ mtx );
extern void	_con_signal(  _con_ con );

#ifdef PowerPC_Oberon_Compiler
extern _thr_	_thr_start( int PC, int SB, int len );
#else
extern _thr_	_thr_start( oberon_proc p, int len );
#endif

extern _thr_	_thr_this( );
extern void	_thr_sleep( int ms );
extern void	_thr_pass( );
extern void	_thr_exit( );
extern void	_thr_sendsig( _thr_ thr, int sig );
extern void	_thr_suspend( _thr_ thr );
extern void	_thr_resume(  _thr_ thr );
extern void	_thr_setprio( _thr_ thr, int prio );
extern int 	_thr_getprio( _thr_ thr );
extern void	_thr_kill( _thr_ thr );

extern int 	_thr_initialize( int *low, int* high );


