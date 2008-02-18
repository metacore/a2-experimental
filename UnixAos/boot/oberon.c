/*------------------------------------------------------
 * Oberon Boot File Loader RC, JS 27.4.93/2.12.93, HP-UX 9.0 Version
 *
 * Oberon Boot File Loader for Linux
 * derived from HP and Windows Boot Loader
 * MAD, 23.05.94
 * PR,  01.02.95  support for sockets added
 * PR,  05.02.95  support for V24 added
 * PR,  23.12.95  migration to shared ELF libraries
 * RLI, 22.08.96  added some math primitives
 * RLI, 27.01.97  included pixmap
 * RLI, 13.10.97  changed name of Fontmap - File
 * g.f. 01.11.99  added InstallTraphandler
 *		  added Threads support
 *		  removed cmd line parameter evaluation
 * g.f. 22.11.04  call to mprotect added
 * g.f. 03.04.07  Darwin/Intel version
 *
 *-----------------------------------------------------------*/

#include <sys/types.h>
#include <fcntl.h>
#include <dlfcn.h>
#include <unistd.h>
#include <stdlib.h>
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>
#include <math.h>		/* RLI */
#include <setjmp.h>		/* g.f. */
#ifdef MAC
#  include <sys/ucontext.h>
#  include <sys/_types.h>
#endif
#include <signal.h>		/* g.f. */
#include <limits.h>		/* g.f. */
#include "Threads.h"		/* g.f. */
#include <sys/mman.h>
#include <X11/Xlib.h>


typedef unsigned int	uint;
typedef unsigned int	addr;

typedef void (*Proc)();

FILE *fd;
char *OBERON;
char path[4096];
char *dirs[255];
char fullname[512];
int nofdir;
char defaultpath[] = ".:/usr/aos:/usr/aos/obj:/usr/aos/XFonts";
#ifdef SOLARIS
  char bootname[64] = "SolarisOberonCore";
#endif
#ifdef LINUX
  char bootname[64] = "LinuxOberonCore";
#endif
#ifdef MAC
  char bootname[64] = "MacOberonCore";
#endif
uint heapSize;
addr heapAdr;
int Argc;
char **Argv;
int debug;
int suid_root;

static stack_t sigstk;

#define BLSIZE	4096
#define SIGSTACKSIZE 32*BLSIZE

typedef	void(*traphandler_t)(long, void*, void*, int);

static traphandler_t	OberonTrapHandler;

	
#ifdef MAC
static traphandler(int sig, siginfo_t *scp, ucontext_t *ucp) {
        mcontext_t mc;

	if (debug)
		printf("\nhandler for signal %d got called\n", sig);
	mc = ucp->uc_mcontext;

	OberonTrapHandler(0, mc, scp, sig); /* rev. order: Oberon <--> C */
	// printf("returned fron Oberon Trap Handler\n");
	return;
}
#else
static void traphandler(int sig, void *scp, void *ucp) {
	int x;
	
	if (debug)
		printf("\nhandler for signal %d got called, ucp = %x, handler sp = %x\n", 
			sig, ucp, &x);
	OberonTrapHandler(0, ucp, scp, sig); /* rev. order: Oberon <--> C */
	// printf("returned fron Oberon Trap Handler\n");
	return;
}

#endif



static void installHandler(int sig) {
	struct sigaction act;
	sigset_t mask;

	sigemptyset(&mask);
	act.sa_mask = mask;
	act.sa_flags =  SA_SIGINFO|SA_ONSTACK|SA_NODEFER;
#ifdef LINUX
	act.sa_handler = (__sighandler_t)traphandler;
#else
	act.sa_handler = traphandler;
#endif
	if (sigaction( sig, &act, NULL ) != 0) {
		perror("sigaction");
	}
}


void InitTrapHandler() {
	int i;
	
	for (i = 1; i <= 15; i++) {
	     if (i != 9) installHandler( i );
	}
}


static void InstallTrapHandler(traphandler_t p) {
	
	if (debug)
		printf("Installing Oberon TrapHandler\n");
	OberonTrapHandler = p;
}


void SetSigaltstack() {

	if (sigaltstack(&sigstk, NULL) < 0)
		perror("sigaltstack");
}


static void CreateSignalstack() {
	sigstk.ss_sp = mmap( NULL, SIGSTACKSIZE, 
			     PROT_READ | PROT_WRITE, 
			     MAP_PRIVATE | MAP_ANON, 
			     -1, 0);
        if (sigstk.ss_sp == MAP_FAILED){
		printf("mmap for signalstack failed\n" );
		exit( 1 );
	}
	sigstk.ss_size = SIGSTACKSIZE;
	sigstk.ss_flags = 0;
	if (debug)
		printf( "Signalstack created [%x ... %x]\n", 
	 	        sigstk.ss_sp, sigstk.ss_sp + SIGSTACKSIZE );
	SetSigaltstack();
}


/*--------------------------------------------------- g.f. -----*/


int dl_open(char *lib, int mode)
{
  void *handle;

  if (debug&1) printf("dl_open: %s\n", lib);
  if ((handle = dlopen(lib, mode)) == NULL) {
    if (debug&1)
      printf("dl_open: %s not loaded, error = %s\n", lib, dlerror());
  }
  if (debug&1) printf("dl_open: handle = %x\n", handle);

  return (int)handle;
}

void dl_close(int handle)	/* not necessary */
{
  dlclose((void *)handle);
}

static int errnof()
{
	return errno;
}

static void o_printf(char *fs, int p1, int p2, int p3, int p4) {
	printf(fs, p1, p2, p3, p4);
	fflush(stdout);
}

int o_stat(char* name, void* buf) {
	return stat(name, (struct stat *) buf);
}

int o_lstat(char* name, void* buf) {
	return lstat(name, (struct stat *) buf);
}

int o_fstat(int fd, void* buf) {
	return fstat(fd, (struct stat *) buf);
}

int o_open(char* name, int flags, int mode) {
	int r;
	
	r = open(name, flags, mode);
	if (r < 0) { fprintf(stderr, "<%s> ", name ); perror("open");  }
	return r;
}

void *o_malloc( long size ) {
	return malloc( size );
}

void *o_memalign( long alignment, long size ) {
	return calloc( (size + alignment - 1)/alignment, alignment );
}

void *o_calloc( long nelem, long elsize ) {
	return calloc( nelem, elsize );
}

int o_lseek( int fd, long pos, int whence ) {
	return lseek( fd, pos, whence );
}


static void (*oberonXErrorHandler) (long p4, long p3, long err, long displ );
static void (*oberonXIOErrorHandler) (long p4, long p3, long p2, long displ );

static int X11ErrorHandler( Display *d, XErrorEvent *err ) {
	printf( "X11ErrorHandler called\n" );
	oberonXErrorHandler( 0, 0, (long)err, (long)d );
}


static int X11IOErrorHandler( Display *d ) {
	printf( "X11IOErrorHandler called\n" );
	oberonXIOErrorHandler( 0, 0, 0, (long)d );
}


void SetupXErrHandlers( long *XE, long *XIOE ) {
	
	if (debug)
		printf( "Setup X11 ErrorHandlers\n" );
	oberonXErrorHandler = XE;
	oberonXIOErrorHandler = XIOE;
	
	XSetErrorHandler(X11ErrorHandler);
	XSetIOErrorHandler(X11IOErrorHandler);	
}


void dl_sym(int handle, char *symbol, int *adr)
{
  void * a;

  if (debug&1) printf("dl_sym: %x %s\n", handle, symbol);
  
  if      (strcmp("dlopen",	symbol) == 0) *adr = (int)dl_open;
  else if (strcmp("dlclose",	symbol) == 0) *adr = (int)dl_close;
  else if (strcmp("debug",	symbol) == 0) *adr = debug;
  else if (strcmp("heapAdr",	symbol) == 0) *adr = heapAdr;
  else if (strcmp("heapSize",	symbol) == 0) *adr = heapSize;
  else if (strcmp("argc",	symbol) == 0) *adr = Argc;
  else if (strcmp("argv",	symbol) == 0) *adr = (int)Argv;
  else if (strcmp("exit",	symbol) == 0) *adr = (int)exit;
  else if (strcmp("errno",	symbol) == 0) *adr = (int)errnof;
  else if (strcmp("printf",	symbol) == 0) *adr = (int)o_printf;
  else if (strcmp("stat",	symbol) == 0) *adr = (int)o_stat;
  else if (strcmp("lstat",	symbol) == 0) *adr = (int)o_lstat;
  else if (strcmp("fstat",	symbol) == 0) *adr = (int)o_fstat;
  else if (strcmp("lseek",	symbol) == 0) *adr = (int)o_lseek;
  else if (strcmp("InstallTrapHandler",
  				symbol) == 0) *adr = (int)InstallTrapHandler;
  else if (strcmp("InitXErrH",  symbol) == 0) *adr = (int)SetupXErrHandlers;
#ifdef LINUX
  else if (strcmp("sigsetjmp",	symbol) == 0) *adr = (int)__sigsetjmp;
  else if (strcmp("setjmp",	symbol) == 0) *adr = (int)__sigsetjmp;
  else if (strcmp("mknod",	symbol) == 0) *adr = (int)mknod;
#endif
#ifdef MAC
  else if (strcmp("malloc",	symbol) == 0) *adr = (int)o_malloc;
  else if (strcmp("calloc",	symbol) == 0) *adr = (int)o_calloc;
  else if (strcmp("memalign",	symbol) == 0) *adr = (int)o_memalign;
#endif
  /* Math.Mod stuff -- added by RLI */  
  else if (strcmp("sin",	symbol) == 0) *adr = (int)sin;
  else if (strcmp("cos",	symbol) == 0) *adr = (int)cos;
  else if (strcmp("log",	symbol) == 0) *adr = (int)log;
  else if (strcmp("atan",	symbol) == 0) *adr = (int)atan;
  else if (strcmp("exp",	symbol) == 0) *adr = (int)exp;
  else if (strcmp("sqrt",	symbol) == 0) *adr = (int)sqrt;

  /* threads support */
  else if (strcmp("mtxInit",   		symbol) == 0) *adr = (int)_mtx_init;
  else if (strcmp("mtxDestroy", 	symbol) == 0) *adr = (int)_mtx_destroy;
  else if (strcmp("mtxLock",    	symbol) == 0) *adr = (int)_mtx_lock;
  else if (strcmp("mtxUnlock",  	symbol) == 0) *adr = (int)_mtx_unlock;
  else if (strcmp("conInit",  		symbol) == 0) *adr = (int)_con_init;
  else if (strcmp("conDestroy", 	symbol) == 0) *adr = (int)_con_destroy;
  else if (strcmp("conWait",  		symbol) == 0) *adr = (int)_con_wait;
  else if (strcmp("conSignal",  	symbol) == 0) *adr = (int)_con_signal;
  else if (strcmp("thrStart",		symbol) == 0) *adr = (int)_thr_start;
  else if (strcmp("thrThis",		symbol) == 0) *adr = (int)_thr_this;
  else if (strcmp("thrSleep",		symbol) == 0) *adr = (int)_thr_sleep;
  else if (strcmp("thrPass",		symbol) == 0) *adr = (int)_thr_pass;
  else if (strcmp("thrExit",		symbol) == 0) *adr = (int)_thr_exit;
  else if (strcmp("thrSuspend",		symbol) == 0) *adr = (int)_thr_suspend;
  else if (strcmp("thrResume",		symbol) == 0) *adr = (int)_thr_resume;
  else if (strcmp("thrGetPriority",	symbol) == 0) *adr = (int)_thr_getprio;
  else if (strcmp("thrSetPriority",	symbol) == 0) *adr = (int)_thr_setprio;
  else if (strcmp("thrKill",		symbol) == 0) *adr = (int)_thr_kill;
  else if (strcmp("thrInitialize",	symbol) == 0) *adr = (int)_thr_initialize;
  else {
    *adr = (int)dlsym((void *)handle, symbol);
    if (*adr == 0) {
      printf("dl_sym: symbol %s not found\n", symbol); 
    }
  }
  //if (debug) printf("dl_sym: %s = %x @ %x\n", symbol, *adr, adr);
}


/*----- Files Reading primitives -----*/

int Rint() 

{
  unsigned char b[4];
  /*
     b[3] = fgetc(fd); b[2] = fgetc(fd); b[1] = fgetc(fd); b[0] = fgetc(fd);
     */
  /* little endian machine reading little endian integer */
  b[0] = fgetc(fd); b[1] = fgetc(fd); b[2] = fgetc(fd); b[3] = fgetc(fd);
  return *((int *) b);
}

int RNum()
{
  int n, shift;
  unsigned char x;
  shift = 0; n = 0; x = fgetc(fd);
  while (x >= 128) {
    n += (x & 0x7f) << shift;
    shift += 7;
    x = fgetc(fd);
  }
  return n + (((x & 0x3f) - ((x >> 6) << 6)) << shift);
}
	
void Relocate(uint heapAdr, int shift)
{
  int len; addr adr; 
  
  len = RNum(); 
  while (len != 0) { 
    adr = RNum(); 
    adr += heapAdr; 
    *((int *)adr) += shift; 
    len--; 
  } 
}

void showProc(addr adr) {
  int i;
  
  printf("Oberon code to be called:\n");
  for (i=0; i<10; i++) {
    printf("%8x: %8x\n", adr, *(int*)adr);
    adr += 4;
  }
  printf("%8x: ...\n", adr);
}

void Boot()
{
  addr adr, fileHeapAdr, dlsymAdr;
  uint len, d, codeSize, fileHeapSize;
  int shift, notfound;  
  Proc body;

  d = 0; notfound = 1;
  while ((d < nofdir) && notfound) {
    strcat(strcat(strcpy(fullname, dirs[d++]), "/"), bootname);
    fd = fopen(fullname, "r");
    if (fd != NULL) notfound = 0;
  }
  if (notfound) {
    printf("oberon: boot file %s not found\n", bootname);  
    exit(-1);
  }
  fileHeapAdr = Rint(); fileHeapSize = Rint();
  if (fileHeapSize >= heapSize) {
    printf("oberon loader: heap too small\n");  
    exit(-1);
  }
  adr = heapAdr; len = fileHeapSize + 32; 
  while (len > 0) { 
    *((int*)adr) = 0; 
    len -= 4; adr += 4; 
  } 
  shift = heapAdr - fileHeapAdr;
  adr = Rint(); len = Rint();
  while (len != 0) {
    adr += shift;
    len += adr;
    codeSize = len - heapAdr;
    while (adr != len) { *((int*)adr) = Rint(); adr += 4; }
    adr = Rint(); len = Rint();
  }
  body = (Proc)(adr + shift);
  Relocate(heapAdr, shift);
  dlsymAdr = Rint();
  if (debug&1) showProc((addr)body);
  *((int *)(heapAdr + dlsymAdr)) = (int)dl_sym;
  fclose(fd);
  codeSize = (codeSize+4095)/4096*4096;
  if(mprotect((void*)heapAdr, codeSize, PROT_READ|PROT_WRITE|PROT_EXEC) != 0)
     perror("mprotect");
  (*body)();
}

void InitPath()
{
  int pos;
  char ch;
  
  if ((OBERON = getenv("OBERON")) == NULL) OBERON = defaultpath;
  strcpy(path, OBERON);
  pos = 0; nofdir = 0;
  ch = path[pos++];
  while (ch != '\0') {
    while ((ch == ' ') || (ch == ':')) ch = path[pos++];
    dirs[nofdir] = &path[pos-1];
    while ((ch > ' ') && (ch != ':')) ch = path[pos++];
    path[pos-1] = '\0';
    nofdir ++;
  }
}

void doexit(int ret, void *arg)
{
  _exit(ret);
}

int main(int argc, char *argv[])
{
  char* p;
  void *a, *h;
  
/*  on_exit(doexit, NULL);	*/
  
  Argc = argc; Argv = argv;

  /* check if we have suid root previlliges */
  if (geteuid() == 0) {
     suid_root = 1;
     seteuid( getuid() );
  } else {
     suid_root = 0;
  }

  debug = 0;
  p = getenv("OBERON_DEBUG");
  if (p != NULL)  debug = atoi(p);

  if (debug) {
     printf("UnixAos Boot Loader 11.12.2007\n");
     printf( "debug = %d\n", debug );
  }

  heapSize = 0x200000;
#ifdef MAC
  heapAdr = (addr)calloc(0x200, 0x1000);
#else
  heapAdr = (addr)memalign(4096, heapSize);
#endif
  if (heapAdr == 0) {
    printf("oberon: cannot allocate initial heap space\n");  
    exit(-1);
  }

  InitPath();
  CreateSignalstack();
  InitTrapHandler();
  
  Boot();
  return 0;
}



