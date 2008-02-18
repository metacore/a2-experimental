#

CC=gcc 
CFLAGS  = -DSOLARIS
LDFLAGS = -lthread -L/usr/openwin/lib -lX11 -ldl -lrt -lm

all:
	@make  aos.solaris



aos.solaris:	clean oberon.o Threads.o
	$(CC) -s -o aos.solaris oberon.o Threads.o $(LDFLAGS)

oberon.o:	oberon.c
	$(CC) -c $(CFLAGS) oberon.c

Threads.o:	Threads.h Threads.c
	$(CC) -c $(CFLAGS) Threads.c 

clean:
	rm -f *.o 

distclean:
	rm -f *.o aos.solaris*

