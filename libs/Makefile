SUF = so
CC = gcc

LINKSO = gcc -O3 -shared -std=c99
LINKA = ar -rc
LINK = $(LINKSO)

INCLUDE = ./include
CFLAGS = -g -Wall -c -std=c99 -fPIC -I$(INCLUDE)

LIBPATH = /usr/local/lib/

vpath %.h $(INCLUDE) ../Adaptive/include
vpath %.c ./src

#OBJS := $(patsubst %.c,%.o, $(wildcard ./sc/*.c))

SOS = libcommon.so libbinary.so libadt.so
LIBS = $(SOS) #-ladt -lcommon -lm -lbinary 

a.out: main.o $(SOS)
	$(CC) $(CFLAGS) -ladt -lcommon -lm -lbinary -o $@ 
	rm *.o	

main.o: main.c makedata.h stack.h binary.h queue.h stack.h
	$(CC) $(CFLAGS) $< -o $@

OBJS = common.o binary.o stack.o queue.o arith.o makedata.o

$(OBJS): common.h
$(OBJS): %.o: %.c %.h
	$(CC) $(CFLAGS) $< -o $@

libcommon.$(SUF): common.o
	$(LINK) $^ -o $(LIBPATH)$@

libbinary.$(SUF): binary.o
	$(LINK) $^ -o $(LIBPATH)$@

ADT = stack.o queue.o arith.o
libadt.$(SUF): $(ADT)
	$(LINK) $^ -o $(LIBPATH)$@

.PHONY: clean ro rso ra
clean : ro rso ra
	-rm a.out
ro :
	-rm *.o
rso:
	-rm $(SOPATH)/*.so
ra:
	-rm $(APATH)/*.a


# libmakedata.$(SUF): makedata.o
# 	$(LINK) $^ -o $(LIBPATH)/$@

