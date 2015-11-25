OBJS = main.o share.o hash.o map.o array.o #:= $(patsubst %.c, %.o, $(wildcard *.c))
LIBPATH = /home/pz/code/libs/so

INCLUDE_1 = /home/pz/code/libs/include
INCLUDE_2 = /home/pz/code/Adaptive/include

vpath %.h $(INCLUDE_1) $(INCLUDE_2)
vpath %.c ./src/

CFLAGS = -Wall -c -O3 -I$(INCLUDE_1) -I$(INCLUDE_2)

a.out:  $(OBJS)
	gcc $(OBJS) -L$(LIBPATH) -lADT -lmakedata -lcommon  -lm -lbinary -ltextools
	rm *.o

main.o: main.c share.h hash.h common.h
	gcc $(CFLAGS) $< -o $@

share.o: share.c share.h common.h
	gcc $(CFLAGS) $< -o $@

hash.o: hash.c hash.h share.h common.h
	gcc $(CFLAGS) $< -o $@

map.o: map.c share.h common.h
	gcc $(CFLAGS) $< -o $@

array.o: array.c share.h common.h
	gcc $(CFLAGS) $< -o $@	

.PHONY: ro ra
ra : ro
	-rm a.out
ro :
	-rm $(OBJS)
