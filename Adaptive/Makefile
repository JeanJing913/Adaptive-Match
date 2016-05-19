OBJS = share.o hash.o map.o array.o statistics.o sorter.o filter.o
LIBS = -ladt -lcommon -lm -lbinary #-lmakedata

#OBJS := $(patsubst ./src/%.c, %.o, $(wildcard ./src/*.c))
CC = gcc

INCLUDE_1 = ../libs/include
INCLUDE_2 = ./include

vpath %.h $(INCLUDE_1) $(INCLUDE_2)
vpath %.c ./src

CFLAGS = -Wall -c -g -std=c99 -I$(INCLUDE_1) -I$(INCLUDE_2)

a.test.out: main.o $(OBJS) $(LIBS)
	$(CC) $^ -o $@
	rm *.o

$(OBJS): share.h common.h binary.h statistics.h

$(OBJS): %.o: %.c %.h
	$(CC) $(CFLAGS) $< -o $@

main.o: main.c hash.h common.h map.h binary.h sorter.h array.h stack.h filter.h #makedata.h
	$(CC) $(CFLAGS) $< -o $@

.PHONY: ra
ra : ro
	-rm a.test.out
ro:
	-rm $(OBJS)
