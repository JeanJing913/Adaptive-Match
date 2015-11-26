CC=gcc
LFLAGS = -shared
CFLAGS = -O3 -Wall -c -fPIC -I$(INCLUDE)

vpath %.h ./include ../Adaptive/include
vpath %.c ./src
vpath %.so ./so

#OBJS := #$(patsubst ./_c/%.c, %.o, $(wildcard *.c))

OBJS = main.o common.o textools.o makedata.o binary.o stack.o queue.o  BST.o lists.o sorter.o
SOS = libcommon.so libtextools.so libmakedata.so libADT.so libbinary.so
SOPATH = /home/pz/code/libs/so
INCLUDE = ./include

ADTS = stack.o queue.o BST.o lists.o sorter.o

a.out: main.o $(SOS) 
	$(CC) $< -L$(SOPATH) -ltextools -lmakedata -lADT  -lbinary -lcommon -lm
	rm *.o

$(OBJS) : common.h

main.o: main.c textools.h makedata.h stack.h  BST.h lists.h binary.h
	$(CC) $(CFLAGS) $< -o $@

libcommon.so: common.o
	$(CC) $(LFLAGS) $^ -o $(SOPATH)/$@
common.o: common.c 
	$(CC) $(CFLAGS) $< -o $@

libtextools.so: textools.o
	$(CC) $(LFLAGS) $^ -o $(SOPATH)/$@
textools.o: textools.c textools.h
	$(CC) $(CFLAGS) $< -o $@

libmakedata.so: makedata.o
	$(CC) $(LFLAGS) $^ -o $(SOPATH)/$@
makedata.o : makedata.c makedata.h textools.h
	$(CC) $(CFLAGS) $< -o $@

libbinary.so: binary.o
	$(CC) $(LFLAGS) $^ -o $(SOPATH)/$@
binary.o: binary.c binary.h
	$(CC) $(CFLAGS) $< -o $@

libADT.so: $(ADTS)
	$(CC) $(LFLAGS) $^ -o $(SOPATH)/$@
stack.o: stack.c stack.h
	$(CC) $(CFLAGS) $< -o $@
queue.o: queue.c queue.h common.h share.h
	$(CC) $(CFLAGS) -I../Adaptive/include $< -o $@
BST.o: BST.c BST.h
	$(CC) $(CFLAGS) $< -o $@
lists.o: lists.c lists.h
	$(CC) $(CFLAGS) $< -o $@
sorter.o : sorter.c sorter.h share.h
	$(CC) $(CFLAGS) $< -I../Adaptive/include -o $@		


.PHONY: ra ro rso
ra : ro rso
	-rm a.out
ro :
	-rm *.o
rso:
	-rm $(SOPATH)/*.so
