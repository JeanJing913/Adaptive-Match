#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>
#include <sys/stat.h>
#include "common.h"
#include "textools.h"
#include "makedata.h"
#include <limits.h>


#define SIZE 100000000
/*
int main(int argc, char **argv)
{
    clock_t start, end;
    int *a = malloc(SIZE *sizeof ( int)),*p;
    int i;

    start = clock();
    for (i = 0; i < SIZE; i++)
        a[i] = 0;
    end = clock();

    printf("%f\n", (double)(end - start)/CLOCKS_PER_SEC);

    start = clock();
    for (p = a; p < a + SIZE; p++)
        *p = 0;
    end = clock();

    printf("%f\n", (double)(end - start)/CLOCKS_PER_SEC);




}
*/
