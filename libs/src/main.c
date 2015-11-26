#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>
#include <sys/stat.h>
#include <assert.h>
#include "common.h"
#include "textools.h"
#include "makedata.h"
#include "stack.h"
#include "BST.h"
#include <limits.h>
#include "lists.h"
#include "binary.h"
#include <stdint.h>

#undef malloc

void bitmap_test(void);

int div16(int x)
{
  int bias = x >> 31 & 0xF;
  return (x + bias) >> 4;

}

struct b {
  int value;
  int key;
};


struct a {
  int len;
  struct b array[0];
};
/*
int main(int argc, char **argv)
{

  char * buf = malloc(100);
  char *s = "fasfasf";

  strcpy(buf, s);

  //  printf("key:%d, value: %d\n", p->array[1].key, p->array[8].value);
  //printf("key:%d, value: %d\n", p->array[1].key, p->array[8].value);


  //str.p = s;


}
*/

