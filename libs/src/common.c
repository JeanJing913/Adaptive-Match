#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>
#include <sys/stat.h>
#include "common.h"
#include "share.h"


char *str_cat(const char *str1, const char *str2)
{
    char *new_str = MALLOC(strlen(str1) + strlen(str2) + 1, char);

    return strcat(strcpy(new_str, str1), str2);
}

/* srand()在调用函数中使用,而非在rand_range中使用 */
int rand_range(int low, int high)
{
    double d = (double) rand() / ((double) RAND_MAX + 1);
    int k = (int) (d * (high - low + 1));

    return low + k;
}

void *mlloc(size_t size, const char *file, const char *fun, int line)
{
    void *new_mem;

    if (!(new_mem = malloc(size))) {
        fprintf(stderr, "Out of memory! function: %s, file:%s, line:%d\n", fun, file, line);
        exit(EXIT_FAILURE);
    }

    return new_mem;
}

void *clloc(size_t num, size_t size, const char *file, const char *fun, int line)
{
    void *new_mem;

    if (!(new_mem = calloc(num, size))) {
        fprintf(stderr, "Out of memory! function: %s, file:%s, line:%d\n", fun, file, line);
        exit(EXIT_FAILURE);
    }

    return new_mem;
}

/* 带错误处理的fopen */
FILE *Fopen(const char *name, const char *mode)
{
    FILE *fp;
    
    if ((fp = fopen(name, mode)) == NULL) {
        perror(name);
        exit(EXIT_FAILURE);
    }
     
    return fp;
}

/* 带错误处理的fclose */
void Fclose(FILE *fp)
{
    if (fclose(fp)) {
        perror("fclose");
        exit(EXIT_FAILURE);
    }
}
