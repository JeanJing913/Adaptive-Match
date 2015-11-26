#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <string.h>
#include <assert.h>
#include "common.h"
#include "makedata.h"

static int Seed;
#define ACMa 16807
#define ACMm 2147483647
#define ACMq 127773
#define ACMr 2836
#define hi (Seed / ACMq)
#define lo (Seed % ACMq)

void cre_rand_text(const char *filename, long text_len, int low, int high)
{
     FILE *fp_text = Fopen(filename, "w");

     if (low < 0 || low > high || high > 255) {
         fprintf(stderr, "Illegal characters set!\n");
         exit(EXIT_FAILURE);
     }

     srand(time(NULL));

     while (text_len--)
         putc(rand_range(low, high), fp_text);

     Fclose(fp_text);
}

void cre_rand_pats(const char *filename, long pat_num, int min_pat_len, int max_pat_len, int low, int high)
{
    FILE *fp_text = Fopen(filename, "w");
    int pat_len;
    int ch;

    srand(time(NULL));

    while (pat_num--) {
        pat_len = rand_range(min_pat_len, max_pat_len);
        while (pat_len--) {
            do {
                ch = rand_range(low, high);
               } while (ch == '\0' || ch == '\n');
               putc(ch, fp_text);
          }
          putc('\n', fp_text);
     }

     Fclose(fp_text);
}

unsigned char buf[1024*1024]; /* 1MB buffer */

static int fst = 1;

/* 用1~alphabet中的字符填充buf的前n个字符*/
/* static void fill_buffer(unsigned char *buf, int n, int alphabet) */
/* { */
/*     int i; */
/*     long test; */
/*     struct timeval t; */

/*     if (fst) { */
/*         gettimeofday(&t, NULL); */
/*         Seed = t.tv_sec * t.tv_usec; */
/*         fst = 0; */
/*     } */

/*    for (i = 0; i < n; i++) { */
/*         Seed = ((test = ACMa * lo - ACMr * hi) > 0) ? test : test + ACMm; */
/*         buf[i] = 1 + ((double)Seed) * alphabet / ACMm; */
/*     } */
/* } */

/* 生成 file_name, 大小为 n MB, 字符集为alphabet  */
/* void fill_file(char const *file_name, int n, int alphabet) */
/* { */
/*     FILE *ofile; */

/*     if ((n < 0) || (n > 4096)) { */
/*         fprintf (stderr,"Error: file length (which is given in MB) must" */
/*                  " be between 0 and 4096 (= 4 GB file)\n"); */
/*         exit(EXIT_FAILURE); */
/*     } */

/*     if ((alphabet < 1) || (alphabet > 256)) { */
/*         fprintf (stderr,"Error: alphabet size must be between 1 and 256\n"); */
/*         exit(EXIT_FAILURE); */
/*     } */

/*     if (alphabet == 256) { */
/*         fprintf (stderr,"Warning: several indexes need alphabet size < 256" */
/*                  " to work properly.\n Generating anyway.\n"); */
/*     } */

/*     if ((ofile = fopen(file_name,"w")) == NULL) { */
/*         perror(file_name); */
/*         exit(EXIT_FAILURE); */
/*     } */

/*     while (n--) { */
/*         fill_buffer(buf, 1024*1024, alphabet); /\* 先填充块儿 *\/ */
/*         if (fwrite (buf,1024*1024,1,ofile) != 1) { /\* 再将块儿写入文件 *\/ */
/*             fprintf (stderr,"Error: cannot write %s\n",file_name); */
/*             fprintf(stderr, "%s\n", strerror(errno)); */
/*             fclose(ofile); */
/*             unlink (file_name); */
/*             exit(EXIT_FAILURE); */
/*         } */
/*     } */

/*     fclose(ofile); */

/*     fprintf (stderr,"File %s successfully generated\n",file_name); */
/* } */

int aleat (int top)
{
    long test;
    struct timeval t;

    if (fst) {
        gettimeofday(&t, NULL);
        Seed = t.tv_sec * t.tv_usec;
        fst = 0;
    }

    Seed = ((test = ACMa * lo - ACMr * hi) > 0) ? test : test + ACMm;
    return ((double) Seed) * top / ACMm;
}

/* 将字符串forbid中的字符序列,转化为真正的转义字符序列存入*forbide中 */
static void parse_forbid(char const *forbid, char ** forbide)
{
     int len, i, j;

     len = strlen(forbid);

     *forbide = MALLOC(len + 1, char);

     for(i = 0, j = 0; i < len; i++) { /* 遍历forbid字符串 */
         if (forbid[i] != '\\') {
	       if(forbid[i] != '\n')
		    (*forbide)[j++] = forbid[i];
	  } else {
	       i++;
	       if(i == len) {
		    /* forbid[i-1] = '\0'; */
		    (*forbide)[j] = '\0';
		    fprintf (stderr, "Not correct forbidden string: only one \\\n");
		    return;
	       }
	       switch (forbid[i]) {
		   case'n':  (*forbide)[j++] = '\n'; break;
		   case'\\': (*forbide)[j++] = '\\'; break;
		   case'b':  (*forbide)[j++] = '\b'; break;
		   case'e':  (*forbide)[j++] = '\e'; break;
		   case'f':  (*forbide)[j++] = '\f'; break;
		   case'r':  (*forbide)[j++] = '\r'; break;
		   case't':  (*forbide)[j++] = '\t'; break;
		   case'v':  (*forbide)[j++] = '\v'; break;
		   case'a':  (*forbide)[j++] = '\a'; break;
		   case'c':     /* \c字符编码(0~255) */
			if(i + 3 >= len) {
			     /* forbid[i-1] = '\0'; */
			     (*forbide)[j] = '\0';
			     fprintf (stderr, "Not correct forbidden string: 3 digits after \\c\n");
			     return;
			}
			(*forbide)[j++] = (forbid[i+1]-48)*100 + (forbid[i+2]-48)*10 + (forbid[i+3]-48);
			i += 3;
			break;
		   default:
			fprintf (stdout, "Unknown escape sequence '\\%c'in forbidden string\n", forbid[i]);
			break;
	       }
	  }
     }
     (*forbide)[j] = '\0';
}

/* 从文件file中, 抽取pat_num个模式串, 构成模式串文件pat_file, 串长分布:min_pat_len~max_pat_len, 禁止的字符在保存在forbid中 */
void extract_pats(char const *text_filename, long pat_num, int min_pat_len, int max_pat_len, char const *pat_filename, char const *forbid)
{
    int pat_len, n, file_len;
    struct stat sdata;
    FILE *ifile, *ofile;
    unsigned char *buff;
    char *forbide = NULL;

    if (stat(text_filename, &sdata) != 0) {
        fprintf(stderr, "Error: cannot stat file %s\n", text_filename);
        exit(EXIT_FAILURE);
    }

    file_len = sdata.st_size; 	/* length of file */

    if (min_pat_len <= 0 || max_pat_len <= 0 || min_pat_len > max_pat_len || max_pat_len > file_len) {
        fprintf(stderr,"Error: pat length must be >= 1 and <= file length");
        exit(EXIT_FAILURE);
    }

    if (pat_num < 1) {
        fprintf(stderr, "Error: number of patterns must be >= 1\n");
        exit(EXIT_FAILURE);
    }

    parse_forbid(forbid, &forbide);

    ifile = Fopen (text_filename, "rb");

    buff = MALLOC(file_len, unsigned char);

    if (fread (buff, file_len, 1, ifile) != 1)  { /* read the whole file into buf */
        fprintf(stderr, "Can not fread file: %s\n", text_filename);
        exit(EXIT_FAILURE);
    }

    Fclose(ifile);

    ofile = Fopen(pat_filename, "w");

    for (n = 0; n < pat_num; n++) {
        int starting_pos, i;
        pat_len = rand_range(min_pat_len, max_pat_len);
        do { /*对每一个产生的起始位置,检查该位置的pat是否包含禁止字符,如果包含,则重新产生一个起始位置,直到该位置的pat不包含任何禁止字符 */
            starting_pos = aleat(file_len - pat_len + 1);
            for (i = 0; i < pat_len; i++)
                if (strchr(forbide, buff[starting_pos+i])) break;
        } while (i < pat_len);

        for (i = 0; i < pat_len; i++)
            putc(buff[starting_pos+i], ofile);

        putc('\n', ofile);      /* 模式串以行为单位 */
    }

    Fclose(ofile);

    printf("File %s successfully generated\n", pat_filename);

    free(buff); free(forbide);
}

//static double cal_sd(patset_t *pat_set);
static void ins_pat(patnode_t *, patset_t *);
static void read_pats(FILE *, patset_t *);

/* 构建集数据结构 */
patset_t *cre_pat_set(const char *pats_file_name)
{
    FILE *fp_pats; /*模式串文件*/
    patset_t *pat_set;

    fp_pats = Fopen(pats_file_name, "rb");

    pat_set = MALLOC(1, patset_t);
    pat_set->pats_file = strdup(pats_file_name);
    pat_set->pat_list = NULL;
    pat_set->total_pats = 0;
    pat_set->min_pat_len = MAX_PAT_LEN;
    pat_set->max_pat_len = 0;
    pat_set->mean_pat_len = 0;
    pat_set->total_pat_len = 0;
    memset(pat_set->pat_len_distri, 0, sizeof(int) * MAX_PAT_LEN);

    read_pats(fp_pats, pat_set);

    Fclose(fp_pats);

    return pat_set;
}

static double cal_sd(patset_t *); /*计算标准差*/
/* 依次读取模式串 */
static void read_pats(FILE *fp_pats, patset_t *pat_set)
{
    char buf[MAX_PAT_LEN+1]; /*模式串缓存，最大1000个字符，包括换行符*/
    int pat_len;
    long pats_readed = 0; /*已经读入的模式数量*/
    char *line_break; /*换行符指针*/

    while (fgets(buf, sizeof(buf), fp_pats)) {
        if (line_break = strchr(buf, '\n'))
            *line_break = '\0';
        if (pat_len = strlen(buf)) {
            ins_pat(cre_pat_node(buf), pat_set); /*构建模式节点，并插入到模式集中*/
            pats_readed++;
            pat_set->total_pats++;
            pat_set->total_pat_len += pat_len;
            pat_set->pat_len_distri[pat_len-1]++;
        }
    }

    pat_set->mean_pat_len = (double) pat_set->total_pat_len / pat_set->total_pats; /*计算模式串平均长度*/
    pat_set->pat_len_sd = cal_sd(pat_set);
}

patnode_t *cre_pat_node(const char *pat_str)
{
    patnode_t *new_pat_node =  MALLOC(1, patnode_t);
    new_pat_node->pat_str = strdup(pat_str);
    new_pat_node->next = NULL;

    return new_pat_node;
}

static void ins_pat(patnode_t *pat_node, patset_t *pat_set)
{
    static patnode_t *tail = NULL; /*静态变量保存模式链表尾指针*/
    int len;

    if (pat_set->total_pats == 0) { /*模式集为空*/
        pat_set->pat_list = pat_node;/*插入到头*/
        tail = pat_node;
    } else { /*插入模式串集合尾部*/
        tail->next = pat_node;
        tail = pat_node;
    }

    if ((len = strlen(pat_node->pat_str)) < pat_set->min_pat_len)
        pat_set->min_pat_len = len;
    if (len > pat_set->max_pat_len)
        pat_set->max_pat_len = len;
}

void des_pat_set(patset_t *pat_set) /*销毁模式集合*/
{
    patnode_t *p, *next;

    /*依次销毁串链表的每个节点*/
    for (p = pat_set->pat_list; p; p = next) {
        next = p->next;
        free(p->pat_str); /*销毁模式字符串*/
        free(p); /*销毁模式节点*/
    }

    free(pat_set->pats_file);
    free(pat_set); /*销毁模式集本身*/
}

static double cal_sd(patset_t *pat_set) /*计算标准差*/
{
     double sd = 0;
     patnode_t *p;

     for (p = pat_set->pat_list; p; p = p->next)
         sd += pow(strlen(p->pat_str) - pat_set->mean_pat_len, 2);

     return sqrt(sd / pat_set->total_pats);
}

/*print the pat set info*/
#ifdef DEBUG

void print_pat_set(const patset_t *pat_set, int max)
{
    patnode_t *p;
    int num;
    int i;

    printf("pats file: %s\n total pats: %ld\n max len: %d min len: %d mean len: %.2f sd: %.2f total len: %ld \n",
            pat_set->pats_file,
            pat_set->total_pats,
            pat_set->max_pat_len, pat_set->min_pat_len, pat_set->mean_pat_len, pat_set->pat_len_sd, pat_set->total_pat_len
            );

    for (i = pat_set->min_pat_len; i <= pat_set->max_pat_len; i++)
        printf("len: %2d  num: %5d  proportion: %%%7f\n", i, pat_set->pat_len_distri[i], ((double) pat_set->pat_len_distri[i] / pat_set->total_pats) * 100);

    for (num = 1, p = pat_set->pat_list; p && num <= max; p = p->next, num++)
        printf("%4d: %s\n", num, p->pat_str);
}

#endif
