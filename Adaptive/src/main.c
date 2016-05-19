#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>
#include "common.h"
//#include "makedata.h"
#include "hash.h"
#include "share.h"
#include "queue.h"
#include "stack.h"
#include "filter.h"
#include "array.h"
#include "map.h"
#include "sorter.h"
#include "statistics.h"
#include "binary.h"

Stack_T stk;

extern unsigned match_num; /* 任何情况下都要输出,以验证程序正确性 */

#if PROFILING
extern Num_Num_T access_depth[LLP];
extern unsigned total_nodes;
#endif 

#if DEBUG
void print_pat_list(Suf_Node_T list_head)
{
  puts("the pat list");
  
  while (list_head) {
    assert(strlen(list_head->str));
    printf("%s\n", list_head->str);
    list_head = list_head->next;
  }
}
#endif 

static Suf_Node_T make_suffix_node(Char_T const *pat, Pat_Len_T pat_len)
{
     Suf_Node_T new_suf_node;

     new_suf_node = VMALLOC(struct Suf_Node, Char_T, pat_len);
     strcpy(new_suf_node->str, pat);
     new_suf_node->next = NULL;

     return new_suf_node;
}

static Suf_Node_T read_pats(FILE *pats_fp)
{
  Char_T buf[MAX_PAT_LEN+1]; /*模式串缓存,包括换行符*/
  Pat_Len_T pat_len;
  Char_T *line_break = NULL; /*换行符指针*/
  Suf_Node_T list_head = NULL, new_suf_node = NULL; /* 链表头指针 */

  while (fgets(buf, sizeof(buf), pats_fp)) {
    if ((line_break = strchr(buf, '\n')))
      *line_break = '\0';
    if ((pat_len = strlen(buf))) { /* 必须是非空模式串 */
      new_suf_node = make_suffix_node(buf, pat_len+1); /* buf末尾包含'\0' */
      new_suf_node->next = list_head; /* 挂到链表头 */
      list_head = new_suf_node; /* 新连表头 */
    }
  }

  return list_head;
}

/* 有序链表去重,头节点一定会保留 */
static void remove_duplicates(Suf_Node_T pat_list)
{
  Suf_Node_T prev = pat_list, cur = prev->next;

  while (cur)
    if (strcmp(prev->str, cur->str) == 0) { /* 模式串不等长,均以'\0'结尾*/
      cur = cur->next; free(prev->next); prev->next = cur;
    } else {
      prev = cur; cur = cur->next;
    }
}

Pat_Len_T get_lss(Suf_Node_T suf_list)
{
  Pat_Len_T suf_len, lss = MAX_PAT_LEN;

  for (Suf_Node_T cur = suf_list; cur; cur = cur->next)
    if ((suf_len = strlen(cur->str)) < lss)
      lss = suf_len;

  return lss;
}

static Pat_Num_T get_ndp(Suf_Node_T suf_list, Pat_Len_T lss)
{
  Pat_Num_T ndp = 1;
  
  for (Suf_Node_T prev = suf_list, cur = prev->next; cur; cur = cur->next)
    if (same_str(prev->str, cur->str, lss))
      continue;
    else {
      ndp++; prev = cur;
    }

  return ndp;
}

static void build_tree_node(Tree_Node_T t)
{
  Pat_Len_T lss = get_lss(t->link); /* length of the shortest suffix */
  Pat_Num_T ndp = get_ndp(t->link, lss); /* number of the distinct prefixes */
//  char pat_buf[MAX_PAT_LEN] = {0}, *p = pat_buf;

#if PROFILING
  total_nodes++;
#endif
 
  /* while (ndp == 1) { */
  /*      memcpy(p, ((Suf_Node_T) t->link)->str, lss); */
  /*      p += lss; */
       
  /*      struct Suf_Node **next_p = (struct Suf_Node **) &t->link; */
  /*      for (Suf_Node_T cur_suf = t->link, next_suf; cur_suf; cur_suf = next_suf) { */
  /* 	    next_suf = cur_suf->next; */
  /* 	    if ((cur_suf = cut_head(cur_suf, lss))) { */
  /* 		 *next_p = cur_suf; next_p = &cur_suf->next; */
  /* 	    } */
  /*      } */
  /*      *next_p = NULL; */
  /*      lss = get_lss(t->link); */
  /*      ndp = get_ndp(t->link, lss); */
  /* } */

  /* if (pat_buf[0]) { */
  /*      if (strlen(pat_buf) > 1) */
  /* 	    build_single_str() */
	    
       

  /* 自适应策略 */
  if (lss == 1) /* 单字符*/
    build_map(t, ndp);
  else if (ndp < NUM_TO_BUILD_HASH)
    build_array(t, ndp, lss);
  else
    build_hash_table(t, ndp, lss);
}

/* static void build_root(Tree_Node_T t) */
/* { */
/*   Pat_Len_T lss = get_lss(t->link); /\* length of the shortest suffix *\/ */
/*   Pat_Num_T ndp = get_ndp(t->link, lss); /\* number of the distinct prefixes *\/ */

/* } */

/* 预处理*/
Filter_T filter;

Tree_Node_T build_AMT(Char_T *pats_file_name)
{
  FILE *pats_fp = Fopen(pats_file_name, "rb");
  fprintf(stderr, "\nBuilding AMT...\n"); fflush(stdout);

  clock_t start = clock();
  Suf_Node_T pat_list = list_radix_sort(read_pats(pats_fp)); /* 读取模式集,并按模式串字典序排序 */
  Fclose(pats_fp);
  remove_duplicates(pat_list); /* 去掉模式集中重复的元素 */
  stk = Stack_new();
  
  filter = build_filter(pat_list); /* 根节点为过滤器 */
  Tree_Node_T root = CALLOC(1, struct Tree_Node);
  root->link = pat_list;

  Stack_push(stk, root);
  while (!Stack_empty(stk)) /* 构建整个AMT */
     build_tree_node(Stack_pop(stk));
  clock_t end = clock();
  fprintf(stderr, "Done! (%f)\n",
	  (double) (end - start) / CLOCKS_PER_SEC);

  Stack_free(&stk);

  return root;
}

static bool check_entrance(Tree_Node_T t, Char_T const *entrance, Char_T *matched_pat_buf, bool output)
{
  bool pat_end = false, find_pat = false;
  Char_T const *p = entrance;

#if PROFILING
  uint8_t depth = 0;
#endif
  
  while (t && t->link) { /*非: 匹配失败或已到达叶节点 */
    t = t->match_fun(t->link, &p, &pat_end);
    
#if PROFILING
    depth++;
#endif

    if (pat_end) {
      match_num++;
      find_pat = true;
      pat_end = false;
#if PROFILING
      if (output) {
	Pat_Len_T pat_len = p - entrance;
	*matched_pat_buf++ = ' ';  /* 模式串以空格分隔 */
	memcpy(matched_pat_buf, entrance, pat_len); /* 复制一个完整模式串 */
	matched_pat_buf += pat_len;
      }
#endif
    }
  }
  
  *matched_pat_buf = '\0';

#if PROFILING
  access_depth[depth].num_1 = depth;
  access_depth[depth].num_2++;
#endif

  return find_pat;
}
 
/* 匹配文本*/
void matching(Tree_Node_T root, Char_T *text_buf, size_t text_len, bool output)
{
  fprintf(stderr, "\nMatching..."); fflush(stdout);
  Char_T matched_pat_buf[500];
  clock_t start = clock();

  Pat_Len_T block_size = filter->block_size;
  Pat_Len_T window_size = filter->window_size;
  Pat_Len_T last_pos = window_size - block_size;
  static Bitmap_T mb = -1; /* 全"1" */
  Bitmap_T *bitmap = filter->bitmap;
  uint64_t hit_num = 0;

  Char_T *entrance = text_buf;
  while (entrance <= text_buf + text_len - window_size) {
    uint32_t v = block_123(entrance + last_pos, block_size);
    mb &= bitmap[v];

    if (test_bit(&mb, last_pos)) {
      hit_num++;
      bool find_pat = check_entrance(root, entrance, matched_pat_buf, output);
#if PROFILING
      if (find_pat && output)
	printf("%ld: %s\n", entrance - text_buf + 1, matched_pat_buf);
#endif
    }
      
    Pat_Len_T skip = 0; /* 至少跳一步 */
    do {
      mb >>= 1;
      skip++;
      set_bit(&mb, 0); /* 首位置1 */
    } while (!test_bit(&mb, last_pos)); /* 末位不是1 */

    entrance += skip;
  }

  clock_t end = clock();
  
  fprintf(stderr, "\nDone! (%f) total skip: %.2f\n",
	  (double) (end - start) / CLOCKS_PER_SEC, (double) (text_len - hit_num) / text_len);
}


int main(int argc, char **argv)
{
  bool output = false, show_sta_info = false;
  Char_T opt;
  
/* 处理命令行参数 */
  if (argc > 3) 		/* 解析随后的参数 */
    for (char **arg = argv + 3; *arg && **arg == '-'; arg++)
      while ((opt = *++*arg))
	switch (opt) {
	case 'o' : output = true; break; /* -o表示显示匹配结果 */
	case 's' : show_sta_info = true; break;   /* -s表示显示统计信息 */
	default : fprintf(stderr, "非法命令行参数!\n"); exit(EXIT_FAILURE);
	}

  /* 构建AMt */
  Tree_Node_T root = build_AMT(argv[1]); /* argv[1]是模式集文件名,root是过滤器 */

  /* 读文本 */
  fprintf(stderr, "\nLoading text...\n"); fflush(stdout);
  size_t file_size;
  Char_T *text_buf = load_file(argv[2], &file_size); /* argv[2]是文本文件名 */

  /* 匹配文本 */
  matching(root, text_buf, file_size, output);
  fprintf(stderr, "\nTotal matched number: %u\n", match_num);
  
#if PROFILING
  if (show_sta_info)
    print_statistics(file_size); /* 打印程序运行过程中的各种统计信息 */
#endif

}
