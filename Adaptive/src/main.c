#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include "common.h"
#include "textools.h"
#include "makedata.h"
#include "hash.h"
#include "share.h"
#include "queue.h"
#include "array.h"
#include "map.h"
#include "sorter.h"
#include "statistics.h"
double memory = 0.0;

Queue_t *queue;

typedef Expand_Node_t * (* Match_Fun_t)(void *, Char_t const **, Bool_t *);

static Expand_Node_t *(*match_fun[]) (void *, Char_t const **, Bool_t *) =
{
     NULL,
     (Match_Fun_t) match_single_ch,
     (Match_Fun_t) match_map_4,
     (Match_Fun_t) match_map_16,
     (Match_Fun_t) match_map_48,
     (Match_Fun_t) match_map_256,
     (Match_Fun_t) match_single_str,
     (Match_Fun_t) match_array,
     (Match_Fun_t) match_hash
};

static Suffix_Node_t *make_suffix_node(Char_t const *pat, Pat_Len_t pat_len)
{
     Suffix_Node_t *new_suf_node;

     new_suf_node = VMALLOC(Suffix_Node_t, char, pat_len + 1);
     memory += sizeof(Suffix_Node_t) + sizeof(char) * (strlen(pat) + 1);

     strcpy(new_suf_node->str, pat);
     new_suf_node->next = NULL;

     return new_suf_node;
}

static Suffix_Node_t *read_pats(FILE *pats_fp)
{
  Char_t buf[MAX_PAT_LEN+1]; /*模式串缓存,包括换行符*/
  Pat_Len_t pat_len;
  Char_t *line_break = NULL; /*换行符指针*/
  Suffix_Node_t *list_head = NULL, *new_suf_node = NULL; /* 链表头指针 */

  while (fgets(buf, sizeof(buf), pats_fp)) {
    if (line_break = strchr(buf, '\n'))
      *line_break = '\0';
    if (pat_len = strlen(buf)) {
      new_suf_node = make_suffix_node(buf, pat_len);
      new_suf_node->next = list_head;
      list_head = new_suf_node;
    }
  }

  return list_head;
}

/* 有序链表去重,头节点一定保留 */
static void remove_duplicates(Suffix_Node_t *pat_list)
{
  Suffix_Node_t *left = pat_list, *right = left->next;

  while (right)
    if (strcmp(left->str, right->str) == 0) {
      right = right->next; free(left->next); left->next = right;
      memory -= (sizeof(Suffix_Node_t) + sizeof(char) * strlen(right->str));

    } else {
      left = right; right = left->next;
    }
}

static Expand_Node_t *make_root(FILE *pats_fp)
{
     Suffix_Node_t *pat_list;
     Expand_Node_t *root = CALLOC(1, Expand_Node_t);
     memory += sizeof(Expand_Node_t);

     pat_list = list_radix_sort(read_pats(pats_fp)); /* 先排序 */
     remove_duplicates(pat_list); /* 再去重 */

     root->next_level = pat_list;

     return root;
}

static void get_ndp_and_lsp(Expand_Node_t const *expand_node, Pat_Num_t *ndp_p, Pat_Len_t *lsp_p)
{
  Suffix_Node_t *cur_suf, *left, *right;
  Pat_Len_t suf_len, lsp = MAX_PAT_LEN;
  Pat_Num_t ndp = 1;

  /* 确定lsp */
  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = cur_suf->next)
    if ((suf_len = strlen(cur_suf->str)) < lsp)
      lsp = suf_len;

  *lsp_p = lsp;

  /* 确定ndp */
  left = expand_node->next_level; right = left->next;
  while (right)
    if (same_str(left->str, right->str, lsp))
      right = right->next;
    else {
      left = right; right = left->next; ndp++;
    }

  *ndp_p = ndp;
}

static void choose_adaptor(Expand_Node_t *expand_node)
{
  Pat_Num_t ndp; /* number of the distinct prefix */
  Pat_Len_t lsp; /* length of the shortest prefix */

  get_ndp_and_lsp(expand_node, &ndp, &lsp);

  if (lsp == 1) {
    build_map(expand_node, ndp);
  } else {
    if (ndp < NUM_TO_BUILD_ARRAY)
      build_array(expand_node, ndp, lsp);
    else
      build_hash(expand_node, ndp, lsp);
  }
}

static Bool_t match_round(Expand_Node_t *expand_node, Char_t const *text_p, Char_t *pat_buf)
{
  Bool_t is_matched = FALSE, is_pat_end = FALSE;
  Char_t const *pos = text_p;
  Pat_Len_t pat_len;

  while (expand_node && expand_node->type != END) {
    expand_node = match_fun[expand_node->type](expand_node->next_level, &pos, &is_pat_end);

#if DEBUG
   if (is_pat_end) {
      is_matched = TRUE;
      pat_len = pos - text_p;
      *pat_buf++ = ' ';
      memcpy(pat_buf, text_p, pat_len);
      pat_buf += pat_len;
      is_pat_end = FALSE;
    }
#endif
  }

  *pat_buf = '\0';

  return is_matched;
}

int main(int argc, char **argv)
{
  FILE *pats_fp, *text_fp;
  Expand_Node_t *root;
  size_t file_size;
  clock_t start, end;
  Char_t *text_buf, *text_p, *text_end;;
  Char_t pat_buf[1000];
  Bool_t show_match_results = FALSE, show_sta_results = FALSE;
  Char_t opt;
  Char_t *text_file_name, *pats_file_name;
  Bool_t is_matched = FALSE;

  /* 处理命令行参数 */
  pats_file_name = argv[1];	/* 模式集文件*/
  text_file_name = argv[2];	/* 文本文件 */
  if (argc > 3)
    for (argv += 3; *argv && **argv == '-'; argv++)
      while (opt = *++*argv)
	switch (opt) {
	case 'o' : show_match_results = TRUE; break;
	case 's' : show_sta_results = TRUE; break;
	default : fprintf(stderr, "非法命令行参数!\n"); exit(EXIT_FAILURE);
	}


  /* 预处理,构建自适应节点 */
  pats_fp = Fopen(pats_file_name, "r");
  fprintf(stderr, "\nConstructing Adaptive Structures..."); fflush(stdout);
  start = clock();
  root = make_root(pats_fp);	/* 构建根节点 */
  Fclose(pats_fp);

  queue = make_queue();
  in_queue(queue, root);
  while (!queue_is_empty(queue))
    choose_adaptor(out_queue(queue));
  end = clock();
  fprintf(stderr, "Done!  \n%f\n",
	  (double) (end - start) / CLOCKS_PER_SEC);
  free_queue(queue);
  memory /= (1024 * 1024);
  printf("memory:%lfMB\n",memory);
  /* 读文本 */
  fprintf(stderr, "\nLoading text..."); fflush(stdout);
  start = clock();
  text_fp = Fopen(text_file_name, "rb");
  file_size = get_file_size(text_fp);
  text_buf = MALLOC(file_size + 1, Char_t);
  fread(text_buf, file_size, 1, text_fp);
  text_buf[file_size] = '\0';
  end = clock();
  fprintf(stderr, "Done!  \n%f\n",
	  (double) (end - start) / CLOCKS_PER_SEC);

  /* 匹配文本*/
  fprintf(stderr, "\nMatching..."); fflush(stdout);
  start = clock();
  text_end = text_buf + file_size - 1;

  for (text_p = text_buf; text_p < text_end; text_p++) {
    is_matched = match_round(root, text_p, pat_buf);
#if DEBUG
    if (is_matched && show_match_results)
      printf("%ld: %s\n", text_p - text_buf + 1, pat_buf);
#endif
  }
  end = clock();
  fprintf(stderr, "Done!  \n%f\n",
	  (double) (end - start) / CLOCKS_PER_SEC);

#if DEBUG
  if (show_sta_results)
    print_statistics(); /* 打印程序运行过程中的各种统计信息 */
#endif

}
