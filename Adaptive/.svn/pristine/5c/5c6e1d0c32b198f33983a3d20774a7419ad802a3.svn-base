#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "share.h"
#include "common.h"

inline void get_num_and_lsp(Expand_Node_t const *expand_node, Pat_Num_t *total_suf_p, Pat_Num_t *dif_prf_p, Pat_Len_t *lsp_p)
{
  Suffix_Node_t *cur_suf;
  Pat_Len_t suf_len, lsp = 255;
  Pat_Num_t num = 0;
  Suffix_Node_t *left, *right;
  
  /* 确定total_suf_num和lsp */
  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = cur_suf->next) {
    num++;
    if ((suf_len = strlen(cur_suf->str)) < lsp)
      lsp = suf_len;
    // assert(suf_len != 0);
  }
  
  *lsp_p = lsp; *total_suf_p = num;
  
  /* 确定dif_prf_num */
  num = 1;
  left = expand_node->next_level; right = left->next;
  while (right)
    if (same_str(left->str, right->str, lsp))
      right = right->next;
    else {
      left = right; right = left->next; num++;
    }

  *dif_prf_p = num;
}

/* 有序链表去重,头节点一定保留 */
void remove_duplicate(Suffix_Node_t *suf_list)
{
  Suffix_Node_t *left = suf_list, *right = left->next;

  while (right) 
    if (strcmp(left->str, right->str) == 0) {
      right = right->next; free(left->next); left->next = right;
    } else {
      left = right; right = left->next;
    }
}

Suffix_Node_t *cut_head(Suffix_Node_t *suf_node, Pat_Len_t lsp)
{
  Pat_Len_t suf_len;
  
  if ((suf_len = strlen(suf_node->str)) == lsp) { /* 该后缀无法再继续分割 */
    free(suf_node);
    return NULL;
  } 
  
  memmove(suf_node->str, suf_node->str + lsp, suf_len - lsp + 1);
  
  return suf_node;
}

inline Bool_t same_str(Char_t const *s1, Char_t const *s2, Pat_Len_t len)
{
  while (len && *s1 == *s2) 
    len--, s1++, s2++;
  
  return len == 0 ? TRUE : FALSE;
}

inline int str_n_cmp(Char_t const *s1, Char_t const *s2, Pat_Len_t len)
{
  while (len && *s1 == *s2)
    len--, s1++, s2++;
  
  return len == 0 ? 0 : *s1 - *s2;
}


#if DEBUG
void print_str(Char_t const *s, Pat_Len_t len, Char_t terminator)
{
  while (len--)
    putchar(*s++);

  putchar(terminator);
}

void print_suffix(Suffix_Node_t *cur_suf)
{
  while (cur_suf) {
    printf("    %s\n", cur_suf->str);
    cur_suf = cur_suf->next;
  }
}

#endif 

/* 有序并去重 */
/* void insert_to_expand(Expand_Node_t *expand_node, Suffix_Node_t *suf_node) */
/* { */
/*   Suffix_Node_t **next_p = (Suffix_Node_t **) &expand_node->next_level; */
/*   Suffix_Node_t *cur_suf; */
/*   int result; */
  
/*   while ((cur_suf = *next_p) && (result = strcmp(cur_suf->str, suf_node->str)) < 0) */
/*     next_p = &cur_suf->next; */
  
/*   if (cur_suf == NULL || result > 0) { */
/*     suf_node->next = cur_suf; */
/*     *next_p = suf_node; */
/*   } else  /\* 已经存在 *\/ */
/*     free(suf_node); */
/* } */
