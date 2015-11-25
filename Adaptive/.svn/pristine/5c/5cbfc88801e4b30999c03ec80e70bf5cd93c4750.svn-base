#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "queue.h"
#include "share.h"
#include "binary.h"
#include "common.h"
#include "map.h"

extern Queue_t *queue;
unsigned ch_num[256];
extern  Sta_Elmt_t type_num[];
extern Sta_Elmt_t fun_calls[];

void build_single_ch(Expand_Node_t *expand_node)
{
    Suffix_Node_t *cur_suf, *next_suf, **next_p;
    Single_Ch_t *single_ch = CALLOC(1, Single_Ch_t);

#if DEBUG
    type_num[SINGLE_CH].num++;
#endif     

    cur_suf = expand_node->next_level;
    single_ch->key = *cur_suf->str;
    next_p = (Suffix_Node_t **) &single_ch->expand_node.next_level;
    
    for (cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) {
      next_suf = cur_suf->next;
      if (cur_suf = cut_head(cur_suf, 1)) {
	*next_p = cur_suf; next_p = &cur_suf->next;
      } else
	single_ch->pat_end_flag = TRUE;
    }
    
    *next_p = NULL;

    expand_node->next_level = single_ch;
    expand_node->type = SINGLE_CH;

    if (single_ch->expand_node.next_level)
      in_queue(queue, &single_ch->expand_node);
}

#define BUILD_MAP_4_OR_16(n)						\
									\
static void build_map_##n(Expand_Node_t *expand_node, Pat_Num_t dif_ch_num) \
{									\
  Suffix_Node_t *cur_suf, *next_suf, **next_p;				\
  Map_##n##_t *map_##n;							\
  Expand_Node_t *expand_nodes_##n;					\
  Char_t *keys;								\
  Char_t ch;								\
  int i;								\
									\
  map_##n = CALLOC(1, Map_##n##_t);					\
  map_##n->dif_ch_num = dif_ch_num;					\
  keys = map_##n->keys;							\
  expand_nodes_##n = map_##n->expand_nodes;				\
  /* 把第一个串的第一个字符拷到第一个key中 */				\
  cur_suf = expand_node->next_level;					\
  keys[0] = *cur_suf->str;						\
  next_p = (Suffix_Node_t **) &expand_nodes_##n[0].next_level;		\
									\
  for (i = 0, cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) {	\
    next_suf = cur_suf->next;						\
    if ((ch = *cur_suf->str) != keys[i]) {				\
      keys[++i] = ch; *next_p = NULL; /* 当前链表截止 */		\
      next_p = (Suffix_Node_t **) &expand_nodes_##n[i].next_level;	\
    }									\
									\
    if (cur_suf = cut_head(cur_suf, 1)) {				\
      *next_p = cur_suf; next_p = &cur_suf->next;			\
    } else								\
      set_bit(map_##n->pat_end_flag, i); /* 是模式尾 */			\
  }									\
									\
  *next_p = NULL;                                                       \
  expand_node->next_level = map_##n;					\
  expand_node->type = MAP_##n;						\
									\
  for (i = 0; i < dif_ch_num; i++) /* 加入到队列 */			\
    if (expand_nodes_##n[i].next_level)					\
      in_queue(queue, expand_nodes_##n + i);                            \
}

BUILD_MAP_4_OR_16(4)

BUILD_MAP_4_OR_16(16)

static void build_map_48(Expand_Node_t *expand_node, Pat_Num_t dif_ch_num)
{
  Suffix_Node_t *cur_suf, *next_suf, **next_p;
  Map_48_t *map_48 = CALLOC(1, Map_48_t);
  Expand_Node_t *expand_nodes_48 = map_48->expand_nodes;
  char *index = map_48->index;
  UC_t ch;
  int i = 0;
  
  memset(index, -1, 256);

  cur_suf = expand_node->next_level; ch = *cur_suf->str;
  index[ch] = 0;
  next_p = (Suffix_Node_t **) &expand_nodes_48[0].next_level;
  
  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) {
    next_suf = cur_suf->next;
    ch = *cur_suf->str;

    if (index[ch] != i) {
      index[ch] = ++i;
      *next_p = NULL; next_p = (Suffix_Node_t **) &expand_nodes_48[i].next_level;
    }
    
    if (cur_suf = cut_head(cur_suf, 1)) {
      *next_p = cur_suf; next_p = &cur_suf->next;
    } else  /* 模式串尾 */
      set_bit(map_48->pat_end_flag, i);
  }
  
  *next_p = NULL;
  expand_node->next_level = map_48;
  expand_node->type = MAP_48;

  for (i = 0; i < dif_ch_num; i++)
    if (expand_nodes_48[i].next_level)
      in_queue(queue, expand_nodes_48 + i);
}

static void build_map_256(Expand_Node_t *expand_node)
{
  Suffix_Node_t *cur_suf, *next_suf, **next_p;
  Map_256_t *map_256 = CALLOC(1, Map_256_t);
  Expand_Node_t *expand_nodes_256 = map_256->expand_nodes;
  UC_t ch, new_ch;
  int n;
  
  cur_suf = expand_node->next_level; ch = *cur_suf->str;
  next_p = (Suffix_Node_t **) &expand_nodes_256[ch].next_level; /* 指向第一个链表头 */

  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) {
    next_suf = cur_suf->next;
    new_ch = *cur_suf->str;

    if (new_ch != ch) { /* 终止上一个链表,跳转到新链表头 */
      *next_p = NULL; next_p = (Suffix_Node_t **) &expand_nodes_256[new_ch].next_level; 
      ch = new_ch;
    }

    if (cur_suf = cut_head(cur_suf, 1)) {
      *next_p = cur_suf; next_p = &cur_suf->next;
    } else
      set_bit(map_256->pat_end_flag, ch);
  }
  
  *next_p = NULL;
  expand_node->next_level = map_256;
  expand_node->type = MAP_256;

  for (n = 256, expand_node = map_256->expand_nodes; n; expand_node++, n--)
    if (expand_node->next_level)
      in_queue(queue, expand_node);
}

void build_map(Expand_Node_t *expand_node, Pat_Num_t dif_ch_num)
{
#if DEBUG  
  ch_num[dif_ch_num]++;
#endif   

  if (dif_ch_num <= 4) {
    build_map_4(expand_node, dif_ch_num);
#if DEBUG
    type_num[MAP_4].num++;
#endif     
  } else if (dif_ch_num <= 16) {
    build_map_16(expand_node, dif_ch_num);
#if DEBUG
    type_num[MAP_16].num++;
#endif     
  } else if (dif_ch_num <= 48) {
    build_map_48(expand_node, dif_ch_num);
#if DEBUG
    type_num[MAP_48].num++;
#endif     
  } else {
    build_map_256(expand_node);
#if DEBUG
    type_num[MAP_256].num++;
#endif     
  }
}

Expand_Node_t *match_single_ch(Single_Ch_t *single_ch, Char_t const **text, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_SINGLE_CH].num++;
#endif 

 if (**text != single_ch->key)
    return NULL;
    
  *is_pat_end = single_ch->pat_end_flag;
  (*text)++;

  return &single_ch->expand_node;
}

Expand_Node_t *match_map_4(Map_4_t *map_4, Char_t const **text, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_MAP_4].num++;
#endif 

 Char_t ch = **text, *key;
  Expand_Node_t *expand_node;
  int n, i;
  
  for (n = map_4->dif_ch_num, key = map_4->keys;
       n && ch > *key; n--, key++) /* key是有序排列的 */
    ;
  
  if (n == 0 || ch < *key) /* 匹配失败 */
    return NULL;

  i = key - map_4->keys;
  expand_node = map_4->expand_nodes + i;
  *is_pat_end = test_bit(map_4->pat_end_flag, i);
  (*text)++;
  
  return expand_node;
}

Expand_Node_t *match_map_16(Map_16_t *map_16, Char_t const **text, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_MAP_16].num++;
#endif 

  Char_t *keys = map_16->keys, ch = **text;
  Expand_Node_t *expand_node;
  char low = 0, high = map_16->dif_ch_num - 1, mid;
  
  while (low <= high) {
    mid = (low + high) >> 1;

    if (ch == keys[mid]) {
      expand_node = map_16->expand_nodes + mid;

      *is_pat_end = test_bit(map_16->pat_end_flag, mid);
      (*text)++;
      return expand_node;
    }  else if (ch < keys[mid])
      high = mid - 1;
    else
      low = mid + 1;
  }
  
  return NULL;
}

Expand_Node_t *match_map_48(Map_48_t *map_48, Char_t const **text, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_MAP_48].num++;
#endif 

  UC_t ch = **text;
  char i;
  
  if ((i = map_48->index[ch]) == -1)
    return NULL;

  *is_pat_end = test_bit(map_48->pat_end_flag, i);
  (*text)++;
  
  return map_48->expand_nodes + i;
}

Expand_Node_t *match_map_256(Map_256_t *map_256, Char_t const **text, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_MAP_256].num++;
#endif 

  UC_t ch = **text;
  
  if (*is_pat_end = test_bit(map_256->pat_end_flag, ch))
    (*text)++;
  
  return map_256->expand_nodes + ch;
}

#if DEBUG
void print_map_4(Map_4_t *map_4)
{
     int i;
     
     printf("\n4 map\n");
     for (i = 0; i < map_4->dif_ch_num; i++) {
	  printf("\n%c:\n ", map_4->keys[i]);
	  print_suffix(map_4->expand_nodes[i].next_level);
     }
}

void print_map_16(Map_16_t *map_16)
{
     int i;
     
     printf("\n16 map\n");
     for (i = 0; i < map_16->dif_ch_num; i++) {
	  printf("\n%c:\n ", map_16->keys[i]);
	  print_suffix(map_16->expand_nodes[i].next_level);
     }
}

void print_map_48(Map_48_t *map_48)
{
     int i;
     
     puts("\n48 map\n");
     for (i = 0; i < 256; i++)
	  if (map_48->index[i] != -1) {
	       printf("\n%c:\n ", i);
	       print_suffix(map_48->expand_nodes[map_48->index[i]].next_level);
	  }
}

void print_map_256(Map_256_t *map_256)
{
     int i;
     
     puts("\n256 map");
     for (i = 0; i < 256; i++)
       if (map_256->expand_nodes[i].next_level) {
	       printf("\n%c:\n ", i);
	       print_suffix(map_256->expand_nodes[i].next_level);
	  }
}
#endif 
