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
#include "statistics.h"

extern double memory;
extern Queue_t *queue;
extern Num_Num_t map_size[];
extern Str_Num_t type_num[];
extern Str_Num_t fun_calls[];

void build_single_ch(Expand_Node_t *expand_node)
{
    Suffix_Node_t *cur_suf, *next_suf, **next_p;
    Single_Ch_t *single_ch = CALLOC(1, Single_Ch_t);
    memory += sizeof(Single_Ch_t);

    cur_suf = expand_node->next_level;
    single_ch->ch = *cur_suf->str;
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
static void build_map_##n(Expand_Node_t *expand_node, Pat_Num_t ch_num) \
{									\
  Suffix_Node_t *cur_suf, *next_suf, **next_p;				\
  Map_##n##_t *map_##n;							\
  Expand_Node_t *expand_nodes_##n;					\
  Char_t *keys;								\
  int i = 0;								\
									\
  map_##n = CALLOC(1, Map_##n##_t);					\
  map_##n->ch_num = ch_num;						\
  keys = map_##n->keys;							\
  expand_nodes_##n = map_##n->expand_nodes;				\
  /* 把第一个串的第一个字符拷到第一个key中 */				\
  cur_suf = expand_node->next_level;					\
  keys[i] = *cur_suf->str;						\
  next_p = (Suffix_Node_t **) &expand_nodes_##n[i].next_level;		\
									\
  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) { \
    next_suf = cur_suf->next;						\
    if (*cur_suf->str != keys[i]) {					\
      keys[++i] = *cur_suf->str; *next_p = NULL; /* 当前链表截止 */	\
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
  for (expand_node = map_##n->expand_nodes; ch_num; expand_node++, ch_num--) \
    if (expand_node->next_level)					\
      in_queue(queue, expand_node);					\
}

BUILD_MAP_4_OR_16(4)

BUILD_MAP_4_OR_16(16)

static void build_map_48(Expand_Node_t *expand_node, Pat_Num_t ch_num)
{
  Suffix_Node_t *cur_suf, *next_suf, **next_p;
  Map_48_t *map_48 = CALLOC(1, Map_48_t);
  memory += sizeof(Map_48_t);

  Expand_Node_t *expand_nodes_48 = map_48->expand_nodes;
  char *index = map_48->index;
  UC_t ch;
  int i = 0;

  memset(index, -1, 256);

  cur_suf = expand_node->next_level;
  ch = *cur_suf->str; index[ch] = i;
  next_p = (Suffix_Node_t **) &expand_nodes_48[i].next_level;

  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) {
    next_suf = cur_suf->next;
    ch = *cur_suf->str;

    if (index[ch] != i) {
      assert(index[ch] == -1);
      index[ch] = ++i;
      *next_p = NULL; next_p = (Suffix_Node_t **) &expand_nodes_48[i].next_level;
    }

    if (cur_suf = cut_head(cur_suf, 1)) {
      *next_p = cur_suf; next_p = &cur_suf->next;
    } else  /* 模式串尾 */
      set_bit(map_48->pat_end_flag, i);
  }

  assert(ch_num-1 == i);
  *next_p = NULL;

  expand_node->next_level = map_48;
  expand_node->type = MAP_48;

  for (expand_node = map_48->expand_nodes; ch_num; expand_node++, ch_num--)
    if (expand_node->next_level)
      in_queue(queue, expand_node);
}

static void build_map_256(Expand_Node_t *expand_node)
{
  Suffix_Node_t *cur_suf, *next_suf, **next_p;
  Map_256_t *map_256 = CALLOC(1, Map_256_t);
  memory += sizeof(Map_256_t);

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

void build_map(Expand_Node_t *expand_node, Pat_Num_t ch_num)
{
#if DEBUG
  map_size[ch_num].num_1 = ch_num;
  map_size[ch_num].num_2++;
#endif

  if (ch_num == 1) {	/* 单个字符 */
    build_single_ch(expand_node);
#if DEBUG
    type_num[SINGLE_CH].num++;
#endif
  } else if (ch_num <= 4) {
      memory += sizeof(Map_4_t);

    build_map_4(expand_node, ch_num);
#if DEBUG
    type_num[MAP_4].num++;
#endif
  } else if (ch_num <= 16) {
    memory += sizeof(Map_16_t);

    build_map_16(expand_node, ch_num);
#if DEBUG
    type_num[MAP_16].num++;
#endif
  } else if (ch_num <= 48) {
    build_map_48(expand_node, ch_num);
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

Expand_Node_t *match_single_ch(Single_Ch_t *single_ch, Char_t const **pos_p, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_SINGLE_CH].num++;
#endif

 if (**pos_p != single_ch->ch)
    return NULL;

  *is_pat_end = single_ch->pat_end_flag;
  (*pos_p)++;

  return &single_ch->expand_node;
}

Expand_Node_t *match_map_4(Map_4_t *map_4, Char_t const **pos_p, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_MAP_4].num++;
#endif

  Char_t ch = **pos_p, *key;
  char ch_num, i;

  /* key是有序排列的 */
  for (ch_num = map_4->ch_num, key = map_4->keys; ch_num && *key < ch; ch_num--, key++)
    ;

  if (ch_num == 0 || *key > ch) /* 匹配失败 */
    return NULL;

  i = key - map_4->keys;
  *is_pat_end = test_bit(map_4->pat_end_flag, i);
  (*pos_p)++;

  return map_4->expand_nodes + i;
}

Expand_Node_t *match_map_16(Map_16_t *map_16, Char_t const **pos_p, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_MAP_16].num++;
#endif

  Char_t *keys = map_16->keys, ch = **pos_p;
  char low = 0, high = map_16->ch_num - 1, mid;

  while (low <= high) {
    mid = (low + high) >> 1;
    if (ch == keys[mid]) {
      *is_pat_end = test_bit(map_16->pat_end_flag, mid);
      (*pos_p)++;
      return map_16->expand_nodes + mid;
    }  else if (ch < keys[mid])
      high = mid - 1;
    else
      low = mid + 1;
  }

  return NULL;
}

Expand_Node_t *match_map_48(Map_48_t *map_48, Char_t const **pos_p, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_MAP_48].num++;
#endif

  UC_t ch = **pos_p;
  char i;

  if ((i = map_48->index[ch]) == -1)
    return NULL;

  *is_pat_end = test_bit(map_48->pat_end_flag, i);
  (*pos_p)++;

  return map_48->expand_nodes + i;
}

Expand_Node_t *match_map_256(Map_256_t *map_256, Char_t const **pos_p, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_MAP_256].num++;
#endif

  UC_t ch = **pos_p;

  if (*is_pat_end = test_bit(map_256->pat_end_flag, ch))
    (*pos_p)++;

  return map_256->expand_nodes + ch;
}

#if DEBUG
void print_map_4(Map_4_t *map_4)
{
     int i;

     printf("\n4 map\n");
     for (i = 0; i < map_4->ch_num; i++) {
	  printf("\n%c:\n ", map_4->keys[i]);
	  print_suffix(map_4->expand_nodes[i].next_level);
     }
}

void print_map_16(Map_16_t *map_16)
{
  int i;

  printf("\n16 map\n");
  for (i = 0; i < map_16->ch_num; i++) {
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
