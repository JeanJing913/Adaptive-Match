#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "share.h"
#include "common.h"
#include "queue.h"
#include "array.h"

extern Queue_t *queue;
extern Sta_Elmt_t type_num[];
extern Sta_Elmt_t fun_calls[];

unsigned array_len[NUM_TO_BUILD_ARRAY];

static Str_Array_t *make_array(Pat_Num_t str_num, Pat_Len_t str_len)
{
     Str_Array_t *new_array = VMALLOC(Str_Array_t, Str_Elmt_t, str_num);
     
     new_array->str_num = str_num;
     new_array->str_len = str_len;
     memset(new_array->array, 0, str_num * sizeof(Str_Elmt_t));
     
     return new_array;
}

void build_array(Expand_Node_t *expand_node, Pat_Num_t str_num, Pat_Len_t str_len)
{
  Suffix_Node_t *cur_suf, *next_suf, *suf_list, **next_p;
  Str_Array_t *str_array = make_array(str_num, str_len); /* 构建str_array */
  Str_Elmt_t *str_elmt = str_array->array;
  Pat_Num_t n = str_num;

#if DEBUG
  type_num[ARRAY].num++;
  array_len[str_array->str_num]++;
#endif

#define BUILD_ARRAY(pointer)						\
  str_elmt = str_array->array;        /* 把第一个字符串拷入数组的第一个元素 */ \
  memcpy(str_elmt->str.pointer, ((Suffix_Node_t *) expand_node->next_level)->str, str_len); \
  next_p = (Suffix_Node_t **) &str_elmt->expand_node.next_level;	\
									\
  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) { \
    next_suf = cur_suf->next;						\
    if (!same_str(str_elmt->str.pointer, cur_suf->str, str_len)) {	\
      memcpy((++str_elmt)->str.pointer, cur_suf->str, str_len); /*原链表终止, 指向新链表头 */ \
      *next_p = NULL;	next_p = (Suffix_Node_t **) &str_elmt->expand_node.next_level; \
    }									\
									\
    if (cur_suf = cut_head(cur_suf, str_len)) {				\
      *next_p = cur_suf; next_p = &cur_suf->next;			\
    } else								\
      str_elmt->pat_end_flag = TRUE;					\
  }									\
									\
  *next_p = NULL;

  if (str_len > POINTER_SIZE) { /* 节点外 */
    while (n--) (str_elmt++)->str.p = MALLOC(str_len, Char_t); /* 为每个节点,在节点外分配空间 */
    BUILD_ARRAY(p);
  } else {
    BUILD_ARRAY(buf);
  }
  
  expand_node->next_level = str_array;
  expand_node->type = ARRAY;
  
  /* 加入到队列 */
  for (str_elmt = str_array->array; str_num; str_elmt++, str_num--)
    if (suf_list = str_elmt->expand_node.next_level) {
      in_queue(queue, &str_elmt->expand_node);
    }
}

static Single_Str_t *make_single_str(Pat_Len_t str_len)
{
     Single_Str_t *new_single_str = VMALLOC(Single_Str_t, Char_t, str_len);
     
     new_single_str->str_len = str_len;
     new_single_str->is_pat_end = FALSE;
     new_single_str->expand_node.type = END;
     new_single_str->expand_node.next_level = NULL;
     
     return new_single_str;
}

void build_single_str(Expand_Node_t *expand_node, Pat_Len_t str_len)
{
  Suffix_Node_t *cur_suf, *next_suf, **next_p;
  Single_Str_t *single_str = make_single_str(str_len);
  
  cur_suf = expand_node->next_level;
  memcpy(single_str->str, cur_suf->str, str_len);
  next_p = (Suffix_Node_t **) &single_str->expand_node.next_level;

  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) {
    next_suf = cur_suf->next;
    if (cur_suf = cut_head(cur_suf, str_len)) {
      *next_p = cur_suf; next_p = &cur_suf->next;
    } else
      single_str->is_pat_end = TRUE;
  }
  
  *next_p = NULL;

  expand_node->next_level = single_str;
  expand_node->type = SINGLE_STR;

#if DEBUG
  type_num[SINGLE_STR].num++;
#endif

  if (single_str->expand_node.next_level)
    in_queue(queue, &single_str->expand_node);
}
 
inline Expand_Node_t *match_single_str(Single_Str_t *single_str, Char_t const **text, Bool_t *is_pat_end)
{
#if DEBUG 
 fun_calls[MATCH_SINGLE_STR].num++;
#endif 

  if (!same_str(single_str->str, *text, single_str->str_len))
    return NULL;
  
  *is_pat_end = single_str->is_pat_end;
  *text += single_str->str_len;
  
  return &single_str->expand_node;
}

/*有序查找*/
inline static Expand_Node_t *ordered_match(Str_Array_t *str_array, Char_t const **text, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_ORDERED_ARRAY].num++;
#endif
  
  Pat_Len_t str_len = str_array->str_len;
  Pat_Num_t str_num;
  Char_t const *s = *text;
  Str_Elmt_t *str_elmt;
  int result;

#define ORDERED_MATCH(pointer)						\
  for (str_num = str_array->str_num, str_elmt = str_array->array;	\
       str_num && (result = str_n_cmp(str_elmt->str.pointer, s, str_len)) < 0; \
       str_num--, str_elmt++)						\
    ;
     
  if (str_len > POINTER_SIZE)  /* 节点外 */
    ORDERED_MATCH(p)
  else 			/* 节点内 */
    ORDERED_MATCH(buf)

  if (str_num == 0 || result > 0) 	/* 没找到 */
    return NULL;

  *is_pat_end = str_elmt->pat_end_flag;
  *text += str_len;
     
  return &str_elmt->expand_node;
}

/* 二分查找 */
inline static Expand_Node_t *binary_match(Str_Array_t *str_array, Char_t const **text, Bool_t *is_pat_end)
{
  int low = 0, high = str_array->str_num - 1, mid;
  Str_Elmt_t *array = str_array->array;
  Pat_Len_t str_len = str_array->str_len;
  Char_t const *s = *text;
  int result;

#if DEBUG
  fun_calls[MATCH_BINARY_ARRAY].num++;
#endif

#define BINARY_MATCH(pointer)                                               \
  while (low <= high) {				                            \
      mid = (low + high) >> 1;                                              \
      if ((result = str_n_cmp(s, array[mid].str.pointer, str_len)) == 0) {  \
	*is_pat_end = array[mid].pat_end_flag;                              \
	*text += str_len;                                                   \
	return &array[mid].expand_node;                                     \
      } else if (result < 0)                                                \
	high = mid - 1;                                                     \
      else 								    \
	low = mid + 1;                                                      \
    }

  if (str_len > POINTER_SIZE) 	/* 节点外 */
    BINARY_MATCH(p)
  else  			/* 节点内 */
    BINARY_MATCH(buf)
  
  return NULL;
}

Expand_Node_t *match_array(Str_Array_t *str_array, Char_t const **text, Bool_t *is_pat_end)
{
  return (str_array->str_num <= SMALL_ARRAY_SIZE) ?
    ordered_match(str_array, text, is_pat_end) :
    binary_match(str_array, text, is_pat_end);
}

#if DEBUG
void print_array(Str_Array_t *str_array)
{
  Str_Elmt_t *str_elmt;
  Pat_Len_t str_len = str_array->str_len;
  Pat_Num_t n;
  
#define PRINT_ARRAY(pointer)                                                       \
  for (str_elmt = str_array->array, n = str_array->str_num; n; str_elmt++, n--) {  \
    print_str(str_elmt->str.pointer, str_len,  ':');                               \
    if (str_elmt->pat_end_flag)                                                    \
      putchar('*');                                                                \
    putchar('\n');                                                                 \
    print_suffix(str_elmt->expand_node.next_level);                                \
  }

  if (str_len > POINTER_SIZE)
    PRINT_ARRAY(p)
  else
    PRINT_ARRAY(buf)
}
#endif 
