#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "share.h"
#include "common.h"
#include "queue.h"
#include "array.h"
#include "statistics.h"
extern double memory;

extern Queue_t *queue;
extern Str_Num_t type_num[];
extern Str_Num_t fun_calls[];
extern Num_Num_t array_size[];

static Single_Str_t *make_single_str(Pat_Len_t str_len)
{
     Single_Str_t *new_single_str = VMALLOC(Single_Str_t, Char_t, str_len);
     memory += sizeof(Single_Str_t) + sizeof(char) * str_len;

     new_single_str->str_len = str_len;
     new_single_str->is_pat_end = FALSE;
     new_single_str->expand_node.type = END;
     new_single_str->expand_node.next_level = NULL;

     return new_single_str;
}

static void build_single_str(Expand_Node_t *expand_node, Pat_Len_t str_len)
{
  Suffix_Node_t *cur_suf, *next_suf, **next_p;
  Single_Str_t *single_str = make_single_str(str_len);

  /* 拷贝第一个后缀 */
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

  if (single_str->expand_node.next_level)
    in_queue(queue, &single_str->expand_node);
}

static Str_Array_t *make_str_array(Pat_Num_t str_num, Pat_Len_t str_len)
{
    int i = 0;
    Str_Array_t *new_array = (Str_Array_t*)malloc(sizeof(Str_Array_t) + sizeof(Char_t) * str_num * str_len);
    memory += sizeof(Str_Array_t) + sizeof(Char_t) * str_num * str_len;

    new_array->str_len = str_len;
    new_array->str_num = str_num;
    memset(new_array->is_pat_end, 0, sizeof(Flag_t));
    new_array->expand_node = (Expand_Node_t*)malloc(sizeof(Expand_Node_t) * str_num);
    memory += sizeof(Expand_Node_t) * str_num;

    for(i = 0;i < str_num;i ++){
        new_array->expand_node[i].type = END;
        new_array->expand_node[i].next_level = NULL;
    }
    return new_array;
}

static void build_str_array(Expand_Node_t *expand_node, Pat_Num_t str_num, Pat_Len_t str_len)
{
    int i = 0;
    Str_Array_t *str_array = make_str_array(str_num,str_len);
    Suffix_Node_t *cur,*next,**next_p;

    cur = (Suffix_Node_t*)expand_node->next_level;
    memcpy(str_array->str,cur->str,str_len);
    next_p = (Suffix_Node_t**)&str_array->expand_node[i].next_level;
    for(cur = (Suffix_Node_t*)expand_node->next_level;cur;cur = next){
        next = cur->next;
        if(!same_str(str_array->str + str_len * i,cur->str,str_len)){
            i ++;
            memcpy(str_array->str + i * str_len,cur->str,str_len);
            *next_p = NULL;
            next_p = (Suffix_Node_t**)&str_array->expand_node[i].next_level;
        }
        if(cur = cut_head(cur,str_len)){
            *next_p = cur;
            next_p = &cur->next;
        }
        else{
            set_bit(str_array->is_pat_end,i);
        }
    }

    *next_p = NULL;
    expand_node->next_level = str_array;
    expand_node->type = ARRAY;

    int j = 0;
    for(j = 0;j < str_num;j ++){
        if(str_array->expand_node[j].next_level){
            in_queue(queue,&str_array->expand_node[j]);
        }
    }
}

void build_array(Expand_Node_t *expand_node, Pat_Num_t str_num, Pat_Len_t str_len)
{
#if DEBUG
     array_size[str_num].num_1 = str_num;
     array_size[str_num].num_2++;
#endif

     if (str_num == 1) {
	  build_single_str(expand_node, str_len);
#if DEBUG
	  type_num[SINGLE_STR].num++;
#endif
     } else {
	  build_str_array(expand_node, str_num, str_len);
#if DEBUG
	  type_num[ARRAY].num++;
#endif
     }


}

inline Expand_Node_t *match_single_str(Single_Str_t *single_str, Char_t const **pos_p, Bool_t *is_pat_end)
{
#if DEBUG
 fun_calls[MATCH_SINGLE_STR].num++;
#endif

  if (!same_str(single_str->str, *pos_p, single_str->str_len))
    return NULL;

  *is_pat_end = single_str->is_pat_end;
  *pos_p += single_str->str_len;

  return &single_str->expand_node;
}

/*有序查找*/
inline static Expand_Node_t *array_ordered_match(Str_Array_t *str_array, Char_t const **pos_p, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_ORDERED_ARRAY].num++;
#endif
    Bool_t flag = 0;
    int i = 0;
    Char_t const *s = *pos_p;
    Pat_Len_t str_len = str_array->str_len;
    for(i = 0;i < str_array->str_num;i ++){
        if(same_str(str_array->str + str_len * i,s,str_len) == 1){
            flag = 1;
            break;
        }
    }
    if(flag == 0){
        return NULL;
    }
    *is_pat_end = test_bit(str_array->is_pat_end,i);
    *pos_p += str_len;
    return &str_array->expand_node[i];
}

/* 二分查找 */
inline static Expand_Node_t *array_binary_match(Str_Array_t *str_array, Char_t const **pos_p, Bool_t *is_pat_end)
{
     Char_t const *s = *pos_p;
    Pat_Len_t str_len = str_array->str_len;
    int low = 0,high = str_array->str_num - 1, mid;
    int result;
#if DEBUG
  fun_calls[MATCH_BINARY_ARRAY].num++;
#endif

    while(low <= high){
        mid = (low + high) >> 1;
        result = str_n_cmp(s,str_array->str + str_len * mid,str_len);
        if(result == 0){
            *is_pat_end = test_bit(str_array->is_pat_end,mid);
            *pos_p += str_len;
            return &str_array->expand_node[mid];
        }
        else if(result < 0){
            high = mid - 1;
        }
        else{
            low = mid + 1;
        }
    }
    return NULL;
}

Expand_Node_t *match_array(Str_Array_t *str_array, Char_t const **pos_p, Bool_t *is_pat_end)
{
  return (str_array->str_num <= SMALL_ARRAY_SIZE) ?
    array_ordered_match(str_array, pos_p, is_pat_end) :
    array_binary_match(str_array, pos_p, is_pat_end);
}

#if DEBUG
void print_array(Str_Array_t *str_array)
{
   Pat_Len_t str_len = str_array->str_len;
    Pat_Num_t str_num = str_array->str_num;
    int i;
    for(i = 0;i < str_num;i ++){
        print_str(str_array->str + str_len * i,str_len,':');
        if(test_bit(str_array->is_pat_end,i)){
            putchar('*');
        }
        putchar('\n');
        print_suffix(str_array->expand_node[i].next_level);
    }
}
#endif
