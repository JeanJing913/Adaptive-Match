#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "share.h"
#include "common.h"
#include "queue.h"
#include "array.h"
#include "binary.h"
extern int cpu_size;
extern Queue_t *queue;
extern Sta_Elmt_t type_num[];
extern Sta_Elmt_t fun_calls[];

unsigned array_len[NUM_TO_BUILD_ARRAY];

static Str_Array_t *make_array(Pat_Num_t str_num, Pat_Len_t str_len)
{
    int i = 0;
    Str_Array_t *new_array = (Str_Array_t*)malloc(sizeof(Str_Array_t) + sizeof(Char_t) * str_num * str_len);
    cpu_size += sizeof(Str_Array_t) + sizeof(Char_t) * str_num * str_len;

    new_array->str_len = str_len;
    new_array->str_num = str_num;
    memset(new_array->is_pat_end, 0, sizeof(Flag_t));
    new_array->expand_node = (Expand_Node_t*)malloc(sizeof(Expand_Node_t) * str_num);
    cpu_size += sizeof(Expand_Node_t) * str_num;

    for(i = 0;i < str_num;i ++){
        new_array->expand_node[i].type = END;
        new_array->expand_node[i].next_level = NULL;
    }
    return new_array;
}

void build_array(Expand_Node_t *expand_node, Pat_Num_t str_num, Pat_Len_t str_len)
{
    int i = 0;
    Str_Array_t *str_array = make_array(str_num,str_len);
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

#if DEBUG
  type_num[ARRAY].num++;//统计信息
  array_len[str_array->str_num]++;
  #endif

    int j = 0;
    for(j = 0;j < str_num;j ++){
        if(str_array->expand_node[j].next_level){
            in_queue(queue,&str_array->expand_node[j]);
        }
    }
}

static Single_Str_t *make_single_str(Pat_Len_t str_len)
{
     Single_Str_t *new_single_str = VMALLOC(Single_Str_t, Char_t, str_len);
     cpu_size += sizeof(Single_Str_t) + sizeof(char) * str_len;

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
    Bool_t flag = 0;
    int i = 0;
    Char_t const *s = *text;
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
    *text += str_len;
    return &str_array->expand_node[i];
}

/* 二分查找 */
inline static Expand_Node_t *binary_match(Str_Array_t *str_array, Char_t const **text, Bool_t *is_pat_end)
{
    Char_t const *s = *text;
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
            *text += str_len;
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

Expand_Node_t *match_array(Str_Array_t *str_array, Char_t const **text, Bool_t *is_pat_end)
{
  return (str_array->str_num <= SMALL_ARRAY_SIZE) ?
    ordered_match(str_array, text, is_pat_end) :
    binary_match(str_array, text, is_pat_end);
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
