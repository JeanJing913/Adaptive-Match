#ifndef ARRAY_H
#define ARRAY_H

#include "share.h"

typedef struct str_array {
  Pat_Num_t str_num;
  Pat_Len_t str_len;
  Str_Elmt_t array[];
} Str_Array_t;

typedef struct single_str_t {
  Pat_Len_t str_len;
  Expand_Node_t expand_node;
  Flag_t is_pat_end;
  Char_t str[];
} Single_Str_t;

void build_array(Expand_Node_t *expand_node, Pat_Num_t str_num, Pat_Len_t str_len);
void build_single_str(Expand_Node_t *expand_node, Pat_Len_t str_len);
Expand_Node_t *match_array(Str_Array_t *str_array, Char_t const **text, Bool_t *is_pat_end);
Expand_Node_t *match_single_str(Single_Str_t *single_str, Char_t const **text, Bool_t *is_pat_end);
void print_array(Str_Array_t *str_array);


#endif 
