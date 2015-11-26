#ifndef MAP_H
#define MAP_H

#include "share.h"


typedef struct single_ch {
  Char_t ch;
  Expand_Node_t expand_node;
  Flag_t pat_end_flag;
} Single_Ch_t;

typedef struct map_4 {
  char ch_num; /* 最大为4 */
  Char_t keys[4];
  Expand_Node_t expand_nodes[4];
  Flag_t pat_end_flag[1];
} Map_4_t;

typedef struct map_16 {
  char ch_num; /* 最大为16 */
  Char_t keys[16];
  Expand_Node_t expand_nodes[16];
  Flag_t pat_end_flag[16/8];
} Map_16_t;

typedef struct map_48 {
  char index[256]; /* 非法索引值用-1表示 */
  Expand_Node_t expand_nodes[48];
  Flag_t pat_end_flag[48/8];
} Map_48_t;

typedef struct map_256{
  Flag_t pat_end_flag[256/8];
  Expand_Node_t expand_nodes[256];
} Map_256_t;

void build_map(Expand_Node_t *expand_node, Pat_Num_t ch_num);

Expand_Node_t *match_single_ch(Single_Ch_t *map_1, Char_t const **pos_p, Bool_t *is_pat_end);
Expand_Node_t *match_map_4(Map_4_t *map_4, Char_t const **pos_p, Bool_t *is_pat_end);
Expand_Node_t *match_map_16(Map_16_t *map_16, Char_t const **pos_p, Bool_t *is_pat_end);
Expand_Node_t *match_map_48(Map_48_t *map_48, Char_t const **pos_p, Bool_t *is_pat_end);
Expand_Node_t *match_map_256(Map_256_t *map_256, Char_t const **pos_p, Bool_t *is_pat_end);

void print_4_map(Map_4_t *map_4);
void print_16_map(Map_16_t *map_16);
void print_48_map(Map_48_t *map_48);
void print_256_map(Map_256_t *map_256);

#endif 
