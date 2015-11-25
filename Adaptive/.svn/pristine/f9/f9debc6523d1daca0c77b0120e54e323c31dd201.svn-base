#ifndef HASH_H
#define HASH_H

#include "share.h"

typedef struct  hast_table {
  UC_t power;
  Pat_Num_t slots_num;
  Pat_Len_t lsp;
  Expand_Node_t slots[];
} Hash_Table_t;

void build_hash(Expand_Node_t *expand_node, Pat_Num_t dist_prf_num, Pat_Len_t lsp);
void print_hash(Hash_Table_t *hash_table);
inline unsigned hash(Char_t const *c, Pat_Len_t len, char power);
Expand_Node_t *match_hash(Hash_Table_t *hash_table, Char_t const **text, Bool_t *is_matched);

#endif 
