#ifndef HASH_H
#define HASH_H

#include "share.h"

typedef struct  hast_table {
  UC_t power;
  Pat_Num_t table_size;
  Pat_Len_t lsp;
  Expand_Node_t slots[];
} Hash_Table_t;

void build_hash(Expand_Node_t *expand_node, Pat_Num_t ndp, Pat_Len_t lsp);
void print_hash(Hash_Table_t *hash_table);
Expand_Node_t *match_hash(Hash_Table_t *hash_table, Char_t const **pos_p, Bool_t *is_pat_end);

#endif 
