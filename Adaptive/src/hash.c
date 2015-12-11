/* 120 lines */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <limits.h>
#include "common.h"
#include "binary.h"
#include "share.h"
#include "hash.h"
#include "queue.h"
#include "statistics.h"

#define L_BITS 6
#define R_BITS 2
#define SEED 50u

static unsigned power2[] = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096,
			    8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576,
			    2097152, 4194304};

extern Queue_t *queue;
extern Str_Num_t type_num[];
extern Str_Num_t fun_calls[];

static inline Hash_Value_t hash(Char_t const *s, Pat_Len_t len, char power)
{
     register Hash_Value_t value = SEED;

     while (len--)
       value ^= (value << L_BITS) + (value >> R_BITS) + *((UC_t const *) s++);
  
     return value & (1 << power) - 1;
}

static Hash_Table_t *make_hash_table(Pat_Num_t table_size, Pat_Len_t lsp, UC_t power)
{
     Hash_Table_t *new_hash_table = VMALLOC(Hash_Table_t, Expand_Node_t, table_size);

     new_hash_table->table_size = table_size;
     new_hash_table->lsp = lsp;
     new_hash_table->power = power;
     memset(new_hash_table->slots, 0, sizeof(Expand_Node_t) * table_size); /* slots初始化为0 */

     return new_hash_table;
}

/* 保存hash槽链表尾指针,用于维持槽链表有序 */
static Suffix_Node_t ***make_tails(Pat_Num_t table_size, Expand_Node_t const *slot)
{
  Suffix_Node_t ***tails = MALLOC(table_size, Suffix_Node_t **), ***p = tails;

  while (table_size--) 
    *p++ = (Suffix_Node_t **) &(slot++)->next_level;
  
  return tails;
}

void build_hash(Expand_Node_t *expand_node, Pat_Num_t ndp, Pat_Len_t lsp)  
{
  UC_t power;
  Hash_Table_t *hash_table;
  Suffix_Node_t *cur_suf, *next_suf, ***tails;
  Pat_Num_t table_size;
  unsigned hash_value;

#if DEBUG
  type_num[HASH].num++;
#endif   

  for (power = 1; ndp > power2[power]; power++)
    ;
  
  table_size = power2[--power];
  hash_table = make_hash_table(table_size, lsp, power);
  tails = make_tails(table_size, hash_table->slots);

  /* 把每个后缀放入其对应的哈希槽中 */
  for (cur_suf = expand_node->next_level; cur_suf; cur_suf = next_suf) { 
    next_suf = cur_suf->next; cur_suf->next = NULL;
    hash_value = hash(cur_suf->str, lsp, power);
    *tails[hash_value] = cur_suf;
    tails[hash_value] = &cur_suf->next;
  }
	
  free(tails);
  expand_node->next_level = hash_table;
  expand_node->type = HASH;
  
  push_queue(hash_table->slots, hash_table->table_size);
}

/* Hash表只能确定一定不匹配的串,可能匹配的串需要由对应expand node的下一级来进一步判断 */
Expand_Node_t *match_hash(Hash_Table_t *hash_table, Char_t const **pos_p, Bool_t *is_pat_end)
{
#if DEBUG
  fun_calls[MATCH_HASH].num++;
#endif 

  Expand_Node_t *slot = hash_table->slots + hash(*pos_p, hash_table->lsp, hash_table->power);
  
  return slot->next_level == NULL ? NULL : slot;
}

#if DEBUG
void print_hash(Hash_Table_t *hash_table)
{
    Expand_Node_t *slot = hash_table->slots;
    Pat_Num_t i;
    Pat_Num_t slots_num = hash_table->table_size;
    Pat_Len_t lsp = hash_table->lsp;
     
    printf("Hashing@ slots number: %u, lsp: %u\n", slots_num, lsp);
    for (i = 0; i < slots_num; slot++, i++)
      if (slot->next_level) {
    	printf("slot num: %u\n", i);
    	print_suffix(slot->next_level);
      }
}
#endif 
