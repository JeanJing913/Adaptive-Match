#ifndef SHARE_H
#define SHARE_H

typedef unsigned char UC_t;
typedef char Char_t;
typedef UC_t Pat_Len_t;
typedef unsigned Pat_Num_t;
typedef char Bool_t;
typedef UC_t Type_t;
typedef UC_t Flag_t;
typedef unsigned Hash_Value_t;
/* 结构类型 */
#define TYPE_NUM    9
#define END         0
#define SINGLE_CH   1
#define MAP_4       2
#define MAP_16      3
#define MAP_48      4
#define MAP_256     5
#define SINGLE_STR  6
#define ARRAY       7
#define HASH        8
/* 匹配函数类型 */
#define MATCH_FUN_NUM       9
#define MATCH_SINGLE_CH     0
#define MATCH_MAP_4         1
#define MATCH_MAP_16        2
#define MATCH_MAP_48        3
#define MATCH_MAP_256       4
#define MATCH_SINGLE_STR    5
#define MATCH_ORDERED_ARRAY 6
#define MATCH_BINARY_ARRAY  7
#define MATCH_HASH          8

#define NUM_TO_BUILD_ARRAY 50
#define TRUE 1
#define FALSE 0
#define MAX_PAT_LEN 255
#define ALPHABET_SIZE 256
#define MIN_PERCENT 1.0
#define POINTER_SIZE 8
#define BITS_PER_BYTE 8
#define SMALL_ARRAY_SIZE 4

#define DEBUG 1

typedef struct expand_node {
  Type_t type;
  void *next_level;
} Expand_Node_t;

typedef struct suffix_node {
  struct suffix_node *next;
  Char_t str[];
} Suffix_Node_t;


Suffix_Node_t *cut_head(Suffix_Node_t *suf_node, Pat_Len_t lsp);
inline Bool_t same_str(Char_t const *s1, Char_t const *s2, Pat_Len_t len);
inline int str_n_cmp(Char_t const *s1, Char_t const *s2, Pat_Len_t len);
void push_queue(Expand_Node_t const *expand_node, Pat_Num_t num);
void print_str(Char_t const *s, Pat_Len_t len, Char_t terminator);

void print_suffix(Suffix_Node_t *cur_suf);

#endif
