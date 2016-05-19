#include <string.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include "binary.h"
#include "filter.h"
#include "share.h"
#include "common.h"

static uint32_t pow_256[] = {1, 256, 256*256, 256*256*256};

static Filter_T filter_new(int8_t block_size, Pat_Len_T lss)
{
     uint32_t n = pow_256[block_size];
     Filter_T new_filter = VMALLOC(struct filter, Bitmap_T, n);
     new_filter->children = CALLOC(n, struct Tree_Node);
     memset(new_filter->bitmap, 0, n * sizeof(Bitmap_T));
     new_filter->block_size = block_size;
     new_filter->window_size = lss;

     return new_filter;
}

Pat_Len_T get_lss(Suf_Node_T suf_list);
extern struct Suf_Node ***make_tails(Pat_Num_T table_size, Tree_Node_T child);

Filter_T build_filter(Suf_Node_T pat_list)
{
     Pat_Len_T lss = get_lss(pat_list);
     int8_t block_size = (lss == 1) ? 1 : 2;
     Filter_T filter = filter_new(block_size, lss);

     for (Suf_Node_T cur_suf = pat_list; cur_suf; cur_suf = cur_suf->next) {
	  for (Pat_Len_T i = 0; i <= lss - block_size; i++) {
	       uint32_t v = block_123(cur_suf->str + i, block_size);
	       set_bit(filter->bitmap + v, i);
	  }
     }

     return filter;
}

