  /*
 * mm-naive.c - The least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by allocating a
 * new page as needed.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused.
 *
 * The heap check and free check always succeeds, because the
 * allocator doesn't depend on any of the old data.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

typedef struct {
 size_t size;
 size_t allocated;
} block_header;

typedef struct list_node {
 struct list_node *prev;
 struct list_node *next;
} list_node;

/* always use 16-byte alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

/* rounds up to the nearest multiple of mem_pagesize() */
#define PAGE_ALIGN(size) (((size) + (mem_pagesize()-1)) & ~(mem_pagesize()-1))

#define BYT_TO_BLK(bytes) (bytes >> 1)
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE((char *)(bp)-OVERHEAD))
#define BLK_TO_BYT(blks) (blks << 1)
#define HDRP(bp) ((char *)(bp) - sizeof(block_header))
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define GO_TO_FTR(bp) ( HDRP(HDRP(NEXT_BLKP(bp))) )
#define OVERHEAD (sizeof(block_header) * 2)
#define FTRP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp))-OVERHEAD)

#define GET(p) (*(size_t *)(p))
#define GET_DATA(p) (GET((void*)p + 8))
#define PUT(p, val) (*(size_t *)(p) = (val))
#define PACK(size, alloc) ((size) | (alloc))
#define GET_SIZE(p) ((block_header *)(p))->size
#define GET_ALLOC(p) ((block_header *)(p))->allocated
#define CNK_HDRP(bp) ((char*)bp - (3*BLK_HDR_SZ))
#define LIST_NODE_HDRP(bp) ((list_node*)((char*)bp -(5*BLK_HDR_SZ)))
#define CHNK_BP(list_node) ((char*)list_node + (5*BLK_HDR_SZ))

#define CHUNK_SIZE (1 << 14)
#define CHUNK_ALIGN(size) (((size)+(CHUNK_SIZE-1)) & ~(CHUNK_SIZE-1))
#define CHUNK_OVERHEAD (sizeof(block_header) * 5)
#define BLK_HDR_SZ (sizeof(block_header))
#define SZ_LIST_NODE (sizeof(list_node))

/* rounds down to the nearest multiple of mem_pagesize() */
#define ADDRESS_PAGE_START(p) ((void *)(((size_t)p) & ~(mem_pagesize()-1)))  
static int ptr_is_mapped(void *p, size_t len);

static void* extend(size_t new_size);
static int set_allocated(void *bp, size_t size);
static void* set_new_chunk(size_t new_size);
static unsigned long calc_offset(void* new_ptr);
static void stack();
static void dbg_data();
static int block_unequal(void* bp);
static int block_mapped(void* p);
static int check_block_hdr(void* bp, int hdr_ftr, int* size_sum, int* alloc, int print_on);
static void initialize();
static int check_chunk_hdr(void* bp, int hdr_ftr, size_t* size_sum , int* valid_nodes, int print_on);
static size_t calc_target();
static int mm_check1();
static int block_mapped1(void* p);

size_t size_target = 0;
int target_count = 0;
double average  = 0;

long delta1 = 0;
long delta2 = 0;
long delta3 = 0;
long delta4 = 0;

int alloc_block_bytes = 0;
int unalloc_block_bytes = 0;
int chunk_bytes = 0;   
int num_chunks_set = 0; 
int num_blocks = 0;
int num_alloc_blocks = 0;
int num_unalloc_blocks = 0;  

int tmp_alloc_block_bytes = 0;
int tmp_unalloc_block_bytes = 0;
int tmp_chunk_bytes = 0;
int tmp_num_chunks_set = 0;
int tmp_num_blocks = 0;
int tmp_num_alloc_blocks = 0;
int tmp_num_unalloc_blocks = 0;

int enter_on = 0;
int scan_on = 0;
int mm_dbg = 0;
int stack_on = 0;
int num_init = 0;
int num_chunks = 0;
int num_extend = 0;
int num_free = 0;
int num_set_chunk = 0;
int num_can_free = 0;
int num_set_alloc = 0;
int num_malloc = 0;
int debug_on = 0;
int set_alloc = 0;
int num_check = 0;
int block_loop = 0;
int chunk_loop = 0;
int check_init = 1;
char in = 'z';
void *current_avail_size = NULL;
void* first_bp = NULL;
size_t num_pages = 16;
int dynamic_page_target = 1;


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  void* current_avail = NULL;
  first_bp = NULL;
  in = 'x';
  initialize();

  if(enter_on)printf("mm_init: %d\n", ++num_init);
  current_avail_size = 0;

  size_t num_bytes = mem_pagesize()*num_pages;
  size_t chunk_bytes = PAGE_ALIGN(num_bytes);

  first_bp = set_new_chunk(chunk_bytes);
  if(first_bp == NULL || ((size_t)first_bp) % 16 != 0){ // NOT ALIGNED
    if(debug_on) {printf("SET NEW CHUNK\n"); /*scanf("%c",&in);*/}
    return -1;
  }

  if(0) scanf("%c", &in);

  return 0; //arb
}

static size_t calc_target()
{

  return 0;
}

static void initialize(){

  if(dynamic_page_target)
  //size_target = mem_pagesize()*64  + (target_count*mem_pagesize()*(1 << ))

  num_init = 0;
  num_chunks = 0;
  num_extend = 0;
  num_free = 0;
  num_set_chunk = 0;
  num_can_free = 0;
  num_set_alloc = 0;

  alloc_block_bytes +=      tmp_alloc_block_bytes;
  unalloc_block_bytes +=    tmp_unalloc_block_bytes;
  chunk_bytes +=            tmp_chunk_bytes;
  num_chunks_set +=         tmp_num_chunks_set;
  num_blocks +=             tmp_num_blocks;
  num_alloc_blocks +=       tmp_num_alloc_blocks;
  num_unalloc_blocks +=     tmp_num_unalloc_blocks;

  tmp_alloc_block_bytes = 0;
  tmp_unalloc_block_bytes = 0;
  tmp_chunk_bytes = 0;
  tmp_num_chunks_set = 0;
  tmp_num_blocks = 0;
  tmp_num_alloc_blocks = 0;
  tmp_num_unalloc_blocks = 0;

}



// chunk_capacity = sum all chunk sizes
// unalloc capacity = sum all unalloc blocks
// alloc capacity = sum all alloc blocks

// byte check = (sum all chunks - num_chunks*chunk_overhead) == (unalloc capacity + alloc capacity)


static void* set_new_chunk(size_t new_size){
  if(enter_on)printf("SET NEW CHUNK: %d\n", ++num_set_chunk);
  void* base_ptr = mem_map(new_size);

  void* bp = (void*)base_ptr + (2*SZ_LIST_NODE) + (2*BLK_HDR_SZ) + (BLK_HDR_SZ);

  list_node* chk_node1 = (list_node*)base_ptr;
  list_node* chk_node2 = (list_node*)((void*)base_ptr + SZ_LIST_NODE);

  chk_node1->next = NULL;
  chk_node1->prev = NULL;

  chk_node2->next = NULL;
  chk_node2->prev = NULL;

  block_header* chk_prolog_hdr  = (block_header*)((void*)base_ptr + (2*SZ_LIST_NODE));
  GET_SIZE(chk_prolog_hdr) = 2*BLK_HDR_SZ;
  GET_ALLOC(chk_prolog_hdr) = new_size;


  block_header* chk_prolog_ftr = (block_header*)((void*)base_ptr + (3*SZ_LIST_NODE));
  GET_SIZE(chk_prolog_ftr) = 2*BLK_HDR_SZ;
  GET_ALLOC(chk_prolog_ftr) = new_size;


  block_header* blk_hdr = (void*)base_ptr + (4*BLK_HDR_SZ);
  GET_SIZE(blk_hdr) = new_size - CHUNK_OVERHEAD;
  GET_ALLOC(blk_hdr) = 0;

  block_header* blk_ftr = (void*)base_ptr + new_size - (2*SZ_LIST_NODE);
  GET_SIZE(blk_ftr) = new_size - CHUNK_OVERHEAD;  
  GET_ALLOC(blk_ftr) = 0;


  block_header* chk_terminator = (void*)base_ptr + new_size - SZ_LIST_NODE;
  GET_SIZE(chk_terminator) = 0;
  GET_ALLOC(chk_terminator) = 1;


  tmp_unalloc_block_bytes += new_size - CHUNK_OVERHEAD - OVERHEAD;
  tmp_chunk_bytes += new_size;
  tmp_num_chunks_set++;
  tmp_num_blocks++;


  if(0) scanf("%c", &in);

  return bp;
}

/* 
 * mm_malloc - Allocate a block by using bytes from current_avail,
 *     grabbing a new page if necessary.
 */
void *mm_malloc(size_t size) {
 if(enter_on)printf("MALLOC: %d\n", ++num_malloc);

 int new_size = ALIGN(size + OVERHEAD);
 void* bp = first_bp;
 list_node* prev_chunk;
 list_node* current_chunk = LIST_NODE_HDRP(first_bp);
 list_node* next_chunk;
 void* end_chunk_ptr;

while(current_chunk != NULL){
 bp = CHNK_BP(current_chunk);  
 size_t chunk_sz = GET_ALLOC((void*)bp - OVERHEAD);
 end_chunk_ptr = (void*)current_chunk + chunk_sz; 

  while (GET_SIZE(HDRP(bp)) != 0) { 
       if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= new_size)) {
           if(ptr_is_mapped(FTRP(bp), BLK_HDR_SZ)){
             if(FTRP(bp) < end_chunk_ptr){
               set_allocated(bp, new_size);
               return bp;
             }
           }
       }
  
    bp = NEXT_BLKP(bp); 
    if(!ptr_is_mapped(HDRP(bp), BLK_HDR_SZ)) break;    
  }

  if(current_chunk->next == NULL) 
    prev_chunk = current_chunk;

  current_chunk = current_chunk->next;
}

 void* new_bp;
 new_bp = extend(new_size);
 current_chunk = LIST_NODE_HDRP(new_bp);
 next_chunk = current_chunk;
 next_chunk->prev = prev_chunk;
 prev_chunk->next = next_chunk;

 if(!set_allocated(new_bp, new_size)) {printf("SET ALLOCATED FAILED:\n"); scanf("%c", &in);}
 return new_bp;
}

static int set_allocated(void *bp, size_t size) {
if(enter_on)printf("SET ALLOC: %d\n", ++set_alloc);  
size_t extra_size = GET_SIZE(HDRP(bp)) - size;

  if (extra_size > ALIGN(1 + OVERHEAD)) {
       if(!block_mapped(bp)) return 0;     
       GET_SIZE(HDRP(bp)) = size;
       GET_SIZE(FTRP(bp)) = size;

       if(!block_mapped(NEXT_BLKP(bp))) return 0;            
       GET_SIZE(HDRP(NEXT_BLKP(bp))) = extra_size;
       GET_SIZE(FTRP(NEXT_BLKP(bp))) = extra_size;       
       GET_ALLOC(HDRP(NEXT_BLKP(bp))) = 0;
       GET_ALLOC(FTRP(NEXT_BLKP(bp))) = 0;    

       tmp_unalloc_block_bytes += extra_size;
       tmp_unalloc_block_bytes -= size;
       tmp_alloc_block_bytes += size;
       tmp_num_alloc_blocks++;

  }else{
    tmp_unalloc_block_bytes -= size;
    tmp_alloc_block_bytes += size;
    tmp_num_alloc_blocks++;    
    tmp_num_unalloc_blocks--;
  }

 GET_ALLOC(HDRP(bp)) = 1;
 GET_ALLOC(FTRP(bp)) = 1; 

 return 1;
}

/*
 * EXTENDS available space by aqcuiring new chunk
 */
static void* extend(size_t new_size) {
if(enter_on) printf("EXTEND: %d\n", ++num_extend);  

  size_t page_bytes = PAGE_ALIGN(new_size);
  size_t extend_bytes = num_pages*page_bytes;

  if(extend_bytes % 4096 != 0) {printf("EXTEND NOT ALIGNED\n"); }

  void *bp = set_new_chunk(extend_bytes);

  if(bp == NULL)
    if(debug_on) 
      {printf("EXTEND failed to init new chunk\n"); /*scanf("%c",&in);*/}
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{

  /*
  failure cases
  1) unallocates only a portion that should be unmapped
  2) unallocates more than the desired portion
  3) unallocates something already unallocated ?
  4) attempts to unallocate something which isn't a previous givern bp

  */
    
  GET_ALLOC(HDRP(ptr)) = 0;
  GET_ALLOC(FTRP(ptr)) = 0;


  return;
}

/*
 * mm_check - Check whether the heap is ok, so that mm_malloc()
 *            and proper mm_free() calls won't crash.
 */
int mm_check()
{
  /*
  if(enter_on)printf("mm_check\n");
  int block_size_sum = 0;
  int block_size_sum_total = 0;  
  int block_alloc = 0;
  int block_size_alloc_sum = 0;
  int block_size_alloc_sum_total = 0;  
  int block_size_unalloc_sum = 0;  
  int block_size_unalloc_sum_total = 0;    
  int valid_nodes = 0;
  size_t chunk_size_sum = 0;
  size_t chunk_size_sum_total = 0;  
  int block_sum = 0;
  int blocks = 0;
  int chunks = 0;
  int block_sum_total = 0;  int chunk_sum = 0;
  int chunk_sum_total = 0;  

  void* bp = first_bp;


  if(!check_chunk_hdr(bp, 1, &chunk_size_sum, &valid_nodes, 0)) { return 0;}
  else{ chunk_size_sum_total += chunk_size_sum; chunks++; }

  while (GET_SIZE(HDRP(bp)) != 0 || in != 'w') { 
    printf("mm_check\n");
    if(!check_block_hdr(bp, 1, &block_size_sum, &block_alloc, 0 )) { return 0;}
    else{
           block_size_sum_total += block_size_sum;
           blocks++;
           if(block_alloc) 
            block_size_alloc_sum_total +=  block_size_alloc_sum;
           else
            block_size_unalloc_sum_total +=  block_size_unalloc_sum;       
    }


    if(0) scanf("%c", &in);
  }

  if(num_blocks == blocks)
    if(num_chunks == chunks)
      return 1;

//  scanf("%c", &in);
  */


  return 1;
}


static int mm_check1()
{

  int block_size_sum = 0;
  int block_size_sum_total = 0;  
  int block_alloc = 0;
  int block_size_alloc_sum = 0;
  int block_size_alloc_sum_total = 0;  
  int block_size_unalloc_sum = 0;  
  int block_size_unalloc_sum_total = 0;    
  int valid_nodes = 0;
  size_t chunk_size_sum = 0;
  size_t chunk_size_sum_total = 0;  
  int block_sum = 0;
  int blocks = 0;
  int chunks = 0;
  int block_sum_total = 0;  
  int chunk_sum = 0;
  int chunk_sum_total = 0;  

  void* bp = first_bp;

  int glob_num_blocks = num_blocks;
  int glob_num_chunks = num_chunks;

  if(!check_chunk_hdr(bp, 1, &chunk_size_sum, &valid_nodes, 0)) { return 0;}
  else{ chunk_size_sum_total += chunk_size_sum; chunks++; }

  while (GET_SIZE(HDRP(bp)) != 0) { 
    if(debug_on)printf("LOOPING mm_check while: BP SIZE:%zu, NUM MALLOC CALLS: %d\n", GET_SIZE(HDRP(bp)), num_malloc);

    if(!check_block_hdr(bp, 1, &block_size_sum, &block_alloc, debug_on)) { return 0;}
    else{
           block_size_sum_total += block_size_sum;
           blocks++;
           if(block_alloc) 
            block_size_alloc_sum_total +=  block_size_alloc_sum;
           else
            block_size_unalloc_sum_total +=  block_size_unalloc_sum;       
    }

    if(scan_on)scanf("%c", &in);
    bp = NEXT_BLKP(bp);

    if(debug_on) printf("NXT_BLKP SIZE: %zu, \tALLOC: %zu\n\n", GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));

  }

  if(tmp_num_blocks == blocks){  
    if(tmp_num_chunks_set == chunks)
      { if(debug_on) { printf("PASSED: NUM COUNTED BLOCKS = %d, \t NUM SET = %d  NUM  COUNTED CHUNKS: %d, \t NUM CHUNKS: %d\n", blocks, tmp_num_blocks, chunks, tmp_num_chunks_set);  dbg_data(); } if(scan_on) scanf("%c", &in); return 1;}
    else
       { if(debug_on) { printf("FAILED: NUM COUNTED BLOCKS = %d, \t NUM SET = %d  NUM COUNTED CHUNKS: %d, \t NUM CHUNKS: %d\n", blocks, tmp_num_blocks, chunks, tmp_num_chunks_set);  dbg_data(); } if(scan_on) scanf("%c", &in); return 1;}
  }else
      { if(debug_on) { printf("FAILED: NUM COUNTED BLOCKS = %d, \t NUM SET = %d  NUM  COUNTED CHUNKS: %d, \t NUM CHUNKS: %d\n", blocks, tmp_num_blocks, chunks, tmp_num_chunks_set);  dbg_data(); } if(scan_on) scanf("%c", &in); return 1;}
  //scanf("%c", &in);
  return 0;
}

/*
 * mm_check - Check whether freeing the given `p`, which means that
 *            calling mm_free(p) leaves the heap in an ok state.
 * 1 = valid, 0 = invalid
 */
int mm_can_free(void *p)
{
  if(enter_on) printf("mm_can_free: %d\n", ++num_can_free);   


  if(!block_mapped(p)){ if(debug_on && mm_dbg) printf("TRIED TO UNMAP ALREADY UNMAPPED: PTR:  %p\n", p ); return 0; }
  if(!ptr_is_mapped(NEXT_BLKP(p) -BLK_HDR_SZ, BLK_HDR_SZ)){ if(debug_on) {printf("UNMAPPED ADJ NEXT BLOCK  %p\n", p );  dbg_data();} return 0;}
  if(!ptr_is_mapped(PREV_BLKP(p) -BLK_HDR_SZ, BLK_HDR_SZ)){ if(debug_on) {printf("UNMAPPED ADJ PREV BLOCK  %p\n", p );  dbg_data();} return 0;}
  if(GET_SIZE(HDRP(p)) % 16 != 0 ) { if(debug_on && mm_dbg) printf("TRIED TO UNMAP UNNALIGNED PORTION  %p\n", p ); return 0; }
  if( GET_ALLOC(HDRP(p)) != 1 /*&& GET_ALLOC(FTRP(p)) != 1*/) { if(debug_on) {printf("TRID TO UNALLOC ALREADY UNALLOC  %p\n", p );  dbg_data();} return 0;}
//  if( GET_SIZE(HDRP(p)) != GET_SIZE(FTRP(p))) { if(debug_on) {printf("TRID TO UNALLOC ALREADY UNALLOC  %p\n", p );  dbg_data();} return 0;}
  if(GET_SIZE(HDRP(p)) == 0){ if(debug_on) {printf("TRIED TO FREE BLOCK SIZE )  %p\n", p );  dbg_data();} return 0;}

  return 1;
}

static int sum_blocks_chunks(void* p, int print_on)
{
  void* temp_bp = p;  
  size_t f_count = 0;

  while(GET_SIZE(HDRP(temp_bp)) != 0){
    f_count += GET_SIZE(HDRP(temp_bp));
    temp_bp = NEXT_BLKP(temp_bp);
    if(!ptr_is_mapped(temp_bp - BLK_HDR_SZ, BLK_HDR_SZ)) break;
  }

  temp_bp = PREV_BLKP(p);
  size_t r_count = 0;

  if(ptr_is_mapped(PREV_BLKP(p) - BLK_HDR_SZ, BLK_HDR_SZ))
  while(GET_SIZE(HDRP(temp_bp)) > 2*BLK_HDR_SZ){
    r_count += GET_SIZE(HDRP(temp_bp));
    temp_bp = PREV_BLKP(temp_bp);
    if(!ptr_is_mapped(temp_bp - BLK_HDR_SZ, BLK_HDR_SZ)) break;
  }

  size_t sum_block_sizes = r_count + f_count;
  size_t chunk_size  = 0;
  if(ptr_is_mapped(temp_bp -BLK_HDR_SZ, BLK_HDR_SZ))
  chunk_size = GET_ALLOC(temp_bp -BLK_HDR_SZ);
  
  if(sum_block_sizes + CHUNK_OVERHEAD != chunk_size) 
    { if(debug_on || print_on) {printf("CHUNK SIZE = %zu,  SUM BLOCKS + CHUNK_OVERHEAD = %zu", chunk_size, sum_block_sizes + CHUNK_OVERHEAD );  printf("Failed block sum:\n"); if(scan_on || 1) scanf("%c", &in);} return 0; }
  
  return 1;  

}

static int block_mapped1(void* p){

  if(!ptr_is_mapped(p , sizeof(block_header))) { printf("FAILED BLOCK IS MAPPED BP\n"); return 0; }
  if(!ptr_is_mapped(HDRP(p) , sizeof(block_header))) { printf("FAILED BLOCK IS MAPPED HDRP(BP)\n"); return 0; }  
  if(GET_SIZE(HDRP(p)) == 0){
    if(!ptr_is_mapped(HDRP(p), sizeof(block_header) )) { printf("FAILED BLOCK IS MAPPED WHOLE BLOCK, \n"); return 0; }
  }else{
    if(!ptr_is_mapped(HDRP(p), GET_SIZE(HDRP(p)))) { printf("FAILED BLOCK IS MAPPED WHOLE BLOCK, \n"); return 0; }
  }

  return 1;
}

static int block_mapped(void* p){

  if(!ptr_is_mapped(p, sizeof(block_header))) { printf("FAILED BLOCK IS MAPPED\n"); return 0; }
  if(!ptr_is_mapped(p, GET_SIZE(HDRP(p)))) { printf("FAILED BLOCK IS MAPPED, \n"); return 0; }
  return 1;
}

static int block_unequal(void* bp){
  int result = 1;
  if(!block_mapped(bp)) {result = 0;} 
  if(GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))) { printf("FAILED BLOCK IS EQUAL, SIZE\n"); dbg_data(); return 0; }
  if(GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))) { printf("FAILED BLOCK IS EQUAL, ALLOC\n"); dbg_data(); return 0; }    
  return result;
}

static int check_block_hdr(void* bp, int hdr_ftr, int* size_sum, int* alloc, int print_on){

  int x = hdr_ftr;
  *size_sum = 0;
  *alloc = 0;

  if(!ptr_is_mapped(bp, sizeof(block_header))) {printf("PRINT FAILED PTR UNMAPPED\n"); return 0; }

  if(print_on)
  printf("\n///  BLK_HDR  ///  PTR: %p\t\t\t OFF: %zu\t\t\t SIZE: %zu\t\t\t  ALLOC: %zu\n", 
  HDRP(bp),
  (size_t)HDRP(bp) - (size_t)first_bp,
  GET_SIZE(HDRP(bp)),
  GET_ALLOC(HDRP(bp))
  );

  if(!hdr_ftr) return;
  if(!ptr_is_mapped(HDRP(bp), GET_SIZE(HDRP(bp)))) {printf("PRINT FAILED PTR UNMAPPED\n"); return 0; }

  if(print_on)
  printf("///  BLK_FTR  ///  PTR: %p\t\t\t OFF: %zu\t\t\t SIZE: %zu\t\t\t  ALLOC: %zu\n", 
  FTRP(bp),
  (size_t)FTRP(bp) - (size_t)first_bp,
  GET_SIZE(FTRP(bp)),
  GET_ALLOC(FTRP(bp))
  );    

  if(GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))) {printf("FTR/HDR SIZE NOT EQUAl\n"); return 0; }
  if(GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))) {printf("FTR/HDR ALLOC NOT EQUAl\n"); return 0; }
  if((size_t)((FTRP(bp) + BLK_HDR_SZ ) - HDRP(bp)) != GET_SIZE(HDRP(bp))) {printf("OFFSET NOT EQUAL TO SIZE\n"); return 0; }

  *size_sum = GET_SIZE(HDRP(bp));
  *alloc = GET_ALLOC(HDRP(bp));

  return 1;
}

static int check_chunk_hdr(void* bp, int hdr_ftr, size_t* size_sum , int* valid_nodes, int print_on){

  int x = hdr_ftr; 
  *size_sum = 0;
  *valid_nodes = 0;

  void* node1 = (void*)bp - CHUNK_OVERHEAD;
  list_node* lnode1 = (list_node*)node1;

  //if( ((list_node*)node1)->next != NULL && ((list_node*)node1)->prev != NULL){
  if(!ptr_is_mapped(node1, SZ_LIST_NODE)) {printf("PRINT FAILED PTR NODE1 UNMAPPED\n"); return 0; }
  //if(!ptr_is_mapped(lnode1->next, SZ_LIST_NODE)) {printf("PRINT FAILED N1 PTR NXT UNMAPPED\n"); return 0; }  
  //if(!ptr_is_mapped(lnode1->prev, SZ_LIST_NODE)) {printf("PRINT FAILED N1 PTR PRV UNMAPPED\n"); return 0; }  
  //}

  void* node2 = (void*)bp - CHUNK_OVERHEAD + SZ_LIST_NODE;
  list_node* lnode2 = (list_node*)node1;

  //if(((list_node*)node2)->next != NULL && ((list_node*)node2)->prev != NULL){
  if(!ptr_is_mapped(node2, SZ_LIST_NODE)) {printf("PRINT FAILED PTR NODE1 UNMAPPED\n"); return 0; }
  //if(!ptr_is_mapped(lnode2->next, SZ_LIST_NODE)) {printf("PRINT FAILED N2 PTR NXT UNMAPPED\n"); return 0; }  
  //if(!ptr_is_mapped(lnode2->prev, SZ_LIST_NODE)) {printf("PRINT FAILED N2 PTR PRV UNMAPPED\n"); return 0; }  
  //}
  void* chunk_prolog_hdr = (void*)bp - (3*BLK_HDR_SZ);
  void* chunk_prolog_ftr = (void*)chunk_prolog_hdr + BLK_HDR_SZ;


  if(!ptr_is_mapped(chunk_prolog_hdr, sizeof(block_header))) {printf("PRINT FAILED PTR UNMAPPED\n"); return 0; }
  if(print_on)
  printf("\n///  CHUNK PRO HDR  ///  PTR: %p\t\t\t OFF: %zu\t\t\t SIZE: %zu\t\t\t  ALLOC: %zu\n", 
  (void*)bp - (3*BLK_HDR_SZ),
  (size_t)HDRP(bp) - (size_t)first_bp,
  GET_SIZE(HDRP(bp)),
  GET_ALLOC(HDRP(bp))
  ); 

  if(!ptr_is_mapped(chunk_prolog_hdr, 2*BLK_HDR_SZ)) {printf("PRINT FAILED PTR OF PROLOG FTR UNMAPPED\n"); return 0; }
  if(print_on)  
  printf("///  CHUNK PRO FTR  ///  PTR: %p\t\t\t OFF: %zu\t\t\t SIZE: %zu\t\t\t  ALLOC: %zu\n", 
  FTRP(bp),
  (size_t)FTRP(bp) - (size_t)first_bp,
  GET_SIZE(FTRP(bp)),
  GET_ALLOC(FTRP(bp))
  );    

  size_t len_from_hdr_to_terminator = GET_ALLOC(chunk_prolog_hdr)  - (3*BLK_HDR_SZ);
  void* chunk_terminator = (void*)chunk_prolog_hdr + len_from_hdr_to_terminator;

  if(!ptr_is_mapped( chunk_terminator, sizeof(block_header))) {printf("PRINT FAILED PTR OF TERMINATOR MAPPED\n"); return 0; }
  if(!ptr_is_mapped( (void*)bp - (5*BLK_HDR_SZ), GET_SIZE(chunk_prolog_hdr) )) {printf("PRINT FAILED CHUNK HDR to TERMINATOR FAILED MAPPED\n"); return 0; }

  if(print_on)  
  printf("///  CHUNK TERM FTR  ///  PTR: %p\t\t\t OFF: %zu\t\t\t SIZE: %zu\t\t\t  ALLOC: %zu\n", 
  (void*)chunk_terminator,
  (size_t)chunk_terminator - (size_t)first_bp,
  GET_SIZE(chunk_terminator),
  GET_ALLOC(chunk_terminator)
  );    

  if( GET_SIZE(chunk_prolog_hdr) != GET_SIZE(chunk_prolog_ftr)) {printf("FTR/HDR SIZE NOT EQUAl\n"); return 0; }
  if( GET_SIZE(chunk_prolog_hdr) != 2*BLK_HDR_SZ) {printf("FTR/HDR SIZE 2 EQUAl\n"); return 0; }  
  if( GET_ALLOC(chunk_prolog_hdr) != GET_ALLOC(chunk_prolog_ftr)) {printf("FTR/HDR ALLOC NOT EQUAl\n"); return 0; }
  if( GET_SIZE(chunk_terminator) != 0) {printf("TERM SIZE NOT 0\n"); return 0; }
  if( GET_ALLOC(chunk_terminator) != 1) {printf("TERM ALLOC NOT 1\n"); return 0; }

  *size_sum = GET_ALLOC(chunk_prolog_hdr);
  *valid_nodes = 1;

  return 1;

}


static void dbg_data()
{
  if(stack_on || 0)
    stack();
}

static void stack()
{
  printf("init: %d\t\t malloc: %d\t\t extend: %d\t\t set_alloc: %d\t\t set_chunk: %d\t\t  block_loop: %d\t\t chunk_loop: %d\t\t\n",num_init, num_malloc, num_extend, num_set_alloc, num_set_chunk, block_loop, chunk_loop);
}

static int ptr_is_mapped(void *p, size_t len) {
    void *s = ADDRESS_PAGE_START(p);
    return mem_is_mapped(s, PAGE_ALIGN((p + len) - s));
}

static size_t calc_offset(void* new_ptr){
  return (void*)new_ptr - ((void*)first_bp - CHUNK_OVERHEAD);
}