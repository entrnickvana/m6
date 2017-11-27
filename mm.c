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
#define CNK_FTRP(bp) ((char *)(bp)+GET_ALLOC(bp)- (3*sizeof(block_header)))

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
static void print_block(void* bp, int hdr_ftr);


/*
  TO DO
  1) extend
  2) set allocated
  3) basic mm_check
  4) basic can_free
  5) basic unmap
  6) 
*/

int enter_on = 0;
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


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{

  enter_on = 1;
  stack_on = 0;
  num_init = 0;
  num_chunks = 0;
  num_extend = 0;
  num_free = 0;
  num_set_chunk = 0;
  num_can_free = 0;
  num_set_alloc = 0;

  void* current_avail = NULL;
  first_bp = NULL;

  if(enter_on)printf("mm_init: %d\n", ++num_init);
  current_avail_size = 0;

  size_t num_pages = 16;
  size_t num_bytes = mem_pagesize()*num_pages;
  size_t chunk_bytes = PAGE_ALIGN(num_bytes);

  first_bp = set_new_chunk(chunk_bytes);
  if(first_bp == NULL || ((size_t)first_bp) % 16 != 0){ // NOT ALIGNED
    if(debug_on) {printf("SET NEW CHUNK\n"); /*scanf("%c",&in);*/}
    return -1;
  }

  return 0; //arb
}


// chunk_capacity = sum all chunk sizes
// unalloc capacity = sum all unalloc blocks
// alloc capacity = sum all alloc blocks

// byte check = (sum all chunks - num_chunks*chunk_overhead) == (unalloc capacity + alloc capacity)
// 

static void* set_new_chunk(size_t new_size){
  if(enter_on)printf("SET NEW CHUNK: %d\n", ++num_set_chunk);
  void* base_ptr = mem_map(new_size);

  void* bp = (void*)base_ptr + (2*SZ_LIST_NODE) + (2*BLK_HDR_SZ) + (BLK_HDR_SZ);

  list_node* chk_node1 = (list_node*)base_ptr;
  list_node* chk_node2 = (list_node*)((void*)base_ptr + SZ_LIST_NODE);


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

  if(check_init){
  if(check_init) print_block((void*)chk_prolog_hdr + BLK_HDR_SZ, 1);
  if(check_init) print_block((void*)blk_hdr + BLK_HDR_SZ, 1);
  if(check_init) print_block((void*)chk_terminator + BLK_HDR_SZ, 0); 
  }
  scanf("%c", &in);

  return bp;
}

/* 
 * mm_malloc - Allocate a block by using bytes from current_avail,
 *     grabbing a new page if necessary.
 */
void *mm_malloc(size_t size) {
 if(enter_on)printf("MALLOC: %d\n", ++num_malloc);

 int new_size = ALIGN(size + OVERHEAD);
 void *bp = first_bp;
 while (GET_SIZE(HDRP(bp)) != 0) { 
    ++block_loop;
    if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= new_size)) {
      set_allocated(bp, new_size);
      return bp;
    }
   bp = NEXT_BLKP(bp);
 }

 extend(new_size);
 if(set_allocated(bp, new_size)) {printf("SET ALLOCATED FAILED:\n");}
 return bp;
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
  }

 if(!block_mapped(bp)) return 0;        

 GET_ALLOC(HDRP(bp)) = 1;
 GET_ALLOC(FTRP(bp)) = 1; 

 return 1;
}

/*
 * EXTENDS available space by aqcuiring new chunk
 */
static void* extend(size_t new_size) {
if(enter_on) printf("EXTEND: %d\n", ++num_extend);  
  size_t chunk_size = CHUNK_ALIGN(new_size);
  void *bp = set_new_chunk(chunk_size);
  if(bp == NULL)
      if(debug_on) {printf("EXTEND failed to init new chunk\n"); /*scanf("%c",&in);*/}
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if(enter_on) printf("mm_free: %d\n", ++num_free);    
    PUT((void*)HDRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 0));
    PUT((void*)FTRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 0));

  return;
}

/*
 * mm_check - Check whether the heap is ok, so that mm_malloc()
 *            and proper mm_free() calls won't crash.
 */
int mm_check()
{
  if(enter_on) printf("mm_check: %d\n", ++num_check);      
  return 1;
}

/*
 * mm_check - Check whether freeing the given `p`, which means that
 *            calling mm_free(p) leaves the heap in an ok state.
 * 1 = valid, 0 = invalid
 */
int mm_can_free(void *p)
{
  if(enter_on) printf("mm_can_free: %d\n", ++num_can_free);      
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

static void print_block(void* bp, int hdr_ftr){
  int print_terminator = 0;

  if(!ptr_is_mapped(bp, sizeof(block_header))) {printf("PRINT FAILED PTR UNMAPPED\n"); return; }
  if(GET_SIZE(HDRP(bp)) == 32)
  print_terminator = 1;

  printf("///  BLK_HDR  ///  PTR: %p\t\t\t OFF: %zu\t\t\t SIZE: %zu\t\t\t  ALLOC: %zu\n", 
  HDRP(bp),
  (size_t)HDRP(bp) - (size_t)first_bp,
  GET_SIZE(HDRP(bp)),
  GET_ALLOC(HDRP(bp))
  );



  if(!hdr_ftr) return;
  if(!ptr_is_mapped(bp, GET_SIZE(HDRP(bp)))) {printf("PRINT FAILED PTR UNMAPPED\n"); return; }

  if(GET_SIZE(FTRP(bp)) == 32 && ptr_is_mapped((void*)bp, (void*)bp + GET_ALLOC(HDRP(bp)) - (3*sizeof(block_header))){
    print_terminator++;  
  }

  printf("///  BLK_FTR  ///  PTR: %p\t\t\t OFF: %zu\t\t\t SIZE: %zu\t\t\t  ALLOC: %zu\n", 
  FTRP(bp),
  (size_t)FTRP(bp) - (size_t)first_bp,
  GET_SIZE(FTRP(bp)),
  GET_ALLOC(FTRP(bp))
  );    

  printf("DIST BETWEEN: %zu\n", GET_SIZE(FTRP(bp)) - GET_SIZE(HDRP(bp)) );

  if(print_terminator <= 1) {return;}

  printf("///  CHUNK_FTR  ///  PTR: %p\t\t\t OFF: %zu\t\t\t SIZE: %zu\t\t\t  ALLOC: %zu\n", 
  CNK_FTRP(bp),
  (size_t)CNK_FTRP() - (size_t)first_bp,
  GET_SIZE(CNK_FTRP(bp)),
  GET_ALLOC(CNK_FTRP(bp))
  );    

  printf("DIST BETWEEN: %zu\n", GET_SIZE(CNK_FTRP(bp)) - GET_SIZE(HDRP(bp)) );

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