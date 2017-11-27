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
 size_t data;
} block_header;

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
#define GET_DATA(bp) ((block_header*)bp)->data
#define PUT(p, val) (*(size_t *)(p) = (val))
#define PACK(size, alloc) ((size) | (alloc))
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_SIZE(p) (GET(p) & ~0xF)
#define CNK_FTRP(bp) ((char *)(bp)+GET_DATA(bp)- sizeof(block_header))

#define CHUNK_SIZE (1 << 14)
#define CHUNK_ALIGN(size) (((size)+(CHUNK_SIZE-1)) & ~(CHUNK_SIZE-1))
#define CHUNK_OVERHEAD (sizeof(block_header) * 3)
#define BLK_HDR_SZ (sizeof(block_header))

/* rounds down to the nearest multiple of mem_pagesize() */
#define ADDRESS_PAGE_START(p) ((void *)(((size_t)p) & ~(mem_pagesize()-1)))  
int ptr_is_mapped(void *p, size_t len);

static void* extend(size_t new_size);
static int set_allocated(void *bp, size_t size, int blk_cntr);
static void* set_new_chunk(size_t new_size);
static unsigned long calc_offset(void* new_ptr);
static void print_chunk_info(void* bp, int debug_level, int from_beginning);
static void print_single_block(void* bp, int i);
static void* blk_bp_to_chnk_bp(void* bp, int debug_level_);
static int debugger();
static void print_single_chunk_info(void* bp, int debug_level_);


//PUT(p, PACK(48, 1));

/*
  TO DO
  1) extend
  2) set allocated
  3) basic mm_check
  4) basic can_free
  5) basic unmap
  6) 
*/

void *current_avail = NULL;
void* first_bp = NULL;
int current_avail_size = 0;
int current_alloc_capacity = 0;
int current_unalloc_capacity = 0;
int current_payload_capacity = 0;
int total_chunk_capacity = 0;
int extend_amt = 8;
char in = 0;
int num_mm_int = 0;
int num_set_chunk = 0;
int num_malloc = 0;
int num_extend = 0;
int num_set_alloc = 0;
int debug_enter = 1;
int debug_on = 1;
int num_blocks_alloc = 0;
int free_count = 0;
int debug_level = 1;


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  debug_enter = (debug_enter) == 1 && (debug_on == 1);

  num_mm_int = 0;
  num_set_chunk = 0;
  num_malloc = 0;
  num_extend = 0;
  num_set_alloc = 0;
  num_blocks_alloc = 0;
  free_count = 0;

  if(debug_enter) {printf("enter mm_init %d\n", ++num_mm_int);}
  // check heap, remove all allocations arb
  current_avail = NULL;
  current_avail_size = 0;
  // GET aligned initial size 
  size_t num_pages = 16;
  size_t chunk_bytes = PAGE_ALIGN(ALIGN(4096*10));

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
 // scanf("%c",&in);
  if(debug_enter) {printf("ENTER SET_NEW_CHUNK: %d\n", ++num_mm_int);}
  block_header* chunk_prolog_hdr = mem_map(new_size);

  //Place chunk header and prolog block, pack size and alloc, embed data specific to each blockgit
  PUT((void*)chunk_prolog_hdr, PACK(2*BLK_HDR_SZ, 1));
  GET_DATA(chunk_prolog_hdr) = new_size;             // REPRESENTS SIZE OF CHUNK

  //Place end of chunk ftr
  block_header* end_of_chunk_ftr = ((void*)chunk_prolog_hdr + new_size - sizeof(block_header));
  PUT((void*)end_of_chunk_ftr, PACK(0, 1));
  GET_DATA(end_of_chunk_ftr) = 0;

  //Place prolog ftr, pack size and alloc
  block_header* prolog_ftr = ((void*)chunk_prolog_hdr + sizeof(block_header));
  PUT((void*)prolog_ftr, PACK(2*BLK_HDR_SZ, 1));
  GET_DATA(end_of_chunk_ftr) = (size_t)first_bp;

  //Place first block header
  block_header* first_block = ((void*)chunk_prolog_hdr + (sizeof(block_header)*2));
  size_t size_first_block = new_size - CHUNK_OVERHEAD; 
  PUT((void*)first_block, PACK(size_first_block, 0));

  // Place first bp
  void* bp = HDRP(first_block);

  // Place first block footer
  block_header* first_block_footer = (block_header*)FTRP(bp);
  PUT((void*)first_block_footer, PACK(size_first_block, 0));

  current_avail_size = size_first_block - OVERHEAD;

  if(!ptr_is_mapped((void*)chunk_prolog_hdr, new_size)){
    printf("FAILED TO SET NEW CHUNK, WAS UNMAPPED,  PTR: %p  SIZE: %zu\n", chunk_prolog_hdr, new_size);
    print_chunk_info(bp, 1, 1); 

    mem_unmap((void*)chunk_prolog_hdr, new_size);
    if(ptr_is_mapped((void*)chunk_prolog_hdr, new_size )){ printf("FAILED TO UNMAP ERRONEOUS MAPPING,  PTR: %p  SIZE: %zu\n", chunk_prolog_hdr, new_size);}

    return NULL;
  }

  return bp;
}

/* 
 * mm_malloc - Allocate a block by using bytes from current_avail,
 *     grabbing a new page if necessary.
 */
void *mm_malloc(size_t size) {
   if(debug_enter) {printf("ENTER MALLOC:  %d\n", ++num_malloc);}  ;
 int new_size = ALIGN(size + OVERHEAD); int blk_cntr = 0;
 void *bp = first_bp;

      while (GET_SIZE(HDRP(bp)) != 0 && ptr_is_mapped(bp, GET_SIZE(HDRP(bp))) ) {  // WHILE HAVE NOT REACHED END OF CHUNK
         if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= new_size)) { 
           if(set_allocated(bp, new_size, blk_cntr)) 
           return bp;
           // Examine chunk
         }
         bp = NEXT_BLKP(bp);

      }

 print_chunk_info(bp, -1, 1);
 
 void* new_bp = extend(new_size); int stuck_counter = 0;
 while(new_bp == NULL){ new_bp = extend(new_size); if(stuck_counter++ >= 10){printf("EXTEND FAILING TO ALLOCATE NEW CHUNK, x to break\n"); scanf("%c", &in);} if(in == 'x') break; }
  

 GET_DATA(HDRP(bp)) = (size_t)new_bp;
  
 if(set_allocated(new_bp, new_size, 0))
  if(debug_on) {printf("Failed to set new chunk\n"); /*scanf("%c",&in);*/}

 return new_bp;

}

static int set_allocated(void *bp, size_t size, int blk_cntr) {
 if(debug_enter) {printf("ENTER SET_ALLLOC: %d\n", ++num_set_alloc);}    
 size_t extra_size = GET_SIZE(HDRP(bp)) - size;

 if(num_set_alloc == 209)
 printf("SIZE_REQUESTED%zu\n", size);
 //if(num_set_alloc == 1170) print_chunk_info(bp, -1, 1);

  if (extra_size > ALIGN(1 + OVERHEAD)) {  // SPLIT BLOCK
     if(!ptr_is_mapped(HDRP(bp), GET_SIZE( HDRP(bp) ))){ if(debug_on){printf("SET ALLOCATED SPLIT ALLOC UNAPPED\n");}
      print_single_block(bp, blk_cntr);  return 0;
     }

     PUT((void*) HDRP(bp), PACK(size, 0)); // SET ALLOC HDR SIZE/ALLOC
     PUT((void*) FTRP(bp), PACK(size, 0)); // SET ALLOC FTR SIZE/ALLOC  

     if(! ptr_is_mapped( HDRP(NEXT_BLKP(bp)) , GET_SIZE(HDRP(NEXT_BLKP(bp)) )) ){if(debug_on){printf("SET ALLOCATED SPLIT UNALLOC UNAPPED\n");}
      print_single_block(bp,blk_cntr);  return 0;
     }

     PUT((void*) HDRP(NEXT_BLKP(bp)), PACK(extra_size, 0)); // SET UNALLOC FTR SIZE/ALLOC
     PUT((void*) FTRP(NEXT_BLKP(bp)), PACK(extra_size, 0)); // SET UNALLOC FTR SIZE/ALLOC


     PUT((void*) HDRP(bp), PACK(size, 1)); // SET ALLOC HDR SIZE/ALLOC
     PUT((void*) FTRP(bp), PACK(size, 1)); // SET ALLOC FTR SIZE/ALLOC ALLOC HDR SIZE/ALLOC  
  }else{ // NO NEED TO SPLIT BLOCK

     if(!ptr_is_mapped(HDRP(bp), GET_SIZE( HDRP(bp) ))){ if(debug_on){printf("SET ALLOCATED SPLIT ALLOC UNAPPED\n");}
      print_single_block(bp, blk_cntr);  return 0;
     }

     PUT((void*) HDRP(bp), PACK(size, 1)); // SET ALLOC HDR SIZE/ALLOC
     PUT((void*) FTRP(bp), PACK(size, 1)); // SET ALLOC FTR SIZE/ALLOC

  }

 return 1;

}

/*
 * EXTENDS available space by aqcuiring new chunk
 */
static void* extend(size_t new_size) {
  if(debug_enter) {printf("ENTER EXTEND %d\n", ++num_extend);}  

  size_t chunk_size = CHUNK_ALIGN(new_size*extend_amt);
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

    PUT((void*)HDRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 0));
    PUT((void*)FTRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 0));
    free_count++;
    num_blocks_alloc--;    


  return;
}

/*
 * mm_check - Check whether the heap is ok, so that mm_malloc()
 *            and proper mm_free() calls won't crash.
 */
int mm_check()
{
  /*
    int is_mapped = ptr_is_mapped(p, GET_SIZE(HDRP(p))); 
  if(!is_mapped){printf("ATTEMPT TO FREE UNMAPPED MEM: %p\t SIZE: %zu\n", p, GET_SIZE(HDRP(p))); if(debug_on) {scanf("%c", &in); print_single_block(p, 0); } return 0; }

  int is_alloc = GET_ALLOC(HDRP(p)) && GET_ALLOC(FTRP(p));
  if(GET_SIZE(HDRP(p)) != GET_SIZE(FTRP(p))) {if(debug_on || 1)
  {printf("CANNOT FREE HDR/FTR WITH UNEQUAL SIZES\n"); print_chunk_info(p, 1) print_single_block(p, 666);} return 0;}

  if(!is_alloc) {printf("ATTEMPT TO FREE ALREADY FREE MEMORY: %p\t SIZE: %zu\n", p, GET_SIZE(HDRP(p))); if(debug_on) {scanf("%c", &in); print_single_block(p, 0); } return 0; }

  return 1;
  */

  return 1;
}

/*
 * mm_check - Check whether freeing the given `p`, which means that
 *            calling mm_free(p) leaves the heap in an ok state.
 * 1 = valid, 0 = invalid
 */
int mm_can_free(void *p)
{
  int is_mapped = ptr_is_mapped(p, GET_SIZE(HDRP(p))); 
  if(!is_mapped){printf("ATTEMPT TO FREE UNMAPPED MEM: %p\t SIZE: %zu\n", p, GET_SIZE(HDRP(p))); if(debug_on) {scanf("%c", &in); print_single_block(p, 0); } return 0; }

  int is_alloc = GET_ALLOC(HDRP(p)) && GET_ALLOC(FTRP(p));
  if(GET_SIZE(HDRP(p)) != GET_SIZE(FTRP(p))) 
  {if(debug_on || 1){printf("CANNOT FREE HDR/FTR WITH UNEQUAL SIZES\n"); print_chunk_info(p, -1, 1); /*print_single_block(p, 666); */} return 0; }

  if(!is_alloc) {printf("ATTEMPT TO FREE ALREADY FREE MEMORY: %p\t SIZE: %zu\n", p, GET_SIZE(HDRP(p))); if(debug_on) {scanf("%c", &in); print_single_block(p, 0); } return 0; }

  return 1;

}

static void print_single_block(void* bp, int i)
{
  if(!debug_on && i != 666  && i >= 0) {return;}
  if(i < 0) { i = i*(-1);}

  if(i == 666)
    printf("ENTERED print single from PTR/FTR size mismatch\n");
  
  char in;

  if(GET_SIZE(HDRP(bp)) != 0){
        printf("BLOCK HDR:\t ptr:%p\t\t\toff: %zu\t\t\t\tsize: %zu\t\t\talloc: %zu\t\t\tNUMBER IN CHUNK: %d\n", HDRP(bp), calc_offset(HDRP(bp)),GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)), i);

        block_header* ftr = (block_header*)FTRP(bp);
        printf("BLOCK FTR:\t ptr:%p\t\t\toff: %zu\t\t\tsize: %zu\t\t\talloc: %zu\t\t\tNUMBER IN CHUNK: %d\n", ftr, calc_offset(ftr),GET_SIZE(ftr), GET_ALLOC(ftr), i);
  
        printf("DIST IN BYTES HDR -> FTR: %zu\n\n\n", calc_offset(ftr) - calc_offset(HDRP(bp)) );
  }else{

        printf("BLOCK HDR:\t ptr:%p\t\t\toff: %zu\t\t\t\tsize: %zu\t\t\talloc: %zu\t\t\tNUMBER IN CHUNK: %d\n", HDRP(bp), calc_offset(HDRP(bp)),GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)), i);


        block_header* ftr = (block_header*)FTRP(bp);
        if(ptr_is_mapped(ftr, sizeof(block_header))){
        printf("BLOCK FTR:\t ptr:%p\t\t\toff: %zu\t\t\tsize: %zu\t\t\talloc: %zu\t\t\tNUMBER IN CHUNK: %d\n", ftr, calc_offset(ftr),GET_SIZE(ftr), GET_ALLOC(ftr), i);
  
        printf("DIST IN BYTES HDR -> FTR: %zu\n\n\n", calc_offset(ftr) - calc_offset(HDRP(bp)) );
        }else{
                  printf("BLOCK FTR IS UNMAPPED, MOST LIKELY TERMINATOR\n");
        }

  }
}


static void* blk_bp_to_chnk_bp(void* bp, int debug_level_)
{
    if(debug_enter){printf("ENTERED GET CHUNK HDR: \n");}
    scanf("%c", &in);

    printf("REVERSE @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");

    void* original_bp;
    int error_count = 0; int reverse_count = 0; int loop_count = 0;

    if(debug_level > 0)
      {print_single_block(bp, -1*(reverse_count + 1)); }

    if(GET_SIZE(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp) - sizeof(block_header)) != 0)  // IF BEGIN AT TERMINATOR BLOCK
      {  bp = bp - GET_SIZE(bp - OVERHEAD);  if(debug_level > 0){ print_single_block(bp, ++reverse_count); } }


    while(GET_SIZE(HDRP(bp)) != 2*BLK_HDR_SZ){

        if(debug_level_ > 0)
          printf("ENTERD WHILE : %d\n", ++loop_count);


        printf("ins 1\n");
        if(GET_SIZE(HDRP(bp)) == 0){
          printf("ERROR REVERSE CHUNK TRAVERSAL, REACHED BP SIZE:\n"); 
          print_single_block(bp, reverse_count);
        }

        printf("ins 2\n");
        if(error_count++ > 200000){ //DEBUG / ERROR CODE, ININITE LOOPING  
          printf("GET CHUNK HDR LOOPING: \tGET_SIZE((bp)) != 2*BLK_HDR_SZ,) ->  %zu  !=  %zu\nsee next = n, break = any key, decrement 3 bps = 3: ", GET_SIZE(HDRP(bp)), 2*BLK_HDR_SZ); 
          scanf("%c", &in);  
          if(in == 'b') {error_count = 0; break;} 
          else if( in == '3'){bp = NEXT_BLKP(HDRP(bp)); bp =  NEXT_BLKP(HDRP(bp)); bp = NEXT_BLKP(HDRP(bp)); bp =  NEXT_BLKP(HDRP(bp));}
        }


        printf("ins 3\n");
        if(ptr_is_mapped(bp - OVERHEAD, sizeof(block_header)) ){
          printf("ins 3.1\n");


          if(ptr_is_mapped(HDRP(PREV_BLKP(bp)) , sizeof(block_header))){ // CHECK IF PREV BLOCK, OR "NEXT BLOCK" IN REVERS TRAVERSAL IS MAPPED
          printf("ins 3.2\n");          


          if(ptr_is_mapped(HDRP(PREV_BLKP(bp)) , GET_SIZE(HDRP(PREV_BLKP(bp))))  ){ // CHECK IF PREV BLOCK, OR "NEXT BLOCK" IN REVERS TRAVERSAL IS MAPPED)
            printf("ins 3.3\n");          
              if( GET_SIZE(HDRP(PREV_BLKP(bp)) ) != GET_SIZE(bp - OVERHEAD)){ // SAFE TO DEREF, CHECK IF SIZES ARE EQUAL
                  printf("ERROR REVERSE CHUNK TRAVERSAL, SIZE MISMATCH ON NEXT BLOCK IN TRAVERSAL:\n");
                  print_single_block(bp, reverse_count);
              }
    
          }else{
            printf("ERROR REVERSE CHUNK TRAVERSAL, NEXT bp is unmapped: \n");
          }

        }else{
            printf("ERROR REVERSE CHUNK TRAVERSAL, ADJ FOOTER UNMAPPED \n");
        }


        printf("ins 4\n");
        if(debug_level_ > 0)
          printf("ENTERD WHILE : %d\n", ++loop_count);


        printf("ins 5 \n");
        bp = PREV_BLKP(bp);  if(debug_level_){ print_single_block(bp, ++reverse_count);}

      }
    }



    bp = bp + OVERHEAD;
    
    printf("END REVERSE @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    return bp;

}


static void print_chunk_info(void* bp, int debug_level_, int from_beginning)
{
  if(!debug_on && debug_level_ == 0 )
  return;
  
  //printf("////////////////////////////////////////////////////////////////////////////////\n\n");
  
  if(from_beginning){
     if(debug_level_){printf("ENTERED print chunk info WITH CHUNK INFO ON\n");}
     bp = blk_bp_to_chnk_bp(bp, debug_level_);

     printf("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n");

     void* chunk_hdr = bp - CHUNK_OVERHEAD;

     printf("CHUNK HDR:\t ptr:%p\t\t\toff: %zu\t\t\t\tsize: %zu\t\t\talloc: %zu\t\t\t CHUNK SIZE: %zu\n", 
       chunk_hdr,
       calc_offset(chunk_hdr),
       GET_SIZE(chunk_hdr), 
       GET_DATA(chunk_hdr),
       (size_t)0);


     void* chunk_ftr = CNK_FTRP(chunk_hdr); 
     printf("CHUNK HDR:\t ptr:%p\t\t\toff: %zu\t\t\t\tsize: %zu\t\t\talloc: %zu\t\t\t NEXT_CHUNK_PTR: %zu\n\n", 
       chunk_ftr,
       calc_offset(chunk_ftr),
       GET_SIZE(chunk_ftr),
       GET_ALLOC(chunk_ftr), 
       GET_DATA(chunk_ftr));


     size_t dist = calc_offset(chunk_ftr) - calc_offset(chunk_hdr );
     printf("DIST IN BYTES HDR -> FTR: %zu which is DIST + 16 = SIZE -> %zu  +  16  = %zu \n\n\n", dist , dist, GET_DATA(chunk_hdr) + (size_t)16);
  }

  if(debug_level_ != 0){printf("ENTERED print chunk info WITH CHUNK INFO OFF\n");}

  int i = 1;
  int loop = 0;


    while (GET_SIZE(HDRP(bp)) != 0) {  // WHILE HAVE NOT REACHED END OF CHUNK

        if(loop++ >= 200000){

          printf("looping !!!\n\n\n@@@@@@@@@@@@@@@@@@@@@@\n");
          scanf("%c", &in);
          break;
        }

        print_single_block(bp, i++);
        bp = NEXT_BLKP(bp);
    }
    
/*scanf("%c",&in);*/
    in = 'a';
    if(in == 'x')
      return;
    bp = (void*)GET_DATA(HDRP(bp));


}

static int debugger(){
  int i = 0;

  return i++;
}

int ptr_is_mapped(void *p, size_t len) {
    void *s = ADDRESS_PAGE_START(p);
    return mem_is_mapped(s, PAGE_ALIGN((p + len) - s));
}

static size_t calc_offset(void* new_ptr){
  return (void*)new_ptr - ((void*)first_bp - CHUNK_OVERHEAD);
}