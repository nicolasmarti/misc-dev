#include<stdio.h> //printf
#include<malloc.h> //memalign
#include<string.h> //memset
/*

   this is a memeory allocator / garbage collector
   based on 
   An Efficient Non-Moving Garbage Collector for Functional Languages (ICFP 2011)
   
   http://www.pllab.riec.tohoku.ac.jp/papers/icfp2011UenoOhoriOtomoAuthorVersion.pdf
   http://www.pllab.riec.tohoku.ac.jp/~katsu/slide-20110920.pdf


 */
typedef unsigned long uint;

// the size of pointers
#define ptr_size_byte (uint)(sizeof(void*))
#define ptr_size_bit (uint)(ptr_size_byte*8) // here we assert 8 bits per byte

// compute floor(log2(x))
uint floor_log2(uint x)
{
  uint r = 0;
  while (x >>= 1) // unroll for more speed...
    {
      r++;
    }
  return (r);
}

// compute the floor value of the division of x by y
uint floor_div(uint x, uint y){
  
  int z = x/y;
  if (x % y == 0)
    return z;
  else 
    return z+1;

}

uint ptr_size_bit_pow2(){

  uint res = floor_log2(ptr_size_bit);
  if(ptr_size_bit != (uint)(1) << res)
    //we assert that it is a proper power of two
    printf("catasrophic: ptr_size_bit is not a power of 2: %lu != 1 << %lu == %lu\n", ptr_size_bit, res, (uint)(1) << res);
  return res;

}

/***********************************************************************************************/
// the segment are defined as an array of 2^n void* and align on 2^n
// this allow to optimize the computation of a segment address from a chunk address
uint segment_size_n;
typedef void** segment;

// in order to make sure that we are pointing to a segment, we create at initialization
// a magic number which will be place at the start of each segment
void* magic_number;

// in order to check if a pointer is in a segment that we allocated we keep the min of all segment starting address, and the max of all segment last address
void* min_segment_start = (void*)(-1);
void* max_segment_end = (void*)(0);

// we have a global list of free segment
void* free_segment_start = NULL;
void* free_segment_end = NULL;

/*
  a segment contain <nb_bulk> elements of void*[<bulk_size>] is composed of

  - a magic number (size = sizeof(void*))
  
  - a pointer to the next segment (size = sizeof(void*))
  - a pointer to the previous segment (size = sizeof(void*))
  
  - a counter of the number of allocated elements (size = sizeof(void*))

  - a bitmap composed of
    (BM[0], ..., BM[L-1]) bitmaps where
    BM[0] is an array of void* of size floor(nb_bulk / ptr_size_bit) (one bit per bulk)
    and recursively BM[i+1] is an array of void* of size floor(size(BM[i]) / ptr_size_bit) (one bit per element on BM[i]

    Thus we can compute statically the max level L as L := floor(log_{ptr_size_bit}(nb_bulk))
    BM[i](j) is the j-th bit of BM[i]
    BM[i][j] is the j-th element of BM[i]

    this bitmap is used to store the information about allocated blocks

  - a bitmap similar to the previous one, keeping the root information

  - an array of void* of size nb_bulk*bulk_size

  - a buffer use as a stack for the tracing algorithm
    (we use for now an array of void* of size nb_bulk)

    Question: given bulk_size and the size of the segment, what is the number of bulk_size that can registered ?
  
 */

// bitmap_size in pointer
uint bitmap_size_elt(uint nb_bulk)
{
  uint size = 0;
  uint curr_level = 0;
  uint curr_level_size = floor_div(nb_bulk, ptr_size_bit);

  for (; curr_level_size > 1; ++curr_level, curr_level_size = floor_div(curr_level_size, ptr_size_bit))
    {
      //printf("sizeof(bitmap[%lu]) := %lu (<= %lu)\n", curr_level, curr_level_size, curr_level_size * ptr_size_bit);
      size += curr_level_size;  
    }
  
  //printf("sizeof(bitmap[%lu]) := 1 (<= %lu)\n", curr_level+1, ptr_size_bit);

  return ++size;
}

// size of a segment in byte
uint segment_size(uint nb_bulk, uint bulk_size)
{
  return (
	  1 + // magic
	  2 + // next/prev
	  1 + // counter
	  bitmap_size_elt(nb_bulk) + //bitmap for allocated bits
	  bitmap_size_elt(nb_bulk) + //bitmap for root bits
	  (nb_bulk * bulk_size) + // data
	  nb_bulk // stack
	  ) * ptr_size_byte;

}

// compute the nb_bulk max for a segment of max_size byte with bulk of bulk_size
uint nb_bulk_ub(uint max_size, uint bulk_size)
{
  // a first guess
  uint res = floor_div(max_size, bulk_size*ptr_size_byte);

  printf("init guess := %lu\n", res);
  
  // then we iterate to find the max number of bulk
  while (segment_size(res, bulk_size) > max_size)
    --res;

  return res;

}

// lookup the magic_number
void* get_magic_number (void* segment){
  return *(void**)(segment);
}

// mutate the magic_number
void set_magic_number (void* segment, void* magic){
  *(void**)(segment) = magic;
}

// lookup the previous segment pointer
void* get_segment_prev(void* segment){
  return *(void**)(segment + 1*ptr_size_byte);
}

// lookup the next segment pointer
void* get_segment_next(void* segment){
  return *(void**)(segment + 2*ptr_size_byte);
}

// mutate the previous segment pointer
void set_segment_prev(void* segment, void* prev){
  *(void**)(segment + 1*ptr_size_byte) = prev;
}

// mutate the next segment pointer
void set_segment_next(void* segment, void* next){
  *(void**)(segment + 2*ptr_size_byte) = next;
}

// lookup the counter
uint get_segment_counter(void* segment){
  return *(uint*)(segment + 3*ptr_size_byte);
}

//mutate the counter
void set_segment_counter(void* segment, uint counter){
  *(uint*)(segment + 3*ptr_size_byte) = counter;
}

// get pointer to the alloc bitmap
void* get_alloc_bitmap_ptr(void* segment)
{
  return (segment + 4*ptr_size_byte);
}

// get pointer to the root bitmap
void* get_root_bitmap_ptr(void* segment, uint nb_bulk)
{
  return (segment + (4 + bitmap_size_elt(nb_bulk))*ptr_size_byte);
}



// clear counter and alloc bitmap of a segment 
void clearABMandCount(void* segment, uint nb_bulk)
{
  memset(segment + 3*ptr_size_byte, // counter is at offset 3
	 0, // we put zeros
	 (1+bitmap_size_elt(nb_bulk))*ptr_size_byte // on an array of void* of the size of the bitmap + counter
	 );
}

// clear counter and alloc&root bitmap of a segment 
void clearARBMandCount(void* segment, uint nb_bulk)
{
  memset(segment + 3*ptr_size_byte, // counter is at offset 3
	 0, // we put zeros
	 (1+2*bitmap_size_elt(nb_bulk))*ptr_size_byte // on an array of void* of the size of the bitmap + counter
	 );
}

/* chaining of segments */

// for debugging
void print_list(void* start, void* end)
{
  printf("start := %p; ", start);
  printf("end := %p\n", end);
  while (start!=NULL)
    {
      void* segment = start;
      printf("%p <- %p -> %p\n", get_segment_prev(segment), segment, get_segment_next(segment));
      start = get_segment_next(segment);
    }

  printf("\n\n");

  return;
}

// inserting a segment at the end of a list
void insert_segment_end(void** start, void** end, void* segment)
{
  // if the list is empty start == end == null
  // thus we set both to segment and set next and prev of segment to nil
  if (*start == NULL){
    *start = segment;
    *end = segment;
    set_segment_prev(segment, NULL);
    set_segment_next(segment, NULL);
    return;
  }

  // else we set the next of segment to NULL,
  // prev, to the value of end
  // the next pointer of the previous segment to segment
  // and end to the segment
  set_segment_next(segment, NULL);
  set_segment_prev(segment, *end);
  set_segment_next(*end, segment);
  *end = segment;
  return;

}

// taking a segment at the begining of a list
void* take_segment_start(void** start, void** end)
{
  // if the list is empty start == end == null
  // thus we return NULL
  if (*start == NULL){
    return NULL;
  }

  // else we grab the value of start as or result,
  // we set it to the next of the grabbed segment,
  // if there is a segment at the head of the list, then we set its prev to NULL
  // else we set end at NULL
  void* res = *start;
  
  *start = get_segment_next(res);
  
  if (*start != NULL)
    set_segment_prev(*start, NULL);
  else
    *end = NULL;

  return res;
}


// allocate a new segment
void* alloc_segment(uint nb_bulk){

  // compute the desired size (which is also the alignment
  uint segment_size_ub = 1 << segment_size_n;

  // allocate
  void* segment = memalign(segment_size_ub, segment_size_ub);
  
  // update boundaries for segments address
  if (min_segment_start > segment) 
    min_segment_start = segment;

  if (max_segment_end < (segment + segment_size_ub)) 
    max_segment_end = (segment + segment_size_ub);

  // update the magic number
  set_magic_number(segment, magic_number);

  // clear counter and alloc/root bitmap
  clearARBMandCount(segment, nb_bulk);

  // 
  set_segment_prev(segment, NULL);
  set_segment_next(segment, NULL);

  // and finally put it in the free segment list
  insert_segment_end(&free_segment_start, &free_segment_end, segment);

  return segment;
}



/***********************************************************************************************/

char gc_init(uint n){

  segment_size_n = n;

  printf("sizeof(void*) = 2^%lu\n", ptr_size_bit_pow2());

  uint bulk_size = 3;

  uint segment_size_ub = 1 << segment_size_n;

  uint nb_bulk = nb_bulk_ub(segment_size_ub, bulk_size);

  printf("segment_size == %lu (>= %lu) /\\ bulk_size == %lu (sizeof == %lu) -> nb_bulk == %lu\n", 
	 segment_size_ub,
	 segment_size(nb_bulk, bulk_size),	 
	 bulk_size, 
	 bulk_size * ptr_size_byte, 
	 nb_bulk
	 );

  printf("(%p, %p)\n", min_segment_start, max_segment_end);

  print_list(free_segment_start, free_segment_end);
  alloc_segment(nb_bulk);
  alloc_segment(nb_bulk);
  alloc_segment(nb_bulk);
  alloc_segment(nb_bulk);
  alloc_segment(nb_bulk);
  alloc_segment(nb_bulk);
  alloc_segment(nb_bulk);
  print_list(free_segment_start, free_segment_end);
  take_segment_start(&free_segment_start, &free_segment_end);
  take_segment_start(&free_segment_start, &free_segment_end);
  take_segment_start(&free_segment_start, &free_segment_end);
  take_segment_start(&free_segment_start, &free_segment_end);
  print_list(free_segment_start, free_segment_end);
  take_segment_start(&free_segment_start, &free_segment_end);

  printf("(%p, %p)\n", min_segment_start, max_segment_end);

  return -1;
}

#define WITHMAIN

#ifdef WITHMAIN
int main(int argc, char** argv, char** arge)
{
  gc_init(12);
  
  return 0;
}
#endif
