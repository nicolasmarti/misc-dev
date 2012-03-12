#include<stdio.h> //printf
#include<malloc.h> //memalign
#include<string.h> //memset
#include<stdbool.h> // bool, true, false
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

uint cell_log_n2(uint x, uint y)
{
  uint r = 1;
  while (x >>= y) // unroll for more speed...
    {
      r++;
    }
  return (r);
}

// compute the floor value of the division of x by y
uint cell_div(uint x, uint y){
  
  int z = x/y;
  if (x % y == 0)
    return z;
  else 
    return z+1;

}

uint ptr_size_bit_pow2;

uint cell_div_ptr_size_bit(uint x)
{
  uint y = x >> ptr_size_bit_pow2;
  
  if (x > y << ptr_size_bit_pow2)
    ++y;

  return y;
 
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

// the max level for a given number of bulk
uint max_level(uint nb_bulk)
{
  return cell_log_n2(nb_bulk, ptr_size_bit_pow2);
}


// bitmap_size in pointer
uint bitmap_size_elt(uint nb_bulk)
{
  uint size = 0;
  uint curr_level = 0;
  uint curr_level_size = cell_div_ptr_size_bit(nb_bulk);

  for (; curr_level_size > 1; 
       ++curr_level, 
	 curr_level_size = cell_div_ptr_size_bit(curr_level_size)
       )
    {
      //printf("sizeof(bitmap[%lu]) := %lu (<= %lu)\n", curr_level, curr_level_size, curr_level_size * ptr_size_bit);
      size += curr_level_size;  
    }

  if (curr_level+1 != max_level(nb_bulk))
    printf("cell_log_n2(...) := %lu <> %lu\n", cell_log_n2(nb_bulk, ptr_size_bit_pow2), curr_level+1);

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
  uint res = cell_div(max_size, bulk_size*ptr_size_byte);

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

// increment the segment counter
void inc_segment_counter(void* segment){
  uint* counter = (uint*)(segment + 3*ptr_size_byte);
  *counter = *counter + 1;
}

// decrement the segment counter
void dec_segment_counter(void* segment){
  uint* counter = (uint*)(segment + 3*ptr_size_byte);
  *counter = *counter - 1;
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

// get a pointer to the data
void* get_bulk_ptr(void* segment, uint nb_bulk)
{
  return (segment + (
		     4 + 
		     bitmap_size_elt(nb_bulk) * 2
		     ) * ptr_size_byte
	  );

}

// from the starting address of a bitmap (given a nb_bulk), return the address of the level l bitmap
void* get_level_bitmap_ptr(void* bitmap_ptr, uint nb_bulk, uint level){
  
  uint offset = 0;
  uint curr_level = 0;
  uint curr_level_size = cell_div_ptr_size_bit(nb_bulk);

  for (; curr_level_size < level; 
       ++curr_level, 
	 curr_level_size = cell_div_ptr_size_bit(curr_level_size))
    {
      offset += curr_level_size;  
    }
  
  //printf("sizeof(bitmap[%lu]) := 1 (<= %lu)\n", curr_level+1, ptr_size_bit);

  return bitmap_ptr + offset*ptr_size_byte; 

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

//***************************************************************
// bit pointers
typedef uint bm_index;
typedef uint bm_mask;
typedef uint bm_level;

//increment a bitpointer
void inc_bitptr(bm_index* index, bm_mask* mask)
{
  // we shift the mask
  *mask <<= 1;

  // if it becomes 0 then we increase the index and reset the mask
  if (*mask == 0)
    {
      ++(*index);
      *mask = 1;
    }

  return;
}

//convert a bit index to a bit pointer
void indexToBitPtr(bm_index i, bm_index* index, bm_mask* mask)
{
  *index = i / ptr_size_bit;
  *mask = 1 << (i % ptr_size_bit);
}

//convert a bitptr to a bit index
bm_index bitPtrToIndex(bm_index index, bm_mask mask)
{
  return index * ptr_size_bit + (floor_log2(mask) - 1);
}

// convert a bitptr to a bulk address
void* blockAddress(void* data_ptr, bm_index index, bm_mask mask, uint bulk_size){

  return data_ptr + bitPtrToIndex(index, mask)*bulk_size*ptr_size_byte;

}

// give the size of element of a given level (correspond to the max index)
bm_index get_level_max_index(uint nb_bulk, uint level){
  
  uint curr_level = 0;
  uint curr_level_size = cell_div_ptr_size_bit(nb_bulk);

  for (; curr_level_size < level; 
       ++curr_level 
       )
    {
      curr_level_size = cell_div_ptr_size_bit(curr_level_size);
    }
  
  //printf("sizeof(bitmap[%lu]) := 1 (<= %lu)\n", curr_level+1, ptr_size_bit);

  return --curr_level_size; 

}

// give the maximal mask for the last index of a given level
bm_mask get_level_max_mask(uint nb_bulk, uint level){
  
  uint level_max_index = get_level_max_index(nb_bulk, level);
  uint max_bulk_num = ptr_size_bit * level_max_index;
  uint i;
  for (i = 0; i < level; ++i) 
    max_bulk_num *= ptr_size_bit;

  return 1 << ptr_size_bit - (max_bulk_num - nb_bulk);
}

// test if the bitptr for level i is set or not
uint isMarked(void* level_bitmap_ptr, bm_index index, bm_mask mask)
{
  return mask & *(uint*)(level_bitmap_ptr + index*ptr_size_byte);

}

//return the next mask
bm_mask nextMask(void* bitmap_ptr, bm_index index, bm_mask mask, uint level, uint nb_bulk)
{
  // overflow of index
  uint level_max_index = get_level_max_index(nb_bulk, level);
  if (index > level_max_index) return 0;
  uint max_index_max_mask = get_level_max_mask(nb_bulk, level);

  void* level_bitmap_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);

  // here we split the cases on the fact or not that we are on the max
  if (index == level_max_index){

    uint is_marked;
    // loop while
    while (mask && // the mask is not 0 and
	   mask < max_index_max_mask && // we are lower or equal to the max mask and
	   (is_marked = isMarked(level_bitmap_ptr, index, mask)) // the current bit is marked
	   )
      // we increment the mask
      mask <<= 1;
    
    // if it is marked, we set the mask to 0
    if (is_marked) mask = 0;
    
  } else {

    // same as before, except that we do not test for the max mask
    uint is_marked;
    // loop while
    while (mask && // the mask is not 0 and
	   (is_marked = isMarked(level_bitmap_ptr, index, mask)) // the current bit is marked
	   )
      // we increment the mask
      mask <<= 1;
    
    // if it is marked, we set the mask to 0
    if (is_marked) mask = 0;

  }
   
  // we return the mask
  return mask;
}

// setBitAnd: set a bit, and update the upper level w.r.t. a bitwise andif all bits are to one
void setBitAnd(void* bitmap_ptr, bm_index index, bm_mask mask, uint nb_bulk, uint level)
{
  // grab the bitmap pointer of the level
  void* bitmap_level_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);
  
  // grab the corresponding bitmap of the index
  uint bm = *(uint*)(bitmap_level_ptr + index*ptr_size_byte);

  // compute and and with the mask and store
  bm |= mask;

  *(uint*)(bitmap_level_ptr + index*ptr_size_byte) = bm;

  // update upper map if necessary
  if (level + 1 < max_level(nb_bulk) && bm == ~0)
    {
      bm_index i = index;
      indexToBitPtr(i, &index, &mask);
      setBitAnd(bitmap_ptr, index, mask, nb_bulk, level+1);
    }

  return;
}

// setBitOr: set a bit, and update the upper level w.r.t. a bitwise andif at least one bit is one
void setBitOr(void* bitmap_ptr, bm_index index, bm_mask mask, uint nb_bulk, uint level)
{
  // grab the bitmap pointer of the level
  void* bitmap_level_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);
  
  // grab the corresponding bitmap of the index
  uint bm = *(uint*)(bitmap_level_ptr + index*ptr_size_byte);

  // compute and and with the mask and store
  bm |= mask;
  *(uint*)(bitmap_level_ptr + index*ptr_size_byte) = bm;

  // update upper map if necessary
  bm_index i = index;
  indexToBitPtr(i, &index, &mask);
  setBitOr(bitmap_ptr, index, mask, nb_bulk, level+1);
  
  return;
}

// forwardBitPtr: forward the bitptr, until it points to a valid unset bit
void forwardBitPtr(void* bitmap_ptr, bm_index *index, bm_mask *mask, uint nb_bulk, uint level)
{
  // we return false, if we are beyond the proper number of level
  if (level + 1 >= max_level(nb_bulk))
    {
      *mask = 0;
      return;
    }

  bm_mask next_mask;
  bm_index next_index;

  // compute the index in the upper level
  indexToBitPtr(*index, &next_index, &next_mask);

  // look for the next mask
  next_mask = nextMask(bitmap_ptr, next_index, next_mask, level+1, nb_bulk);

  // in case we fail => try to look at upper lovel
  if (next_mask == 0)
    {
      forwardBitPtr(bitmap_ptr, &next_index, &next_mask, nb_bulk, level+1);
      if (next_mask == 0)
	{
	  *mask = 0;
	  return;
	}
    }

  // we have or info in next_xxx
  *index = bitPtrToIndex(next_index, next_mask);
  *mask = nextMask(bitmap_ptr, *index, 1, level, nb_bulk);
  return;
}

// findNextFreeBlock: look for the next available free block
void findNextFreeBlock(void* bitmap_ptr, bm_index *index, bm_mask *mask, uint nb_bulk, uint level)
{
  *mask = nextMask(bitmap_ptr, *index, *mask, level, nb_bulk);

  if (*mask == 0)
    {
      forwardBitPtr(bitmap_ptr, index, mask, nb_bulk, level);
      if (*mask == 0)
	  return;
    }
  
  return;
}

// getBulkBitPtr: from a bulk address, get the 

// alloc in a segment
void* allocSegment(void* segment, bm_index *index, bm_mask *mask, uint nb_bulk, uint bulk_size, bool root)
{
  // we grab the bitmap pointer
  void* bitmap_ptr = get_alloc_bitmap_ptr(segment);
  
  // check that the bit pointer is valid, else return NULL
  uint level_max_index = get_level_max_index(nb_bulk, 0);
  if (*index > level_max_index) return NULL;
  uint max_index_max_mask = get_level_max_mask(nb_bulk, 0);
  if (*index >= level_max_index && *mask >= max_index_max_mask) return NULL;  

  // test if the current pointed bit is marked
  if (isMarked(bitmap_ptr, *index, *mask))
    {
      // yes, let's find the next free block
      findNextFreeBlock(bitmap_ptr, index, mask, nb_bulk, 0);
      
      // if there is none, return NULL
      if (*mask == 0)
	return NULL;
    }
  
  // grab the data pointer
  void* data_ptr = get_bulk_ptr(segment, nb_bulk);

  // compute the allocated block index
  void* block = blockAddress(data_ptr, *index, *mask, bulk_size);

  // update the root bitmap if necessary
  if (root)
    {
      void* root_bitmap_ptr = get_root_bitmap_ptr(segment, nb_bulk);
      setBitOr(root_bitmap_ptr, *index, *mask, nb_bulk, 0);
    }
  // update the alloc bitmap
  setBitAnd(bitmap_ptr, *index, *mask, nb_bulk, 0);

  // increment the counter
  inc_segment_counter(segment);

  // increment the bit pointer
  inc_bitptr(index, mask);

  // we found the next free block, pointed by index/mask
  return block;

}

//***************************************************************
const char *byte_to_binary
(
    uint x
)
{
    static char b[33];
    b[0] = '\0';

    uint z;
    for (z = 1; z > 0; z <<= 1)
    {
        strcat(b, ((x & z) == z) ? "1" : "0");
    }

    return b;
}

// print bitmap
void print_bitmap(void* bitmap_ptr, uint nb_bulk)
{
  uint level; 
  for (level = 0; level < max_level(nb_bulk); ++level)
    {
      printf("level: %lu\n", level);
      uint index;
      void* level_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);
      for (index = 0; index <= get_level_max_index(nb_bulk, level); ++index)
	printf("bm[%lu] := %s\n", level, byte_to_binary(*(uint*)(level_ptr + index*ptr_size_byte)));

    }
  return;
}


//***************************************************************


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

  ptr_size_bit_pow2 = floor_log2(ptr_size_bit);

  if(sizeof(void*) != sizeof(uint)) {
    //we assert that it is a proper power of two
    printf("catasrophic: uint and void* are of different size !!!");
    return 0;
  }

  if(ptr_size_bit != (uint)(1) << ptr_size_bit_pow2) {
    //we assert that it is a proper power of two
    printf("catasrophic: ptr_size_bit is not a power of 2: %lu != 1 << %lu == %lu\n", ptr_size_bit, ptr_size_bit_pow2, (uint)(1) << ptr_size_bit_pow2);
    return 0;
  }


  segment_size_n = n;

  printf("sizeof(void*) = 2^%lu\n", ptr_size_bit_pow2);

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

  /*
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
  */


  void* segment = alloc_segment(nb_bulk);  

  printf("segment: %p <--> %p\n", segment, segment + (1 << segment_size_n));

  void* alloc_ptr = get_alloc_bitmap_ptr(segment);

  printf("alloc_bitmap_ptr = %p\n", alloc_ptr);

  bm_index index = 0;
  bm_mask mask = 1;
  void* alloc = (void*)(1);
  uint count = 0;
  while (alloc != NULL)
    {
      print_bitmap(alloc_ptr, nb_bulk);
      alloc = allocSegment(segment, &index, &mask, nb_bulk, bulk_size, false);
      ++count;
      printf("alloc(%lu/%lu): %p\n", count, nb_bulk, alloc);
    }

  print_bitmap(get_alloc_bitmap_ptr(segment), nb_bulk);

  print_bitmap(alloc_ptr, nb_bulk);
  index = 0;
  mask = 1;
  alloc = allocSegment(segment, &index, &mask, nb_bulk, bulk_size, false);
  ++count;
  printf("alloc(%lu/%lu): %p\n", count, nb_bulk, alloc);

  /*
  uint i;
  for (i = 0; i < 10000; ++i)
    {
      if (cell_div(i, ptr_size_bit) != cell_div_ptr_size_bit(i))
	printf("%lu != %lu\n", cell_div(i, ptr_size_bit), cell_div_ptr_size_bit(i));
	
    }
  */

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
