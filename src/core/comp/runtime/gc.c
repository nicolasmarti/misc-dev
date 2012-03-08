#include<stdio.h>
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

// the segment are defined as an array of 2^n void* and align on 2^n
// this allow to optimize the computation of a segment address from a chunk address
uint segment_size_n;
typedef void** segment;

// in order to make sure that we are pointing to a segment, we create at initialization
// a magic number which will be place at the start of each segment
void* magic_number;

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

  - an array of void* of size nb_bulk*bulk_size

  - a buffer use as a stack for the tracing algorithm
    (we use for now an array of void* of size nb_bulk)

    Question: given bulk_size and the size of the segment, what is the number of bulk_size that can registered ?
  
 */


uint bitmap_size(uint nb_bulk)
{
  uint size = 0;
  uint curr_level = 0;
  uint curr_level_size = floor_div(nb_bulk, ptr_size_bit);

  for (; curr_level_size > 1; ++curr_level, curr_level_size = floor_div(curr_level_size, ptr_size_bit))
    {
      printf("sizeof(bitmap[%lu]) := %lu (<= %lu)\n", curr_level, curr_level_size, curr_level_size * ptr_size_bit);
      size += curr_level_size;  
    }
  
  printf("sizeof(bitmap[%lu]) := 1 (<= %lu)\n", curr_level+1, ptr_size_bit);

  return ++size;
}

// size of a segment in byte
uint segment_size(uint nb_bulk, uint bulk_size)
{
  return (
	  1 + // magic
	  2 + // next/prev
	  1 + // counter
	  bitmap_size(nb_bulk) + //bitmap
	  (nb_bulk * bulk_size) + // data
	  nb_bulk // stack
	  ) * sizeof(void*);

}

char gc_init(uint n){

  segment_size_n = n;

  printf("sizeof(void*) = 2^%lu\n", ptr_size_bit_pow2());

  uint nb_bulk = 200;
  uint bulk_size = 3;

  printf("sizeof(segment(%lu, %lu)) = %lu bytes\n", nb_bulk, bulk_size, segment_size(nb_bulk, bulk_size));

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
