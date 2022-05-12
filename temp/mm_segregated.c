#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <sys/mman.h>
#include <errno.h>
#include "mm.h"
#include "memlib.h"

/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 9: segregated free list ",
    /* First member's full name */
    "--",
    /* First member's email address */
    "--",
    /* Second member's full name (leave blank if none) */
    "",
    /* Third member's full name (leave blank if none) */
    ""};

/*------------------------------------------------------------------------------------------------------------------------------------------------------*/

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(HDRP(bp) - WSIZE))
#define MIN_BLK_SIZE (2*DSIZE)
static char *heap_listp;
static char* seg_listp;

/* explicit 추가 매크로 */
#define PRED_FREEP(bp) (*(void **)(bp))
#define SUCC_FREEP(bp) (*(void **)(bp + WSIZE))
// #define SUCC_FREEP(bp) (*(void **)(bp))


/* Forward Declaration */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void removeBlock(void *bp);
static void putFreeBlock(void *bp);
static void seg_init(void);
static void* seg_find(int size);


void seg_init(void){
	if ((seg_listp = mem_sbrk(32*WSIZE)) == (void*)-1) return;

	for (int i = 0; i < 32; i++){
		PUT(seg_listp + (i * WSIZE), (unsigned int)NULL);
	}
}

static void* seg_find(int size){
	static char* seg;

	int i = 0;
	for (i = 32; i > 0; i--){
		if((size & (1<<i)) > 0){
			break;
		}
	}
	seg = seg_listp + (i * WSIZE);
	return seg;
}


int mm_init(void)
{
	seg_init();

    if ((heap_listp = mem_sbrk(6 * WSIZE))== (void *)-1) return -1;
    PUT(heap_listp, 0);                                         //padding
    PUT(heap_listp + WSIZE, PACK(2 * DSIZE, 1));                // header of prologue
    PUT(heap_listp + 2 * WSIZE, (unsigned int)NULL);            // point at succesor
    PUT(heap_listp + 3 * WSIZE, (unsigned int)NULL);            // padding
    PUT(heap_listp + 4 * WSIZE, PACK(2 * DSIZE, 1));            // footer of prologue
    PUT(heap_listp + 5 * WSIZE, PACK(0, 1));                    // header of epilogue

    heap_listp += DSIZE;

    if (extend_heap(CHUNKSIZE / DSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words)
{
    size_t size;
    char *bp;

    size = words * DSIZE; 
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extend_size;
    void *bp;

    if (size <= 0)
        return NULL;

    asize = MAX(2 * DSIZE, ALIGN(size) + DSIZE);
    
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extend_size = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extend_size / DSIZE);
    if (bp == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void* find_fit(size_t asize)
{
	void* bp;
	static char* seg;

	int i = 0;
	for (i = 32; i > 0; i--){
		if ((asize & (1<<i)) > 0){
			break;
		}
	}

	int j = i;
	for(j = i; j <= 32; j++){
		seg = seg_listp + (j*WSIZE);
		if(GET(seg) != (unsigned int)NULL){         // exist free block
            // return PRED_FREEP(seg);
			for(bp = PRED_FREEP(seg); bp != NULL; bp = PRED_FREEP(bp)){
				if (asize <= GET_SIZE(HDRP(bp))){
					return bp;
				}
			}
		}
	}
    return NULL;

}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    removeBlock(bp);
    if (csize - asize >= MIN_BLK_SIZE)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        putFreeBlock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void removeBlock(void *bp)
{
	if(PRED_FREEP(bp) != NULL){
		PUT(PRED_FREEP(bp)+WSIZE, (unsigned int)SUCC_FREEP(bp));
	}
	if(SUCC_FREEP(bp) != NULL){
		PUT(SUCC_FREEP(bp), (unsigned int)PRED_FREEP(bp));
	}
}


void putFreeBlock(void* bp)
{
	char* seg;
	seg = seg_find(GET_SIZE(HDRP(bp)));

	if(PRED_FREEP(seg) != NULL){
		PUT(PRED_FREEP(seg)+WSIZE, (unsigned int)bp);
	}
	PUT(bp, (unsigned int)PRED_FREEP(seg));
	PUT(bp + WSIZE, (unsigned int)seg);
	PUT(seg, (unsigned int)bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        putFreeBlock(bp);
        return bp;
    }
    if (prev_alloc && !next_alloc)
    {
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else
    {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    putFreeBlock(bp);
    return bp;
}

void* mm_realloc(void* bp, size_t size)
{
	char* old_dp = bp;
	char* new_dp;

	size_t copySize;

		new_dp = mm_malloc(size);

		if (new_dp == NULL)
			return NULL;

		copySize = GET_SIZE(HDRP(old_dp));
		if (size < copySize)
			copySize = size;
		memcpy(new_dp, old_dp, copySize);

		mm_free(old_dp);

		return new_dp;
}
