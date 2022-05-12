/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * >> 묵시적 가용 리스트 Implicit
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 9",
    /* First member's full name */
    "--",
    /* First member's email address */
    " ~ @gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/** 기본 상수와 매크로 */
#define WSIZE 4             // word, header와 footer 사이즈
#define DSIZE 8             // double word
#define CHUNKSIZE (1<<12)   // 초기 가용 블록과 힙 확장을 위한 기본 크기
#define MINBLOCKSIZE 16     // 블록의 최소 사이즈 payload 8 + header 4 + footer 4

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))    // 크기와 할당 비트를 통합해서 header와 footer에 저장할 값을 리턴

#define GET(p) (*(unsigned int *)(p))               // 인자 p가 참조하는 워드를 읽어 반환
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // 인자 p가 가리키는 워드에 val을 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 블록의 header와 footer의 사이즈를 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) // 주소 p에 있는 블록의 header와 footer의 할당 비트를 리턴

// bp : block pointer
#define HDRP(bp) ((char *)(bp) - WSIZE)                                 // header를 가리키는 포인터를 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)            // footer를 가리키는 포인터를 리턴

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))   // 다음 블록의 bp를 리턴
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))   // 이전 블록의 bp를 리턴

/** 추가 선언 */
static void *heap_listp;
static void *next_fit;                      // for next fit 
static void *extend_heap(size_t words);     // 새 가용 블록으로 힙을 확장하는 함수
static void *coalesce(void *bp);            // 인접 가용 블록들을 연결하고 새 블록 포인트를 리턴하는 함수
static void *find_fit(size_t asize);        // 할당하고자하는 크기의 블록이 있는지 탐색하고 가능하면 할당 가능한 블록의 bp를 리턴
static void place(void *bp, size_t asize);  // bp에 asize 크기의 블록을 할당

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 빈 힙을 생성
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    
    PUT(heap_listp, 0);                             // alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // epilogue header
    heap_listp += (2*WSIZE);
    next_fit = heap_listp;

    // 빈 힙을 CHUNKSIZE의 가용 블록으로 확장
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

    return 0;
}

/** (추가 함수) 힙의 크기를 확장 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;   // 더블 워드 정렬 요구조건을 맞추기 위해 words(늘리고자 하는 크기)가 홀수이면 크기를 맞춰서 늘림
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;         // 확장에 실패한 경우 NULL 리턴

    PUT(HDRP(bp), PACK(size, 0));                               // free block header
    PUT(FTRP(bp), PACK(size, 0));                               // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                       // new epilogue header

    return coalesce(bp);                                        // 이전 블록이 가용하면 연결
}

/** (추가 함수) 인접 가용 블록들을 연결하고 새 블록 포인트를 리턴하는 함수 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) return bp;            // 경우 1
    else if (prev_alloc && !next_alloc) {               // 경우 2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {               // 경우 3
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {                                              // 경우 4
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    if ((next_fit > bp) && (char *)next_fit < NEXT_BLKP(bp)) {              // for next-fit
        next_fit = bp;                                              // 기존의 next-fit이 연결(경우 3, 4)로 인해 더 큰 가용 블럭으로 합쳐진 경우 보정
    }

    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;           // 할당할 블록 사이즈
    size_t extendsize;      // 할당할 사이즈가 없을 떄 늘릴 힙 사이즈
    char *bp;

    if (size == 0) return NULL;     // 이상한 할당 요청일 경우 NULL 리턴

    asize = MAX(ALIGN(size) + DSIZE, MINBLOCKSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;

    place(bp, asize);
    return bp;
}

/** (추가 함수) 할당하고자하는 크기의 블록이 있는지 탐색하고 가능하면 할당 가능한 블록의 bp를 리턴 */
static void *find_fit(size_t asize)
{
    void *bp = next_fit;
    for (next_fit = bp; GET_SIZE(HDRP(next_fit)) > 0; next_fit = NEXT_BLKP(next_fit)) {         // Next fit
        if (!GET_ALLOC(HDRP(next_fit)) && (asize <= GET_SIZE(HDRP(next_fit)))) {
            return next_fit;
        }
    }

    for (next_fit = heap_listp; next_fit < bp; next_fit = NEXT_BLKP(next_fit)) {
        if (!GET_ALLOC(HDRP(next_fit)) && (asize <= GET_SIZE(HDRP(next_fit)))) {
            return next_fit;
        }
    }

    // next_listp = heap_listp; // 탐색 불가시 제일 앞으로 초기화?
    return NULL;        // no fit
}

/** (추가 함수) bp에 asize 크기의 블록을 할당 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));  // 현재 bp의 블록의 사이즈

    if ((csize - asize) >= MINBLOCKSIZE) { // 최소 블록 사이즈보다 크면 분할
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));       // header의 할당 비트를 0으로 설정
    PUT(FTRP(ptr), PACK(size, 0));       // footer의 할당 비트를 0으로 설정
    coalesce(ptr);                       // 연결
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) return mm_malloc(size);                // bp가 null이면 새로 할당

    if (size == 0) {                                        // size가 0이면 free와 같음
        mm_free(ptr);
        return NULL;
    }

    size_t asize = ALIGN(size) + DSIZE;                     // 할당해줘야할 블록 크기
    size_t csize = GET_SIZE(HDRP(ptr));                     // 기존의 블록 크기

    if (asize == csize) return ptr;                         // 기존 블록 크기와 변경할 크기가 같으면 그냥 bp를 리턴

    void *bp = mm_malloc(asize);                            // 새로 할당할 크기로 할당
    size_t data_size = csize;                               // 데이터의 크기 (초기값: 기존의 블록 사이즈)

    if (asize < csize) data_size = asize;                   // 할당할 크기가 기존의 크기보다 작으면 데이터를 자름

    memcpy(bp, ptr, data_size);                             // 새로운 블록에 기존 데이터를 복사
    mm_free(ptr);                                           // 기존 블록을 반환
    return bp;
}
