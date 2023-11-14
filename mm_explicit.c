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
    "4",
    /* First member's full name */
    "Hyung Min Kim",
    /* First member's email address */
    "2018ds21112@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* PACK은 size와 alloc여부를 or연산하여 나타내줍니다*/
#define PACK(size, alloc) ((size) | (alloc))

/* GET과 PUT 은 각각 주소 p에 있는 값을 읽거나, 값을 저장해줍니다.*/
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* GET_SIZE, GET_ALLOC은 각각 p의 size와 할당여부비트를 가져옵니다*/
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* HDRP와 FTRP는 각각 헤더와 푸터를 가리키는 포인터를 리턴합니다.*/
#define HDRP(bp)    ((void *)(bp) - WSIZE)
#define SUCC(bp)    (*(void **)(bp))
#define PRED(bp)    (*(void **)(bp + WSIZE))
#define FTRP(bp)    ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*각각 다음 블록과 이전 블록에 해당하는 포인터를 리턴합니다.*/
#define NEXT_BLKP(bp)   ((void *)(bp) + GET_SIZE(((void *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((void *)(bp) - GET_SIZE(((void *)(bp) - DSIZE)))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 
 * mm_init - initialize the malloc package.
 */
static void *heap_listp =NULL;
static void *free_rootp =NULL;
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);



int mm_init(void)
{   
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); // 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE*2, 1)); // 프롤로그헤더 DSIZE*2 하는 이유는, 프롤로그에 SUC, PRE가 추가되기 때문.
    PUT(heap_listp + (2*WSIZE), NULL); //suc
    PUT(heap_listp + (3*WSIZE), NULL); //pre
    PUT(heap_listp + (4*WSIZE), PACK(DSIZE*2, 1)); // 프롤로그푸터
    PUT(heap_listp + (5*WSIZE), PACK(0,1));      // 에필로그 헤더

    free_rootp = heap_listp + 2*WSIZE;  // free_rootp는 프롤로그의 suc 주소임. (여기에 모든 가용리스트가 연결됨.)
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/*블록을 가용리스트로 연결해주는 과정*/
void unalloc_block(void *bp) {
    SUCC(bp) = free_rootp;
    PRED(bp) = NULL;
    
    PRED(free_rootp) = bp;
    free_rootp = bp;
}

/*블록을 가용리스트에서 해제해주는 과정*/
void alloc_block(void *bp) {
    if (bp == free_rootp) {
        free_rootp = SUCC(bp);
        PRED(free_rootp) = NULL;
    }
    else {
        SUCC(PRED(bp)) = SUCC(bp);
        PRED(SUCC(bp)) = PRED(bp);
    }
}

static void *extend_heap(size_t words) {
    void *bp;
    size_t size;
    /*alignment를 유지하기 위해*/
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /*프리블럭 헤더 푸터, 그리고  맨 마지막으로는 에필로그가 온다*/
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //에필로그를 맨뒤로 옮기는작업.
    
    /*이전 블록이 free이면 합체시킴*/
    return coalesce(bp);

}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        unalloc_block(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        alloc_block(NEXT_BLKP(bp)); 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        unalloc_block(bp);
    }

    else if (!prev_alloc && next_alloc) {
        alloc_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        unalloc_block(bp);
    }

    else {
        alloc_block(PREV_BLKP(bp));
        alloc_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        unalloc_block(bp);
    }
   
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   
    size_t asize;
    size_t extendsize;
    void *bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE) 
        asize = 2 * DSIZE;
    else
        asize = DSIZE *((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
   
    return bp;
   
}

static void *find_fit(size_t asize)
{   
    /* first-fit*/
    void *bp;
    for (bp = free_rootp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    alloc_block(bp); 
    
    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
                
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        unalloc_block(bp);
        
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize = GET_SIZE(HDRP(oldptr));
    size_t asize;
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    if (size == 0) {
        mm_free(oldptr);
        return NULL;
    }
    
    if (size <= DSIZE) 
        asize = 2 * DSIZE;
    else
        asize =  DSIZE *((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if (asize == copySize) {
        return oldptr;
    }
    // if (asize <= copySize) {   //realloc 개선도중 실패..
    //     //printf("asize = %d copysize = %d\n", asize, copySize);
    //     //place(oldptr, asize);
    //     //unalloc_block(oldptr);
    //     PUT(HDRP(oldptr), PACK(copySize, 1));
    //     PUT(FTRP(oldptr), PACK(copySize, 1));
    //     //alloc_block(oldptr);
    //     return oldptr;
    // }
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














