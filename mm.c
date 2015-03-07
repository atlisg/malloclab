/* 
 * mm.c -  Explicit free lists, LIFO policy, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. 
 *
 * Each free block also has a nextlink and a prevlink and looks like this (next- and prevlink are 32-bit addressess pointing to the next and previous (respectively) free blocks in the free list):
 *
 *      -------------------------------------------------------
 *     |  header  | nextlink | prevlink | padding   |  footer  |
 *      -------------------------------------------------------
 *
 * Padding can be of varying size depending on the block size itself.
 *
 * The list has the following form:
 *
 * begin                                                           end
 * heap                                                           heap  
 *  -----------------------------------------------------------------
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |      prologue       |                       | epilogue |
 *          |        block        |                       |   block  |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 * We plan to implement this like so:
 *
 * Initialize: Make padding, prologue and epilogue block, as well as making space for the allocating of blocks on the imaginary heap.
 *
 * Free: When we are asked to free a block we first check if the blocks next to it are free as well. 
 * If they are not, we simply free the block and put it at the front of our list.
 * If it has a free adjecent block, we first coalesce the two (or three) blocks and put the resulting block to the front of our list.
 * We also have to think about updating the links of the blocks that were previously pointing to the blocks being changed.
 *
 * Allocate: We find the first free block of matching size with linear search.
 * If there is no match, we find the first free block of matching size++ and so on.
 * If we have time, we will try to implement segregation list to make this a faster process.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <assert.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in below _AND_ in the
 * struct that follows.
 *
 * === User information ===
 * Group:  ::Hnífapar::
 * User 1: atlisg12
 * SSN:    0301803489
 * User 2: aegir13
 * SSN:    0507922699
 * === End User Information ===
 ********************************************************/
team_t team = {
    /* Group name */
    "::Hnífapar::",
    /* First member's full name */
    "Atli Sævar Guðmundsson",
    /* First member's email address */
    "atlisg12@ru.is",
    /* Second member's full name (leave blank if none) */
    "Ægir Már Jónsson",
    /* Second member's email address (leave blank if none) */
    "aegir13@ru.is",
    /* Leave blank */
    "",
    /* Leave blank */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALLIGNMENT 8
#define WORD 4
#define OVERHEAD 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WORD)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - ALLIGNMENT)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WORD)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - ALLIGNMENT)))

#define NEXT_LINK(bp)  ((char *)(bp))
#define PREV_LINK(bp)  ((char *)(bp) + WORD)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static char *heapBegin;
static char *freeBegin;

static void *extendHeap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
//static void printblock(void *bp); 
//static void checkblock(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heapBegin = mem_sbrk(4 * (WORD))) == NULL) {
        return -1;
    }
    PUT(heapBegin, 0);                               // Búa til padding
    PUT(heapBegin + WORD, PACK(OVERHEAD, 1));        // Búa til prologue header
    PUT(heapBegin + ALLIGNMENT, PACK(OVERHEAD, 1));  // Búa til prologue footer
    PUT(heapBegin + ALLIGNMENT + WORD, PACK(0, 1));  // Búa til epilogue header
    heapBegin += ALLIGNMENT;                         // látum heapBegin benda framhjá padding
    // búum til pláss fyrir blokkir
    if (extendHeap(CHUNKSIZE/WORD) == NULL) {
        return -1;
    }
    freeBegin = NEXT_BLKP(heapBegin);
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= ALLIGNMENT)
        asize = ALLIGNMENT + OVERHEAD;
    else
        asize = ALLIGNMENT * ((size + (OVERHEAD) + (ALLIGNMENT-1)) / ALLIGNMENT);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extendHeap(extendsize/WORD)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
    // Jess ég er frír!
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}
// Extend heap with free block and return its block pointer
static void *extendHeap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WORD : words * WORD;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));              /* free block header */
    PUT(FTRP(bp), PACK(size, 0));              /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));      /* new epilogue header */
    PUT(HDRP(bp) + WORD, NEXT_BLPT(bp));       // nextlink points to epilogue
    PUT(HDRP(bp) + ALLIGNMENT, PREV_BLPT(bp)); // prevlink points to prologue

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
// Boundary tag coalescing. Return ptr to coalesced block
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        // todo: Update freelist pointers

    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // todo: Update freelist pointers
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // todo: Update freelist pointers
    }

    return bp;
}
// Find a fit for a block with asize bytes 
static void *find_fit(size_t asize) {
    /* first fit search */
    void *bp;

    for (bp = freeBegin; GET_SIZE(HDRP(bp)) > 0; bp = *NEXT_LINK(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    // todo: make this best fit.
    return NULL; /* no fit */
}
// Place block of asize bytes at start of free block bp 
// and split if remainder would be at least minimum block size
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (ALLIGNMENT + OVERHEAD)) { 
        // update links of free blocks
        PUT(*PREV_LINK(bp), bp + asize);
        PUT(bp + asize, *bp);
        PUT(bp + asize + WORD, *PREV_LINK(bp));
        PUT(*(NEXT_LINK(bp) + WORD), bp + asize);  

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        // update links of freelees
        PUT(*PREV_LINK(bp), *NEXT_LINK(bp));
        PUT(PREV_LINK(*NEXT_LINK(bp)), *PREV_LINK(bp));
    }
}











