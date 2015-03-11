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

extern int verbose;

/* single word (4) or double word (8) alignment */
#define ALLIGNMENT 8
#define WORD 4
#define OVERHEAD 16
#define HF_OVERHEAD 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
#define GET_SIZE(p)    (GET(p) & ~0x7)
#define GET_ALLOC(p)   (GET(p) & 0x1)
#define GET_LAST(p)    (GET(p) & 0x2)

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
static void printblock(void *bp); 
static void checkblock(void *bp);
static void removeAdj(void *wp);
static void insertFront(void *bp);
void mm_checkheap(int verbose);


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heapBegin = mem_sbrk(4 * (WORD))) == NULL) {
        return -1;
    }
    PUT(heapBegin, 0);                               // Búa til padding
    PUT(heapBegin + WORD, PACK(ALLIGNMENT, 1));              // Búa til prologue header
    PUT(heapBegin + ALLIGNMENT, PACK(ALLIGNMENT, 1));        // Búa til prologue footer
    PUT(heapBegin + ALLIGNMENT + WORD, PACK(0, 1));  // Búa til epilogue header
    heapBegin += ALLIGNMENT;                         // látum heapBegin benda framhjá padding

    freeBegin = NULL;
    // búum til pláss fyrir blokkir
    if (extendHeap(CHUNKSIZE/WORD) == NULL) {
        // printf("extendHeap skilaði NULL\n");
        return -1;
    }

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // printf("About to allocate a block of size %d\n", size);
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= ALLIGNMENT)
        asize = ALLIGNMENT + HF_OVERHEAD;
    else
        asize = ALLIGNMENT * ((size + (HF_OVERHEAD) + (ALLIGNMENT-1)) / ALLIGNMENT);
    // printf("asize = %d\n", asize);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        // printf("er að fara að kalla á place með bp = %p og asize = %d", bp, asize);
        place(bp, asize);
        // printf("var að klára place með bp = %p og asize = %d\n", bp, asize);
        //mm_checkheap(verbose);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    // printf("Going to extend\n");
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extendHeap(extendsize/WORD)) == NULL)
        return NULL;
    place(bp, asize);
    //mm_checkheap(verbose);
    return bp;
}

/*
 * mm_free - Freeing a block does everything.
 */
void mm_free(void *ptr)
{
    // printf("Kemst í free");
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
    //mm_checkheap(verbose);
    // Jess ég er frír!
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (size == 0) {
        mm_free(ptr);
        return ptr;
    }
    if (ptr == NULL) {
        if ((ptr = mm_malloc(size)) == NULL) {
            printf("ERROR: mm_malloc failed in mm_realloc\n");
            exit(1);
        } else
            return ptr;
    }

    size_t oldSize = GET_SIZE(HDRP(ptr));
    size_t newSize;

    // ReAllocate the block pointed to by ptr (change the block size)
    if (size <= ALLIGNMENT) /*adjusting the size*/
        newSize = ALLIGNMENT + HF_OVERHEAD;
    else
        newSize = ALLIGNMENT * ((size + (HF_OVERHEAD) + (ALLIGNMENT-1)) / ALLIGNMENT);

    if (newSize == oldSize) return ptr;
    if (newSize > oldSize) { /*simply allocate a block of newSize and free the old one*/
        void *nptr = mm_malloc(size);
        if (nptr == NULL) {
            printf("ERROR: mm_malloc failed in mm_realloc\n");
            exit(1);
        } else {
            memcpy(nptr, ptr, oldSize);
            mm_free(ptr);
            return nptr;
        }
    } else {
        place(ptr, newSize);
    }

    return NULL;
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
    PUT(HDRP(bp), PACK(size, 2));               // free block header and set it as last
    PUT(FTRP(bp), PACK(size, 2));               // free block footer and set it as last
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       // new epilogue header
    PUT(NEXT_LINK(bp), 0);                      // nextlink points to NULL
    PUT(PREV_LINK(bp), 0);                      // prevlink points to NULL

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
// Boundary tag coalescing. Return ptr to coalesced block
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    void *wp = bp;

    if (prev_alloc && !next_alloc) {      /* Case 2 */
        wp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(wp));
        removeAdj(wp);
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
     	wp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(wp));
        removeAdj(wp);
        bp = wp;
    }
    else if (!prev_alloc && !next_alloc) {      /* Case 4 */
        wp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(wp));
        removeAdj(wp);
        wp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(wp));
        removeAdj(wp);
    	bp = wp;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    insertFront(bp);

    return bp;
}

// amazing
// static void *coalesce2() {
//     for (void *bp = freeBegin; GET(NEXT_LINK(bp)) != 0; bp = NEXT_OF(bp)) {
        
//     }

//     return NULL;
// }

// static void *findEdges(void *curr, size_t direction) {
//     if (!GET_ALLOC(HDRP(curr)))
//     {
//         if (GET(NEXT_LINK(curr)))
//         {
//             if (direction)
//                 return findEdges(NEXT_OF(curr), direction);
//             else
//                 return findEdges(PREV_OF(curr), direction);
//         } else {
//             return curr;
//         }
//     }
//     else {
//         if (direction)
//             return PREV_BLKP(curr);
//         else
//             return NEXT_BLKP(curr);
//     }
// }

static void insertFront(void *bp) {
    if (freeBegin != NULL) {
    	PUT(bp, (size_t)freeBegin);
	PUT(PREV_LINK(freeBegin), (size_t)bp);
    } else {
    	PUT(NEXT_LINK(bp), 0);
    }
    PUT(PREV_LINK(bp), 0);
    freeBegin = bp;
}

static void removeAdj(void *wp) {
    if (GET(NEXT_LINK(wp)) == 0 && GET(PREV_LINK(wp)) == 0) {
    	freeBegin = NULL;
    } else if (GET(NEXT_LINK(wp)) == 0) {
    	PUT(NEXT_LINK((size_t*)GET(PREV_LINK(wp))), 0);
    } else if (GET(PREV_LINK(wp)) == 0)  {
    	freeBegin = (void*)GET(wp);
    	PUT(PREV_LINK(freeBegin), 0);
    } else {
    	PUT(NEXT_LINK((size_t*)GET(PREV_LINK(wp))), (size_t)GET(NEXT_LINK(wp)));
    	PUT(PREV_LINK((size_t*)GET(NEXT_LINK(wp))), (size_t)GET(PREV_LINK(wp)));
    }
}
// Find a fit for a block with asize bytes 
static void *find_fit(size_t asize) {
    /* first fit search */
    char *bp = freeBegin;

    if (bp != NULL) {
        size_t running = 1;
        while (running) {
		if (GET(NEXT_LINK(bp)) == 0) {
                running = 0;
            }
            if (asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
            bp = (char*)GET(NEXT_LINK(bp));
        } 
    }
    // todo: make this best fit.
    return NULL; /* no fit */
}
// Place block of asize bytes at start of free block bp 
// and split if remainder would be at least minimum block size
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    // remove bp from the freelist
    if (!GET_ALLOC(HDRP(bp)))
        removeAdj(bp);

    if ((csize - asize) >= (OVERHEAD)) { 
        // splitting them
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        
        // insert bp into freelist
        insertFront(bp);
    }
    else { 
        // not splitting, remainder too small
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
// Check the heap for consistency 
void mm_checkheap(int verbose) 
{
    char *bp = heapBegin;
    // print heap
    if (verbose)
        printf("Heap (%p):\n", heapBegin);

    if ((GET_SIZE(HDRP(heapBegin)) != ALLIGNMENT) || !GET_ALLOC(HDRP(heapBegin)))
        printf("Bad prologue header\n");
    checkblock(heapBegin);

    for (bp = heapBegin; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }
     
    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

    // print freelist
    bp = freeBegin;
    if (verbose) {
        printf("Free (%p):\n", freeBegin);
        for (bp = freeBegin; GET(NEXT_LINK(bp)) != 0; bp = (char*)GET(NEXT_LINK(bp))) {
            printblock(bp);
        }
        printblock(bp);
    }
}
static void printblock(void *bp) 
{
    size_t hsize, halloc, hlast, fsize, falloc, flast;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    hlast = GET_LAST(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp)); 
    flast = GET_LAST(HDRP(bp)); 
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c:%c] footer: [%d:%c:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), (hlast ? 'l' : 'n'),
           fsize, (falloc ? 'a' : 'f'), (flast ? 'l' : 'n')); 
}
static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}










