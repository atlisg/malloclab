/* 
 * mm.c -  Explicit free list, LIFO policy, and boundary tag coalescing. 
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
 * Each free block also has a nextlink and a prevlink and looks like this 
 * (next- and prevlink are 32-bit addressess pointing to the next and previous 
 * (respectively) free blocks in the free list):
 *
 *      -------------------------------------------------------
 *     |  header  | nextlink | prevlink |  padding  |  footer  |
 *      -------------------------------------------------------
 *
 * Padding can be of varying size depending on the block size itself.
 *
 * The heaplist has the following form:
 *
 * begin                                                           end
 * heap                                                           heap  
 *  -----------------------------------------------------------------
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(0:a) |
 *  -----------------------------------------------------------------
 *          |      prologue       |                       | epilogue |
 *          |        block        |                       |   block  |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 * +++++++++++++++++++++++++++++++
 *         Implementation:
 * +++++++++++++++++++++++++++++++
 *
 * The three main functions are mm_free, mm_malloc and mm_realloc,
 * they are implemented as described below.
 *
 * Free: When we are asked to free a block we set the block's header and footer
 * allocated bit to 0 and check if it can coalesce.
 *
 * Allocate: We find the best fitting free block of sufficient size with linear search.
 * If there is no match, we extend the heap just enough so we can fit it.
 *
 * ReAllocate: If we are decreasing the block's size we simply split the block into two iff
 * the remainder is big enough to be a block.
 * If we are increasing the block's size we first check if adjacent blocks are free and
 * of sufficient size for the block enlargement. If not, we allocate a new block, copy the data
 * and free the old block.
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

#define ALIGNMENT 8
#define WORD 4
#define OVERHEAD 16
#define HF_OVERHEAD 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
#define GET_SIZE(p)    (GET(p) & ~0x7)
#define GET_ALLOC(p)   (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WORD)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - ALIGNMENT)
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WORD)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - ALIGNMENT)))
/* Given block ptr bp, compute address of where it keeps it's next and prev address */
#define NEXT_LINK(bp)  ((char *)(bp))
#define PREV_LINK(bp)  ((char *)(bp) + WORD)
/* Given block ptr bp, compute address of next and previous block in the free list */
#define NEXT_OF(bp)    (GET(NEXT_LINK(bp)))
#define PREV_OF(bp)    (GET(PREV_LINK(bp)))

static char *heapBegin;
static char *heapEnd;
static char *freeBegin;

static void *extendHeap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
static void removeFree(void *wp);
static void insertFront(void *bp);
void mm_checkheap(int verbose);
size_t contains(void *bp);


/* 
 * Initialize the malloc package.
 */
int mm_init(void)
{
    if ((heapBegin = mem_sbrk(4 * (WORD))) == NULL) {
        return -1;
    }
    PUT(heapBegin, 0);                               /* Create padding */
    PUT(heapBegin + WORD, PACK(ALIGNMENT, 1));       /* Create prologue header */
    PUT(heapBegin + ALIGNMENT, PACK(ALIGNMENT, 1));  /* Create prologue footer */
    PUT(heapBegin + ALIGNMENT + WORD, PACK(0, 1));   /* Create epilogue header */
    heapBegin += ALIGNMENT;
    heapEnd = heapBegin;
    freeBegin = NULL;

    return 0;
}
/* 
 * Allocate a block from the freelist or extend heap to fit it.
 * Always allocate a block whose size is a multiple of the alignment.
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
    if (size <= ALIGNMENT)
        asize = ALIGNMENT + HF_OVERHEAD;
    else
        asize = ALIGNMENT * ((size + (HF_OVERHEAD) + (ALIGNMENT-1)) / ALIGNMENT);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    if (!GET_ALLOC(heapEnd))
    {
        /* last block is free, so extend heap just enough to be able to insert the new block */
        extendsize = asize - GET_SIZE(heapEnd);
    } else
        extendsize = asize;

    if ((bp = extendHeap(extendsize/WORD)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}
/*
 * Freeing a block does everything.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
    /* Jess ég er frír! */
}
/*
 * Reallocates the block to it's new size and returns a pointer to the block.
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

    /* ReAllocate the block pointed to by ptr (change the block size) */
    if (size <= ALIGNMENT)                  /* adjusting the size */
        newSize = ALIGNMENT + HF_OVERHEAD;
    else
        newSize = ALIGNMENT * ((size + (HF_OVERHEAD) + (ALIGNMENT-1)) / ALIGNMENT);

    if (newSize == oldSize) return ptr;
    if (newSize > oldSize) { 
        
        void *prevp = PREV_BLKP(ptr), *nextp = NEXT_BLKP(ptr);

        if ((GET_SIZE(HDRP(nextp)) + oldSize >= newSize) && !GET_ALLOC(HDRP(nextp))) {
            /* merging ptr block and the next one is big enough. */
            removeFree(nextp);
            PUT(HDRP(ptr), PACK((GET_SIZE(HDRP(nextp)) + oldSize), 1));
            PUT(FTRP(ptr), PACK((GET_SIZE(HDRP(nextp)) + oldSize), 1));
            place(ptr, newSize);
            return ptr;
        } else if ((GET_SIZE(HDRP(prevp)) + oldSize >= newSize) && !GET_ALLOC(HDRP(prevp))) {
            /* merging ptr block and the prev one is big enough. */
            removeFree(prevp);
            PUT(HDRP(prevp), PACK((GET_SIZE(HDRP(prevp)) + oldSize), 1));
            PUT(FTRP(prevp), PACK((GET_SIZE(HDRP(prevp)) + oldSize), 1));
            memcpy(prevp, ptr, oldSize);
            place(prevp, newSize);
            return prevp;
        } else if (((GET_SIZE(HDRP(prevp)) + GET_SIZE(HDRP(nextp)) + oldSize) >= newSize) && !GET_ALLOC(HDRP(prevp)) && !GET_ALLOC(HDRP(nextp))) {
            /* merging ptr block and both next and prev is big enough. */
            removeFree(prevp);
            removeFree(nextp);
            PUT(HDRP(prevp), PACK((GET_SIZE(HDRP(prevp)) + oldSize + GET_SIZE(HDRP(nextp))), 1));
            PUT(FTRP(prevp), PACK((GET_SIZE(HDRP(prevp)) + oldSize + GET_SIZE(HDRP(nextp))), 1));
            memcpy(prevp, ptr, oldSize);
            place(prevp, newSize);
            return prevp;
        } else {
            /* we will need to create a new block on the heap and free the old one */
            void *nptr;
            if ((nptr = mm_malloc(size)) == NULL) {
                printf("ERROR: mm_malloc failed in mm_realloc\n");
                exit(1);
            } else {
                memcpy(nptr, ptr, oldSize);
                mm_free(ptr);
                return nptr;
            }
        }

    } else {
        place(ptr, newSize);
    }
    return ptr;
}
/*
 * Extend heap with free block and return its block pointer
 */ 
static void *extendHeap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WORD : words * WORD;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(NEXT_LINK(bp), 0);                      /* nextlink points to NULL */
    PUT(PREV_LINK(bp), 0);                      /* prevlink points to NULL */
    PUT(HDRP(bp), PACK(size, 0));               /* free block header */
    PUT(FTRP(bp), PACK(size, 0));               /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       /* new epilogue header */
    heapEnd = FTRP(bp);                         /* put heapEnd to where it's supposed to be */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/*
 * Boundary tag coalescing. Return ptr to coalesced block
 */ 
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    void *wp = bp;

    if (prev_alloc && !next_alloc) {           /* Coalesce with block to the right */
        wp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(wp));
        removeFree(wp);
    }
    else if (!prev_alloc && next_alloc) {      /* Coalesce with block to the left */
     	wp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(wp));
        removeFree(wp);
        bp = wp;
    }
    else if (!prev_alloc && !next_alloc) {      /* Coalesce with both blocks  */
        wp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(wp));
        removeFree(wp);
        wp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(wp));
        removeFree(wp);
    	bp = wp;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    insertFront(bp);

    return bp;
}
/*
 * Inserts the free block at the front of the freelist.
 */ 
static void insertFront(void *bp) 
{
    if (freeBegin != NULL) {
    	PUT(bp, (size_t)freeBegin);
	PUT(PREV_LINK(freeBegin), (size_t)bp);
    } else {
    	PUT(NEXT_LINK(bp), 0);
    }
    PUT(PREV_LINK(bp), 0);
    freeBegin = bp;
}
/*
 * Removes the block from the freelist.
 */
static void removeFree(void *wp) 
{
    if (NEXT_OF(wp) == 0 && PREV_OF(wp) == 0) {
    	freeBegin = NULL;
    } else if (NEXT_OF(wp) == 0) {
    	PUT(NEXT_LINK((size_t*)PREV_OF(wp)), 0);
    } else if (PREV_OF(wp) == 0)  {
    	freeBegin = (void*)GET(wp);
    	PUT(PREV_LINK(freeBegin), 0);
    } else {
    	PUT(NEXT_LINK((size_t*)PREV_OF(wp)), NEXT_OF(wp));
    	PUT(PREV_LINK((size_t*)NEXT_OF(wp)), PREV_OF(wp));
    }
}
/*
 * Find best fit for a block with asize bytes 
 */
static void *find_fit(size_t asize) 
{
    /* best fit search */
    char *bp = freeBegin;
    void *bestBlock = NULL;
    size_t margin = 1 << 9, best = 1 << 31, diff;

    if (bp != NULL) {
        size_t running = 1;
        while (running) {
            if (NEXT_OF(bp) == 0) {
                running = 0;
            }
            if (asize <= GET_SIZE(HDRP(bp))) {
                diff = GET_SIZE(HDRP(bp)) - asize;
                if (best > diff) {
                    best = diff;
                    bestBlock = bp;
                }
                if (diff < margin)
                    return bp;
            }
            bp = (char*)NEXT_OF(bp);
        } 
    }
    return bestBlock;
}
/*
 * Place block of asize bytes at start of free block bp 
 * and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize) 
{
    size_t csize = GET_SIZE(HDRP(bp));
    /* remove bp from the freelist */
    if (!GET_ALLOC(HDRP(bp)))
        removeFree(bp);

    if ((csize - asize) >= (OVERHEAD)) { 
        /* splitting them */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        
        /* insert bp into freelist */
        insertFront(bp);
    }
    else { 
        /* not splitting, remainder too small */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/*
 * Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heapBegin;
    /* print heap */
    if (verbose)
        printf("Heap (%p):\n", heapBegin);

    if ((GET_SIZE(HDRP(heapBegin)) != ALIGNMENT) || !GET_ALLOC(HDRP(heapBegin)))
        printf("Bad prologue header\n");
    checkblock(heapBegin);

    for (bp = heapBegin; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        if (!GET_ALLOC(HDRP(bp)) && !GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
            printf("Error: Heap contains contiguous free blocks that somehow escaped coalescing!\n");
            exit(1);
        }
        if (!GET_ALLOC(HDRP(bp))) {
            if (!contains(bp)) {
                printf("Error: There exists a free block which is NOT in the freelist!\n");
                exit(1);
            }
        }
        checkblock(bp);
    }
     
    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

    /* print freelist */
    if (freeBegin != NULL) {
        bp = freeBegin;
        if (verbose) {
            printf("Free (%p):\n", freeBegin);
            size_t running = 1;
            while (running) {
                if (NEXT_OF(bp) == 0) 
                    running = 0;
                /* Is every block in the free list marked as free? */
                if (GET_ALLOC(HDRP(bp))) {
                    printf("Error: Allocated block in freelist!\n");
                    exit(1);
                }
                if ((NEXT_OF(bp) != 0 && !contains((void*)NEXT_OF(bp))) || (PREV_OF(bp) != 0 && !contains((void*)PREV_OF(bp)))) {
                    printf("Error: A link in a free block does not point to a valid free block!");
                    exit(1);
                }
                if (verbose)
                    printblock(bp);
                bp = (void*)NEXT_OF(bp);
            }
        }
    }

    
}
/*
 * Print block
 */
static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f')); 
}
/*
 * Check if block is obeying the rules
 */
static void checkblock(void *bp) 
{
    if ((size_t)bp % 8) {
        printf("Error: %p is not doubleword aligned\n", bp);
        exit(1);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: header does not match footer\n");
        exit(1);
    }
}

/*
 * Check if free block bp is in the freelist
 */
size_t contains(void *bp)
{
    void *curr = freeBegin;
    if (curr != NULL)
    {
        size_t running = 1;
        while (running) {
            if (NEXT_OF(curr) == 0)
                running = 0;
            if (curr == bp)
                return 1;

            curr = (void*)NEXT_OF(curr);
        }
    }
    return 0;
}

/*
-- INSERT --                                                                 */
