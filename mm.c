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
 * Each free block also has a nextlink and a prevlink and looks like this:
 *
 *      -------------------------------------------------------
 *     |  header  | nextlink | prevlink | padding   |  footer  |
 *      -------------------------------------------------------
 *
 * Padding can be of varying size depending on the block size itself.
 *
 * The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  ---------------------------------------------------------------------------------------
 * |  pad   | hdr(8:a) | nextlink | ftr(8:a) | zero or more usr blks | hdr(8:a) | prevlink |
 *  ---------------------------------------------------------------------------------------
 *          |            prologue            |                       |      epilogue       |
 *          |              block             |                       |        block        |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 * We plan to implement this like so:
 *
 * Free: when we are asked to free a block we first check if the blocks next to it are free as well. 
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
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define PUT(p, val)  (*(size_t *)(p) = (val))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static char *heapBegin;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    assert((heapBegin = mem_sbrk(4 * (ALIGNMENT / 2))) != NULL);
    // Búa til padding
    // Búa til umgjörð á hýpinn
    // látum heapBegin benda framhjá padding
    // búum til pláss fyrir blokkir
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    //jess ég er frír!!!   
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
