/*
 * mm.c
 *
 * Name: Brian Klammer
 *
 * Implemented using a segregated free list consisting of 15 individual free lists for various payload sizes.
 * Each free list is a doubly linked-list.
 * 
 * Each block has an 8-byte header where the first bit is the free/alloc indicator (1 for alloc)
 * and the second bit is the previous block free/alloc indicator (1 for alloc).
 * Payload size (not including header size) is also stored in the header.
 * 
 * Only free blocks have footers. When a block is free, the last 8-bytes of the payload become the footer.
 * Footer also stores payload size and free/alloc indicator
 * In order to maintain 16-byte aligned payloads, the allowed payload sizes are 24, 40, 56, 72,... bytes.
 * Minimum payload size is 24 bytes to allow room for next/prev free block pointers.
 * 
 * The next/prev free block pointers for blocks in a free list are stored within the payload.
 * Next free block pointer is stored in the first 8 bytes and prev free block pointer in the second 8 bytes.
 * 
 * Implemented using automatic coalescing upon a block being freed as well as block splitting when applicable.
 * 
 * A global pointer to the last block in heap is kept in order to determine the prev block free/alloc bit for a new block.
 *
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16
#define BASE_ALIGNMENT 24
#define HEADER_SIZE 8
#define FOOTER_SIZE 8
#define FREE_OFFSET 8

static uint64_t* segFreeList[15];
static u_int64_t* lastHeader;

// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 * newAlign: rounds up to the nearest block size to maintain alignment (b/c of footer optimization)
 * NOTE: in order to have room for next/prev free block, minimum block size is 24 bytes
 */
static size_t newAlign(size_t x)
{
    if(x <= BASE_ALIGNMENT)
    {
        return BASE_ALIGNMENT;
    }
    else
    {
        return align(x - BASE_ALIGNMENT) + BASE_ALIGNMENT;
    }
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * isFree: returns if a payload block is free
 */
static bool isFree(uint64_t* ptr)
{
    return !(*ptr & 0x1);
}

/*
 * setFree: sets the alloc/free bit of a header to free
 */
static void setFree(uint64_t* ptr)
{
    *ptr &= 0xFFFFFFFFFFFFFFFE;
}

/*
 * setAlloc: sets the alloc/free bit of a header to alloc
 */
static void setAlloc(uint64_t* ptr)
{
    *ptr |= 0x1;
}

/*
 * isPrevFree: returns if a payload block's previous block is free
 */
static bool isPrevFree(uint64_t* ptr)
{
    return !(*ptr & 0x2);
}

/*
 * setPrevFree: sets the prev block alloc/free bit of a header to free
 */
static void setPrevFree(uint64_t* ptr)
{
    *ptr &= 0xFFFFFFFFFFFFFFFD;
}

/*
 * setPrevAlloc: sets the prev block alloc/free bit of a header to alloc
 */
static void setPrevAlloc(uint64_t* ptr)
{
    *ptr |= 0x2;
}

/*
 * getBlockSize: returns the number of bytes in a payload block
 */
static size_t getBlockSize(uint64_t* ptr)
{
    return (size_t) (*ptr & 0xFFFFFFFFFFFFFFF8);
}

/*
 * setBlockSize: sets the number of bytes in a payload block
 */
static void setBlockSize(uint64_t* ptr, size_t size)
{
    *ptr &= 0x7;
    *ptr |= (uint64_t) size;
}

/*
 * get8ByteAlignment: returns the number of uint64_t in a given number of bytes (assumes numBytes will always be a multiple of 8)
 */
static size_t get8ByteAlignment(size_t numBytes)
{
    return (numBytes) / 8;
}

/*
 * getFooter: returns a pointer to the footer of a block, given the header and payload size (only to be used on free blocks)
 */
static uint64_t *getFooter(uint64_t* header, size_t size)
{
    return header + get8ByteAlignment(HEADER_SIZE + size - FOOTER_SIZE);
}

/*
 * getPrevFooter: returns a pointer to the footer of a the previous block, given the current header (only to be used on free blocks)
 */
static uint64_t *getPrevFooter(uint64_t* header)
{
    return header - get8ByteAlignment(FOOTER_SIZE);
}

/*
 * getNextHeader: returns a pointer to the header of the next block, given the current header and payload size
 */
static uint64_t *getNextHeader(uint64_t* header, size_t size)
{
    return header + get8ByteAlignment(HEADER_SIZE + size);
}

/*
 * getPrevHeader: returns a pointer to the header of the previous block, given the current header and previous block payload size (only to be used on free blocks)
 */
static uint64_t *getPrevHeader(uint64_t* header, size_t size)
{
    return header - get8ByteAlignment(HEADER_SIZE + size);
}

/*
 * getPayload: returns a pointer to the start of the payload, given the current header
 */
static void *getPayload(uint64_t* header)
{
    return (void *) (header + get8ByteAlignment(HEADER_SIZE));
}

/*
 * getNextFreeBlock: returns a pointer to the next block from ptr in the free list
 */
static uint64_t* getNextFreeBlock(uint64_t* ptr)
{
    return *(uint64_t **) (ptr);
}

/*
 * getPrevFreeBlock: returns a pointer to the previous block from ptr in the free list
 */
static uint64_t* getPrevFreeBlock(uint64_t* ptr)
{
    return *(uint64_t **) (ptr + get8ByteAlignment(FREE_OFFSET));
}

/*
 * setNextFreeBlock: sets the pointer to the next block from ptr in the free list
 */
static void setNextFreeBlock(uint64_t* ptr, uint64_t* newptr)
{
    *(uint64_t **) (ptr) = newptr;
}

/*
 * setPrevFreeBlock: sets the pointer to the previous block from ptr in the free list
 */
static void setPrevFreeBlock(uint64_t* ptr, uint64_t* newptr)
{
    *(uint64_t **) (ptr + get8ByteAlignment(FREE_OFFSET)) = newptr;
}

/*
 * removeFreeBlock: removes the block ptr from the free list; assumes freeListIndex is a valid index
 */
static void removeFreeBlock(uint64_t* ptr, int freeListIndex)
{
    if(ptr == segFreeList[freeListIndex]) //when ptr is head of its respective free list
    {
        uint64_t* nextptr = getNextFreeBlock(ptr);
        if(nextptr)
        {
            setPrevFreeBlock(nextptr, NULL);
        }
        segFreeList[freeListIndex] = nextptr;
    }
    else
    {
        uint64_t* nextptr = getNextFreeBlock(ptr);
        uint64_t* prevptr = getPrevFreeBlock(ptr);
        if(nextptr)
        {
            setPrevFreeBlock(nextptr, prevptr);
        }
        setNextFreeBlock(prevptr, nextptr);
    }
}

/*
 * addFreeBlock: adds the block ptr to the beginning of the free list; assumes freeListIndex is a valid index
 */
static void addFreeBlock(uint64_t* ptr, int freeListIndex)
{
    if (!segFreeList[freeListIndex]) //when the free list for the specific index is empty
    {
        setNextFreeBlock(ptr, NULL);
        setPrevFreeBlock(ptr, NULL);
    }
    else
    {
        setNextFreeBlock(ptr, segFreeList[freeListIndex]);
        setPrevFreeBlock(segFreeList[freeListIndex], ptr);
        setPrevFreeBlock(ptr, NULL);
    }
    segFreeList[freeListIndex] = ptr;
}

/*
 * getFreeListIndex: returns the index of the desired free list in the segregated free list array; assumes the given the block size is valid (24, 40, 56,...)
 */
static int getFreeListIndex(size_t size)
{
    size_t sizeMul = (size - 8) / 16;
    if(sizeMul <= 4)
    {
        return sizeMul - 1;
    }
    else if(sizeMul <= 6)
    {
        return 4;
    }
    else if(sizeMul <= 8)
    {
        return 5;
    }
    else if(sizeMul <= 16)
    {
        return 6;
    }
    else if(sizeMul <= 32)
    {
        return 7;
    }
    else if(sizeMul <= 64)
    {
        return 8;
    }
    else if(sizeMul <= 128)
    {
        return 9;
    }
    else if(sizeMul <= 256)
    {
        return 10;
    }
    else if(sizeMul <= 512)
    {
        return 11;
    }
    else if(sizeMul <= 1024)
    {
        return 12;
    }
    else if(sizeMul <= 2048)
    {
        return 13;
    }
    else
    {
        return 14;
    }
}

/*
 * extendHeap: extends the heap by size bytes plus 8 bytes for a header and initializes the header; returns a pointer the header of the new block
 */
static uint64_t* extendHeap(size_t size)
{
    uint64_t* header = mm_sbrk(HEADER_SIZE + size); //extend heap
    if((void *) header == (void *) (-1))        
    {
        return NULL;
    }
    //update header for new block
    *header = 0x0;
    setAlloc(header);
    setBlockSize(header, size);
    if(lastHeader != (uint64_t *) mm_heap_lo())
    {
        if(!isFree(lastHeader))
        {
            setPrevAlloc(header);
        }
    }
    else
    {
        setPrevAlloc(header);
    }
    lastHeader = header;
    return header;
}

/*
 * mm_init: returns false on error, true on success.
 */
bool mm_init(void)
{
    // IMPLEMENT THIS
    uint64_t* heap_start = mm_sbrk(HEADER_SIZE); //allocate space for prologue
    if(heap_start != (uint64_t *) mm_heap_lo())
    {
        return false;
    }
    *heap_start = 0x0;
    setAlloc(heap_start);
    //Initialize global variables to reset heap to its initial state
    lastHeader = (uint64_t *) mm_heap_lo();
    for(int i = 0; i < 15; i++)
    {
        segFreeList[i] = NULL;
    }
    return true;
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    // IMPLEMENT THIS
    #ifdef DEBUG
        mm_checkheap(__LINE__);
    #endif
    if(!size)
    {
        return NULL;
    }
    size_t new_block_size = newAlign(size);
    int index = getFreeListIndex(new_block_size);
    uint64_t* ptr = segFreeList[index];
    bool nextList = true;
    while(ptr || nextList) //traverse free lits; checking if a free block exists that will fit the size
    {
        if(!ptr) //reached end of free list
        {
            if(index == 14) //reached end of the free list of largest block size
            {
                nextList = false;
            }
            else //go to head of free list of next block size
            {
                index++;
                ptr = segFreeList[index];
            }
        }
        else
        {
            uint64_t* header = ptr - get8ByteAlignment(HEADER_SIZE);
            size_t block_size = getBlockSize(header);
            if(new_block_size <= block_size) //free block has enough room for requested size
            {
                if(block_size - new_block_size >= 32) //free block is big enough to split
                {
                    size_t split_block_size = block_size - new_block_size - HEADER_SIZE;
                    setBlockSize(header, new_block_size);
                    //get information for the second half of the split block
                    uint64_t* nextHeader = getNextHeader(header, new_block_size);
                    uint64_t* nextFooter = getFooter(nextHeader, split_block_size);
                    //set information for the second half of the split block
                    *nextHeader = 0x0;
                    setBlockSize(nextHeader, split_block_size);
                    setPrevAlloc(nextHeader);
                    *nextFooter = 0x0;
                    setBlockSize(nextFooter, split_block_size);
                    //add second half of split block to its respective free list
                    int split_block_index = getFreeListIndex(split_block_size);
                    addFreeBlock((uint64_t *) getPayload(nextHeader), split_block_index);
                    if(header == lastHeader)
                    {
                        lastHeader = nextHeader;
                    }
                }
                else
                {
                    if(header != lastHeader)
                    {
                        setPrevAlloc(getNextHeader(header, block_size));
                    }

                }
                setAlloc(header);
                removeFreeBlock(ptr, index);
                #ifdef DEBUG
                    mm_checkheap(__LINE__);
                #endif
                return ptr;
            }
            else
            {
                if(index <= 3) //free lists in indices 0-3 are all the same size, so no need to check the entire list if first block isn't big enough
                {
                    index++;
                    ptr = segFreeList[index];
                }
                else
                {
                    ptr = getNextFreeBlock(ptr);
                }
            }
        }
    }
    //no free blocks available for requested size, so need to extend heap
    uint64_t* newHeader = extendHeap(new_block_size);
    #ifdef DEBUG
        mm_checkheap(__LINE__);
    #endif
    return getPayload(newHeader);
}

/*
 * free
 */
void free(void* ptr)
{
    // IMPLEMENT THIS
    #ifdef DEBUG
        mm_checkheap(__LINE__);
    #endif
    if(in_heap(ptr))
    {
        //get preprocessing data 
        uint64_t* header = (uint64_t *) (((unsigned char *) ptr) - HEADER_SIZE);
        size_t block_size = getBlockSize(header);
        uint64_t* footer = getFooter(header, block_size);
        int index = getFreeListIndex(block_size);
        uint64_t* nextHeader = getNextHeader(header, block_size);
        bool nextFree = (header != lastHeader && isFree(nextHeader)); //represents if the next block is free
        bool prevFree = (header - get8ByteAlignment(HEADER_SIZE)) != (uint64_t *) mm_heap_lo() && isPrevFree(header); //represents if the previous block is free
        uint64_t* prevFooter = getPrevFooter(header);
        if(nextFree && prevFree) //Case 1: coalesce previous, current, and next blocks
        {
            //get preprocessing data for new free block
            uint64_t* prevHeader = getPrevHeader(header, getBlockSize(prevFooter));
            uint64_t* nextFooter = getFooter(nextHeader, getBlockSize(nextHeader));
            int prevBlock_index = getFreeListIndex(getBlockSize(prevHeader));
            int nextBlock_index = getFreeListIndex(getBlockSize(nextHeader));
            size_t newSize = getBlockSize(prevHeader) + getBlockSize(header) + getBlockSize(nextHeader) + (2 * HEADER_SIZE);
            index = getFreeListIndex(newSize); //updates free list index so new free block is added to correct free list
            //update header and footer data for new free block
            setBlockSize(prevHeader, newSize);
            setBlockSize(nextFooter, newSize);
            setFree(prevHeader);
            setFree(nextFooter);
            //removes coalesced free blocks from each respective free list
            removeFreeBlock(prevHeader + get8ByteAlignment(HEADER_SIZE), prevBlock_index);
            removeFreeBlock(nextHeader + get8ByteAlignment(HEADER_SIZE), nextBlock_index);
            ptr = (uint64_t *) getPayload(prevHeader);
            if(nextHeader == lastHeader)
            {
                lastHeader = prevHeader;
            }
        }
        else if(nextFree) //Case 2: coalesce current and next blocks
        {
            //get preprocessing data for new free block
            uint64_t* nextFooter = getFooter(nextHeader, getBlockSize(nextHeader));
            int nextBlock_index = getFreeListIndex(getBlockSize(nextHeader));
            size_t newSize = getBlockSize(header) + getBlockSize(nextFooter) + HEADER_SIZE;
            index = getFreeListIndex(newSize); //updates free list index so new free block is added to correct free list
            //update header and footer data for new free block
            setBlockSize(header, newSize);
            setBlockSize(nextFooter, newSize);
            setFree(nextFooter);
            setFree(header);
            //removes coalesced free block from respective free list
            removeFreeBlock(nextHeader + get8ByteAlignment(HEADER_SIZE), nextBlock_index);
            if(nextHeader == lastHeader)
            {
                lastHeader = header;
            }
        }
        else if(prevFree) //Case 3: coalesce current and previous blocks
        {
            //get preprocessing data for new free block
            uint64_t* prevHeader = getPrevHeader(header, getBlockSize(prevFooter));
            int prevBlock_index = getFreeListIndex(getBlockSize(prevHeader));
            size_t newSize = getBlockSize(prevHeader) + getBlockSize(header) + HEADER_SIZE;
            index = getFreeListIndex(newSize); //updates free list index so new free block is added to correct free list
            //update header and footer data for new free block
            setBlockSize(footer, newSize);
            setBlockSize(prevHeader, newSize);
            setFree(prevHeader);
            setFree(footer);
            //removes coalesced free block from respective free list
            removeFreeBlock(prevHeader + get8ByteAlignment(HEADER_SIZE), prevBlock_index);
            ptr = (uint64_t *) getPayload(prevHeader);
            if(header != lastHeader)
            {
                setPrevFree(nextHeader);
            }
            else
            {
                lastHeader = prevHeader;
            }
        }
        else //Case 4: no coalescing
        {
            //update header and footer data for new free block
            setBlockSize(footer, block_size);
            setFree(footer);
            setFree(header);
            if(header != lastHeader)
            {
                setPrevFree(nextHeader);
            }
        }
        addFreeBlock((uint64_t *) ptr, index);
    }
    #ifdef DEBUG
        mm_checkheap(__LINE__);
    #endif
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    // IMPLEMENT THIS
    if(!oldptr)
    {
        return malloc(size);
    }
    else if(!size)
    {
        free(oldptr);
        return NULL;
    }
    else
    {
        void* newptr = malloc(size);
        if(!newptr)
        {
            return NULL;
        }
        //copy data from old payload into new block
        size_t old_size = getBlockSize(((uint64_t *) oldptr) - get8ByteAlignment(HEADER_SIZE));
        newptr = (size > old_size)?mm_memcpy(newptr, oldptr, old_size):mm_memcpy(newptr, oldptr, size);
        free(oldptr);
        return newptr;
    }
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    // Write code to check heap invariants here
    // IMPLEMENT THIS
    uint64_t* header = ((uint64_t *) mm_heap_lo()) + 1;
    while(header + 1 < (uint64_t *) mm_heap_hi()) //traverse heap
    {
        size_t blockSize = getBlockSize(header);
        if((blockSize - 8) % 16 != 0) //checks that each block is a valid size
        {
            dbg_printf("BLOCK SIZE IS NOT A VALID SIZE\n");
            dbg_printf("HEADER: %p BLOCK SIZE: %ld\n", header, blockSize);
            dbg_printf("LINE: %d\n", lineno);
            return false;
        }
        if(isFree(header))
        {
            u_int64_t* footer = getFooter(header, blockSize);
            size_t footerSize = getBlockSize(footer);
            if(blockSize != footerSize) //checks that each free block header and footer is storing the same size
            {
                dbg_printf("HEADER AND FOOTER SIZE NOT EQUAL\n");
                dbg_printf("HEADER: %p BLOCK SIZE: %ld\n", header, blockSize);
                dbg_printf("FOOTER: %p BLOCK SIZE: %ld\n", footer, footerSize);
                return false;
            }
            u_int64_t* nextHeader = getNextHeader(header, blockSize);
            if(nextHeader + 1 < (uint64_t *) mm_heap_hi() && isFree(nextHeader)) //checks that no contiguous free blocks escaped coalescing
            {
                dbg_printf("CONTIGUOUS FREE BLOCKS ESCAPED COALESCING\n");
                dbg_printf("HEADER1: %p\n", header);
                dbg_printf("HEADER2: %p\n", nextHeader);
                return false;
            }
            if(nextHeader + 1 < (uint64_t *) mm_heap_hi() && !isPrevFree(nextHeader)) //checks that each previous block alloc/free bit is correct
            {
                dbg_printf("NEXT HEADER PREVFREE BIT WRONG\n");
                dbg_printf("HEADER1: %p\n", header);
                dbg_printf("HEADER2: %p\n", nextHeader);
                return false;
            }
            int index = getFreeListIndex(blockSize);
            if(index != -1)
            {
                bool inList = false;
                uint64_t* counter = segFreeList[index];
                while(counter)
                {
                    if(header == counter - get8ByteAlignment(HEADER_SIZE))
                    {
                        inList = true;
                    }
                    counter = getNextFreeBlock(counter); 
                }
                if(!inList) //checks that each free block is in the correct free list
                {
                    dbg_printf("BLOCK NOT IN FREE LIST\n");
                    dbg_printf("HEADER: %p\n", header);
                    return false;
                }
            }
        }
        header = getNextHeader(header, getBlockSize(header));
    }
    //Checking free lists invariants
    int index = 0;
    uint64_t* ptr = segFreeList[index];
    bool nextList = true;
    while(ptr || nextList) //traverse free lists
    {
        if(!ptr)
        {
            if(index == 14)
            {
                nextList = false;
            }
            else
            {
                index++;
                ptr = segFreeList[index];
            }
        }
        else
        {
            uint64_t* header = ptr - get8ByteAlignment(HEADER_SIZE);
            if(getFreeListIndex(getBlockSize(header)) != index) //checks that each block in a free list is in the correct one
            {
                dbg_printf("BLOCK NOT IN CORRECT FREE LIST\n");
                dbg_printf("HEADER: %p\n", header);
                return false;
            }
            if(!isFree(header)) //checks that each block in a free list is marked as free
            {
                dbg_printf("BLOCK IN FREE LIST, BUT MARKED AS ALLOC\n");
                dbg_printf("HEADER: %p BLOCK SIZE: %ld\n", header, getBlockSize(header));
                return false;
            }
            ptr = getNextFreeBlock(ptr);
        }
    }
#endif // DEBUG
    return true;
}
