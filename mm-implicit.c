/*
 * mm-implicit.c - 묵시적 가용리스트와 Next Fit으로 동적 할당기 구현
 * MAX_SCORE: 86
 *
 */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* ========================== Team Info =============================== */

team_t team = {
    /* Team name */
    "Team 4",
    /* First member's full name */
    "Lee Seo Yeon",
    /* First member's email address */
    "sylee6529@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* ========================== Macros =============================== */

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4              // Word size(=header, footer size)
#define DSIZE 8              // Double word size
#define CHUNKSIZE (1 << 12)  // heap 늘릴 때 늘어나는 size

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))                           // size와 가용여부 비트를 통합하여 header와 footer에 저장할 수 있는 값을 리턴
#define GET(p) (*(unsigned int *)(p))                                  // p의 주소을 read
#define PUT(p, val) (*(unsigned int *)(p) = (val))                     // p의 값을 write
#define GET_SIZE(p) (GET(p) & ~0x7)                                    // p에서 size를 read
#define GET_ALLOC(p) (GET(p) & 0x1)                                    // p에서 alloc을 read (최하위 비트를 가져온다, 홀수면 'allocated', 짝수면 'free'-비트 표현 때문)
#define HDRP(bp) ((char *)(bp)-WSIZE)                                  // header의 주소를 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)           // footer의 주소를 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))  // 다음 bp 위치를 계산
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))    // 이전 bp 위치를 계산

/* ======================= Private Global Variables ============================== */

static char *next_ptr;
static char *heap_listp;

/* ========================== Function Prototype Declaration =============================== */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_first_fit(size_t asize);
static void *find_next_fit(size_t asize);
static void *find_best_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *bp, size_t size);

/* =========================== Functions ================================== */

/*
 * coalesce
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1: 이전/다음 블록이 모두 'a' -> 현재 블록의 상태만 'a'->'f'
    if (prev_alloc && next_alloc) {
        next_ptr = bp;
        return bp;  // 이미 free 처리되어 있어 그대로 리턴
    }

    // Case 2: 이전 블록은 'a' and 다음 블록은 'f' -> 현재 블록과 다음 블록을 coalesce
    else if (prev_alloc && !next_alloc) {
        // 다음 블록의 크기만큼 더하고 header와 footer를 갱신
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // Case 3: 이전 블록은 'f' and 다음 블록은 'a' -> 이전 블록과 현재 블록을 coalesce
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));             // footer를 먼저 늘려준다
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  //
        bp = PREV_BLKP(bp);
    }

    // Case 4:
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    next_ptr = bp;
    return bp;
}

/*
 * extend_heap
 * 새로운 free block을 만들어 힙을 확장하는 함수
 * 확장한 공간을 allocator가 사용할 수 있도록 세팅
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // alignment 유지를 위해 짝수 개수의 words를 할당함
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {  // mem_sbrk가 반환되면 bp는 현재 만들어진 블록의 끝??에 있다
        return NULL;
    }

    // 새로운 free block의 header와 footer를 만들고 epilogue 헤더를 다음 블록 위치로 조정
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);  // 만약 이전 block이 free block이었다면, coalesce 하기 위해 호출
}

/* First Fit으로 검색 */
static void *find_first_fit(size_t asize) {
    void *bp;

    // heap에 있는 블록들을 탐색 (size가 0인 epilogue header까지)
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        // 해당 블록이 'f'이고 asize보다 블록 사이즈가 클 때
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;  // 공간을 찾지 못하면 NULL 리턴
}

static void *find_next_fit(size_t asize) {
    char *bp = next_ptr;

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            next_ptr = bp;
            return bp;
        }
    }

    bp = heap_listp;
    while (bp < next_ptr) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            next_ptr = bp;
            return bp;
        }
    }
    return NULL;
}

static void *find_best_fit(size_t asize) {
    char *bp = NULL;
    size_t best_fit = SIZE_MAX;

    // Iterate over the free blocks to find the best fit
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            size_t current_fit = GET_SIZE(HDRP(bp)) - asize;
            if (current_fit < best_fit) {
                best_fit = current_fit;
                next_ptr = bp;
            }
        }
    }

    return (best_fit != SIZE_MAX) ? next_ptr : NULL;
}

/*
 * place
 * 들어갈 위치를 포인터로 받아, asize만큼의 블록을 배치하는 함수
 * 가용 블록의 시작 부분에 포인터를 배치하고, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));  // 현재 블록의 size

    // 현재 블록의 사이즈가 최소 블록 사이즈보다 크면, 사용하고 남은 블록들은 free 한다
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));  // header에 asize로 사이즈 갱신
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);                     // bp를 다음 블럭 위치에 둔다
        PUT(HDRP(bp), PACK(csize - asize, 0));  // 다음 블록에는 'f' 표시, size 갱신
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    // 아니라면 현재 블록을 다 사용한다
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_init - 메모리 힙을 초기화하는 일을 하는 함수
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }

    PUT(heap_listp, 0);                             // padding 생성
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // prologue header 생성
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // prologue footer 생성
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      // block header 생성
    heap_listp += (2 * WSIZE);                      // prologue header와 footer 사이로 포인터로 옮긴다

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }

    next_ptr = (char *)heap_listp;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t adjustedSize;
    size_t extendSize;
    char *bp;

    // size가 0이면 할당하지 않는다
    if (size == 0) {
        return NULL;
    }

    // size가 더블워드 이하면 블록의 최소 크기(header+footer)로 설정
    if (size <= DSIZE) {
        adjustedSize = 2 * DSIZE;
    }

    // size보다 더블워드보다 클 때, 블록이 가질 수 있는 크기 중에 최적화된 크기(인접한 8의 배수)로 재조정
    else {
        adjustedSize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // fit에 맞는 free 리스트를 찾는다
    if ((bp = find_next_fit(adjustedSize)) != NULL) {
        place(bp, adjustedSize);
        next_ptr = bp;
        return bp;
    }

    // fit에 맞는 공간이 없으면, 힙을 늘린 후 그 공간에 할당
    extendSize = MAX(adjustedSize, CHUNKSIZE);
    if ((bp = extend_heap(extendSize / WSIZE)) == NULL) {
        return NULL;
    }

    place(bp, adjustedSize);
    next_ptr = bp;
    return bp;
}

/*
 * mm_free - 블록을 반환, free 표시해주는 함수
 */
void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));

    // header와 footer를 'f'로 갱신
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc
 * 기존에 malloc으로 동적 할당된 메모리 크기를 변경시켜주는 함수
 * size만큼의 블록을 할당하고 memcopy로 데이터를 똑같이 옮긴 후 bp를 free한다
 * 무조건 새로 할당하는 것이 아니라, 다음 블록이 가용상태이고 사용가능하면 합쳐쓸 수 있게 최적화
 */
void *mm_realloc(void *bp, size_t size) {
    size_t oldSize = GET_SIZE(HDRP(bp));
    size_t newSize = size + (2 * WSIZE);

    if (newSize <= oldSize) {
        return bp;
    }

    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = oldSize + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        if (!next_alloc && current_size >= newSize) {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }

        else {
            void *new_bp = mm_malloc(newSize);
            place(new_bp, newSize);
            memcpy(new_bp, bp, newSize);
            mm_free(bp);
            return new_bp;
        }
    }
}
