#include <assert.h>
#include <stdbool.h>
#include <err.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#define ALLOC_SIZE 524288
#define HEAP_SIZE (ALLOC_SIZE - 31 * 8)
#define BITFIELD_SIZE 8192 
#define BITFIELD_COUNT 512

// This is used as the end of the list of objects from oldest to youngest. An
// object cannot be odd because they are double word aligned.
#define OBJECT_LIST_END 1

// This is used in lists of fields to update. Index 0 cannot be a field
//  because it would contain a header word.
#define FIELD_LIST_END 0

struct state {
  uint64_t frontier;
  uint64_t limit;
  uint64_t sentinel;
  uint64_t mark_bitfield[BITFIELD_COUNT];
  void (*f)(struct state *);
  uint64_t arguments[31];
  void (*saved)(struct state *);
  uint32_t argument_bitfield;
};

extern int main();
static void finished(struct state *);
static void unreachable(struct state *);
static void gc(struct state *);
static void finish_marking(struct state *, uint16_t *);

static void check_many(struct state *s, uint32_t bitfield, uint64_t elements);
static void check_one(struct state *s, uint64_t p);

static void finished(struct state *s) {
  exit(EXIT_SUCCESS);
  return;
}

static void unreachable(struct state *s) {
  errx(EXIT_FAILURE, "unreachable");
  return;
}

// Mark an object in the bitfield. Add the field to the list of fields
// to update when the object is moved.
//
//   p  a pointer to the field which points to the object to mark
//
//   q  the index of the field in the heap in words, which is used
//      by field update lists
//
//   o  a pointer to the object to mark
//
//   i  the index of the object in the heap in double words, which is
//      what is used by the bitfield
//
static void mark(struct state *s, uint64_t p) {
  uint64_t start = s->limit - HEAP_SIZE;
  uint64_t o = *(uintptr_t *)p;
  *(uint64_t *)p = 0;
  check_one(s, o);
  uint64_t i = (o - start) / 16;
  // Mark the bitfield.
  s->mark_bitfield[i / 64] |= ((uint64_t)1 << (i % 64));
  uint64_t q = (p - start) / 8;
  // Push the list of fields to update.
  *(uint16_t *)p = *(uint16_t *)(o + 10);
  *(uint16_t *)(o + 10) = (uint16_t)q;
}

static bool valid(uint64_t p) {
  uint8_t tag = *(uint8_t *)p;
  return tag < 3;
}

// Mark the contents of a tuple, constructor, or the arguments to a function.
//   elements is a pointer to the first element
//
static void mark_pointers(struct state *s, uint32_t bitfield, uint64_t elements) {
  while (bitfield != 1) {
    if ((bitfield & 1) == 1) {
      mark(s, elements);
    }
    elements += 8;
    bitfield >>= 1;
  }
}

static int bitfield_length(uint32_t bitfield) {
  return 2 + (((31 - __builtin_clz(bitfield)) + 1) / 2) * 2;
}

// This function takes an object which has already been marked and
// marks its contents.
//
//   p  the object whose contents we want to mark
//
static void mark_object_contents(struct state *s, uint64_t p) {
  switch (*(uint8_t *)p) {
    // Tuple
    case 0: {
      uint32_t bitfield = *(uint32_t *)(p + 4);
      mark_pointers(s, bitfield, p + 16);
      // length in double words
      uint16_t len = 1 + ((31 - __builtin_clz(bitfield)) + 1) / 2;
      *(uint16_t *)(p + 12) = len;
      return;
    }
    // Constructor
    case 1: {
      uint32_t bitfield = *(uint32_t *)(p + 4);
      mark_pointers(s, bitfield, p + 16);
      // length in double words
      uint16_t len = 1 + ((31 - __builtin_clz(bitfield)) + 1) / 2;
      *(uint16_t *)(p + 12) = len;
      return;
    }
    // String
    case 2: {
      return;
    }
    default: {
      errx(EXIT_FAILURE, "not an object");
    }
  }
}

// This is written to scan the mark bitfield as fast as possible, skipping
// over empty bitfields.
//
//   p  the address of the bitfield being examined
//   m  the bitfield being examined
//
static void finish_marking(struct state *s, uint16_t *oldest) {
  // Record the index of the oldest object as we work.
  uint16_t x = OBJECT_LIST_END;
  uint64_t *p = &(s->mark_bitfield[BITFIELD_COUNT]);
  uint64_t bitfield_start = (uint64_t)&(s->mark_bitfield[0]);
  uint64_t heap_start = s->limit - HEAP_SIZE;
  for (;;) {
    p--;
    uint64_t m = *p;
    if (m == 0)
      continue;
    if (p == &(s->sentinel))
      break;
    uint64_t q = heap_start + ((uint64_t)p - bitfield_start) * 128;
    for (int64_t i = 63; i >= 0; i--) {
      if ((m & ((uint64_t)1 << (uint64_t)i)) != 0) {
        uint64_t r = (uint64_t)(q + (uint64_t)i * 16);
        check_one(s, r);
        *(uint16_t *)(r + 8) = x;
        x = (r - heap_start) / 8;
        mark_object_contents(s, r);
        // We must fetch p again because it may be marked.
        m = *p;
      }
    }
    // Clear the bitfield when we are done with it.
    *p = 0;
  }
  *oldest = x;
}

// Update every field which points to p to point to the frontier.
//
//   p  is the address of the old location of the object
//   i  is the index of the field in the heap in words
//   q  is the address of the field to update
//
static void update_fields(struct state *s, uint64_t p) {
  uint64_t heap_start = s->limit - HEAP_SIZE;
  uint64_t frontier = s->frontier;
  uint16_t i = *(uint16_t *)(p + 10);
  *(uint16_t *)(p + 10) = FIELD_LIST_END;
  while (i != FIELD_LIST_END) {
    uint64_t q = heap_start + (uint64_t)i * 8;
    i = *(uint16_t *)q;
    *(uint64_t *)q = frontier;
  }
}

// Slide the object from address p to the frontier.
//
//   p  is the old location of the object
//   l  is the length of the object in double words
//
static void slide(struct state *s, uint64_t p) {
  check_one(s, p);
  uint64_t frontier = s->frontier;
  uint64_t old = frontier;
  uint64_t l = *(uint16_t *)(p + 12);
  *(uint16_t *)(p + 12) = 0;
  if (p == frontier)
    return;
  for (uint64_t i = 0; i < l; i++) {
    *(uint64_t *)frontier = *(uint64_t *)(p + i * 16);
    frontier += 8;
    *(uint64_t *)frontier = *(uint64_t *)(p + i * 16 + 8);
    frontier += 8;
  }
  s->frontier = frontier;
  check_one(s, old);
}

// Slides the objects to their new locations.
//
//   x  the index of the oldest object in words
//
static void compact(struct state *s, uint16_t x) {
  uint64_t start = s->limit - HEAP_SIZE;
  while (x != OBJECT_LIST_END) {
    uint64_t p = start + (uint64_t)x * 8;
    check_one(s, p);
    x = *(uint16_t *)(p + 8);
    *(uint16_t *)(p + 8) = 0;
    // update fields for the new location, which is the frontier.
    printf("update fields\n");
    update_fields(s, p);
    // slide to the new location 2 words at a time
    printf("slide\n");
    slide(s, p);
  }
}

static void check_one(struct state *s, uint64_t p) {
  uint64_t start = s->limit - HEAP_SIZE;
  uint64_t limit = s->limit;
  //printf("check one %ld\n", p);
  assert(p >= start);
  assert(p < limit);
  uint8_t tag = *(uint8_t *)p;
  switch (tag) {
    // Tuple
    case 0: {
      // uint32_t bitfield = *(uint32_t *)(p + 4);
      // printf("tuple %d\n", bitfield_length(bitfield));
      // check_many(s, bitfield, p + 16);
      return;
    }
    // Constructor
    case 1: {
      // uint32_t bitfield = *(uint32_t *)(p + 4);
      // printf("constructor %d\n", bitfield_length(bitfield));
      // check_many(s, bitfield, p + 16);
      return;
    }
    // String
    case 2: {
      // printf("string\n");
      return;
    }
    default: {
      errx(EXIT_FAILURE, "check failed for tag: %d", tag);
      return;
    }
  }
}

static void check_many(struct state *s, uint32_t bitfield, uint64_t elements) {
  while (bitfield != 1) {
    if ((bitfield & 1) == 1) {
      check_one(s, *(uint64_t *)elements);
    }
    elements += 8;
    bitfield >>= 1;
  }
}

static void check(struct state *s) {
  check_many(s, s->argument_bitfield, (uint64_t)(&(s->arguments[0])));
} 

// Compacts the heap.
//
//   x  is the list of objects from oldest to youngest.
//
static void gc(struct state *s) {
  printf("entering gc\n");

  for (uint64_t i = 0; i < 31; i++) {
    *(uint64_t *)(s->limit + i * 8) = s->arguments[i];
  }

  check(s);

  // Reset the frontier to the start of the heap.
  s->frontier = s->limit - HEAP_SIZE;
  // Mark the arguments in the state, which are the only root pointers.
  printf("mark pointers\n");
  mark_pointers(s, s->argument_bitfield, s->limit);
  uint16_t x = OBJECT_LIST_END;
  // As we finish marking the objects using the bitfield, we create a list of
  // objects from oldest to youngest, which is used during compaction.
  printf("finish marking\n");
  finish_marking(s, &x);
  // Now we can move the objects to their new locations.
  printf("compact\n");

  assert(s->frontier == s->limit - HEAP_SIZE);

  compact(s, x);
  // Restore the function to call. The arguments have all been updated.
  s->f = s->saved;

  for (uint64_t i = 0; i < 31; i++) {
    s->arguments[i] = *(uint64_t *)(s->limit + i * 8);
  }

  printf("checking\n");
  check(s);

  if (s->limit - s->frontier < HEAP_SIZE / 2) {
    errx(EXIT_FAILURE, "heap exhausted");
  }

  printf("leaving gc\n");
  return;
}

