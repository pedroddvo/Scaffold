// #define SFD_DEBUG_ALLOC

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

typedef struct {
    int rc;
    unsigned tag:8;
    unsigned fields:8;
} sfd_object;

typedef struct {
    sfd_object header;
    size_t size, capacity;
    char data[0];
} sfd_string;

typedef enum {
    ScaffoldCtor = 254,
    ScaffoldString,
} sfd_object_tag;

typedef sfd_object sfd_ctor;
typedef sfd_object* sfd_boxed;

#define sfd_string(obj) ((sfd_string*)obj)

static inline void sfd_free_object(sfd_object* o);

static inline sfd_object* sfd_box(size_t n) { return (sfd_object*)(((size_t)(n) << 1) | 1); }
static inline size_t sfd_unbox(sfd_object* o) { return (size_t)(o) >> 1; }
static inline bool sfd_is_boxed(sfd_object* o) { return ((size_t)(o) & 1) == 1; }

static inline sfd_object_tag sfd_obj_tag(sfd_object* o) { return (sfd_object_tag)o->tag; }

static inline void sfd_set_header(sfd_object* o, unsigned tag, unsigned fields) {
    o->rc = 1;
    o->tag = tag;
    o->fields = fields;
}

static inline void sfd_free(void* ptr) {
    static int x = 0;
#ifdef SFD_DEBUG_ALLOC
    printf("%d object deallocated\n", x++);
#endif
    free(ptr);
}

static inline void* sfd_malloc(size_t sz) {
    static int x = 0;
#ifdef SFD_DEBUG_ALLOC
    printf("%d object allocated\n", x++);
#endif
    return malloc(sz);
}

static inline sfd_ctor* sfd_ctor_alloc(unsigned tag, size_t fields) {
    sfd_ctor* ctor = (sfd_ctor*)sfd_malloc(sizeof(sfd_ctor) + sizeof(sfd_object*)*fields);
    sfd_set_header((sfd_object*)ctor, tag, fields);
    return ctor;
}

typedef struct {
    sfd_object* header;
    sfd_boxed fields[1];
} sfd_ctor_fields;

static inline bool sfd_is_exclusive(sfd_object* o) {
    return o->rc == 1;
}

static inline void sfd_inc_ref(sfd_object* o) {
    o->rc++;
}

static inline void sfd_dec_ref(sfd_object* o) {
    if (o->rc > 1) o->rc--;
    else sfd_free_object(o);
}

static inline void sfd_inc(sfd_object* o) { if (!sfd_is_boxed(o)) sfd_inc_ref(o); }
static inline void sfd_dec(sfd_object* o) { if (!sfd_is_boxed(o)) sfd_dec_ref(o); }

static inline bool sfd_is_ctor(sfd_object* o) { return o->tag <= ScaffoldCtor; }

static inline void sfd_ctor_set(sfd_ctor* ctor, unsigned i, sfd_boxed obj) {
    sfd_ctor_fields* ctorf = (sfd_ctor_fields*)ctor;
    ctorf->fields[i] = obj;
}

static inline sfd_boxed sfd_ctor_get(sfd_ctor* ctor, unsigned i) {
    sfd_ctor_fields* ctorf = (sfd_ctor_fields*)ctor;
    return ctorf->fields[i];
}

static inline void sfd_ctor_free(sfd_ctor* ctor) {
    sfd_ctor_fields* ctorf = (sfd_ctor_fields*)ctor;
    for (size_t i = 0; i < ctor->fields; i++) {
        if (sfd_is_boxed(ctorf->fields[i])) continue;
        sfd_dec(ctorf->fields[i]);
    }
    sfd_free(ctor);
}

static inline void sfd_free_object(sfd_object* o) {
    switch (o->tag) {
        case ScaffoldString: sfd_free(o); break;
        default: 
            if (sfd_is_ctor(o)) sfd_ctor_free(o);
            else assert(0 && "cannot free object of this type"); break;
    }
}

static inline size_t _sfd_next_pow2(size_t n) {
    size_t v = n;

    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;

    return v;
}

static inline sfd_object* sfd_alloc_string(size_t size, size_t capacity) {
    sfd_string* o = (sfd_string*)sfd_malloc(sizeof(sfd_string) + capacity);
    sfd_set_header((sfd_object*)o, ScaffoldString, 0);
    o->size = size;
    o->capacity = capacity;
    return (sfd_object*)o;
}

static inline sfd_object* sfd_string_mk(const char* str) {
    size_t len = strlen(str);
    sfd_object* obj = sfd_alloc_string(len, _sfd_next_pow2(len));
    memcpy(sfd_string(obj)->data, str, len);
    return obj;
}

static inline sfd_object* sfd_string_append(sfd_object* a, sfd_object* b) {
    sfd_string* astr = sfd_string(a);
    sfd_string* bstr = sfd_string(b);
    size_t a_size = astr->size, b_size = bstr->size, new_size = a_size + b_size;

    sfd_object* r;
    if (!sfd_is_exclusive(a)) {
        r = sfd_alloc_string(new_size, _sfd_next_pow2(new_size));
        memcpy(sfd_string(r)->data, astr->data, a_size);
        sfd_dec_ref(a);
    } else {
        if (new_size > astr->capacity) {
            r = sfd_alloc_string(new_size, _sfd_next_pow2(new_size));
            memcpy(sfd_string(r)->data, astr->data, a_size);
            sfd_free_object(a);
        } else {
            r = a;
        }
    }

    memcpy(sfd_string(r)->data + a_size, bstr->data, b_size);
    sfd_string(r)->size = new_size;
    return r;
}

static inline int sfd_string_len(sfd_object* a) { return sfd_string(a)->size; }

static inline size_t sfd_int_to_usize(int n) { return (size_t)n; }

static inline FILE* sfd_io_get_stdout() { return stdout; }

static inline int sfd_io_put_str(FILE* handle, sfd_object* a) {
    sfd_string* str = sfd_string(a);
    return fprintf(handle, "%.*s", (int)str->size, str->data);
}

static inline int sfd_int_add(int a, int b) { return a + b; }
static inline int sfd_int_sub(int a, int b) { return a - b; }
static inline int sfd_int_mul(int a, int b) { return a * b; }

static inline bool sfd_int_eql(int a, int b) { return a == b; }
