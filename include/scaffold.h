#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

typedef struct {
    int rc;
    unsigned tag:8;
} sfd_object;

typedef struct {
    sfd_object header;
    size_t size, capacity;
    char data[0];
} sfd_string;

typedef enum {
    ScaffoldString,
} sfd_object_tag;

#define sfd_string(obj) ((sfd_string*)obj)

static inline void sfd_set_header(sfd_object* o, unsigned tag) {
    o->rc = 1;
    o->tag = tag;
}

static inline void sfd_free_object(sfd_object* o) {
    switch (o->tag) {
        case ScaffoldString: free(o); break;
        default: assert(0 && "cannot free object of this type"); break;
    }
}

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
    sfd_string* o = (sfd_string*)malloc(sizeof(sfd_string) + capacity);
    sfd_set_header((sfd_object*)o, ScaffoldString);
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
    size_t new_cap = _sfd_next_pow2(new_size);

    sfd_object* r;
    if (!sfd_is_exclusive(a)) {
        r = sfd_alloc_string(new_size, new_cap);
        memcpy(sfd_string(r)->data, astr->data, a_size);
        sfd_dec_ref(a);
    } else {
        if (new_size >= astr->capacity) {
            r = sfd_alloc_string(new_size, new_cap);
            memcpy(sfd_string(r)->data, astr->data, a_size);
            sfd_free_object(a);
        } else {
            r = a;
        }
    }

    memcpy(sfd_string(r)->data + a_size, bstr->data, b_size);
    sfd_string(r)->size = new_size;
    sfd_string(r)->capacity = new_cap;
    return r;
}

static inline size_t sfd_int_to_usize(int n) { return (size_t)n; }

static inline FILE* sfd_io_get_stdout() { return stdout; }

static inline int sfd_io_put_str(FILE* handle, sfd_object* a) {
    sfd_string* str = sfd_string(a);
    return fprintf(handle, "%.*s", (int)str->size, str->data);
}
