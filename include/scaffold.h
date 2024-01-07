#include <stdio.h>

inline FILE* sfd_get_stdout() {
    return stdout;
}

inline void sfd_putstr(FILE* handle, const char* str) {
    fputs(str, handle);
}

inline void sfd_putint(FILE* handle, int n) {
    fputc(n, handle);
}

inline int sfd_int_add(int a, int b) {
    return a + b;
}
