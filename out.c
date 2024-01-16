#include <scaffold.h>

typedef int Int;
typedef size_t _USize_1;
typedef sfd_object* String;

extern _USize_1 sfd_int_to_usize(Int _a_3);

extern String sfd_alloc_string(_USize_1 _size_5, _USize_1 _cap_6);

extern String sfd_string_append(String _a_8, String _b_9);

Int main() {
    String _a_10 = sfd_alloc_string(sfd_int_to_usize(0), sfd_int_to_usize(10));
    String _b_11 = sfd_string_mk("world!\n");
    String _18 = sfd_string_mk("hello");
    String _19 = sfd_string_append(_a_10, _b_11);
    sfd_dec_ref(_b_11);
    String _20 = sfd_string_append(_19, _18);
    sfd_dec_ref(_18);
    String _c_12 = _20;
    sfd_dec_ref(_c_12);
    return 0;
}
