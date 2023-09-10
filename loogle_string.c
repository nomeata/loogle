#include <lean/lean.h>

LEAN_EXPORT uint8_t lean_string_get_byte(b_lean_obj_arg s, b_lean_obj_arg i) {
  char const * str = lean_string_cstr(s);
  size_t idx = lean_unbox(i);
  if (idx + 1 < lean_string_size(s)) return str[idx];
  return 0;
}
