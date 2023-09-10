import Init.Data.String.Extra

@[extern "lean_string_get_byte"]
def String.getUtf8Byte (s : @& String) (n : Nat) : UInt8 := s.toUTF8.get! n
