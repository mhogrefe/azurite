namespace UInt64

/-- Combined quotient/remainder of `x / y` and `x % y`, returned as `(q, r)`.
Compilers (GCC/Clang/MSVC) recognize this idiom and emit a single hardware
`DIV` instruction, which produces both quotient and remainder simultaneously. -/
@[inline]
def divMod (x y : UInt64) : UInt64 × UInt64 :=
  (x / y, x % y)

end UInt64
