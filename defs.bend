import Base

# A "nibble" is half of a byte, a four-bit numeral, which can be
# represented by a single hexadecimal digit.

def Nibble() -> Data:
  Word(4n)

# Type alias for a tuple of eight bools.
def Bit8() -> Type:
  Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool

# Bits are grouped into bytes, most significant byte and bit first.
def Bit32() -> Type:
  Bit8() & Bit8() & Bit8() & Bit8()

