import Base

# Type alias for a tuple of eight bools.
def Bit8() -> Type:
  Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool

# Bits are grouped into bytes, most significant byte and bit first.
def Byte4() -> Type:
  Bit8() & Bit8() & Bit8() & Bit8()

