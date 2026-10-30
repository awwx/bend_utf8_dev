import Base
import ./hexdigits.bend as Hexdigits

law example:
  {U32.is_lt(Hexdigits.ascii_0, Hexdigits.ascii_9) == True{} : Bool}
