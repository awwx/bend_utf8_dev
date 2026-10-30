import Base
import ./hexdigits.bend as H

law example:
  {U32.is_lt(H.ascii_0, H.ascii_9) == True{} : Bool}
