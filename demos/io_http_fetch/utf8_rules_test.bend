# Independent byte-pattern/rule examples. The proof import fills all laws.
# Run with: bend demos/io_http_fetch/utf8_rules_test.bend
import Base
import ./utf8_laws.bend as Spec
import ./utf8_proof.bend as Proof

def bytes_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> xt y <> yt:
      Bool.and(U32.is_eq(x, y), bytes_eq(xt, yt))
    case _ _:
      False{}

def same(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

def test(name: String, +p: Spec.Pattern, bytes: List<&2, U32>,
  short: Bool, surrogate: Bool, bound: Bool) -> IO(Unit):
  IO.print(name ++ ": " ++ Bool.show(
    Bool.and(bytes_eq(Spec.pattern_bytes(p), bytes),
      Bool.and(same(Spec.shortest(p), short),
        Bool.and(same(Spec.not_surrogate(p), surrogate),
          same(Spec.within_unicode(p), bound))))))

def main() -> IO(Unit):
  do IO<Unit>:
    test("ASCII NUL", Spec.One{Word.zero(7n)},
      [0], True{}, True{}, True{})
    test("ASCII maximum", Spec.One{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}},
      [127], True{}, True{}, True{})
    test("C0 BF overlong", Spec.Two{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(5n)}}}}}}},
      [192, 191], False{}, True{}, True{})
    test("C1 BF overlong", Spec.Two{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(4n)}}}}}}}},
      [193, 191], False{}, True{}, True{})
    test("two-byte minimum", Spec.Two{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(3n)}}}}}}}}},
      [194, 128], True{}, True{}, True{})
    test("two-byte maximum", Spec.Two{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}},
      [223, 191], True{}, True{}, True{})
    test("three-byte overlong", Spec.Three{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(5n)}}}}}}}}}}}},
      [224, 159, 191], False{}, True{}, True{})
    test("three-byte minimum", Spec.Three{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(4n)}}}}}}}}}}}}},
      [224, 160, 128], True{}, True{}, True{})
    test("before surrogates", Spec.Three{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}},
      [237, 159, 191], True{}, True{}, True{})
    test("first surrogate", Spec.Three{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}},
      [237, 160, 128], True{}, False{}, True{})
    test("last surrogate", Spec.Three{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}},
      [237, 191, 191], True{}, False{}, True{})
    test("after surrogates", Spec.Three{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}},
      [238, 128, 128], True{}, True{}, True{})
    test("BOM", Spec.Three{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}},
      [239, 187, 191], True{}, True{}, True{})
    test("noncharacter", Spec.Three{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}},
      [239, 191, 191], True{}, True{}, True{})
    test("unassigned scalar", Spec.Two{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(1n)}}}}}}}}}}},
      [205, 184], True{}, True{}, True{})
    test("four-byte overlong", Spec.Four{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(5n)}}}}}}}}}}}}}}}}},
      [240, 143, 191, 191], False{}, True{}, True{})
    test("overlong surrogate", Spec.Four{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(5n)}}}}}}}}}}}}}}}}},
      [240, 141, 160, 128], False{}, False{}, True{})
    test("four-byte minimum", Spec.Four{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(4n)}}}}}}}}}}}}}}}}}},
      [240, 144, 128, 128], True{}, True{}, True{})
    test("Unicode maximum", Spec.Four{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}}}}}}},
      [244, 143, 191, 191], True{}, True{}, True{})
    test("above Unicode maximum", Spec.Four{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}}}}}}},
      [244, 144, 128, 128], True{}, True{}, False{})
    test("raw pattern maximum", Spec.Four{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}}}}}}}}}}}}}}}}}}},
      [247, 191, 191, 191], True{}, True{}, False{})

#|ASCII NUL: True
#|ASCII maximum: True
#|C0 BF overlong: True
#|C1 BF overlong: True
#|two-byte minimum: True
#|two-byte maximum: True
#|three-byte overlong: True
#|three-byte minimum: True
#|before surrogates: True
#|first surrogate: True
#|last surrogate: True
#|after surrogates: True
#|BOM: True
#|noncharacter: True
#|unassigned scalar: True
#|four-byte overlong: True
#|overlong surrogate: True
#|four-byte minimum: True
#|Unicode maximum: True
#|above Unicode maximum: True
#|raw pattern maximum: True
