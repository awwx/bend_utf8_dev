# Run with: bend demos/io_http_fetch/utf8_hex_test.bend
import Base
import ./utf8_laws.bend as Spec
import ./utf8_proof.bend as Proof

def converted(name: String, text: String,
  -valid: {Spec.hex_u32.valid(text) == True{} : Bool}, expected: U32) -> IO(Unit):
  IO.print(name ++ ": " ++ Bool.show(U32.is_eq(Spec.hex_u32(text, valid), expected)))

def rejected(name: String, text: String) -> IO(Unit):
  IO.print(name ++ ": " ++ Bool.show(Bool.not(Spec.hex_u32.valid(text))))

def main() -> IO(Unit):
  do IO<Unit>:
    converted("zero", "00000000", {==}, 0)
    converted("maximum", "FFFFFFFF", {==}, 4294967295)
    converted("digits 0 through 7", "01234567", {==}, 19088743)
    converted("digits 8 through F", "89ABCDEF", {==}, 2309737967)
    converted("Unicode codepoint", "0001F600", {==}, 128512)
    converted("high bit", "80000000", {==}, 2147483648)
    rejected("empty", "")
    rejected("foo", "foo")
    rejected("seven digits", "1234567")
    rejected("nine digits", "012345678")
    rejected("lowercase", "abcdef01")
    rejected("mixed case", "0123456a")
    rejected("prefix", "0x12ABCD")
    rejected("space", "0000000 ")
    rejected("sign", "+0000000")
    rejected("before zero", "0000000/")
    rejected("after nine", "0000000:")
    rejected("before A", "0000000@")
    rejected("after F", "0000000G")
    rejected("fullwidth A", "0000000Ａ")
    rejected("NUL", "0000000\0")

#|zero: True
#|maximum: True
#|digits 0 through 7: True
#|digits 8 through F: True
#|Unicode codepoint: True
#|high bit: True
#|empty: True
#|foo: True
#|seven digits: True
#|nine digits: True
#|lowercase: True
#|mixed case: True
#|prefix: True
#|space: True
#|sign: True
#|before zero: True
#|after nine: True
#|before A: True
#|after F: True
#|fullwidth A: True
#|NUL: True
