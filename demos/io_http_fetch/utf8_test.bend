# Run with: bend demos/io_http_fetch/utf8_test.bend
# Compare every feed's output, not only the concatenated final string.
import Base
import ./utf8.bend as UTF8

def check_step(decoded: UTF8.State & String, want: String,
  rest: UTF8.State -> Bool) -> Bool:
  (state, text) = decoded
  Bool.and(String.eq(text, want), rest(state))

def check(chunks: List<&2, List<&2, U32>>, wants: List<&2, String>,
  state: UTF8.State, final: String) -> Bool:
  match chunks wants:
    case Nil{} Nil{}:
      String.eq(UTF8.done(state), final)
    case bytes <> chunks2 want <> wants2:
      check_step(UTF8.feed(state, bytes), want,
        next => check(chunks2, wants2, next, final))
    case _ _:
      False{}

def test(name: String, chunks: List<&2, List<&2, U32>>,
  wants: List<&2, String>, final: String) -> IO(Unit):
  IO.print(name ++ ": " ++ Bool.show(check(chunks, wants, UTF8.new(), final)))

def bytes_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> xt y <> yt:
      Bool.and(U32.is_eq(x, y), bytes_eq(xt, yt))
    case _ _:
      False{}

def test_encode(name: String, text: String, want: List<&2, U32>) -> IO(Unit):
  IO.print(name ++ ": " ++ Bool.show(bytes_eq(UTF8.encode(text), want)))

def main() -> IO(Unit):
  do IO<Unit>:
    test("empty", [], [], "")
    test("ASCII and NUL", [[0, 65]], [SCon{Chr{0}, "A"}], "")
    test("split characters", [[65, 195], [169, 226], [130], [],
      [172, 240, 159], [152], [128, 90]],
      ["A", "é", "", "", "€", "", "😀Z"], "")
    test("empty chunk preserves pending", [[226], [], [130], [], [172]],
      ["", "", "", "", "€"], "")
    test("EOF after lead", [[226]], [""], "�")
    test("EOF after continuation", [[65, 240, 159, 152]], ["A"], "�")
    test("ASCII interrupts sequence", [[226], [65]], ["", "�A"], "")
    test("prefix is one replacement", [[226, 130], [65]], ["", "�A"], "")
    test("new lead interrupts sequence", [[226], [195], [169]], ["", "�", "é"], "")
    test("invalid leads and stray continuations", [[255, 255, 128, 191]], ["����"], "")
    test("overlong two-byte sequence", [[192], [175]], ["�", "�"], "")
    test("overlong three-byte sequence", [[224], [128], [128]], ["", "��", "�"], "")
    test("surrogate", [[237], [160], [128]], ["", "��", "�"], "")
    test("overlong four-byte sequence", [[240], [143], [191, 191]], ["", "��", "��"], "")
    test("above Unicode maximum", [[244], [144], [128, 128]], ["", "��", "��"], "")
    test("scalar boundaries", [[194, 128, 223, 191, 224, 160, 128,
      237, 159, 191, 238, 128, 128, 239, 191, 191,
      240, 144, 128, 128, 244, 143, 191, 191]],
      [SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048}, SCon{Chr{55295},
        SCon{Chr{57344}, SCon{Chr{65535}, SCon{Chr{65536},
        SCon{Chr{1114111}, ""}}}}}}}}], "")
    test("BOM is preserved", [[239], [187], [191, 65]],
      ["", "", SCon{Chr{65279}, "A"}], "")
    test("out-of-range U32", [[256, 4294967295]], ["��"], "")
    test_encode("encode empty", "", [])
    test_encode("encode ASCII and NUL", SCon{Chr{0}, "A"}, [0, 65])
    test_encode("encode mixed widths", "Aé€😀", [65, 195, 169, 226, 130, 172, 240, 159, 152, 128])
    test_encode("encode boundaries",
      SCon{Chr{127}, SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048},
      SCon{Chr{55295}, SCon{Chr{57344}, SCon{Chr{65535}, SCon{Chr{65536},
      SCon{Chr{1114111}, ""}}}}}}}}},
      [127, 194, 128, 223, 191, 224, 160, 128, 237, 159, 191,
       238, 128, 128, 239, 191, 191, 240, 144, 128, 128, 244, 143, 191, 191])
    test_encode("encode non-scalars",
      SCon{Chr{55296}, SCon{Chr{57343}, SCon{Chr{1114112}, SCon{Chr{4294967295}, ""}}}},
      [239, 191, 189, 239, 191, 189, 239, 191, 189, 239, 191, 189])
    test_encode("encode BOM", SCon{Chr{65279}, "A"}, [239, 187, 191, 65])

#|empty: True
#|ASCII and NUL: True
#|split characters: True
#|empty chunk preserves pending: True
#|EOF after lead: True
#|EOF after continuation: True
#|ASCII interrupts sequence: True
#|prefix is one replacement: True
#|new lead interrupts sequence: True
#|invalid leads and stray continuations: True
#|overlong two-byte sequence: True
#|overlong three-byte sequence: True
#|surrogate: True
#|overlong four-byte sequence: True
#|above Unicode maximum: True
#|scalar boundaries: True
#|BOM is preserved: True
#|out-of-range U32: True
#|encode empty: True
#|encode ASCII and NUL: True
#|encode mixed widths: True
#|encode boundaries: True
#|encode non-scalars: True
#|encode BOM: True
