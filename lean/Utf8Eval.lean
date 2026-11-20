-- Sanity test by evaluation: RefDecoder on the decodes_examples cases (and one more),
-- each under several buffer splits.  Prints `true`.
import Utf8Ref
open Utf8Pure
def runSplit (bufs : List (List UInt8)) : Text := decoded RefDecoder bufs
def splits (l : List UInt8) : List (List (List UInt8)) :=
  [[l], l.map (fun b => [b]), [[], l, []]] ++ (List.range (l.length+1)).map (fun k => [l.take k, l.drop k])
def cases : List (List UInt8 × Text) :=
 [([], []), ([65,66],[65,66]), ([194,169],[169]), ([194,65],[0xFFFD,65]), ([192,128],[0xFFFD,0xFFFD]),
  ([194],[0xFFFD]), ([194,194,169],[0xFFFD,169]), ([72,194,169,255],[72,169,0xFFFD]), ([226,130,172],[8364]),
  ([240,159,152,128],[128512]), ([226,130],[0xFFFD]), ([226,130,65],[0xFFFD,65]), ([240,159,152],[0xFFFD]),
  ([240,159,152,65],[0xFFFD,65]), ([224,128,128],[0xFFFD,0xFFFD,0xFFFD]), ([237,160,128],[0xFFFD,0xFFFD,0xFFFD]),
  ([244,144,128,128],[0xFFFD,0xFFFD,0xFFFD,0xFFFD]), ([0xEF,0xBF,0xBD,0xF4,0x8F,0xBF,0xBF],[0xFFFD,0x10FFFF])]
#eval cases.all (fun (i, o) => (splits i).all (fun s => runSplit s == o))

