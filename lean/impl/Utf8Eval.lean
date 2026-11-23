-- Sanity test by evaluation: RefDecoder on the decodes_examples cases (and one more),
-- each under several buffer splits. A mismatch is a build error.
import Utf8Ref
open Utf8Pure
def runSplit (bufs : List (List UInt8)) : Text := decoded RefDecoder bufs
def splits (l : List UInt8) : List (List (List UInt8)) :=
  [[l], l.map (fun b => [b]), [[], l, []]] ++ (List.range (l.length+1)).map (fun k => [l.take k, l.drop k])
def cases : List (List UInt8 × Text) :=
  let r := '\uFFFD'
  [([], []), ([65, 66], ['A', 'B']), ([194, 169], ['©']), ([194, 65], [r, 'A']),
   ([192, 128], [r, r]), ([194], [r]), ([194, 194, 169], [r, '©']),
   ([72, 194, 169, 255], ['H', '©', r]), ([226, 130, 172], ['€']),
   ([240, 159, 152, 128], ['😀']), ([226, 130], [r]), ([226, 130, 65], [r, 'A']),
   ([240, 159, 152], [r]), ([240, 159, 152, 65], [r, 'A']),
   ([224, 128, 128], [r, r, r]), ([237, 160, 128], [r, r, r]),
   ([244, 144, 128, 128], [r, r, r, r]),
   ([0xEF, 0xBF, 0xBD, 0xF4, 0x8F, 0xBF, 0xBF], [r, Char.ofNat 0x10FFFF])]
#guard cases.all (fun (i, o) => (splits i).all (fun s => runSplit s == o))

