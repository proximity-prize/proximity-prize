import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thinwide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top8
private abbrev P := PaidBatch .two6thinwide 8
private def p0 : List P := [⟨unpack [56610152481,48122140725,26781245663,26513079519,17621162251,17554320651,4702978315,4535201127], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4434539879,139574631,89309551,55756143,8846809463,4568753527,5424508,5424512], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [22200708,106083723,72530315,22199691,22200712,22200716,13359938963,8947535251], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [38976912,38976916,38976920,55753116,72461731,55751075,55753120,72529316], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [72529320,72529324,89305520,4468087223,173121975,5352884,89305524,89236923], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [38906299,5352888,89305528,5352892,89305532,106081728,5351876,106081732], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [5351880,106081736,5351884,106081740,21681168851,206600657,22128080,106081744], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [22128084,106081748,22128088,106081752,22128092,106081756,106011107,38903267], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [38904288,106081760,22127076,122857956,4400975339,106010091,22127080,122857960], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [38903276,122857964,38903280,122857968,38903284,122857972,38903288,122857976], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [55679484,122857980,55679488,122857984], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 128 24 8 = true := by decide +kernel
private theorem i32 : checks ts 128 32 8 = true := by decide +kernel
private theorem i40 : checks ts 128 40 8 = true := by decide +kernel
private theorem i48 : checks ts 128 48 2 = true := by decide +kernel
private theorem rows : checks ts 128 24 26 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 10 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .two6thinwide 9
private def p0 : List P := [⟨unpack [48070552613,43860728885,22385618159,22167782639,17638137107,17470435603,391234833,4518424923], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4434540891,139575643,22201715,5424504,106084735,55754111,22200703,5424508], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8813387139,4451314051,5424512,22200708,22200712,38976908,89239955,72529299], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [38976912,9048196503,8897270167,38976916,55753112,55753116,55753120,72529316], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [106015147,38907307,22196651,72529320,72529324,89305520,5352884,89305524], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [223452603,156344763,89236923,5352888,89305528,5352892,89305532,106081728], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [5351876,106081732,21714988491,5351880,106081736,5351884,106081740,22128080], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [106081744,22128084,106081748,22128088,106081752,22128092,106081756,4417753571], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [122788323,38904288,106081760,22127076,122857956,22127080,122857960,22127084], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [122857964,38903280,122857968,38903284,122857972,38903288,122857976,38903292], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [122857980,5345795,5346819,55679488,122857984], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 128 27 8 = true := by decide +kernel
private theorem i35 : checks ts 128 35 8 = true := by decide +kernel
private theorem i43 : checks ts 128 43 7 = true := by decide +kernel
private theorem rows : checks ts 128 27 23 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 11 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

end Compact50PriceTableTwo6thinwide
