import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1242

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1228 : binChunk w2 1228 4 = 83409033426 := by decide +kernel
private theorem leaf1232 : binChunk w2 1232 4 = 85714655637 := by decide +kernel
private theorem leaf1236 : binChunk w2 1236 4 = 88080618453 := by decide +kernel
private theorem leaf1240 : binChunk w2 1240 4 = 90507880408 := by decide +kernel
private theorem leaf1244 : binChunk w2 1244 4 = 92996880168 := by decide +kernel
private theorem leaf1248 : binChunk w2 1248 4 = 95546444995 := by decide +kernel
private theorem leaf1252 : binChunk w2 1252 4 = 98154542085 := by decide +kernel
private theorem leaf1256 : binChunk w2 1256 4 = 100819492631 := by decide +kernel
private theorem leaf1260 : binChunk w2 1260 4 = 103539205957 := by decide +kernel
private theorem leaf1264 : binChunk w2 1264 4 = 106311161039 := by decide +kernel
private theorem leaf1268 : binChunk w2 1268 4 = 109133253805 := by decide +kernel
private theorem leaf1272 : binChunk w2 1272 4 = 112002960769 := by decide +kernel
private theorem leaf1276 : binChunk w2 1276 4 = 114917330661 := by decide +kernel
private theorem leaf1280 : binChunk w2 1280 4 = 117873841227 := by decide +kernel
private theorem leaf1284 : binChunk w2 1284 4 = 120869546005 := by decide +kernel
private theorem leaf1288 : binChunk w2 1288 4 = 123901066243 := by decide +kernel
private theorem batch2_1228_1236 : binChunk w2 1228 8 = 169123689063 :=
  binChunk_join (w := w2) (start := 1228) (left := 4) (right := 4) (x := 83409033426) (y := 85714655637) leaf1228 leaf1232
private theorem batch2_1236_1244 : binChunk w2 1236 8 = 178588498861 :=
  binChunk_join (w := w2) (start := 1236) (left := 4) (right := 4) (x := 88080618453) (y := 90507880408) leaf1236 leaf1240
private theorem batch2_1228_1244 : binChunk w2 1228 16 = 347712187924 :=
  binChunk_join (w := w2) (start := 1228) (left := 8) (right := 8) (x := 169123689063) (y := 178588498861) batch2_1228_1236 batch2_1236_1244
private theorem batch2_1244_1252 : binChunk w2 1244 8 = 188543325163 :=
  binChunk_join (w := w2) (start := 1244) (left := 4) (right := 4) (x := 92996880168) (y := 95546444995) leaf1244 leaf1248
private theorem batch2_1252_1260 : binChunk w2 1252 8 = 198974034716 :=
  binChunk_join (w := w2) (start := 1252) (left := 4) (right := 4) (x := 98154542085) (y := 100819492631) leaf1252 leaf1256
private theorem batch2_1244_1260 : binChunk w2 1244 16 = 387517359879 :=
  binChunk_join (w := w2) (start := 1244) (left := 8) (right := 8) (x := 188543325163) (y := 198974034716) batch2_1244_1252 batch2_1252_1260
private theorem batch2_1228_1260 : binChunk w2 1228 32 = 735229547803 :=
  binChunk_join (w := w2) (start := 1228) (left := 16) (right := 16) (x := 347712187924) (y := 387517359879) batch2_1228_1244 batch2_1244_1260
private theorem batch2_1260_1268 : binChunk w2 1260 8 = 209850366996 :=
  binChunk_join (w := w2) (start := 1260) (left := 4) (right := 4) (x := 103539205957) (y := 106311161039) leaf1260 leaf1264
private theorem batch2_1268_1276 : binChunk w2 1268 8 = 221136214574 :=
  binChunk_join (w := w2) (start := 1268) (left := 4) (right := 4) (x := 109133253805) (y := 112002960769) leaf1268 leaf1272
private theorem batch2_1260_1276 : binChunk w2 1260 16 = 430986581570 :=
  binChunk_join (w := w2) (start := 1260) (left := 8) (right := 8) (x := 209850366996) (y := 221136214574) batch2_1260_1268 batch2_1268_1276
private theorem batch2_1276_1284 : binChunk w2 1276 8 = 232791171888 :=
  binChunk_join (w := w2) (start := 1276) (left := 4) (right := 4) (x := 114917330661) (y := 117873841227) leaf1276 leaf1280
private theorem batch2_1284_1292 : binChunk w2 1284 8 = 244770612248 :=
  binChunk_join (w := w2) (start := 1284) (left := 4) (right := 4) (x := 120869546005) (y := 123901066243) leaf1284 leaf1288
private theorem batch2_1276_1292 : binChunk w2 1276 16 = 477561784136 :=
  binChunk_join (w := w2) (start := 1276) (left := 8) (right := 8) (x := 232791171888) (y := 244770612248) batch2_1276_1284 batch2_1284_1292
private theorem batch2_1260_1292 : binChunk w2 1260 32 = 908548365706 :=
  binChunk_join (w := w2) (start := 1260) (left := 16) (right := 16) (x := 430986581570) (y := 477561784136) batch2_1260_1276 batch2_1276_1292
theorem batch2_1228_1292 : binChunk w2 1228 64 = 1643777913509 :=
  binChunk_join (w := w2) (start := 1228) (left := 32) (right := 32) (x := 735229547803) (y := 908548365706) batch2_1228_1260 batch2_1260_1292

end Low48PrimaryPivot
