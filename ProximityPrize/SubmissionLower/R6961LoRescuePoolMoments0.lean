import ProximityPrize.SubmissionLower.HighCore82258Source

set_option Elab.async false

-- merged module R6963LoPoolFast
section Merged_R6963LoPoolFast
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6963.Lo.PoolFast
open P1_7_1_3
def mn (a b : ℕ) : ℕ := bif Nat.ble a b then a else b
def mx (a b : ℕ) : ℕ := bif Nat.ble a b then b else a
def lowF (J t : ℕ) : ℕ := Nat.sub J t
def highF (B J t : ℕ) : ℕ := mn J (Nat.sub (Nat.sub (Nat.add B (Nat.mul 2 J)) 1) t)
def widthF (B J t : ℕ) : ℕ := Nat.sub (Nat.add (highF B J t) 1) (lowF J t)
def edgeF (B J t : ℕ) : ℕ := Nat.sub (Nat.add B (Nat.mul 2 J)) t
def peakF (B J t : ℕ) : ℕ := mn (widthF B J t) (Nat.div (Nat.add (Nat.sub (edgeF B J t) (lowF J t)) 1) 2)
def productSum6F (n a b : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.mul (Nat.mul (Nat.mul 6 n) a) b) (Nat.mul (Nat.mul (Nat.mul 3 (Nat.add a b)) n) (Nat.sub n 1)))
    (Nat.mul (Nat.mul n (Nat.sub n 1)) (Nat.add (Nat.mul 2 (Nat.sub n 1)) 1))
def rampCount6F (N a : ℕ) : ℕ := Nat.mul (Nat.mul 3 (Nat.sub N a)) (Nat.add (Nat.sub N a) 1)
def rampWeight6F (N a : ℕ) : ℕ := productSum6F (Nat.sub N a) a 1
def rampExcess6F (N k a : ℕ) : ℕ :=
  productSum6F (Nat.sub N (mx (Nat.add k 1) a)) (Nat.sub (mx (Nat.add k 1) a) k) (Nat.sub (Nat.add (mx (Nat.add k 1) a) 1) a)
def pivotVolume6F (B J t : ℕ) (stat : ℕ → ℕ) : ℕ :=
  Nat.sub (Nat.add (stat (lowF J t)) (stat (Nat.add (edgeF B J t) 1)))
    (Nat.add (stat (Nat.add (lowF J t) (peakF B J t))) (stat (Nat.sub (Nat.add (edgeF B J t) 1) (peakF B J t))))
def columnVolume6F (B J t : ℕ) (stat : ℕ → ℕ) : ℕ :=
  Nat.sub (stat (lowF J t)) (stat (Nat.add (lowF J t) (widthF B J t)))
def pivotRank6F (B J t : ℕ) : ℕ := pivotVolume6F B J t (rampCount6F (Nat.add B 1))
def pivotWeight6F (B J t : ℕ) : ℕ := pivotVolume6F B J t (rampWeight6F (Nat.add B 1))
def excess6F (B J t k : ℕ) : ℕ := columnVolume6F B J t (rampExcess6F (Nat.add B 1) k)
def triangularCutF (omitted : ℕ) (fuel lo hi : ℕ) : ℕ := triangularCut omitted fuel lo hi
def thresholdF (B J t : ℕ) : ℕ :=
  bif Nat.ble (Nat.div (pivotRank6F B J t) 6) (Nat.mul (widthF B J t) (Nat.sub (Nat.add B 1) (highF B J t)))
  then Nat.sub B (Nat.div (Nat.sub (Nat.div (pivotRank6F B J t) 6) 1) (widthF B J t))
  else mn B (Nat.add (lowF J t) (triangularCutF
      (Nat.sub (Nat.div (columnVolume6F B J t (rampCount6F (Nat.add B 1))) 6) (Nat.div (pivotRank6F B J t) 6)) 16 0 (Nat.add (widthF B J t) 1)))
def offsetEstimateF (B J t : ℕ) : ℕ :=
  Nat.div (Nat.sub (Nat.add (Nat.mul (pivotRank6F B J t) (thresholdF B J t)) (excess6F B J t (thresholdF B J t))) (pivotWeight6F B J t)) 6
def evaluateF (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.add (evaluateF f n) (f n)
def blockEstimateF (B J start length : ℕ) : ℕ := evaluateF (fun i => offsetEstimateF B J (Nat.add start i)) length

theorem mn_eq (a b : ℕ) : mn a b = min a b := by
  unfold mn; by_cases h : a ≤ b <;> simp [h, Nat.ble_eq] <;> omega
theorem mx_eq (a b : ℕ) : mx a b = max a b := by
  unfold mx; by_cases h : a ≤ b <;> simp [h, Nat.ble_eq] <;> omega
theorem bleC {α : Type} (a b : ℕ) (x y : α) : (bif Nat.ble a b then x else y) = if a ≤ b then x else y := by
  by_cases h : a ≤ b <;> simp [h, Nat.ble_eq]
theorem bltC {α : Type} (a b : ℕ) (x y : α) : (bif Nat.blt a b then x else y) = if a < b then x else y := by
  by_cases h : a < b <;> simp [h, Nat.blt_eq]

theorem lowF_eq : lowF = low := rfl
theorem edgeF_eq : edgeF = edge := rfl
theorem highF_eq : highF = high := by
  funext B J t; unfold highF high; rw [mn_eq]
  all_goals rfl
theorem widthF_eq : widthF = width := by
  funext B J t; unfold widthF width; rw [highF_eq, lowF_eq]
  all_goals rfl
theorem peakF_eq : peakF = peak := by
  funext B J t; unfold peakF peak; rw [mn_eq, widthF_eq, edgeF_eq, lowF_eq]
  all_goals rfl
theorem productSum6F_eq : productSum6F = productSum6 := rfl
theorem rampCount6F_eq : rampCount6F = rampCount6 := rfl
theorem rampWeight6F_eq : rampWeight6F = rampWeight6 := by
  funext N a; unfold rampWeight6F rampWeight6; rw [productSum6F_eq]
  all_goals rfl
theorem rampExcess6F_eq : rampExcess6F = rampExcess6 := by
  funext N k a; unfold rampExcess6F rampExcess6; simp only [mx_eq, productSum6F_eq]
  all_goals rfl
theorem pivotVolume6F_eq : pivotVolume6F = pivotVolume6 := by
  funext B J t stat; unfold pivotVolume6F pivotVolume6; rw [lowF_eq, edgeF_eq, peakF_eq]
  all_goals rfl
theorem columnVolume6F_eq : columnVolume6F = columnVolume6 := by
  funext B J t stat; unfold columnVolume6F columnVolume6; rw [lowF_eq, widthF_eq]
  all_goals rfl
theorem pivotRank6F_eq : pivotRank6F = pivotRank6 := by
  funext B J t; unfold pivotRank6F pivotRank6; rw [pivotVolume6F_eq, rampCount6F_eq]
  all_goals rfl
theorem pivotWeight6F_eq : pivotWeight6F = pivotWeight6 := by
  funext B J t; unfold pivotWeight6F pivotWeight6; rw [pivotVolume6F_eq, rampWeight6F_eq]
  all_goals rfl
theorem excess6F_eq : excess6F = excess6 := by
  funext B J t k; unfold excess6F excess6; rw [columnVolume6F_eq, rampExcess6F_eq]
  all_goals rfl
theorem triangularCutF_eq (omitted fuel lo hi : ℕ) :
    triangularCutF omitted fuel lo hi = triangularCut omitted fuel lo hi := rfl
theorem thresholdF_eq : thresholdF = threshold := by
  funext B J t
  unfold thresholdF threshold
  rw [bleC, pivotRank6F_eq, widthF_eq, highF_eq, lowF_eq, columnVolume6F_eq, rampCount6F_eq]
  simp only [triangularCutF_eq, mn_eq]
  rfl
theorem offsetEstimateF_eq : offsetEstimateF = offsetEstimate := by
  funext B J t
  unfold offsetEstimateF offsetEstimate
  rw [thresholdF_eq, pivotRank6F_eq, excess6F_eq, pivotWeight6F_eq]
  all_goals rfl
theorem evaluateF_eq (f : ℕ → ℕ) (n : ℕ) : evaluateF f n = evaluate f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.add (evaluateF f n) (f n) = evaluate f n + f n
    rw [ih]
    all_goals rfl
theorem blockEstimateF_eq (B J start length : ℕ) :
    blockEstimateF B J start length = blockEstimate B J start length := by
  unfold blockEstimateF blockEstimate
  rw [evaluateF_eq]
  have : (fun i => offsetEstimateF B J (Nat.add start i)) = fun i => offsetEstimate B J (start + i) := by
    funext i; rw [offsetEstimateF_eq]; rfl
  rw [this]

end Lower6963.Lo.PoolFast

end Merged_R6963LoPoolFast

-- merged module R6961LoRescuePoolMoments0
section Merged_R6961LoRescuePoolMoments0

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescuePoolMoments
open P1_7_1_3 (blockEstimate block_append momentEstimate)

private theorem moment_584_129_part0 :
    blockEstimate 584 129 129 128 = 174855200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_584_129_part1 :
    blockEstimate 584 129 257 128 = 813275840 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_584_129_part2 :
    blockEstimate 584 129 385 128 = 1104009920 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_584_129_part3 :
    blockEstimate 584 129 513 128 = 855632022 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_584_129_part4 :
    blockEstimate 584 129 641 128 = 316790335 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_584_129_part5 :
    blockEstimate 584 129 769 73 = 18961145 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_584_129_join0 :
    blockEstimate 584 129 257 256 = 1917285760 :=
  block_append moment_584_129_part1 moment_584_129_part2 rfl rfl rfl
private theorem moment_584_129_join1 :
    blockEstimate 584 129 129 384 = 2092140960 :=
  block_append moment_584_129_part0 moment_584_129_join0 rfl rfl rfl
private theorem moment_584_129_join2 :
    blockEstimate 584 129 641 201 = 335751480 :=
  block_append moment_584_129_part4 moment_584_129_part5 rfl rfl rfl
private theorem moment_584_129_join3 :
    blockEstimate 584 129 513 329 = 1191383502 :=
  block_append moment_584_129_part3 moment_584_129_join2 rfl rfl rfl
private theorem moment_584_129_join4 :
    blockEstimate 584 129 129 713 = 3283524462 :=
  block_append moment_584_129_join1 moment_584_129_join3 rfl rfl rfl

theorem moment_584_129 : momentEstimate 584 129 = 3283524462 := moment_584_129_join4

private theorem moment_862_190_part0 :
    blockEstimate 862 190 190 128 = 274312480 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_part1 :
    blockEstimate 862 190 318 128 = 1593432017 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_part2 :
    blockEstimate 862 190 446 128 = 2957437888 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_part3 :
    blockEstimate 862 190 574 128 = 3548883904 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_part4 :
    blockEstimate 862 190 702 128 = 3339217856 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_part5 :
    blockEstimate 862 190 830 128 = 2372343926 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_part6 :
    blockEstimate 862 190 958 128 = 1145634375 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_part7 :
    blockEstimate 862 190 1086 128 = 255228960 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_part8 :
    blockEstimate 862 190 1214 28 = 1813735 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_862_190_join0 :
    blockEstimate 862 190 190 256 = 1867744497 :=
  block_append moment_862_190_part0 moment_862_190_part1 rfl rfl rfl
private theorem moment_862_190_join1 :
    blockEstimate 862 190 446 256 = 6506321792 :=
  block_append moment_862_190_part2 moment_862_190_part3 rfl rfl rfl
private theorem moment_862_190_join2 :
    blockEstimate 862 190 190 512 = 8374066289 :=
  block_append moment_862_190_join0 moment_862_190_join1 rfl rfl rfl
private theorem moment_862_190_join3 :
    blockEstimate 862 190 702 256 = 5711561782 :=
  block_append moment_862_190_part4 moment_862_190_part5 rfl rfl rfl
private theorem moment_862_190_join4 :
    blockEstimate 862 190 1086 156 = 257042695 :=
  block_append moment_862_190_part7 moment_862_190_part8 rfl rfl rfl
private theorem moment_862_190_join5 :
    blockEstimate 862 190 958 284 = 1402677070 :=
  block_append moment_862_190_part6 moment_862_190_join4 rfl rfl rfl
private theorem moment_862_190_join6 :
    blockEstimate 862 190 702 540 = 7114238852 :=
  block_append moment_862_190_join3 moment_862_190_join5 rfl rfl rfl
private theorem moment_862_190_join7 :
    blockEstimate 862 190 190 1052 = 15488305141 :=
  block_append moment_862_190_join2 moment_862_190_join6 rfl rfl rfl

theorem moment_862_190 : momentEstimate 862 190 = 15488305141 := moment_862_190_join7

private theorem moment_1251_277_part0 :
    blockEstimate 1251 277 277 128 = 413481120 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part1 :
    blockEstimate 1251 277 405 128 = 2584610976 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part2 :
    blockEstimate 1251 277 533 128 = 5985606201 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part3 :
    blockEstimate 1251 277 661 128 = 8814859584 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part4 :
    blockEstimate 1251 277 789 128 = 10479621440 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part5 :
    blockEstimate 1251 277 917 128 = 10978366784 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part6 :
    blockEstimate 1251 277 1045 128 = 10311095616 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part7 :
    blockEstimate 1251 277 1173 128 = 8485878907 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part8 :
    blockEstimate 1251 277 1301 128 = 5891614618 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part9 :
    blockEstimate 1251 277 1429 128 = 3328850485 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part10 :
    blockEstimate 1251 277 1557 128 = 1290861280 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_part11 :
    blockEstimate 1251 277 1685 120 = 178654970 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1251_277_join0 :
    blockEstimate 1251 277 405 256 = 8570217177 :=
  block_append moment_1251_277_part1 moment_1251_277_part2 rfl rfl rfl
private theorem moment_1251_277_join1 :
    blockEstimate 1251 277 277 384 = 8983698297 :=
  block_append moment_1251_277_part0 moment_1251_277_join0 rfl rfl rfl
private theorem moment_1251_277_join2 :
    blockEstimate 1251 277 789 256 = 21457988224 :=
  block_append moment_1251_277_part4 moment_1251_277_part5 rfl rfl rfl
private theorem moment_1251_277_join3 :
    blockEstimate 1251 277 661 384 = 30272847808 :=
  block_append moment_1251_277_part3 moment_1251_277_join2 rfl rfl rfl
private theorem moment_1251_277_join4 :
    blockEstimate 1251 277 277 768 = 39256546105 :=
  block_append moment_1251_277_join1 moment_1251_277_join3 rfl rfl rfl
private theorem moment_1251_277_join5 :
    blockEstimate 1251 277 1173 256 = 14377493525 :=
  block_append moment_1251_277_part7 moment_1251_277_part8 rfl rfl rfl
private theorem moment_1251_277_join6 :
    blockEstimate 1251 277 1045 384 = 24688589141 :=
  block_append moment_1251_277_part6 moment_1251_277_join5 rfl rfl rfl
private theorem moment_1251_277_join7 :
    blockEstimate 1251 277 1557 248 = 1469516250 :=
  block_append moment_1251_277_part10 moment_1251_277_part11 rfl rfl rfl
private theorem moment_1251_277_join8 :
    blockEstimate 1251 277 1429 376 = 4798366735 :=
  block_append moment_1251_277_part9 moment_1251_277_join7 rfl rfl rfl
private theorem moment_1251_277_join9 :
    blockEstimate 1251 277 1045 760 = 29486955876 :=
  block_append moment_1251_277_join6 moment_1251_277_join8 rfl rfl rfl
private theorem moment_1251_277_join10 :
    blockEstimate 1251 277 277 1528 = 68743501981 :=
  block_append moment_1251_277_join4 moment_1251_277_join9 rfl rfl rfl

theorem moment_1251_277 : momentEstimate 1251 277 = 68743501981 := moment_1251_277_join10

private theorem moment_1669_369_part0 :
    blockEstimate 1669 369 369 128 = 563024800 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part1 :
    blockEstimate 1669 369 497 128 = 3617612704 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part2 :
    blockEstimate 1669 369 625 128 = 8960520036 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part3 :
    blockEstimate 1669 369 753 128 = 15207805120 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part4 :
    blockEstimate 1669 369 881 128 = 20236300480 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part5 :
    blockEstimate 1669 369 1009 128 = 23712903360 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part6 :
    blockEstimate 1669 369 1137 128 = 25637613760 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part7 :
    blockEstimate 1669 369 1265 128 = 26010431680 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part8 :
    blockEstimate 1669 369 1393 128 = 24831357120 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part9 :
    blockEstimate 1669 369 1521 128 = 22100390080 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part10 :
    blockEstimate 1669 369 1649 128 = 17929292750 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part11 :
    blockEstimate 1669 369 1777 128 = 13177480625 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part12 :
    blockEstimate 1669 369 1905 128 = 8590923095 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part13 :
    blockEstimate 1669 369 2033 128 = 4629444117 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part14 :
    blockEstimate 1669 369 2161 128 = 1734188816 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_part15 :
    blockEstimate 1669 369 2289 118 = 229544965 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_1669_369_join0 :
    blockEstimate 1669 369 369 256 = 4180637504 :=
  block_append moment_1669_369_part0 moment_1669_369_part1 rfl rfl rfl
private theorem moment_1669_369_join1 :
    blockEstimate 1669 369 625 256 = 24168325156 :=
  block_append moment_1669_369_part2 moment_1669_369_part3 rfl rfl rfl
private theorem moment_1669_369_join2 :
    blockEstimate 1669 369 369 512 = 28348962660 :=
  block_append moment_1669_369_join0 moment_1669_369_join1 rfl rfl rfl
private theorem moment_1669_369_join3 :
    blockEstimate 1669 369 881 256 = 43949203840 :=
  block_append moment_1669_369_part4 moment_1669_369_part5 rfl rfl rfl
private theorem moment_1669_369_join4 :
    blockEstimate 1669 369 1137 256 = 51648045440 :=
  block_append moment_1669_369_part6 moment_1669_369_part7 rfl rfl rfl
private theorem moment_1669_369_join5 :
    blockEstimate 1669 369 881 512 = 95597249280 :=
  block_append moment_1669_369_join3 moment_1669_369_join4 rfl rfl rfl
private theorem moment_1669_369_join6 :
    blockEstimate 1669 369 369 1024 = 123946211940 :=
  block_append moment_1669_369_join2 moment_1669_369_join5 rfl rfl rfl
private theorem moment_1669_369_join7 :
    blockEstimate 1669 369 1393 256 = 46931747200 :=
  block_append moment_1669_369_part8 moment_1669_369_part9 rfl rfl rfl
private theorem moment_1669_369_join8 :
    blockEstimate 1669 369 1649 256 = 31106773375 :=
  block_append moment_1669_369_part10 moment_1669_369_part11 rfl rfl rfl
private theorem moment_1669_369_join9 :
    blockEstimate 1669 369 1393 512 = 78038520575 :=
  block_append moment_1669_369_join7 moment_1669_369_join8 rfl rfl rfl
private theorem moment_1669_369_join10 :
    blockEstimate 1669 369 1905 256 = 13220367212 :=
  block_append moment_1669_369_part12 moment_1669_369_part13 rfl rfl rfl
private theorem moment_1669_369_join11 :
    blockEstimate 1669 369 2161 246 = 1963733781 :=
  block_append moment_1669_369_part14 moment_1669_369_part15 rfl rfl rfl
private theorem moment_1669_369_join12 :
    blockEstimate 1669 369 1905 502 = 15184100993 :=
  block_append moment_1669_369_join10 moment_1669_369_join11 rfl rfl rfl
private theorem moment_1669_369_join13 :
    blockEstimate 1669 369 1393 1014 = 93222621568 :=
  block_append moment_1669_369_join9 moment_1669_369_join12 rfl rfl rfl
private theorem moment_1669_369_join14 :
    blockEstimate 1669 369 369 2038 = 217168833508 :=
  block_append moment_1669_369_join6 moment_1669_369_join13 rfl rfl rfl

theorem moment_1669_369 : momentEstimate 1669 369 = 217168833508 := moment_1669_369_join14

private theorem moment_2225_492_part0 :
    blockEstimate 2225 492 492 128 = 761939360 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part1 :
    blockEstimate 2225 492 620 128 = 4991653280 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part2 :
    blockEstimate 2225 492 748 128 = 12676425120 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part3 :
    blockEstimate 2225 492 876 128 = 23008662907 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part4 :
    blockEstimate 2225 492 1004 128 = 34315608128 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part5 :
    blockEstimate 2225 492 1132 128 = 43935686720 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part6 :
    blockEstimate 2225 492 1260 128 = 51487973440 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part7 :
    blockEstimate 2225 492 1388 128 = 56972468288 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part8 :
    blockEstimate 2225 492 1516 128 = 60389171264 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part9 :
    blockEstimate 2225 492 1644 128 = 61738082368 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part10 :
    blockEstimate 2225 492 1772 128 = 61019201600 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part11 :
    blockEstimate 2225 492 1900 128 = 58232528960 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part12 :
    blockEstimate 2225 492 2028 128 = 53378064448 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part13 :
    blockEstimate 2225 492 2156 128 = 46478735551 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part14 :
    blockEstimate 2225 492 2284 128 = 38237146739 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part15 :
    blockEstimate 2225 492 2412 128 = 29749278062 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part16 :
    blockEstimate 2225 492 2540 128 = 21573668590 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part17 :
    blockEstimate 2225 492 2668 128 = 14168145664 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part18 :
    blockEstimate 2225 492 2796 128 = 7959681296 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part19 :
    blockEstimate 2225 492 2924 128 = 3385724176 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part20 :
    blockEstimate 2225 492 3052 128 = 708837648 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_part21 :
    blockEstimate 2225 492 3180 29 = 5220452 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_2225_492_join0 :
    blockEstimate 2225 492 492 256 = 5753592640 :=
  block_append moment_2225_492_part0 moment_2225_492_part1 rfl rfl rfl
private theorem moment_2225_492_join1 :
    blockEstimate 2225 492 876 256 = 57324271035 :=
  block_append moment_2225_492_part3 moment_2225_492_part4 rfl rfl rfl
private theorem moment_2225_492_join2 :
    blockEstimate 2225 492 748 384 = 70000696155 :=
  block_append moment_2225_492_part2 moment_2225_492_join1 rfl rfl rfl
private theorem moment_2225_492_join3 :
    blockEstimate 2225 492 492 640 = 75754288795 :=
  block_append moment_2225_492_join0 moment_2225_492_join2 rfl rfl rfl
private theorem moment_2225_492_join4 :
    blockEstimate 2225 492 1260 256 = 108460441728 :=
  block_append moment_2225_492_part6 moment_2225_492_part7 rfl rfl rfl
private theorem moment_2225_492_join5 :
    blockEstimate 2225 492 1132 384 = 152396128448 :=
  block_append moment_2225_492_part5 moment_2225_492_join4 rfl rfl rfl
private theorem moment_2225_492_join6 :
    blockEstimate 2225 492 1644 256 = 122757283968 :=
  block_append moment_2225_492_part9 moment_2225_492_part10 rfl rfl rfl
private theorem moment_2225_492_join7 :
    blockEstimate 2225 492 1516 384 = 183146455232 :=
  block_append moment_2225_492_part8 moment_2225_492_join6 rfl rfl rfl
private theorem moment_2225_492_join8 :
    blockEstimate 2225 492 1132 768 = 335542583680 :=
  block_append moment_2225_492_join5 moment_2225_492_join7 rfl rfl rfl
private theorem moment_2225_492_join9 :
    blockEstimate 2225 492 492 1408 = 411296872475 :=
  block_append moment_2225_492_join3 moment_2225_492_join8 rfl rfl rfl
private theorem moment_2225_492_join10 :
    blockEstimate 2225 492 1900 256 = 111610593408 :=
  block_append moment_2225_492_part11 moment_2225_492_part12 rfl rfl rfl
private theorem moment_2225_492_join11 :
    blockEstimate 2225 492 2284 256 = 67986424801 :=
  block_append moment_2225_492_part14 moment_2225_492_part15 rfl rfl rfl
private theorem moment_2225_492_join12 :
    blockEstimate 2225 492 2156 384 = 114465160352 :=
  block_append moment_2225_492_part13 moment_2225_492_join11 rfl rfl rfl
private theorem moment_2225_492_join13 :
    blockEstimate 2225 492 1900 640 = 226075753760 :=
  block_append moment_2225_492_join10 moment_2225_492_join12 rfl rfl rfl
private theorem moment_2225_492_join14 :
    blockEstimate 2225 492 2668 256 = 22127826960 :=
  block_append moment_2225_492_part17 moment_2225_492_part18 rfl rfl rfl
private theorem moment_2225_492_join15 :
    blockEstimate 2225 492 2540 384 = 43701495550 :=
  block_append moment_2225_492_part16 moment_2225_492_join14 rfl rfl rfl
private theorem moment_2225_492_join16 :
    blockEstimate 2225 492 3052 157 = 714058100 :=
  block_append moment_2225_492_part20 moment_2225_492_part21 rfl rfl rfl
private theorem moment_2225_492_join17 :
    blockEstimate 2225 492 2924 285 = 4099782276 :=
  block_append moment_2225_492_part19 moment_2225_492_join16 rfl rfl rfl
private theorem moment_2225_492_join18 :
    blockEstimate 2225 492 2540 669 = 47801277826 :=
  block_append moment_2225_492_join15 moment_2225_492_join17 rfl rfl rfl
private theorem moment_2225_492_join19 :
    blockEstimate 2225 492 1900 1309 = 273877031586 :=
  block_append moment_2225_492_join13 moment_2225_492_join18 rfl rfl rfl
private theorem moment_2225_492_join20 :
    blockEstimate 2225 492 492 2717 = 685173904061 :=
  block_append moment_2225_492_join9 moment_2225_492_join19 rfl rfl rfl

theorem moment_2225_492 : momentEstimate 2225 492 = 685173904061 := moment_2225_492_join20

private theorem moment_3060_677_part0 :
    blockEstimate 3060 677 677 128 = 1060668960 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part1 :
    blockEstimate 3060 677 805 128 = 7055185440 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part2 :
    blockEstimate 3060 677 933 128 = 18255881760 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part3 :
    blockEstimate 3060 677 1061 128 = 33857451552 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part4 :
    blockEstimate 3060 677 1189 128 = 53054588448 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part5 :
    blockEstimate 3060 677 1317 128 = 74751236985 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part6 :
    blockEstimate 3060 677 1445 128 = 95420201280 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part7 :
    blockEstimate 3060 677 1573 128 = 113265768768 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part8 :
    blockEstimate 3060 677 1701 128 = 128267598144 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part9 :
    blockEstimate 3060 677 1829 128 = 140425689408 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part10 :
    blockEstimate 3060 677 1957 128 = 149740042560 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part11 :
    blockEstimate 3060 677 2085 128 = 156210657600 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part12 :
    blockEstimate 3060 677 2213 128 = 159837534528 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part13 :
    blockEstimate 3060 677 2341 128 = 160620673344 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part14 :
    blockEstimate 3060 677 2469 128 = 158560074048 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part15 :
    blockEstimate 3060 677 2597 128 = 153655736640 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part16 :
    blockEstimate 3060 677 2725 128 = 145907661120 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part17 :
    blockEstimate 3060 677 2853 128 = 135315847488 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part18 :
    blockEstimate 3060 677 2981 128 = 121898078744 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part19 :
    blockEstimate 3060 677 3109 128 = 106469415077 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part20 :
    blockEstimate 3060 677 3237 128 = 90436086306 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part21 :
    blockEstimate 3060 677 3365 128 = 74414505319 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part22 :
    blockEstimate 3060 677 3493 128 = 58917936281 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part23 :
    blockEstimate 3060 677 3621 128 = 44420548265 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part24 :
    blockEstimate 3060 677 3749 128 = 31271660336 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part25 :
    blockEstimate 3060 677 3877 128 = 20014769968 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part26 :
    blockEstimate 3060 677 4005 128 = 11035058992 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part27 :
    blockEstimate 3060 677 4133 128 = 4584185648 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part28 :
    blockEstimate 3060 677 4261 128 = 913808176 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_part29 :
    blockEstimate 3060 677 4389 25 = 4716691 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_3060_677_join0 :
    blockEstimate 3060 677 805 256 = 25311067200 :=
  block_append moment_3060_677_part1 moment_3060_677_part2 rfl rfl rfl
private theorem moment_3060_677_join1 :
    blockEstimate 3060 677 677 384 = 26371736160 :=
  block_append moment_3060_677_part0 moment_3060_677_join0 rfl rfl rfl
private theorem moment_3060_677_join2 :
    blockEstimate 3060 677 1061 256 = 86912040000 :=
  block_append moment_3060_677_part3 moment_3060_677_part4 rfl rfl rfl
private theorem moment_3060_677_join3 :
    blockEstimate 3060 677 1317 256 = 170171438265 :=
  block_append moment_3060_677_part5 moment_3060_677_part6 rfl rfl rfl
private theorem moment_3060_677_join4 :
    blockEstimate 3060 677 1061 512 = 257083478265 :=
  block_append moment_3060_677_join2 moment_3060_677_join3 rfl rfl rfl
private theorem moment_3060_677_join5 :
    blockEstimate 3060 677 677 896 = 283455214425 :=
  block_append moment_3060_677_join1 moment_3060_677_join4 rfl rfl rfl
private theorem moment_3060_677_join6 :
    blockEstimate 3060 677 1573 256 = 241533366912 :=
  block_append moment_3060_677_part7 moment_3060_677_part8 rfl rfl rfl
private theorem moment_3060_677_join7 :
    blockEstimate 3060 677 1829 256 = 290165731968 :=
  block_append moment_3060_677_part9 moment_3060_677_part10 rfl rfl rfl
private theorem moment_3060_677_join8 :
    blockEstimate 3060 677 1573 512 = 531699098880 :=
  block_append moment_3060_677_join6 moment_3060_677_join7 rfl rfl rfl
private theorem moment_3060_677_join9 :
    blockEstimate 3060 677 2085 256 = 316048192128 :=
  block_append moment_3060_677_part11 moment_3060_677_part12 rfl rfl rfl
private theorem moment_3060_677_join10 :
    blockEstimate 3060 677 2341 256 = 319180747392 :=
  block_append moment_3060_677_part13 moment_3060_677_part14 rfl rfl rfl
private theorem moment_3060_677_join11 :
    blockEstimate 3060 677 2085 512 = 635228939520 :=
  block_append moment_3060_677_join9 moment_3060_677_join10 rfl rfl rfl
private theorem moment_3060_677_join12 :
    blockEstimate 3060 677 1573 1024 = 1166928038400 :=
  block_append moment_3060_677_join8 moment_3060_677_join11 rfl rfl rfl
private theorem moment_3060_677_join13 :
    blockEstimate 3060 677 677 1920 = 1450383252825 :=
  block_append moment_3060_677_join5 moment_3060_677_join12 rfl rfl rfl
private theorem moment_3060_677_join14 :
    blockEstimate 3060 677 2725 256 = 281223508608 :=
  block_append moment_3060_677_part16 moment_3060_677_part17 rfl rfl rfl
private theorem moment_3060_677_join15 :
    blockEstimate 3060 677 2597 384 = 434879245248 :=
  block_append moment_3060_677_part15 moment_3060_677_join14 rfl rfl rfl
private theorem moment_3060_677_join16 :
    blockEstimate 3060 677 2981 256 = 228367493821 :=
  block_append moment_3060_677_part18 moment_3060_677_part19 rfl rfl rfl
private theorem moment_3060_677_join17 :
    blockEstimate 3060 677 3237 256 = 164850591625 :=
  block_append moment_3060_677_part20 moment_3060_677_part21 rfl rfl rfl
private theorem moment_3060_677_join18 :
    blockEstimate 3060 677 2981 512 = 393218085446 :=
  block_append moment_3060_677_join16 moment_3060_677_join17 rfl rfl rfl
private theorem moment_3060_677_join19 :
    blockEstimate 3060 677 2597 896 = 828097330694 :=
  block_append moment_3060_677_join15 moment_3060_677_join18 rfl rfl rfl
private theorem moment_3060_677_join20 :
    blockEstimate 3060 677 3493 256 = 103338484546 :=
  block_append moment_3060_677_part22 moment_3060_677_part23 rfl rfl rfl
private theorem moment_3060_677_join21 :
    blockEstimate 3060 677 3749 256 = 51286430304 :=
  block_append moment_3060_677_part24 moment_3060_677_part25 rfl rfl rfl
private theorem moment_3060_677_join22 :
    blockEstimate 3060 677 3493 512 = 154624914850 :=
  block_append moment_3060_677_join20 moment_3060_677_join21 rfl rfl rfl
private theorem moment_3060_677_join23 :
    blockEstimate 3060 677 4005 256 = 15619244640 :=
  block_append moment_3060_677_part26 moment_3060_677_part27 rfl rfl rfl
private theorem moment_3060_677_join24 :
    blockEstimate 3060 677 4261 153 = 918524867 :=
  block_append moment_3060_677_part28 moment_3060_677_part29 rfl rfl rfl
private theorem moment_3060_677_join25 :
    blockEstimate 3060 677 4005 409 = 16537769507 :=
  block_append moment_3060_677_join23 moment_3060_677_join24 rfl rfl rfl
private theorem moment_3060_677_join26 :
    blockEstimate 3060 677 3493 921 = 171162684357 :=
  block_append moment_3060_677_join22 moment_3060_677_join25 rfl rfl rfl
private theorem moment_3060_677_join27 :
    blockEstimate 3060 677 2597 1817 = 999260015051 :=
  block_append moment_3060_677_join19 moment_3060_677_join26 rfl rfl rfl
private theorem moment_3060_677_join28 :
    blockEstimate 3060 677 677 3737 = 2449643267876 :=
  block_append moment_3060_677_join13 moment_3060_677_join27 rfl rfl rfl

theorem moment_3060_677 : momentEstimate 3060 677 = 2449643267876 := moment_3060_677_join28

private theorem moment_4173_924_part0 :
    blockEstimate 4173 924 924 128 = 1458855840 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part1 :
    blockEstimate 4173 924 1052 128 = 9805737888 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part2 :
    blockEstimate 4173 924 1180 128 = 25692929952 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part3 :
    blockEstimate 4173 924 1308 128 = 48315125664 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part4 :
    blockEstimate 4173 924 1436 128 = 76867018656 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part5 :
    blockEstimate 4173 924 1564 128 = 110543302560 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part6 :
    blockEstimate 4173 924 1692 128 = 148538671008 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part7 :
    blockEstimate 4173 924 1820 128 = 189518787207 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part8 :
    blockEstimate 4173 924 1948 128 = 228713339200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part9 :
    blockEstimate 4173 924 2076 128 = 264040110400 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part10 :
    blockEstimate 4173 924 2204 128 = 295487150400 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part11 :
    blockEstimate 4173 924 2332 128 = 323054459200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part12 :
    blockEstimate 4173 924 2460 128 = 346742036800 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part13 :
    blockEstimate 4173 924 2588 128 = 366549883200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part14 :
    blockEstimate 4173 924 2716 128 = 382477998400 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part15 :
    blockEstimate 4173 924 2844 128 = 394526382400 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part16 :
    blockEstimate 4173 924 2972 128 = 402695035200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part17 :
    blockEstimate 4173 924 3100 128 = 406983956800 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part18 :
    blockEstimate 4173 924 3228 128 = 407393147200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part19 :
    blockEstimate 4173 924 3356 128 = 403922606400 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part20 :
    blockEstimate 4173 924 3484 128 = 396572334400 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part21 :
    blockEstimate 4173 924 3612 128 = 385342331200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part22 :
    blockEstimate 4173 924 3740 128 = 370232596800 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part23 :
    blockEstimate 4173 924 3868 128 = 351243131200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part24 :
    blockEstimate 4173 924 3996 128 = 328373934400 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part25 :
    blockEstimate 4173 924 4124 128 = 301726027200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part26 :
    blockEstimate 4173 924 4252 128 = 272797056895 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part27 :
    blockEstimate 4173 924 4380 128 = 243060340445 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part28 :
    blockEstimate 4173 924 4508 128 = 213096253341 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part29 :
    blockEstimate 4173 924 4636 128 = 183435753559 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part30 :
    blockEstimate 4173 924 4764 128 = 154581940185 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part31 :
    blockEstimate 4173 924 4892 128 = 127010052647 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part32 :
    blockEstimate 4173 924 5020 128 = 101135659542 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part33 :
    blockEstimate 4173 924 5148 128 = 77217465616 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part34 :
    blockEstimate 4173 924 5276 128 = 55990538512 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part35 :
    blockEstimate 4173 924 5404 128 = 37798911248 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part36 :
    blockEstimate 4173 924 5532 128 = 22894242064 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part37 :
    blockEstimate 4173 924 5660 128 = 11528189200 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part38 :
    blockEstimate 4173 924 5788 128 = 3952410896 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_part39 :
    blockEstimate 4173 924 5916 105 = 415113192 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_4173_924_join0 :
    blockEstimate 4173 924 924 256 = 11264593728 :=
  block_append moment_4173_924_part0 moment_4173_924_part1 rfl rfl rfl
private theorem moment_4173_924_join1 :
    blockEstimate 4173 924 1308 256 = 125182144320 :=
  block_append moment_4173_924_part3 moment_4173_924_part4 rfl rfl rfl
private theorem moment_4173_924_join2 :
    blockEstimate 4173 924 1180 384 = 150875074272 :=
  block_append moment_4173_924_part2 moment_4173_924_join1 rfl rfl rfl
private theorem moment_4173_924_join3 :
    blockEstimate 4173 924 924 640 = 162139668000 :=
  block_append moment_4173_924_join0 moment_4173_924_join2 rfl rfl rfl
private theorem moment_4173_924_join4 :
    blockEstimate 4173 924 1564 256 = 259081973568 :=
  block_append moment_4173_924_part5 moment_4173_924_part6 rfl rfl rfl
private theorem moment_4173_924_join5 :
    blockEstimate 4173 924 1948 256 = 492753449600 :=
  block_append moment_4173_924_part8 moment_4173_924_part9 rfl rfl rfl
private theorem moment_4173_924_join6 :
    blockEstimate 4173 924 1820 384 = 682272236807 :=
  block_append moment_4173_924_part7 moment_4173_924_join5 rfl rfl rfl
private theorem moment_4173_924_join7 :
    blockEstimate 4173 924 1564 640 = 941354210375 :=
  block_append moment_4173_924_join4 moment_4173_924_join6 rfl rfl rfl
private theorem moment_4173_924_join8 :
    blockEstimate 4173 924 924 1280 = 1103493878375 :=
  block_append moment_4173_924_join3 moment_4173_924_join7 rfl rfl rfl
private theorem moment_4173_924_join9 :
    blockEstimate 4173 924 2204 256 = 618541609600 :=
  block_append moment_4173_924_part10 moment_4173_924_part11 rfl rfl rfl
private theorem moment_4173_924_join10 :
    blockEstimate 4173 924 2588 256 = 749027881600 :=
  block_append moment_4173_924_part13 moment_4173_924_part14 rfl rfl rfl
private theorem moment_4173_924_join11 :
    blockEstimate 4173 924 2460 384 = 1095769918400 :=
  block_append moment_4173_924_part12 moment_4173_924_join10 rfl rfl rfl
private theorem moment_4173_924_join12 :
    blockEstimate 4173 924 2204 640 = 1714311528000 :=
  block_append moment_4173_924_join9 moment_4173_924_join11 rfl rfl rfl
private theorem moment_4173_924_join13 :
    blockEstimate 4173 924 2844 256 = 797221417600 :=
  block_append moment_4173_924_part15 moment_4173_924_part16 rfl rfl rfl
private theorem moment_4173_924_join14 :
    blockEstimate 4173 924 3228 256 = 811315753600 :=
  block_append moment_4173_924_part18 moment_4173_924_part19 rfl rfl rfl
private theorem moment_4173_924_join15 :
    blockEstimate 4173 924 3100 384 = 1218299710400 :=
  block_append moment_4173_924_part17 moment_4173_924_join14 rfl rfl rfl
private theorem moment_4173_924_join16 :
    blockEstimate 4173 924 2844 640 = 2015521128000 :=
  block_append moment_4173_924_join13 moment_4173_924_join15 rfl rfl rfl
private theorem moment_4173_924_join17 :
    blockEstimate 4173 924 2204 1280 = 3729832656000 :=
  block_append moment_4173_924_join12 moment_4173_924_join16 rfl rfl rfl
private theorem moment_4173_924_join18 :
    blockEstimate 4173 924 924 2560 = 4833326534375 :=
  block_append moment_4173_924_join8 moment_4173_924_join17 rfl rfl rfl
private theorem moment_4173_924_join19 :
    blockEstimate 4173 924 3484 256 = 781914665600 :=
  block_append moment_4173_924_part20 moment_4173_924_part21 rfl rfl rfl
private theorem moment_4173_924_join20 :
    blockEstimate 4173 924 3868 256 = 679617065600 :=
  block_append moment_4173_924_part23 moment_4173_924_part24 rfl rfl rfl
private theorem moment_4173_924_join21 :
    blockEstimate 4173 924 3740 384 = 1049849662400 :=
  block_append moment_4173_924_part22 moment_4173_924_join20 rfl rfl rfl
private theorem moment_4173_924_join22 :
    blockEstimate 4173 924 3484 640 = 1831764328000 :=
  block_append moment_4173_924_join19 moment_4173_924_join21 rfl rfl rfl
private theorem moment_4173_924_join23 :
    blockEstimate 4173 924 4124 256 = 574523084095 :=
  block_append moment_4173_924_part25 moment_4173_924_part26 rfl rfl rfl
private theorem moment_4173_924_join24 :
    blockEstimate 4173 924 4508 256 = 396532006900 :=
  block_append moment_4173_924_part28 moment_4173_924_part29 rfl rfl rfl
private theorem moment_4173_924_join25 :
    blockEstimate 4173 924 4380 384 = 639592347345 :=
  block_append moment_4173_924_part27 moment_4173_924_join24 rfl rfl rfl
private theorem moment_4173_924_join26 :
    blockEstimate 4173 924 4124 640 = 1214115431440 :=
  block_append moment_4173_924_join23 moment_4173_924_join25 rfl rfl rfl
private theorem moment_4173_924_join27 :
    blockEstimate 4173 924 3484 1280 = 3045879759440 :=
  block_append moment_4173_924_join22 moment_4173_924_join26 rfl rfl rfl
private theorem moment_4173_924_join28 :
    blockEstimate 4173 924 4764 256 = 281591992832 :=
  block_append moment_4173_924_part30 moment_4173_924_part31 rfl rfl rfl
private theorem moment_4173_924_join29 :
    blockEstimate 4173 924 5148 256 = 133208004128 :=
  block_append moment_4173_924_part33 moment_4173_924_part34 rfl rfl rfl
private theorem moment_4173_924_join30 :
    blockEstimate 4173 924 5020 384 = 234343663670 :=
  block_append moment_4173_924_part32 moment_4173_924_join29 rfl rfl rfl
private theorem moment_4173_924_join31 :
    blockEstimate 4173 924 4764 640 = 515935656502 :=
  block_append moment_4173_924_join28 moment_4173_924_join30 rfl rfl rfl
private theorem moment_4173_924_join32 :
    blockEstimate 4173 924 5404 256 = 60693153312 :=
  block_append moment_4173_924_part35 moment_4173_924_part36 rfl rfl rfl
private theorem moment_4173_924_join33 :
    blockEstimate 4173 924 5788 233 = 4367524088 :=
  block_append moment_4173_924_part38 moment_4173_924_part39 rfl rfl rfl
private theorem moment_4173_924_join34 :
    blockEstimate 4173 924 5660 361 = 15895713288 :=
  block_append moment_4173_924_part37 moment_4173_924_join33 rfl rfl rfl
private theorem moment_4173_924_join35 :
    blockEstimate 4173 924 5404 617 = 76588866600 :=
  block_append moment_4173_924_join32 moment_4173_924_join34 rfl rfl rfl
private theorem moment_4173_924_join36 :
    blockEstimate 4173 924 4764 1257 = 592524523102 :=
  block_append moment_4173_924_join31 moment_4173_924_join35 rfl rfl rfl
private theorem moment_4173_924_join37 :
    blockEstimate 4173 924 3484 2537 = 3638404282542 :=
  block_append moment_4173_924_join27 moment_4173_924_join36 rfl rfl rfl
private theorem moment_4173_924_join38 :
    blockEstimate 4173 924 924 5097 = 8471730816917 :=
  block_append moment_4173_924_join18 moment_4173_924_join37 rfl rfl rfl

theorem moment_4173_924 : momentEstimate 4173 924 = 8471730816917 := moment_4173_924_join38

private theorem moment_5842_1293_part0 :
    blockEstimate 5842 1293 1293 128 = 2055957280 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part1 :
    blockEstimate 5842 1293 1421 128 = 13930330912 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part2 :
    blockEstimate 5842 1293 1549 128 = 36845161248 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part3 :
    blockEstimate 5842 1293 1677 128 = 69995141920 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part4 :
    blockEstimate 5842 1293 1805 128 = 112574966560 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part5 :
    blockEstimate 5842 1293 1933 128 = 163779328800 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part6 :
    blockEstimate 5842 1293 2061 128 = 222802922272 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part7 :
    blockEstimate 5842 1293 2189 128 = 288840440608 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part8 :
    blockEstimate 5842 1293 2317 128 = 361086577440 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part9 :
    blockEstimate 5842 1293 2445 128 = 438736026400 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part10 :
    blockEstimate 5842 1293 2573 128 = 519852225775 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part11 :
    blockEstimate 5842 1293 2701 128 = 597710856768 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part12 :
    blockEstimate 5842 1293 2829 128 = 670143717952 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part13 :
    blockEstimate 5842 1293 2957 128 = 737149149760 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part14 :
    blockEstimate 5842 1293 3085 128 = 798727152192 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part15 :
    blockEstimate 5842 1293 3213 128 = 854877725248 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part16 :
    blockEstimate 5842 1293 3341 128 = 905600868928 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part17 :
    blockEstimate 5842 1293 3469 128 = 950896583232 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part18 :
    blockEstimate 5842 1293 3597 128 = 990764868160 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part19 :
    blockEstimate 5842 1293 3725 128 = 1025205723712 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part20 :
    blockEstimate 5842 1293 3853 128 = 1054219149888 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part21 :
    blockEstimate 5842 1293 3981 128 = 1077805146688 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part22 :
    blockEstimate 5842 1293 4109 128 = 1095963714112 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part23 :
    blockEstimate 5842 1293 4237 128 = 1108694852160 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part24 :
    blockEstimate 5842 1293 4365 128 = 1115998560832 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part25 :
    blockEstimate 5842 1293 4493 128 = 1117874840128 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part26 :
    blockEstimate 5842 1293 4621 128 = 1114323690048 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part27 :
    blockEstimate 5842 1293 4749 128 = 1105345110592 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part28 :
    blockEstimate 5842 1293 4877 128 = 1090939101760 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part29 :
    blockEstimate 5842 1293 5005 128 = 1071105663552 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part30 :
    blockEstimate 5842 1293 5133 128 = 1045844795968 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part31 :
    blockEstimate 5842 1293 5261 128 = 1015156499008 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part32 :
    blockEstimate 5842 1293 5389 128 = 979040772672 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part33 :
    blockEstimate 5842 1293 5517 128 = 937497616960 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part34 :
    blockEstimate 5842 1293 5645 128 = 890527031872 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part35 :
    blockEstimate 5842 1293 5773 128 = 838187300883 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part36 :
    blockEstimate 5842 1293 5901 128 = 782148228890 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part37 :
    blockEstimate 5842 1293 6029 128 = 724581267155 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part38 :
    blockEstimate 5842 1293 6157 128 = 666146309857 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part39 :
    blockEstimate 5842 1293 6285 128 = 607398250566 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part40 :
    blockEstimate 5842 1293 6413 128 = 548872066532 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part41 :
    blockEstimate 5842 1293 6541 128 = 491082821398 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part42 :
    blockEstimate 5842 1293 6669 128 = 434525663102 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part43 :
    blockEstimate 5842 1293 6797 128 = 379675825088 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part44 :
    blockEstimate 5842 1293 6925 128 = 326988626173 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part45 :
    blockEstimate 5842 1293 7053 128 = 276846696004 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part46 :
    blockEstimate 5842 1293 7181 128 = 229271827936 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part47 :
    blockEstimate 5842 1293 7309 128 = 185298060768 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part48 :
    blockEstimate 5842 1293 7437 128 = 145374352864 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part49 :
    blockEstimate 5842 1293 7565 128 = 109752362464 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part50 :
    blockEstimate 5842 1293 7693 128 = 78683747808 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part51 :
    blockEstimate 5842 1293 7821 128 = 52420167136 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part52 :
    blockEstimate 5842 1293 7949 128 = 31213278688 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part53 :
    blockEstimate 5842 1293 8077 128 = 15314740704 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part54 :
    blockEstimate 5842 1293 8205 128 = 4976211424 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_part55 :
    blockEstimate 5842 1293 8333 95 = 434117864 := by rw [← Lower6963.Lo.PoolFast.blockEstimateF_eq]; decide +kernel
private theorem moment_5842_1293_join0 :
    blockEstimate 5842 1293 1421 256 = 50775492160 :=
  block_append moment_5842_1293_part1 moment_5842_1293_part2 rfl rfl rfl
private theorem moment_5842_1293_join1 :
    blockEstimate 5842 1293 1293 384 = 52831449440 :=
  block_append moment_5842_1293_part0 moment_5842_1293_join0 rfl rfl rfl
private theorem moment_5842_1293_join2 :
    blockEstimate 5842 1293 1677 256 = 182570108480 :=
  block_append moment_5842_1293_part3 moment_5842_1293_part4 rfl rfl rfl
private theorem moment_5842_1293_join3 :
    blockEstimate 5842 1293 1933 256 = 386582251072 :=
  block_append moment_5842_1293_part5 moment_5842_1293_part6 rfl rfl rfl
private theorem moment_5842_1293_join4 :
    blockEstimate 5842 1293 1677 512 = 569152359552 :=
  block_append moment_5842_1293_join2 moment_5842_1293_join3 rfl rfl rfl
private theorem moment_5842_1293_join5 :
    blockEstimate 5842 1293 1293 896 = 621983808992 :=
  block_append moment_5842_1293_join1 moment_5842_1293_join4 rfl rfl rfl
private theorem moment_5842_1293_join6 :
    blockEstimate 5842 1293 2317 256 = 799822603840 :=
  block_append moment_5842_1293_part8 moment_5842_1293_part9 rfl rfl rfl
private theorem moment_5842_1293_join7 :
    blockEstimate 5842 1293 2189 384 = 1088663044448 :=
  block_append moment_5842_1293_part7 moment_5842_1293_join6 rfl rfl rfl
private theorem moment_5842_1293_join8 :
    blockEstimate 5842 1293 2573 256 = 1117563082543 :=
  block_append moment_5842_1293_part10 moment_5842_1293_part11 rfl rfl rfl
private theorem moment_5842_1293_join9 :
    blockEstimate 5842 1293 2829 256 = 1407292867712 :=
  block_append moment_5842_1293_part12 moment_5842_1293_part13 rfl rfl rfl
private theorem moment_5842_1293_join10 :
    blockEstimate 5842 1293 2573 512 = 2524855950255 :=
  block_append moment_5842_1293_join8 moment_5842_1293_join9 rfl rfl rfl
private theorem moment_5842_1293_join11 :
    blockEstimate 5842 1293 2189 896 = 3613518994703 :=
  block_append moment_5842_1293_join7 moment_5842_1293_join10 rfl rfl rfl
private theorem moment_5842_1293_join12 :
    blockEstimate 5842 1293 1293 1792 = 4235502803695 :=
  block_append moment_5842_1293_join5 moment_5842_1293_join11 rfl rfl rfl
private theorem moment_5842_1293_join13 :
    blockEstimate 5842 1293 3213 256 = 1760478594176 :=
  block_append moment_5842_1293_part15 moment_5842_1293_part16 rfl rfl rfl
private theorem moment_5842_1293_join14 :
    blockEstimate 5842 1293 3085 384 = 2559205746368 :=
  block_append moment_5842_1293_part14 moment_5842_1293_join13 rfl rfl rfl
private theorem moment_5842_1293_join15 :
    blockEstimate 5842 1293 3469 256 = 1941661451392 :=
  block_append moment_5842_1293_part17 moment_5842_1293_part18 rfl rfl rfl
private theorem moment_5842_1293_join16 :
    blockEstimate 5842 1293 3725 256 = 2079424873600 :=
  block_append moment_5842_1293_part19 moment_5842_1293_part20 rfl rfl rfl
private theorem moment_5842_1293_join17 :
    blockEstimate 5842 1293 3469 512 = 4021086324992 :=
  block_append moment_5842_1293_join15 moment_5842_1293_join16 rfl rfl rfl
private theorem moment_5842_1293_join18 :
    blockEstimate 5842 1293 3085 896 = 6580292071360 :=
  block_append moment_5842_1293_join14 moment_5842_1293_join17 rfl rfl rfl
private theorem moment_5842_1293_join19 :
    blockEstimate 5842 1293 4109 256 = 2204658566272 :=
  block_append moment_5842_1293_part22 moment_5842_1293_part23 rfl rfl rfl
private theorem moment_5842_1293_join20 :
    blockEstimate 5842 1293 3981 384 = 3282463712960 :=
  block_append moment_5842_1293_part21 moment_5842_1293_join19 rfl rfl rfl
private theorem moment_5842_1293_join21 :
    blockEstimate 5842 1293 4365 256 = 2233873400960 :=
  block_append moment_5842_1293_part24 moment_5842_1293_part25 rfl rfl rfl
private theorem moment_5842_1293_join22 :
    blockEstimate 5842 1293 4621 256 = 2219668800640 :=
  block_append moment_5842_1293_part26 moment_5842_1293_part27 rfl rfl rfl
private theorem moment_5842_1293_join23 :
    blockEstimate 5842 1293 4365 512 = 4453542201600 :=
  block_append moment_5842_1293_join21 moment_5842_1293_join22 rfl rfl rfl
private theorem moment_5842_1293_join24 :
    blockEstimate 5842 1293 3981 896 = 7736005914560 :=
  block_append moment_5842_1293_join20 moment_5842_1293_join23 rfl rfl rfl
private theorem moment_5842_1293_join25 :
    blockEstimate 5842 1293 3085 1792 = 14316297985920 :=
  block_append moment_5842_1293_join18 moment_5842_1293_join24 rfl rfl rfl
private theorem moment_5842_1293_join26 :
    blockEstimate 5842 1293 1293 3584 = 18551800789615 :=
  block_append moment_5842_1293_join12 moment_5842_1293_join25 rfl rfl rfl
private theorem moment_5842_1293_join27 :
    blockEstimate 5842 1293 5005 256 = 2116950459520 :=
  block_append moment_5842_1293_part29 moment_5842_1293_part30 rfl rfl rfl
private theorem moment_5842_1293_join28 :
    blockEstimate 5842 1293 4877 384 = 3207889561280 :=
  block_append moment_5842_1293_part28 moment_5842_1293_join27 rfl rfl rfl
private theorem moment_5842_1293_join29 :
    blockEstimate 5842 1293 5261 256 = 1994197271680 :=
  block_append moment_5842_1293_part31 moment_5842_1293_part32 rfl rfl rfl
private theorem moment_5842_1293_join30 :
    blockEstimate 5842 1293 5517 256 = 1828024648832 :=
  block_append moment_5842_1293_part33 moment_5842_1293_part34 rfl rfl rfl
private theorem moment_5842_1293_join31 :
    blockEstimate 5842 1293 5261 512 = 3822221920512 :=
  block_append moment_5842_1293_join29 moment_5842_1293_join30 rfl rfl rfl
private theorem moment_5842_1293_join32 :
    blockEstimate 5842 1293 4877 896 = 7030111481792 :=
  block_append moment_5842_1293_join28 moment_5842_1293_join31 rfl rfl rfl
private theorem moment_5842_1293_join33 :
    blockEstimate 5842 1293 5901 256 = 1506729496045 :=
  block_append moment_5842_1293_part36 moment_5842_1293_part37 rfl rfl rfl
private theorem moment_5842_1293_join34 :
    blockEstimate 5842 1293 5773 384 = 2344916796928 :=
  block_append moment_5842_1293_part35 moment_5842_1293_join33 rfl rfl rfl
private theorem moment_5842_1293_join35 :
    blockEstimate 5842 1293 6157 256 = 1273544560423 :=
  block_append moment_5842_1293_part38 moment_5842_1293_part39 rfl rfl rfl
private theorem moment_5842_1293_join36 :
    blockEstimate 5842 1293 6413 256 = 1039954887930 :=
  block_append moment_5842_1293_part40 moment_5842_1293_part41 rfl rfl rfl
private theorem moment_5842_1293_join37 :
    blockEstimate 5842 1293 6157 512 = 2313499448353 :=
  block_append moment_5842_1293_join35 moment_5842_1293_join36 rfl rfl rfl
private theorem moment_5842_1293_join38 :
    blockEstimate 5842 1293 5773 896 = 4658416245281 :=
  block_append moment_5842_1293_join34 moment_5842_1293_join37 rfl rfl rfl
private theorem moment_5842_1293_join39 :
    blockEstimate 5842 1293 4877 1792 = 11688527727073 :=
  block_append moment_5842_1293_join32 moment_5842_1293_join38 rfl rfl rfl
private theorem moment_5842_1293_join40 :
    blockEstimate 5842 1293 6797 256 = 706664451261 :=
  block_append moment_5842_1293_part43 moment_5842_1293_part44 rfl rfl rfl
private theorem moment_5842_1293_join41 :
    blockEstimate 5842 1293 6669 384 = 1141190114363 :=
  block_append moment_5842_1293_part42 moment_5842_1293_join40 rfl rfl rfl
private theorem moment_5842_1293_join42 :
    blockEstimate 5842 1293 7053 256 = 506118523940 :=
  block_append moment_5842_1293_part45 moment_5842_1293_part46 rfl rfl rfl
private theorem moment_5842_1293_join43 :
    blockEstimate 5842 1293 7309 256 = 330672413632 :=
  block_append moment_5842_1293_part47 moment_5842_1293_part48 rfl rfl rfl
private theorem moment_5842_1293_join44 :
    blockEstimate 5842 1293 7053 512 = 836790937572 :=
  block_append moment_5842_1293_join42 moment_5842_1293_join43 rfl rfl rfl
private theorem moment_5842_1293_join45 :
    blockEstimate 5842 1293 6669 896 = 1977981051935 :=
  block_append moment_5842_1293_join41 moment_5842_1293_join44 rfl rfl rfl
private theorem moment_5842_1293_join46 :
    blockEstimate 5842 1293 7693 256 = 131103914944 :=
  block_append moment_5842_1293_part50 moment_5842_1293_part51 rfl rfl rfl
private theorem moment_5842_1293_join47 :
    blockEstimate 5842 1293 7565 384 = 240856277408 :=
  block_append moment_5842_1293_part49 moment_5842_1293_join46 rfl rfl rfl
private theorem moment_5842_1293_join48 :
    blockEstimate 5842 1293 7949 256 = 46528019392 :=
  block_append moment_5842_1293_part52 moment_5842_1293_part53 rfl rfl rfl
private theorem moment_5842_1293_join49 :
    blockEstimate 5842 1293 8205 223 = 5410329288 :=
  block_append moment_5842_1293_part54 moment_5842_1293_part55 rfl rfl rfl
private theorem moment_5842_1293_join50 :
    blockEstimate 5842 1293 7949 479 = 51938348680 :=
  block_append moment_5842_1293_join48 moment_5842_1293_join49 rfl rfl rfl
private theorem moment_5842_1293_join51 :
    blockEstimate 5842 1293 7565 863 = 292794626088 :=
  block_append moment_5842_1293_join47 moment_5842_1293_join50 rfl rfl rfl
private theorem moment_5842_1293_join52 :
    blockEstimate 5842 1293 6669 1759 = 2270775678023 :=
  block_append moment_5842_1293_join45 moment_5842_1293_join51 rfl rfl rfl
private theorem moment_5842_1293_join53 :
    blockEstimate 5842 1293 4877 3551 = 13959303405096 :=
  block_append moment_5842_1293_join39 moment_5842_1293_join52 rfl rfl rfl
private theorem moment_5842_1293_join54 :
    blockEstimate 5842 1293 1293 7135 = 32511104194711 :=
  block_append moment_5842_1293_join26 moment_5842_1293_join53 rfl rfl rfl

theorem moment_5842_1293 : momentEstimate 5842 1293 = 32511104194711 := moment_5842_1293_join54


end Lower6961.Lo.RescuePoolMoments

end Merged_R6961LoRescuePoolMoments0
