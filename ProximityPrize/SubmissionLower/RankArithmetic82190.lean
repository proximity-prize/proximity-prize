import ProximityPrize.SubmissionLower.Pascal82190
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000
namespace RankArithmetic82190
open K1_13_1_1
open Pascal82190 (degree lineCharge pairCharge pascalCharge)
open private sumRange_prefix sumRange_suffix sumRange_zero sumRange_congr sumToCap_eq
  from ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic

def natBandTwelve (d lo hi : ℕ) : ℕ :=
  sumRange (min (min d 12) (hi / 3) + 1) fun f =>
    sumRange (min (d - f) ((hi - 3 * f) / 2) + 1) fun c =>
      min (d - f - c) (hi - 2 * c - 3 * f) + 1 - (lo - (2 * c + 3 * f))
def lineNat (d lo o b c : ℕ) : ℕ :=
  let fmin := (lo - (b + 2 * min c 24) + 2) / 3
  let rowMin := max fmin (3 * d + 1 - (3 * b + 2 * c + o))
  min (min d 12 + 1 - fmin) (d - b - c + 1 - rowMin)
def pairsNat (d lo b : ℕ) : ℕ :=
  sumRange (min d 12 + 1) fun f =>
    min (d - f) ((48 - 3 * f) / 2) + 1 - ((lo - (b + 3 * f) + 1) / 2)
def pascalNat (s r : ℕ) : ℕ :=
  let d := degree s
  let lo := 48 - r
  let o := 138 - (s + r)
  let hi := min 48 (137 - r)
  let startB := d + 1 - o
  sumToCap (fun b =>
    let startC := 2 * (d - b) + 1 - o
    sumToCap (lineNat d lo o b) (d - b + 1 - startC) startC (pairsNat d lo b))
    (d + 1 - startB) startB (natBandTwelve d lo hi)

theorem natBandTwelve_eq (d : ℕ) (lo hi : ℤ) (hhi : 0 ≤ hi) :
    bandCount d lo hi 12 = natBandTwelve d lo.toNat hi.toNat := by
  unfold bandCount natBandTwelve
  rw [sumRange_prefix (min d 12 + 1) (min (min d 12) (hi.toNat / 3) + 1)]
  · apply sumRange_congr
    intro f hf
    have hf' : 3 * f ≤ hi.toNat := by omega
    have hdiv : ((hi - 3 * (f : ℤ)) / 2).toNat = (hi.toNat - 3 * f) / 2 := by omega
    rw [hdiv]
    apply sumRange_congr
    intro c hc
    unfold intervalSize
    omega
  · omega
  · intro f hlo hf
    apply sumRange_zero
    intro c _
    unfold intervalSize
    omega
private theorem lineNat_eq (d : ℕ) (lo order : ℤ) (ho : 0 ≤ order) (b c : ℕ)
    (hbc : b + c ≤ d) :
    lineCharge d lo order b c = lineNat d lo.toNat order.toNat b c := by
  let lower := max 0 ((lo - (b : ℤ) - 2 * (min c 24 : ℕ) + 2) / 3)
  let lowerNat := (lo.toNat - (b + 2 * min c 24) + 2) / 3
  have hlow : lower = (lowerNat : ℤ) := by dsimp [lower, lowerNat]; omega
  unfold lineCharge lineNat
  dsimp only
  change min (intervalSize lower _) (intervalSize (max lower _) _) =
    min (min d 12 + 1 - lowerNat) (d - b - c + 1 - max lowerNat _)
  rw [hlow]
  congr 1 <;> unfold intervalSize <;> omega
private theorem pairsNat_eq (d : ℕ) (lo : ℤ) (b : ℕ) :
    pairCharge d lo b = pairsNat d lo.toNat b := by
  unfold pairCharge pairsNat
  apply sumRange_congr
  intro f hf
  unfold intervalSize
  omega
private theorem lineNat_zero (d lo order b c : ℕ) (hbc : b + c ≤ d)
    (h : c < 2 * (d - b) + 1 - order) : lineNat d lo order b c = 0 := by
  unfold lineNat
  dsimp only
  omega
private theorem innerSlice_eq (d lo order b : ℕ) (hb : b ≤ d) :
    (let startC := 2 * (d - b) + 1 - order
     sumToCap (lineNat d lo order b) (d - b + 1 - startC) startC (pairsNat d lo b)) =
     min (pairsNat d lo b) (sumRange (d - b + 1) (lineNat d lo order b)) := by
  let startC := 2 * (d - b) + 1 - order
  change sumToCap (lineNat d lo order b) (d - b + 1 - startC) startC _ = _
  rw [sumToCap_eq]
  congr 1
  by_cases hc : startC ≤ d - b + 1
  · symm
    apply sumRange_suffix _ _ _ hc
    intro c h
    exact lineNat_zero d lo order b c (by omega) h
  · rw [show d - b + 1 - startC = 0 by omega]
    symm
    apply sumRange_zero
    intro c h
    exact lineNat_zero d lo order b c (by omega) (by omega)
theorem pascalNat_eq (s r : ℕ) (h : s + r < 138) :
    pascalNat s r = pascalCharge s (offset r) := by
  let d := degree s
  let lo := -(offset r)
  let order := orderCutoff s (offset r)
  let hi := activeIndex (offset r)
  have hl : lo.toNat = 48 - r := by dsimp [lo, offset]; omega
  have ho : order.toNat = 138 - (s + r) := by dsimp [order, orderCutoff, offset]; omega
  have hpos : 0 < order := by dsimp [order, orderCutoff, offset]; omega
  have hh : hi.toNat = min 48 (137 - r) := by dsimp [hi, activeIndex, offset]; omega
  have hhi : 0 ≤ hi := by dsimp [hi, activeIndex, offset]; omega
  let startB := d + 1 - order.toNat
  change (sumToCap (fun b =>
      let startC := 2 * (d - b) + 1 - (138 - (s + r))
      sumToCap (lineNat d (48 - r) (138 - (s + r)) b) (d - b + 1 - startC)
        startC (pairsNat d (48 - r) b))
      (d + 1 - (d + 1 - (138 - (s + r)))) (d + 1 - (138 - (s + r)))
      (natBandTwelve d (48 - r) (min 48 (137 - r)))) =
    min (bandCount d lo hi 12) (sumRange (d + 1) fun b =>
      min (pairCharge d lo b) (sumRange (d - b + 1) (lineCharge d lo order b)))
  rw [← hl, ← ho, ← hh, ← natBandTwelve_eq d lo hi hhi, sumToCap_eq]
  congr 1
  change sumRange (d + 1 - startB) _ = _
  symm
  rw [sumRange_suffix (d + 1) startB _ (Nat.sub_le _ _)]
  · apply sumRange_congr
    intro i hi
    simp only [pairsNat_eq]
    have hb : i + startB ≤ d := by omega
    rw [innerSlice_eq d lo.toNat order.toNat _ hb]
    congr 1
    apply sumRange_congr
    intro c hc
    exact lineNat_eq d lo order hpos.le _ c (by omega)
  · intro b hb
    have hz : sumRange (d - b + 1) (lineCharge d lo order b) = 0 := by
      apply sumRange_zero
      intro c hc
      have hbc : b + c ≤ d := by dsimp [startB] at hb; omega
      rw [lineNat_eq d lo order hpos.le b c hbc]
      apply lineNat_zero _ _ _ _ _ hbc
      dsimp [startB] at hb
      omega
    simp [hz]

def targetNat (d lo o : ℕ) : ℕ :=
  if o = 0 then 0 else
    sumRange (min d ((o-1)/3) + 1) fun a =>
      sumRange (min (d-a) ((o-1-3*a)/2) + 1) fun f =>
        min (d-a-f + 1) (o - (3*a+2*f)) - (lo+a - (d+2*f))

theorem targetNat_eq (d : ℕ) (lo order : ℤ) :
    targetCount d lo order = targetNat d lo.toNat order.toNat := by
  unfold targetNat targetCount
  split
  next ho =>
    apply sumRange_zero
    intro a _
    apply sumRange_zero
    intro f _
    unfold intervalSize
    omega
  next ho =>
    have hpos : 0 < order := by omega
    rw [sumRange_prefix (d+1) (min d ((order.toNat-1)/3)+1) _ (by omega)]
    · apply sumRange_congr
      intro a ha
      rw [sumRange_prefix (d-a+1) (min (d-a) ((order.toNat-1-3*a)/2)+1) _ (by omega)]
      · apply sumRange_congr
        intro f hf
        unfold intervalSize
        omega
      · intro f hf hf'
        unfold intervalSize
        omega
    · intro a ha ha'
      apply sumRange_zero
      intro f _
      unfold intervalSize
      omega

#print axioms targetNat_eq
#print axioms pascalNat_eq
end RankArithmetic82190
