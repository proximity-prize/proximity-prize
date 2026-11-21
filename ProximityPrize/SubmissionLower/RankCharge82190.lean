import ProximityPrize.SubmissionLower.RankArithmetic82190
import ProximityPrize.SubmissionLower.RankCatalog82190

set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2200000
namespace RankCharge82190
open MvPolynomial
open K1_13 (Geom)
open K1_13_1_1
open Pascal82190 (block degree)
open RankArithmetic82190
open AnchorBlock82190 (boundAt rank_at)
open SoundnessAnchor (Powers)
open scoped BigOperators

/-- For each block, select a proved scalar upper bound on its image rank. -/
inductive Method where
  | source
  | target
  | pascal
  | factor (powers : Powers)
  | rows

def value (s r : ℕ) (m : Method) : ℕ :=
  if s + r < 138 then
    let d := degree s
    let g := offset r
    let band := natBandTwelve d (48-r) 48
    match m with
    | .source => band
    | .target => targetNat d (48-r) (138-(s+r))
    | .pascal => pascalNat s r
    | .factor v => boundAt d s g v
    | .rows =>
      if d = 48 then band - (RankRows82190.catalog.filter (RankRows82190.accept s g)).length
      else band
  else 0

theorem bounded (s r : ℕ) (hs : s ≤ 120) (m : Method) :
    Module.finrank Geom (LinearMap.range (block s (offset r))) ≤ value s r m := by
  let g := offset r
  let d := degree s
  let φ := block s g
  change Module.finrank Geom (LinearMap.range φ) ≤ _
  have hglo : -48 ≤ g := by dsimp [g,offset]; omega
  have hlo : (-g).toNat = 48-r := by dsimp [g,offset]; omega
  have hord : (orderCutoff s g).toNat = 138-(s+r) := by dsimp [orderCutoff,g,offset]; omega
  have hband : bandCount d (-g) 48 12 = natBandTwelve d (48-r) 48 := by
    rw [natBandTwelve_eq d (-g) 48 (by decide),hlo]; rfl
  have hsource : Module.finrank Geom (LinearMap.range φ) ≤ bandCount d (-g) 48 12 := by
    let : Module.Finite Geom (bandSpace d (-g) 48 12) := bandSpace_finite _ _ _ _
    exact (LinearMap.finrank_range_le φ).trans_eq (finrank_bandSpace d (-g) 48 12)
  unfold value
  split
  next h =>
    have hg : g < 90-(s : ℤ) := by dsimp [g,offset]; omega
    cases m with
    | source => exact hsource.trans_eq hband
    | factor v => exact rank_at d s g v
    | pascal => exact (Pascal82190.rank_le s g hs hglo hg).trans_eq (pascalNat_eq s r h).symm
    | target =>
      let zero : Powers := ⟨⟨0,0,0,0⟩,0⟩
      have hz := rank_at d s g zero
      change Module.finrank Geom (LinearMap.range φ) ≤ _ at hz
      have hz' : boundAt d s g zero =
          bandCount d (-g) 48 12 - (bandCount d (-g) 48 12 - targetCount d (-g) (orderCutoff s g)) := by
        simp [boundAt,zero,Powers.degree,Powers.minIndex,Powers.maxIndex,Powers.maxTop,
          Powers.minOrder,FactorPowers.degree,FactorPowers.minIndex,FactorPowers.maxIndex,
          FactorPowers.maxTop,FactorPowers.minOrder]
      rw [hz',targetNat_eq,hlo,hord] at hz
      change Module.finrank Geom (LinearMap.range φ) ≤ targetNat d (48-r) (138-(s+r))
      omega
    | rows =>
      dsimp only
      by_cases hd : d = 48
      · rw [ite_eq_left hd,← hband]
        change Module.finrank Geom (LinearMap.range (AnchorBlock82190.blockAt d s g)) ≤ _
        rw [hd]
        have hx := RankRows82190.count_bound RankRows82190.catalog 48 s g
          RankRows82190.good RankRows82190.sorted
        change Module.finrank Geom (LinearMap.range (AnchorBlock82190.blockAt 48 s g)) ≤
          bandCount 48 (-g) 48 12 - (RankRows82190.catalog.filter (RankRows82190.accept s g)).length
        omega
      · exact (ite_eq_right hd).symm ▸ hsource.trans_eq hband
  next h =>
    have hz : φ = 0 := by
      apply LinearMap.ext
      intro q
      change weightedTruncation targetOrder (orderCutoff s g).toNat (backShift q) = 0
      have ho : (orderCutoff s g).toNat = 0 := by omega
      rw [ho, weightedTruncation_eq_zero_iff, restrictWeightedOrder_zero]
      trivial
    change Module.finrank Geom (LinearMap.range φ) ≤ 0
    rw [hz,LinearMap.range_zero,finrank_bot]

def grade (s : ℕ) (schedule : ℕ → Method) := sumRange 138 fun r => value s r (schedule r)
theorem grade_bound (s : Fin 121) (schedule : ℕ → Method) :
    (∑ r : Fin 138, Module.finrank Geom (LinearMap.range (block s (offset r)))) ≤ grade s schedule := by
  rw [grade,sumRange_eq_fin]
  exact Finset.sum_le_sum fun r _ => bounded s r (by omega) (schedule r)

theorem join {f : ℕ → ℕ} {n k x y : ℕ}
    (left : sumRange n f = x) (right : sumRange k (fun i => f (i+n)) = y) :
    sumRange (n+k) f = x+y := by rw [sumRange_add,left,right]

/-- Record the sum over the next six offsets of a grade. -/
theorem six {f : ℕ → ℕ} {n x : ℕ} (h : sumRange n f = x) (y : ℕ)
    (hy : sumRange 6 (fun i => f (i+n)) = y) : sumRange (n+6) f = x+y :=
  join h hy

#print axioms grade_bound
end RankCharge82190
