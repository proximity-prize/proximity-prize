/- Joint projection accounting at 68.36, derived from the pinned 68.33 source. -/
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from the frozen 68.32 submission of Bome2017, building on Lucieno
(PR 618) and BitWonka (PRs 581 and 582). KoalaBear 68.33 long branch, November 18. -/
/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,66 errors, right cap 168 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartCaps
import ProximityPrize.SubmissionLower.Koala6831IntrinsicPoleBound

namespace ProximityPrize.SubmissionLower.KB36JFactorCount
open Koala6831Intrinsic

open scoped BigOperators
open MvPolynomial RCN002 RCN044 RCN135 RCN136 RCN187 RCN234 RCN257 RCN264 RCN341 RCN344

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {K : Type} [Field K]

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K

private theorem embed_y_weight_lp32 : Fin.cases 0 (![1, 0, 0] : Fin 3 → ℕ) =
    (![0, 1, 0, 0] : Fin 4 → ℕ) := by
  ext i
  fin_cases i <;> rfl

private theorem embed_pair_weight_lp32 : Fin.cases 0 (![1, 1, 0] : Fin 3 → ℕ) =
    (![0, 1, 1, 0] : Fin 4 → ℕ) := by
  ext i
  fin_cases i <;> rfl

private theorem embed_z_weight_lp32 : Fin.cases 0 (![0, 0, 1] : Fin 3 → ℕ) =
    (![0, 0, 0, 1] : Fin 4 → ℕ) := by
  ext i
  fin_cases i <;> rfl

def longFlagPole_lp32 {P : Ideal (MvPolynomial (Fin 3) Ω)} [P.IsPrime]
    (a b c : ℕ) (v : Place Ω (CoordinateField Ω P)) : ℤ :=
  (a : ℤ) * max (poleOrder v.val (coordinate Ω P 1)) (poleOrder v.val (coordinate Ω P 0)) +
    ((b : ℤ) - a) * poleOrder v.val (coordinate Ω P 1) +
    (c : ℤ) * poleOrder v.val (coordinate Ω P 2)

private theorem longFlagPole_nonnegative_lp32 {P : Ideal (MvPolynomial (Fin 3) Ω)} [P.IsPrime]
    (a b c : ℕ) (hab : a ≤ b) (v : Place Ω (CoordinateField Ω P)) :
    0 ≤ longFlagPole_lp32 (P := P) a b c v := by
  have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
  unfold longFlagPole_lp32 poleOrder
  positivity

private theorem finite_flag_poles_le_relevant_lp32 {P : Ideal (MvPolynomial (Fin 3) Ω)} [P.IsPrime]
    (seed : SeparableLiteralCoordinate P) (a b c : ℕ) (hab : a ≤ b)
    (W : Finset (Place Ω (CoordinateField Ω P))) :
    (∑ v ∈ W, longFlagPole_lp32 (P := P) a b c v) ≤
      ∑ v ∈ literalRelevantPlaces seed, longFlagPole_lp32 (P := P) a b c v := by
  classical
  have hzero (v : Place Ω (CoordinateField Ω P)) (hv : v ∉ literalRelevantPlaces seed) :
      longFlagPole_lp32 (P := P) a b c v = 0 := by
    simp [longFlagPole_lp32, coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant seed v hv]
  calc
    _ = ∑ v ∈ W ∩ literalRelevantPlaces seed, longFlagPole_lp32 (P := P) a b c v := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro v hv hvin
      exact hzero v (fun h => hvin (Finset.mem_inter.mpr ⟨hv, h⟩))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun v _ _ => longFlagPole_nonnegative_lp32 a b c hab v)

theorem proper_tail_curve_point_count_lp32
    (F : Carrier K) (w p : ℕ) [CharP K p] (hp : p.Prime)
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (chart : CurveChartData F w P) (seed : SeparableLiteralCoordinate P)
    (hnonpersistent : ¬ ∀ delay, surfaceMap φ (tailNumerator F (w + delay)) ∈ P)
    (a b c y t z : ℕ) (hy : 1 ≤ y) (htt : 1 ≤ t) (hab : a ≤ b)
    (hY : wt ![0, 1, 0, 0] F ≤ y)
    (hT : wt ![0, 1, 1, 0] F ≤ t)
    (hZ : wt ![0, 0, 0, 1] F ≤ z)
    (ha : 1 + (2 * w + 3) * (y - 1) ≤ a)
    (hb : 1 + (2 * w + 3) * (t - 1) ≤ b)
    (hc : (2 * w + 3) * z ≤ c)
    (S : Finset (Fin 3 → Ω))
    (hpoint : ∀ v ∈ S, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hreg : ∀ v ∈ S, MvPolynomial.aeval v (surfaceMap φ (implicitRegularity F)) ≠ 0)
    (hroot : ∀ v ∈ S, ∀ j, MvPolynomial.aeval v (surfaceMap φ (tailNumerator F (w + j))) = 0) :
    (S.card : ℤ) ≤ (curveTailOrder F w P chart : ℤ) *
      ∑ v ∈ literalRelevantPlaces seed, longFlagPole_lp32 (P := P) a b c v := by
  classical
  let μ := curveTailOrder F w P chart
  let H := surfaceMap φ (implicitRegularity F)
  obtain ⟨_, hcase⟩ := curve_intrinsic_tail_dichotomy F w p hp P chart
  obtain ⟨delay, hd, hdμ, hproper⟩ := hcase.resolve_right hnonpersistent
  let N := surfaceMap φ (tailNumerator F (w + delay))
  have hY' : wt (Fin.cases 0 (![1, 0, 0] : Fin 3 → ℕ)) F ≤ y := by rwa [embed_y_weight_lp32]
  have hT' : wt (Fin.cases 0 (![1, 1, 0] : Fin 3 → ℕ)) F ≤ t := by rwa [embed_pair_weight_lp32]
  have hZ' : wt (Fin.cases 0 (![0, 0, 1] : Fin 3 → ℕ)) F ≤ z := by rwa [embed_z_weight_lp32]
  have hycap : N.weightedTotalDegree ![1, 0, 0] ≤ μ * a :=
    (tailNumerator_surface_wt_le_order_mul φ F ![1, 0, 0] y w delay μ hy hY' hd hdμ).trans
      (Nat.mul_le_mul_left _ ha)
  have htcap : N.weightedTotalDegree ![1, 1, 0] ≤ μ * b :=
    (tailNumerator_surface_wt_le_order_mul φ F ![1, 1, 0] t w delay μ htt hT' hd hdμ).trans
      (Nat.mul_le_mul_left _ hb)
  have hzcap : N.weightedTotalDegree ![0, 0, 1] ≤ μ * c :=
    (tailNumerator_surface_wt_le_order_mul φ F ![0, 0, 1] z w delay μ (Nat.zero_le z)
      hZ' hd hdμ).trans (Nat.mul_le_mul_left _ (by simpa using hc))
  have hcap : ∀ d ∈ N.support, d 0 ≤ μ * a ∧ d 0 + d 1 ≤ μ * b ∧ d 2 ≤ μ * c := by
    intro d hd
    refine ⟨?_, ?_, ?_⟩
    · simpa [RCN372.weight_fin3] using
        (MvPolynomial.le_weightedTotalDegree ![1, 0, 0] hd).trans hycap
    · simpa [RCN372.weight_fin3, add_comm] using
        (MvPolynomial.le_weightedTotalDegree ![1, 1, 0] hd).trans htcap
    · simpa [RCN372.weight_fin3] using
        (MvPolynomial.le_weightedTotalDegree ![0, 0, 1] hd).trans hzcap
  let cost : ℤ := (μ : ℤ) *
    ∑ v ∈ literalRelevantPlaces seed, longFlagPole_lp32 (P := P) a b c v
  have hcost : 0 ≤ cost := mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun v _ => longFlagPole_nonnegative_lp32 a b c hab v))
  have hpole (W : Finset (Place Ω (CoordinateField Ω P))) :
      (∑ v ∈ W, RCN346.poleOrder Ω (CoordinateField Ω P) v
        (MvPolynomial.aeval (coordinate Ω P) N /
          (MvPolynomial.aeval (coordinate Ω P) H) ^ (0 : ℕ))) ≤ (cost.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hcost]
    simp only [pow_zero, div_one]
    calc
      _ ≤ ∑ v ∈ W, (μ : ℤ) * longFlagPole_lp32 (P := P) a b c v := by
        apply Finset.sum_le_sum
        intro v _
        letI := v.property.2
        have he := poleOrder_eval_le_quotient_caps v.val
          (fun k => Valuation.IsTrivialOn.valuation_algebraMap_le_one v.val k)
          (Equiv.refl (Fin 3)) (coordinate Ω P) N (μ * a) (μ * b) (μ * c)
          (Nat.mul_le_mul_left μ hab) hcap
        change poleOrder v.val (MvPolynomial.aeval (coordinate Ω P) N) ≤ _
        refine he.trans_eq ?_
        simp only [Equiv.refl_apply, Nat.cast_mul, longFlagPole_lp32, max_comm]
        ring
      _ ≤ cost := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (finite_flag_poles_le_relevant_lp32 seed a b c hab W)
          (by positivity)
  have hbound := RCN257.finite_regular_zero_bound_of_separator Ω P seed H N 0 cost.toNat
    hproper chart.separant_not_mem hpole S hpoint hreg (fun v hv => hroot v hv delay)
  have hcast : (S.card : ℤ) ≤ (cost.toNat : ℤ) := by exact_mod_cast hbound
  rwa [Int.toNat_of_nonneg hcost] at hcast

theorem sum_point_counts_le_long_flag_poles_lp32 {A : Type} [Fintype A]
    (E : A → Type) [∀ i, Field (E i)] [∀ i, Algebra Ω (E i)]
    (W : ∀ i, Finset (Place Ω (E i))) (coords : ∀ i, Fin 3 → E i)
    (μ n : A → ℕ) (a b c dU dZ₀ dZ₁ : ℕ) (hab : a ≤ b)
    (hcount : ∀ i, (n i : ℤ) ≤ (μ i : ℤ) * ∑ v ∈ W i,
      ((a : ℤ) * max (poleOrder v.val (coords i 1)) (poleOrder v.val (coords i 0)) +
       ((b : ℤ) - a) * poleOrder v.val (coords i 1) +
       (c : ℤ) * poleOrder v.val (coords i 2)))
    (hU : (∑ i, (μ i : ℤ) * ∑ v ∈ W i,
      max (poleOrder v.val (coords i 1)) (poleOrder v.val (coords i 0))) ≤ dU)
    (hZ₀ : (∑ i, (μ i : ℤ) * ∑ v ∈ W i, poleOrder v.val (coords i 1)) ≤ dZ₀)
    (hZ₁ : (∑ i, (μ i : ℤ) * ∑ v ∈ W i, poleOrder v.val (coords i 2)) ≤ dZ₁) :
    (∑ i, n i) ≤ a * dU + (b - a) * dZ₀ + c * dZ₁ := by
  have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hs : (∑ i, (n i : ℤ)) ≤
      (a : ℤ) * dU + ((b : ℤ) - a) * dZ₀ + (c : ℤ) * dZ₁ := by
    calc
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hcount i)
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
        apply add_le_add (add_le_add ?_ ?_) ?_
        · simp_rw [show ∀ x y : ℤ, x * ((a : ℤ) * y) = (a : ℤ) * (x * y) by intros; ring,
            ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hU (by positivity)
        · simp_rw [show ∀ x y : ℤ, x * (((b : ℤ) - a) * y) = ((b : ℤ) - a) * (x * y) by intros; ring,
            ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hZ₀ (sub_nonneg.mpr hab')
        · simp_rw [show ∀ x y : ℤ, x * ((c : ℤ) * y) = (c : ℤ) * (x * y) by intros; ring,
            ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hZ₁ (by positivity)
  exact_mod_cast (show (∑ i, (n i : ℤ)) ≤ ((a * dU + (b - a) * dZ₀ + c * dZ₁ : ℕ) : ℤ) by
    simpa only [Nat.cast_add, Nat.cast_mul, Int.natCast_sub hab] using hs)

theorem long_first_tail_caps_lp32 (F : Carrier K)
    (hY : wt ![0, 1, 0, 0] F ≤ 22)
    (hT : wt ![0, 1, 1, 0] F ≤ 197)
    (hZ : wt ![0, 0, 0, 1] F ≤ 168) :
    let T := surfaceMap φ (tailNumerator F 131071)
    T.degreeOf 0 ≤ 5505004 ∧
      (∀ d ∈ T.support, d 0 + d 1 ≤ 51380029) ∧
      T.degreeOf 2 ≤ 44040024 := by
  let T := surfaceMap φ (tailNumerator F 131071)
  have hw (α : Fin 3 → ℕ) (cap : ℕ) (hg : wt (Fin.cases 0 α) F ≤ cap)
      (hα : α 0 ≤ cap) :
      T.weightedTotalDegree α ≤ α 0 + (2 * 131071 + 1) * (cap - α 0) := by
    have hu := tailNumerator_surface_wt_le_order_mul φ F α cap 131070 1 1 hα hg
      (by decide) (by decide)
    simpa only [one_mul, show 131070 + 1 = 131071 by decide] using hu
  refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_, ?_, MvPolynomial.degreeOf_le_iff.mpr ?_⟩
  · intro d hd
    simpa [RCN372.weight_fin3] using
      ((MvPolynomial.le_weightedTotalDegree ![1, 0, 0] hd).trans
        (hw ![1, 0, 0] 22 (by rwa [embed_y_weight_lp32]) (by decide)))
  · intro d hd
    simpa [RCN372.weight_fin3, add_comm] using
      ((MvPolynomial.le_weightedTotalDegree ![1, 1, 0] hd).trans
        (hw ![1, 1, 0] 197 (by rwa [embed_pair_weight_lp32]) (by decide)))
  · intro d hd
    simpa [RCN372.weight_fin3] using
      ((MvPolynomial.le_weightedTotalDegree ![0, 0, 1] hd).trans
        (hw ![0, 0, 1] 168 (by rwa [embed_z_weight_lp32]) (by decide)))

end

end ProximityPrize.SubmissionLower.KB36JFactorCount

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
