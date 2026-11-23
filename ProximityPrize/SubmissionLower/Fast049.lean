import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_5_3Proof
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_2_3_5
end K1_13_2_3_5
end
section
namespace K1_13_2_3_5
end K1_13_2_3_5
end
section
namespace K1_13_2_3_1
open K1_13_2
private def scaledDen (q r : ℤ) : ℤ :=
  2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem scaled_denominator (u : ℤ) (hu : 0 ≤ u) :
    2 * denominator u = scaledDen (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, not_lt.mpr hu, ite_false, scaledDen]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = _
  have h := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at h
  change _ = 2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
  linear_combination h + q * twice_half r + (57 + 6 * r) * twice_half q
private def prefixPolynomial (q r : ℤ) : ℤ :=
  984 * q + 3084 * q * (q - 1) + 1728 * q * (q - 1) * (q - 2) +
    216 * q * (q - 1) * (q - 2) * (q - 3) +
    24 * r + 4 * r * (r - 1) * (r + 1) +
    q * (528 * r + 84 * r * (r - 1) + 4 * r * (r - 1) * (r - 2)) +
    (684 * r + 36 * r * (r - 1)) * q * (q - 1) + 144 * r * q * (q - 1) * (q - 2)
def denPrefix (u : ℤ) : ℤ :=
  if u < 0 then 0 else prefixPolynomial (u / 6) (u % 6)
theorem denPrefix_of_nonpos (u : ℤ) (hu : u ≤ 0) : denPrefix u = 0 := by
  rcases lt_or_eq_of_le hu with h | rfl
  · simp [denPrefix, h]
  · decide
private theorem denPrefix_step (u : ℤ) :
    denPrefix (u + 1) - denPrefix u = 24 * denominator u := by
  by_cases h : u < 0
  · rw [denPrefix_of_nonpos _ (by omega), denPrefix_of_nonpos _ (by omega)]
    simp [denominator, h]
  have hd := scaled_denominator u (by omega)
  have hq : (u + 1) / 6 = u / 6 + (u % 6 + 1) / 6 := by omega
  have hr : (u + 1) % 6 = (u % 6 + 1) % 6 := by omega
  simp only [denPrefix, h, show ¬ u + 1 < 0 by omega, ite_false, hq, hr]
  have hlo : 0 ≤ u % 6 := by omega
  have hhi : u % 6 < 6 := by omega
  generalize u % 6 = r at hd hlo hhi ⊢
  interval_cases r <;> norm_num [prefixPolynomial, scaledDen] at hd ⊢ <;>
    linear_combination -12 * hd
theorem denPrefix_sum (a : ℤ) (n : ℕ) :
    24 * (∑ j ∈ Finset.range n, denominator (a + (j : ℤ))) =
      denPrefix (a + n) - denPrefix a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Nat.cast_succ, ← add_assoc, ← denPrefix_step]
    ring
end K1_13_2_3_1
end
section
namespace K1_13_2_3_1
open K1_13_2 K1_13_2_3
private theorem denominator_of_neg (u : ℤ) (h : u < 0) : denominator u = 0 := by
  simp [denominator, h]
private theorem cumulative_of_neg (d u : ℤ) (h : u < 0) : cumulative d u = 0 := by
  simp [cumulative, h]
private theorem cumulative_of_neg_degree (d u : ℤ) (h : d < 0) : cumulative d u = 0 := by
  simp [cumulative, h]
private theorem cumulative_eq_denominator (d u : ℤ) (h : u < d + 1) :
    cumulative d u = denominator u := by
  by_cases hu : u < 0
  · rw [cumulative_of_neg _ _ hu, denominator_of_neg _ hu]
  have hd : ¬ d < 0 := by omega
  simp (disch := omega) [cumulative, hu, hd, denominator_of_neg]
private theorem cumulative_nonneg (d : ℕ) (u : ℤ) : 0 ≤ cumulative (d : ℤ) u := by
  by_cases hu : u < 0
  · simp [cumulative_of_neg _ _ hu]
  have h := cumulative_mono d (show (-1 : ℤ) ≤ u by omega)
  rwa [cumulative_of_neg _ _ (by decide)] at h
private theorem denominator_nonneg (u : ℤ) : 0 ≤ denominator u := by
  by_cases hu : u < 0
  · simp [denominator_of_neg _ hu]
  have h := cumulative_nonneg u.toNat u
  rwa [Int.toNat_of_nonneg (by omega : 0 ≤ u), cumulative_eq_denominator _ _ (by omega)] at h
private theorem baseline_le_counts (i : BlockIndex) :
    baseline i ≤ (oldCount (initialFlag i)).toNat ∧
      baseline i ≤ (targetCount (initialFlag i)).toNat := by
  have hk : kernelLower (initialFlag i) = oldCount (initialFlag i) - targetCount (initialFlag i) := by
    simp [kernelLower, initialFlag]
  unfold baseline blockBound
  dsimp only
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · constructor <;> apply Int.toNat_le_toNat <;> apply (min_le_right _ _).trans
    · exact sub_le_self _ (le_max_left _ _)
    · have hm : kernelLower (initialFlag i) ≤ max 0 (max (kernelLower (initialFlag i))
          (kernelLower (residualFlag (initialFlag i) (fun _ => 0)))) :=
        (le_max_left _ _).trans (le_max_right _ _)
      omega
private def offsetBound (s x cut : ℕ) : ℤ :=
  let u := (x : ℤ) - (3000 - (s : ℤ))
  (if x < cut then cumulative (s : ℤ) x + denominator u else cumulative (s : ℤ) 1650) -
    cumulative (s : ℤ) u
private theorem oldCount_eq (s : Fin 4013) (j : Fin 4650) (hs : s.val < 1650)
    (x : ℕ) (hx : x + j.val + s.val = 4649) :
    oldCount (initialFlag (s, j)) =
      cumulative (s.val : ℤ) 1650 - cumulative (s.val : ℤ) ((x : ℤ) - (3000 - s.val)) := by
  have hc (u : ℤ) (hu : u ≤ 1650) : cappedCount (s.val : ℤ) u 550 = cumulative (s.val : ℤ) u := by
    simp (disch := omega) only [cappedCount, show ¬ (550 : ℤ) < 0 by decide, ite_false,
      cumulative_of_neg, sub_zero]
  simp only [oldCount, initialFlag, offset, min_eq_left (show (s.val : ℤ) ≤ 1650 by omega)]
  rw [show -((j.val : ℤ) - 1650) - 1 = (x : ℤ) - (3000 - s.val) by omega,
    min_eq_right (by omega : (x : ℤ) - (3000 - s.val) ≤ 1650), hc _ (by omega), hc _ (by omega)]
private theorem targetCount_eq (s : Fin 4013) (j : Fin 4650) (hs : s.val < 1650)
    (x : ℕ) (hx : x + j.val + s.val = 4649) (hx' : x < 1650) :
    targetCount (initialFlag (s, j)) = cumulative (s.val : ℤ) x +
      denominator ((x : ℤ) - (3000 - s.val)) -
      cumulative (s.val : ℤ) ((x : ℤ) - (3000 - s.val)) := by
  simp only [targetCount, initialFlag, offset, min_eq_left (show (s.val : ℤ) ≤ 1650 by omega)]
  rw [show 3000 - (s.val : ℤ) - ((j.val : ℤ) - 1650) - 1 = x by omega,
    show -((j.val : ℤ) - 1650) - 1 = (x : ℤ) - (3000 - s.val) by omega]
  rw [show (x : ℤ) - -((j.val : ℤ) - 1650) + s.val = 2999 by omega]
  norm_num only [Int.reduceLT, ite_false, Int.reduceDiv]
  by_cases h : s.val ≤ 749
  · rw [min_eq_left (show (s.val : ℤ) ≤ 749 by omega)]
    simp (disch := omega) only [cumulative_of_neg_degree, denominator_of_neg, sub_zero, add_zero]
  · rw [min_eq_right (show (749 : ℤ) ≤ s.val by omega)]
    rw [cumulative_of_neg ((s.val : ℤ) - (749 + 1)) ((x : ℤ) - 3 * (749 + 1)) (by omega),
      cumulative_eq_denominator ((s.val : ℤ) - (749 + 1)) ((x : ℤ) - (3000 - s.val)) (by omega),
      sub_zero]
    ring
private theorem offsetBound_nonneg (s x cut : ℕ) (hs : s < 1650) (hx : x < 4650 - s) :
    0 ≤ offsetBound s x cut := by
  unfold offsetBound
  dsimp only
  split
  · have hm := cumulative_mono s (show (x : ℤ) - (3000 - s) ≤ x by omega)
    have hd := denominator_nonneg ((x : ℤ) - (3000 - s))
    omega
  · exact sub_nonneg.mpr (cumulative_mono s (by omega))
private theorem baseline_le_offsetBound (s : Fin 4013) (j : Fin 4650) (hs : s.val < 1650)
    (cut x : ℕ) (hcut : cut ≤ 1650) (hx : x + j.val + s.val = 4649) :
    baseline (s, j) ≤ (offsetBound s.val x cut).toNat := by
  unfold offsetBound
  dsimp only
  split
  · rw [← targetCount_eq s j hs x hx (by omega)]
    exact (baseline_le_counts (s, j)).2
  · rw [← oldCount_eq s j hs x hx]
    exact (baseline_le_counts (s, j)).1
private theorem sum_cutoff {α : Type*} [AddCommMonoid α] (f : ℕ → α) {m n : ℕ} (h : m ≤ n) :
    (∑ j ∈ Finset.range n, if j < m then f j else 0) = ∑ j ∈ Finset.range m, f j := by
  calc
    _ = ∑ j ∈ Finset.range m, if j < m then f j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono h)
      intro j _ hj
      rw [Finset.mem_range] at hj
      rw [ite_eq_right hj]
    _ = _ := Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
private theorem sum_row (s : Fin 4013) (hs : s.val < 1650) (cut : ℕ) (hcut : cut ≤ 1650) :
    (∑ j : Fin 4650, baseline (s, j)) ≤
      ∑ x ∈ Finset.range (4650 - s.val), (offsetBound s.val x cut).toNat := by
  let n := 4650 - s.val
  calc
    _ ≤ ∑ j : Fin 4650, if j.val < n then (offsetBound s.val (n - 1 - j.val) cut).toNat else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j.val < n
      · rw [ite_eq_left hj]
        exact baseline_le_offsetBound s j hs cut _ hcut (by dsimp [n] at *; omega)
      · have ho : (initialFlag (s, j)).order ≤ 0 := by
          simp only [initialFlag, offset]
          dsimp [n] at hj
          omega
        simp [baseline, blockBound, ho, hj]
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if j < n then (offsetBound s.val (n - 1 - j) cut).toNat else 0)]
      rw [sum_cutoff _ (show n ≤ 4650 by dsimp [n]; omega)]
      exact Finset.sum_range_reflect (fun x : ℕ => (offsetBound s.val x cut).toNat) n
private def rowScaled (s cut : ℕ) : ℤ :=
  24 * (((4650 - s - cut : ℕ) : ℤ) * cumulative (s : ℤ) 1650 -
    ∑ x ∈ Finset.range (1650 - cut), cumulative (s : ℤ) ((cut + x : ℕ) : ℤ)) +
    denPrefix ((cut : ℤ) - (3000 - s))
private theorem sum_offsetBound (s cut : ℕ) (hs : s < 1650) (hcut : cut ≤ 1650) :
    24 * (∑ x ∈ Finset.range (4650 - s), offsetBound s x cut) = rowScaled s cut := by
  let n := 4650 - s
  let k : ℤ := 3000 - (s : ℤ)
  let C := cumulative (s : ℤ)
  let f := fun x : ℕ => C x + denominator ((x : ℤ) - k)
  have hChosen : (∑ x ∈ Finset.range n, if x < cut then f x else C 1650) =
      (∑ x ∈ Finset.range cut, f x) + ((n - cut : ℕ) : ℤ) * C 1650 := by
    conv_lhs => rw [show n = cut + (n - cut) by dsimp [n]; omega, Finset.sum_range_add]
    congr 1
    · exact Finset.sum_congr rfl fun _ hx => ite_eq_left (Finset.mem_range.mp hx)
    · simp (disch := omega) only [not_lt.mpr (Nat.le_add_right cut _), ite_false,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hLower : (∑ x ∈ Finset.range n, C ((x : ℤ) - k)) = ∑ x ∈ Finset.range 1650, C x := by
    rw [show n = (3000 - s) + 1650 by dsimp [n]; omega, Finset.sum_range_add]
    have hz : (∑ x ∈ Finset.range (3000 - s), C ((x : ℤ) - k)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hx' := Finset.mem_range.mp hx
      exact cumulative_of_neg _ _ (by dsimp [k]; omega)
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Nat.cast_add, Nat.cast_sub (show s ≤ 3000 by omega)]
    dsimp [k]
    ring
  have hSplit : (∑ x ∈ Finset.range 1650, C x) =
      (∑ x ∈ Finset.range cut, C x) +
        ∑ x ∈ Finset.range (1650 - cut), C ((cut + x : ℕ) : ℤ) := by
    rw [← Finset.sum_range_add, Nat.add_sub_of_le hcut]
  have hp : 24 * (∑ x ∈ Finset.range cut, denominator ((x : ℤ) - k)) = denPrefix ((cut : ℤ) - k) := by
    simp_rw [show ∀ x : ℕ, (x : ℤ) - k = -k + (x : ℤ) from fun x => by ring]
    rw [denPrefix_sum, denPrefix_of_nonpos (-k) (by dsimp [k]; omega), sub_zero]
  unfold rowScaled
  simp only [offsetBound, Finset.sum_sub_distrib]
  change 24 * ((∑ x ∈ Finset.range n, if x < cut then f x else C 1650) -
    ∑ x ∈ Finset.range n, C ((x : ℤ) - k)) =
      24 * (((n - cut : ℕ) : ℤ) * C 1650 -
        ∑ x ∈ Finset.range (1650 - cut), C ((cut + x : ℕ) : ℤ)) + denPrefix ((cut : ℤ) - k)
  rw [hChosen, hLower, hSplit]
  dsimp only [f]
  rw [Finset.sum_add_distrib]
  linear_combination hp
private def gradeCut (s : ℕ) : ℕ :=
  if s < 1549 then 1650 else if s < 1603 then 1649 else if s < 1641 then 1648 else 1647
private def grade (s : ℕ) : ℤ := rowScaled s (gradeCut s)
private theorem grade_bound (s : Fin 4013) (hs : s.val < 1650) :
    24 * ((∑ j : Fin 4650, baseline (s, j) : ℕ) : ℤ) ≤ grade s.val := by
  have hcut : gradeCut s.val ≤ 1650 := by
    unfold gradeCut
    split <;> (try split) <;> (try split) <;> omega
  calc
    _ ≤ 24 * ((∑ x ∈ Finset.range (4650 - s.val), (offsetBound s.val x (gradeCut s.val)).toNat : ℕ) : ℤ) := by
      apply mul_le_mul_of_nonneg_left _ (by decide)
      exact_mod_cast sum_row s hs _ hcut
    _ = 24 * (∑ x ∈ Finset.range (4650 - s.val), offsetBound s.val x (gradeCut s.val)) := by
      rw [Nat.cast_sum]
      congr 1
      exact Finset.sum_congr rfl fun x hx =>
        Int.toNat_of_nonneg (offsetBound_nonneg _ _ _ hs (Finset.mem_range.mp hx))
    _ = _ := sum_offsetBound _ _ hs hcut
private def total (start : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => total start n + grade (start + n)
private theorem total_eq (start n : ℕ) :
    total start n = ∑ j ∈ Finset.range n, grade (start + j) := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [total, Finset.sum_range_succ, ih]
private theorem k1231_total_append (s m n : ℕ) :
    total s (m + n) = total s m + total (s + m) n := by
  simp only [total_eq, Finset.sum_range_add, Nat.add_assoc]
private theorem k1231_total_join {s t m n k : ℕ} {a b c : ℤ}
    (ha : total s m = a) (hb : total t n = b)
    (ht : s + m = t) (hk : m + n = k) (hs : a + b = c) : total s k = c := by
  rw [← hk, k1231_total_append, ht, ha, hb, hs]
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private theorem k1231_grades_551 : total 551 16 = 27517850683872 := by
  decide +kernel
private theorem k1231_grades_567 : total 567 16 = 29734411311072 := by
  decide +kernel
private theorem k1231_grades_583 : total 583 16 = 32028905051616 := by
  decide +kernel
private theorem k1231_grades_599 : total 599 16 = 34385973281760 := by
  decide +kernel
private theorem k1231_grades_615 : total 615 16 = 36790609699296 := by
  decide +kernel
private theorem k1231_grades_631 : total 631 16 = 39228160323552 := by
  decide +kernel
private theorem k1231_grades_647 : total 647 16 = 41684323495392 := by
  decide +kernel
private theorem k1231_grades_663 : total 663 16 = 44145149877216 := by
  decide +kernel
private theorem k1231_grades_679 : total 679 16 = 46597042452960 := by
  decide +kernel
private theorem k1231_grades_695 : total 695 16 = 49026756528096 := by
  decide +kernel
private theorem k1231_grades_711 : total 711 16 = 51421399729632 := by
  decide +kernel
private theorem k1231_grades_727 : total 727 16 = 53768432006112 := by
  decide +kernel
private theorem k1231_grades_743 : total 743 16 = 56055665627616 := by
  decide +kernel
private theorem k1231_grades_759 : total 759 16 = 58271265185760 := by
  decide +kernel
private theorem k1231_grades_775 : total 775 16 = 60403747593696 := by
  decide +kernel
private theorem k1231_grades_791 : total 791 16 = 62441982086112 := by
  decide +kernel
private theorem k1231_grades_807 : total 807 16 = 64375190219232 := by
  decide +kernel
private theorem k1231_grades_823 : total 823 16 = 66193253109384 := by
  decide +kernel
private theorem k1231_grades_839 : total 839 16 = 67891598872128 := by
  decide +kernel
private theorem k1231_grades_855 : total 855 16 = 69472878502464 := by
  decide +kernel
private theorem k1231_grades_871 : total 871 16 = 70940659492416 := by
  decide +kernel
private theorem k1231_grades_887 : total 887 16 = 72298459159104 := by
  decide +kernel
private theorem k1231_grades_903 : total 903 16 = 73549744488000 := by
  decide +kernel
private theorem k1231_grades_919 : total 919 16 = 74697932132928 := by
  decide +kernel
private theorem k1231_grades_935 : total 935 16 = 75746388416064 := by
  decide +kernel
private theorem k1231_grades_951 : total 951 16 = 76698429327936 := by
  decide +kernel
private theorem k1231_grades_967 : total 967 16 = 77557320527424 := by
  decide +kernel
private theorem k1231_grades_983 : total 983 16 = 78326277341760 := by
  decide +kernel
private theorem k1231_grades_999 : total 999 16 = 79008464766528 := by
  decide +kernel
private theorem k1231_grades_1015 : total 1015 16 = 79606997465664 := by
  decide +kernel
private theorem k1231_grades_1031 : total 1031 16 = 80124939771456 := by
  decide +kernel
private theorem k1231_grades_1047 : total 1047 16 = 80565305684544 := by
  decide +kernel
private theorem k1231_grades_1063 : total 1063 16 = 80931058873920 := by
  decide +kernel
private theorem k1231_grades_1079 : total 1079 16 = 81225112676928 := by
  decide +kernel
private theorem k1231_grades_1095 : total 1095 16 = 81450330099264 := by
  decide +kernel
private theorem k1231_grades_1111 : total 1111 16 = 81609523814976 := by
  decide +kernel
private theorem k1231_grades_1127 : total 1127 16 = 81705456166464 := by
  decide +kernel
private theorem k1231_grades_1143 : total 1143 16 = 81740839164480 := by
  decide +kernel
private theorem k1231_grades_1159 : total 1159 16 = 81718334488128 := by
  decide +kernel
private theorem k1231_grades_1175 : total 1175 16 = 81640553484864 := by
  decide +kernel
private theorem k1231_grades_1191 : total 1191 16 = 81510057170496 := by
  decide +kernel
private theorem k1231_grades_1207 : total 1207 16 = 81329356229184 := by
  decide +kernel
private theorem k1231_grades_1223 : total 1223 16 = 81100911013440 := by
  decide +kernel
private theorem k1231_grades_1239 : total 1239 16 = 80827131544128 := by
  decide +kernel
private theorem k1231_grades_1255 : total 1255 16 = 80510377510464 := by
  decide +kernel
private theorem k1231_grades_1271 : total 1271 16 = 80152958270016 := by
  decide +kernel
private theorem k1231_grades_1287 : total 1287 16 = 79757132848704 := by
  decide +kernel
private theorem k1231_grades_1303 : total 1303 16 = 79325109940800 := by
  decide +kernel
private theorem k1231_grades_1319 : total 1319 16 = 78859047908928 := by
  decide +kernel
private theorem k1231_grades_1335 : total 1335 16 = 78361054784064 := by
  decide +kernel
private theorem k1231_grades_1351 : total 1351 16 = 77833188356040 := by
  decide +kernel
private theorem k1231_grades_1367 : total 1367 16 = 77277457488840 := by
  decide +kernel
private theorem k1231_grades_1383 : total 1383 16 = 76695824339568 := by
  decide +kernel
private theorem k1231_grades_1399 : total 1399 16 = 76090204918728 := by
  decide +kernel
private theorem k1231_grades_1415 : total 1415 16 = 75462469099464 := by
  decide +kernel
private theorem k1231_grades_1431 : total 1431 16 = 74814440617584 := by
  decide +kernel
private theorem k1231_grades_1447 : total 1447 16 = 74147897071560 := by
  decide +kernel
private theorem k1231_grades_1463 : total 1463 16 = 73464569922504 := by
  decide +kernel
private theorem k1231_grades_1479 : total 1479 16 = 72766144494192 := by
  decide +kernel
private theorem k1231_grades_1495 : total 1495 16 = 72054259973064 := by
  decide +kernel
private theorem k1231_grades_1511 : total 1511 16 = 71330509408200 := by
  decide +kernel
private theorem k1231_grades_1527 : total 1527 16 = 70596439711344 := by
  decide +kernel
private theorem k1231_grades_1543 : total 1543 16 = 69853547426688 := by
  decide +kernel
private theorem k1231_grades_1559 : total 1559 16 = 69103274454600 := by
  decide +kernel
private theorem k1231_grades_1575 : total 1575 16 = 68347041289800 := by
  decide +kernel
private theorem k1231_grades_1591 : total 1591 16 = 67586210218392 := by
  decide +kernel
private theorem k1231_grades_1607 : total 1607 16 = 66822074236464 := by
  decide +kernel
private theorem k1231_grades_1623 : total 1623 16 = 66055914261384 := by
  decide +kernel
private theorem k1231_grades_1639 : total 1639 11 = 44968541077224 := by
  decide +kernel
end
private theorem total_check : total 551 1099 = 4709579868565680 := by
  have h551_583 : total 551 32 = 57252261994944 :=
    k1231_total_join k1231_grades_551 k1231_grades_567 rfl rfl rfl
  have h583_615 : total 583 32 = 66414878333376 :=
    k1231_total_join k1231_grades_583 k1231_grades_599 rfl rfl rfl
  have h551_615 : total 551 64 = 0x70797ff83b80 :=
    k1231_total_join h551_583 h583_615 rfl rfl rfl
  have h615_647 : total 615 32 = 76018770022848 :=
    k1231_total_join k1231_grades_615 k1231_grades_631 rfl rfl rfl
  have h647_679 : total 647 32 = 85829473372608 :=
    k1231_total_join k1231_grades_647 k1231_grades_663 rfl rfl rfl
  have h615_679 : total 615 64 = 0x93333b0e1b80 :=
    k1231_total_join h615_647 h647_679 rfl rfl rfl
  have h551_679 : total 551 128 = 285515383723776 :=
    k1231_total_join h551_615 h615_679 rfl rfl rfl
  have h679_711 : total 679 32 = 95623798981056 :=
    k1231_total_join k1231_grades_679 k1231_grades_695 rfl rfl rfl
  have h711_743 : total 711 32 = 0x5fab6a8df9c0 :=
    k1231_total_join k1231_grades_711 k1231_grades_727 rfl rfl rfl
  have h679_743 : total 679 64 = 0xb6a3911ffb80 :=
    k1231_total_join h679_711 h711_743 rfl rfl rfl
  have h743_775 : total 743 32 = 0x67fad01971c0 :=
    k1231_total_join k1231_grades_743 k1231_grades_759 rfl rfl rfl
  have h791_823 : total 791 32 = 0x7356ec81b5c0 :=
    k1231_total_join k1231_grades_791 k1231_grades_807 rfl rfl rfl
  have h775_823 : total 775 48 = 0xaa46c46cd3a0 :=
    k1231_total_join k1231_grades_775 h791_823 rfl rfl rfl
  have h743_823 : total 743 80 = 301547850712416 :=
    k1231_total_join h743_775 h775_823 rfl rfl rfl
  have h679_823 : total 679 144 = 502361481429216 :=
    k1231_total_join h679_743 h743_823 rfl rfl rfl
  have h551_823 : total 551 272 = 787876865152992 :=
    k1231_total_join h551_679 h679_823 rfl rfl rfl
  have h823_855 : total 823 32 = 0x79f30ff8dcc8 :=
    k1231_total_join k1231_grades_823 k1231_grades_839 rfl rfl rfl
  have h855_887 : total 855 32 = 0x7fb4930dc880 :=
    k1231_total_join k1231_grades_855 k1231_grades_871 rfl rfl rfl
  have h823_887 : total 823 64 = 0xf9a7a306a548 :=
    k1231_total_join h823_855 h855_887 rfl rfl rfl
  have h887_919 : total 887 32 = 0x84a5ee5e9880 :=
    k1231_total_join k1231_grades_887 k1231_grades_903 rfl rfl rfl
  have h919_951 : total 919 32 = 0x88d40c48e880 :=
    k1231_total_join k1231_grades_919 k1231_grades_935 rfl rfl rfl
  have h887_951 : total 887 64 = 296292524196096 :=
    k1231_total_join h887_919 h919_951 rfl rfl rfl
  have h823_951 : total 823 128 = 570790914172488 :=
    k1231_total_join h823_887 h887_951 rfl rfl rfl
  have h951_983 : total 951 32 = 0x8c4b772cb880 :=
    k1231_total_join k1231_grades_951 k1231_grades_967 rfl rfl rfl
  have h983_1015 : total 983 32 = 0x8f18596a0880 :=
    k1231_total_join k1231_grades_983 k1231_grades_999 rfl rfl rfl
  have h951_1015 : total 951 64 = 311590491963648 :=
    k1231_total_join h951_983 h983_1015 rfl rfl rfl
  have h1015_1047 : total 1015 32 = 0x91467d60d880 :=
    k1231_total_join k1231_grades_1015 k1231_grades_1031 rfl rfl rfl
  have h1063_1095 : total 1063 32 = 0x937aed00e080 :=
    k1231_total_join k1231_grades_1063 k1231_grades_1079 rfl rfl rfl
  have h1047_1095 : total 1047 48 = 0xdcc0ff6e12c0 :=
    k1231_total_join k1231_grades_1047 h1063_1095 rfl rfl rfl
  have h1015_1095 : total 1015 80 = 402453414472512 :=
    k1231_total_join h1015_1047 h1047_1095 rfl rfl rfl
  have h951_1095 : total 951 144 = 714043906436160 :=
    k1231_total_join h951_1015 h1015_1095 rfl rfl rfl
  have h823_1095 : total 823 272 = 0x4908ceb13d288 :=
    k1231_total_join h823_951 h951_1095 rfl rfl rfl
  have h551_1095 : total 551 544 = 0x75d1ecbc06a68 :=
    k1231_total_join h551_823 h823_1095 rfl rfl rfl
  have h1095_1127 : total 1095 32 = 0x944d54ab7080 :=
    k1231_total_join k1231_grades_1095 k1231_grades_1111 rfl rfl rfl
  have h1127_1159 : total 1127 32 = 0x94a74e5f8080 :=
    k1231_total_join k1231_grades_1127 k1231_grades_1143 rfl rfl rfl
  have h1095_1159 : total 1095 64 = 326506149245184 :=
    k1231_total_join h1095_1127 h1127_1159 rfl rfl rfl
  have h1159_1191 : total 1159 32 = 0x9492f47d1080 :=
    k1231_total_join k1231_grades_1159 k1231_grades_1175 rfl rfl rfl
  have h1191_1223 : total 1191 32 = 0x941a01642080 :=
    k1231_total_join k1231_grades_1191 k1231_grades_1207 rfl rfl rfl
  have h1159_1223 : total 1159 64 = 326198301372672 :=
    k1231_total_join h1159_1191 h1191_1223 rfl rfl rfl
  have h1095_1223 : total 1095 128 = 652704450617856 :=
    k1231_total_join h1095_1159 h1159_1223 rfl rfl rfl
  have h1223_1255 : total 1223 32 = 0x9345cf74b080 :=
    k1231_total_join k1231_grades_1223 k1231_grades_1239 rfl rfl rfl
  have h1255_1287 : total 1255 32 = 0x921f590ec080 :=
    k1231_total_join k1231_grades_1255 k1231_grades_1271 rfl rfl rfl
  have h1223_1287 : total 1223 64 = 322591378338048 :=
    k1231_total_join h1223_1255 h1255_1287 rfl rfl rfl
  have h1287_1319 : total 1287 32 = 0x90af38925080 :=
    k1231_total_join k1231_grades_1287 k1231_grades_1303 rfl rfl rfl
  have h1335_1367 : total 1335 32 = 0x8e0ece60da08 :=
    k1231_total_join k1231_grades_1335 k1231_grades_1351 rfl rfl rfl
  have h1319_1367 : total 1319 48 = 0xd5c79bea9048 :=
    k1231_total_join k1231_grades_1319 h1335_1367 rfl rfl rfl
  have h1287_1367 : total 1287 80 = 394135533838536 :=
    k1231_total_join h1287_1319 h1319_1367 rfl rfl rfl
  have h1223_1367 : total 1223 144 = 716726912176584 :=
    k1231_total_join h1223_1287 h1287_1367 rfl rfl rfl
  have h1095_1367 : total 1095 272 = 0x4dd7d95ec73c8 :=
    k1231_total_join h1095_1223 h1223_1367 rfl rfl rfl
  have h1367_1399 : total 1367 32 = 0x8c09b2c4ae38 :=
    k1231_total_join k1231_grades_1367 k1231_grades_1383 rfl rfl rfl
  have h1399_1431 : total 1399 32 = 0x89d61b4cb390 :=
    k1231_total_join k1231_grades_1399 k1231_grades_1415 rfl rfl rfl
  have h1367_1431 : total 1367 64 = 305525955846600 :=
    k1231_total_join h1367_1399 h1399_1431 rfl rfl rfl
  have h1431_1463 : total 1431 32 = 0x877aff390e38 :=
    k1231_total_join k1231_grades_1431 k1231_grades_1447 rfl rfl rfl
  have h1479_1511 : total 1479 32 = 0x83b6a0c3b638 :=
    k1231_total_join k1231_grades_1479 k1231_grades_1495 rfl rfl rfl
  have h1463_1511 : total 1463 48 = 0xc6876e5bba00 :=
    k1231_total_join k1231_grades_1463 h1479_1511 rfl rfl rfl
  have h1431_1511 : total 1431 80 = 367247312078904 :=
    k1231_total_join h1431_1463 h1463_1511 rfl rfl rfl
  have h1367_1511 : total 1367 144 = 672773267925504 :=
    k1231_total_join h1367_1431 h1431_1511 rfl rfl rfl
  have h1511_1543 : total 1511 32 = 0x8114f162e638 :=
    k1231_total_join k1231_grades_1511 k1231_grades_1527 rfl rfl rfl
  have h1543_1575 : total 1543 32 = 0x7e616801e1c8 :=
    k1231_total_join k1231_grades_1543 k1231_grades_1559 rfl rfl rfl
  have h1511_1575 : total 1511 64 = 0xff765964c800 :=
    k1231_total_join h1511_1543 h1543_1575 rfl rfl rfl
  have h1575_1607 : total 1575 32 = 0x7ba16d2b57e0 :=
    k1231_total_join k1231_grades_1575 k1231_grades_1591 rfl rfl rfl
  have h1623_1650 : total 1623 27 = 0x64f9e538ca70 :=
    k1231_total_join k1231_grades_1623 k1231_grades_1639 rfl rfl rfl
  have h1607_1650 : total 1607 43 = 0xa1c01f3848a0 :=
    k1231_total_join k1231_grades_1607 h1623_1650 rfl rfl rfl
  have h1575_1650 : total 1575 75 = 313779781083264 :=
    k1231_total_join h1575_1607 h1607_1650 rfl rfl rfl
  have h1511_1650 : total 1511 139 = 594663552084096 :=
    k1231_total_join h1511_1575 h1575_1650 rfl rfl rfl
  have h1367_1650 : total 1367 283 = 0x480ba216e9280 :=
    k1231_total_join h1367_1511 h1511_1650 rfl rfl rfl
  have h1095_1650 : total 1095 555 = 0x95e37b75b0648 :=
    k1231_total_join h1095_1367 h1367_1650 rfl rfl rfl
  exact k1231_total_join h551_1095 h1095_1650 rfl rfl rfl
private theorem sum_grades :
    (∑ s ∈ Finset.range 4013, if 551 ≤ s ∧ s < 1650 then grade s else 0) = total 551 1099 := by
  simp_rw [show ∀ s : ℕ, (if 551 ≤ s ∧ s < 1650 then grade s else 0) =
    if s < 1650 then (if 551 ≤ s then grade s else 0) else 0 from fun s => by
      by_cases h : s < 1650 <;> simp [h]]
  rw [sum_cutoff _ (by decide : 1650 ≤ 4013), total_eq]
  rw [show (1650 : ℕ) = 551 + 1099 by decide, Finset.sum_range_add]
  have hz : (∑ x ∈ Finset.range 551, if 551 ≤ x then grade x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact ite_eq_right (not_le.mpr (Finset.mem_range.mp hx))
  rw [hz, zero_add]
  exact Finset.sum_congr rfl fun x _ => ite_eq_left (Nat.le_add_right 551 x)
theorem proof : K1_13_2_3.c1 := by
  have hb : 24 * ((baselineSum 551 1650 : ℕ) : ℤ) ≤
      ∑ s : Fin 4013, if 551 ≤ s.val ∧ s.val < 1650 then grade s.val else 0 := by
    unfold baselineSum baselineSumOn
    rw [← Finset.univ_product_univ, Finset.sum_product, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    by_cases h : 551 ≤ s.val ∧ s.val < 1650
    · simpa only [ite_eq_left h] using grade_bound s h.2
    · simp [h]
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => if 551 ≤ s ∧ s < 1650 then grade s else 0),
    sum_grades, total_check] at hb
  unfold K1_13_2_3.c1
  omega
end K1_13_2_3_1
end
section
namespace K1_13_2_3_3
open K1_13_2
open K1_13_2_3_1 (denPrefix denPrefix_of_nonpos denPrefix_sum)
private def twiceDenPoly (q r : ℤ) : ℤ :=
  12 * q^3 + (21 + 6 * r) * q^2 + (11 + 7 * r + r^2) * q + 2 + r + r^2
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem twice_denominator (u : ℤ) (hu : 0 ≤ u) :
    2 * denominator u = twiceDenPoly (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, ite_eq_right (not_lt.mpr hu)]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = twiceDenPoly q r
  have h := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at h
  unfold twiceDenPoly
  linear_combination h + q * twice_half r + (57 + 6 * r) * twice_half q
theorem prefix_offset_step (a j : ℤ) :
    denPrefix (a - j) - denPrefix (a - (j + 1)) = 24 * denominator (a - 1 - j) := by
  have h := (denPrefix_sum (a - 1 - j) 1).symm
  simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, Nat.cast_one] at h
  convert h using 1
  ring_nf
theorem denominator_of_neg (u : ℤ) (hu : u < 0) : denominator u = 0 := by
  simp only [denominator, ite_eq_left hu]
def smallCount (d u : ℤ) : ℤ :=
  denominator u - denominator (u - d - 1) - denominator (u - d - 2) -
    denominator (u - d - 3)
theorem cumulative_eq_small (d u : ℤ) (hd : 2 ≤ d) (hu : u ≤ 2 * d + 2) :
    cumulative d u = smallCount d u := by
  by_cases hn : u < 0
  · simp only [cumulative, hn, decide_true, Bool.or_true, ite_true, smallCount,
      denominator_of_neg u hn, denominator_of_neg (u - d - 1) (by omega),
      denominator_of_neg (u - d - 2) (by omega), denominator_of_neg (u - d - 3) (by omega),
      sub_zero]
  simp only [cumulative, smallCount, show ¬ d < 0 by omega, hn,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false, min_eq_left (by omega : u ≤ 3*d),
    show denominator (u - 2*d - 3) = 0 by simp [denominator, show u - 2*d - 3 < 0 by omega],
    show denominator (u - 2*d - 4) = 0 by simp [denominator, show u - 2*d - 4 < 0 by omega],
    show denominator (u - 2*d - 5) = 0 by simp [denominator, show u - 2*d - 5 < 0 by omega],
    show denominator (u - 3*d - 6) = 0 by simp [denominator, show u - 3*d - 6 < 0 by omega],
    add_zero, sub_zero]
theorem smallCount_eq_denominator (d u : ℤ) (h : u ≤ d) : smallCount d u = denominator u := by
  simp only [smallCount, denominator_of_neg (u - d - 1) (by omega),
    denominator_of_neg (u - d - 2) (by omega), denominator_of_neg (u - d - 3) (by omega), sub_zero]
def smallPrefix (d t : ℤ) : ℤ :=
  denPrefix t - denPrefix (t - (d + 1)) - denPrefix (t - (d + 2)) - denPrefix (t - (d + 3))
theorem smallPrefix_of_nonpos (d t : ℤ) (hd : 0 ≤ d) (ht : t ≤ 0) :
    smallPrefix d t = 0 := by
  unfold smallPrefix
  simp only [denPrefix_of_nonpos t ht, denPrefix_of_nonpos (t - (d + 1)) (by omega),
    denPrefix_of_nonpos (t - (d + 2)) (by omega), denPrefix_of_nonpos (t - (d + 3)) (by omega), sub_zero]
theorem smallPrefix_offset_step (d a j : ℤ) :
    smallPrefix d (a - j) - smallPrefix d (a - (j + 1)) = 24 * smallCount d (a - 1 - j) := by
  unfold smallPrefix smallCount
  have h (k : ℤ) :
      denPrefix (a - j - k) - denPrefix (a - (j + 1) - k) = 24 * denominator (a - 1 - j - k) := by
    convert prefix_offset_step (a - k) j using 1 <;> ring_nf
  rw [show a - 1 - j - d - 1 = a - 1 - j - (d + 1) by ring,
    show a - 1 - j - d - 2 = a - 1 - j - (d + 2) by ring,
    show a - 1 - j - d - 3 = a - 1 - j - (d + 3) by ring]
  linear_combination (norm := ring_nf) prefix_offset_step a j - h (d + 1) - h (d + 2) - h (d + 3)
theorem denominator_mono_to (u v : ℤ) (h : u ≤ v) (hv : v ≤ 1650) :
    denominator u ≤ denominator v := by
  have he (x : ℤ) (hx : x ≤ 1650) : cumulative 1650 x = denominator x :=
    (cumulative_eq_small _ _ (by decide) (by omega)).trans (smallCount_eq_denominator _ _ hx)
  rw [← he u (h.trans hv), ← he v hv]
  exact K1_13_2_3.cumulative_mono 1650 h
theorem denominator_quadruple (t : ℤ) (ht : 0 ≤ t) :
    4 * denominator t ≤ denominator (6 * (2 * (t / 6) + 1) + t % 6) := by
  let q := t / 6
  let r := t % 6
  have hq : 0 ≤ q := by dsimp [q]; omega
  have hr : 0 ≤ r := by dsimp [r]; omega
  have hr' : 0 ≤ 5 - r := by dsimp [r]; omega
  have h := twice_denominator t ht
  change 2 * denominator t = twiceDenPoly q r at h
  have hw := twice_denominator (6 * (2 * q + 1) + r) (by omega)
  rw [show (6 * (2 * q + 1) + r) / 6 = 2 * q + 1 by omega,
    show (6 * (2 * q + 1) + r) % 6 = r by omega] at hw
  have hp : twiceDenPoly (2 * q + 1) r - 4 * twiceDenPoly q r =
      48 * q^3 + 144 * q^2 + (134 + 2 * r * (5 - r)) * q + 38 + 2 * r * (5 - r) := by
    unfold twiceDenPoly
    ring
  have hn : 0 ≤ 48 * q^3 + 144 * q^2 + (134 + 2 * r * (5 - r)) * q + 38 + 2 * r * (5 - r) := by
    positivity
  change 4 * denominator t ≤ denominator (6 * (2 * q + 1) + r)
  omega
end K1_13_2_3_3
end
section
namespace K1_13_2_3_4
open K1_13_2 K1_13_2_3
def windowFlag (s j : ℕ) : Flag :=
  ⟨min s 1650, 1650 - (j : ℤ), 1650, 550, 4650 - (s : ℤ) - j⟩
def cubicFlag (F : Flag) (k : ℕ) : Flag :=
  ⟨F.degree - 3 * (k : ℤ), F.lower - 2 * k, F.upper - 3 * k, F.cap - k,
    F.order - 3 * k⟩
def cubicSavings (s j k : ℕ) : ℕ :=
  if k = 0 then 0 else
    let F := windowFlag s j
    let old := oldCount F
    let lower := max 0 (kernelLower F)
    (old - lower).toNat - (old - max lower (kernelLower (cubicFlag F k))).toNat
def entry (s q k : ℕ) : ℕ :=
  let j := 3000 + q - s
  if 993 ≤ j ∧ j ≤ 1581 then cubicSavings s j k else 0
def rowPower (code : ℕ) : ℕ → ℕ
  | 0 => code % 512
  | q + 1 => rowPower (code / 512) q
def rowSum (s q code : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => entry s q (code % 512) + rowSum s (q + 1) (code / 512) n
def rowsSum (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | row :: rows => rowSum s 0 row 71 + rowsSum (s + 1) rows
end K1_13_2_3_4
end
section
namespace K1_13_2_3_7
open K1_13_2 K1_13_2_3
def valuePower (s j : ℕ) : ℕ := 4650 - s - 4 * j
def witness (i : BlockIndex) : Powers := ⟨valuePower i.1.val i.2.val, 0, 0⟩
def fastDen (u : ℤ) : ℤ :=
  if u < 0 then 0 else u * (u * (2 * u + 21) + 66) / 72 + 1
def fastCum (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    if v ≤ d then fastDen v else
      let a := v - d
      let first := fastDen v - fastDen (a - 1) - fastDen (a - 2) -
        fastDen (a - 3)
      if v ≤ 2 * d + 2 then first else
        let b := v - 2 * d
        first + fastDen (b - 3) + fastDen (b - 4) + fastDen (b - 5)
def signedKernel (d j h : ℤ) : ℤ :=
  let low := 1649 - j
  let balance := h - (1650 - j) + d
  if balance < 0 then fastCum d 1650 - fastCum d low else
    let removed := min d (balance / 4) + 1
    fastCum d 1650 - fastCum d h + fastCum (d - removed) (h - 3 * removed) -
      fastCum (d - removed) low
def rangeSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rangeSum f n + f n
end K1_13_2_3_7
end
section
namespace K1_14_2_2_7
noncomputable section
open K1_14 K1_14_2 K1_14_2_2
open scoped Classical
def cutComponents (I : Ideal Ambient) (P : Jet) : Finset (Ideal Ambient) :=
  (I ⊔ Ideal.span {toJet P}).minimalPrimesFinset
def ConstantSeed (Q : Ideal Ambient) : Prop :=
  ∀ i : Fin 2, IsAlgebraic FX
    (Ideal.Quotient.mk Q (MvPolynomial.X (Fin.castLE (by decide : 2 ≤ 4) i)))
def movingComponents (I : Ideal Ambient) (P : Jet) : Finset (Ideal Ambient) :=
  (cutComponents I P).filter fun Q => ¬ ConstantSeed Q
def constantComponents (I : Ideal Ambient) (P : Jet) : Finset (Ideal Ambient) :=
  (cutComponents I P).filter ConstantSeed
end
end K1_14_2_2_7
end
