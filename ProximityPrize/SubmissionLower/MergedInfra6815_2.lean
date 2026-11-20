import ProximityPrize.SubmissionLower.BoundaryTailArithmetic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import ProximityPrize.SubmissionLower.MergedInfra6815_1
import ProximityPrize.SubmissionLower.LowerFoundation
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.BoundaryTail

open scoped BigOperators

noncomputable section

variable {L : Type*} [Field L]

local instance : DecidableEq L := Classical.decEq L

def refinedMonomial (n j : ℕ) (H G J C : L) : L :=
  H ^ j * G ^ (n - 1 - j) * J ^ (n - 2 - 2 * j) * C

def refinedWeight (n j : ℕ) (a b c : ℤ) : ℤ :=
  (j : ℤ) * a + ((n - 1 - j : ℕ) : ℤ) * b +
    ((n - 2 - 2 * j : ℕ) : ℤ) * c

theorem refinedWeight_eq {n j : ℕ} (hn : 2 ≤ n) (hj : j < n)
    (a b c : ℤ) :
    refinedWeight n j a b c =
      (j : ℤ) * a + ((n : ℤ) - 1 - j) * b +
        max ((n : ℤ) - 2 - 2 * j) 0 * c := by
  have hsub : ((n - 1 - j : ℕ) : ℤ) = (n : ℤ) - 1 - j := by omega
  have htail : ((n - 2 - 2 * j : ℕ) : ℤ) =
      max ((n : ℤ) - 2 - 2 * j) 0 := by omega
  simp only [refinedWeight, hsub, htail]

theorem refined_monomial_value_le_exp
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n j : ℕ} (hn : 2 ≤ n) (hj : j < n)
    (H G J C : L) (h g q A B D : ℤ)
    (hH : v H ≤ WithZero.exp h) (hG : v G ≤ WithZero.exp g)
    (hJ : v J ≤ WithZero.exp q)
    (hC : v C ≤ WithZero.exp
      ((j : ℤ) * (B - A) + ((min (2 * j) (n - 2) : ℕ) : ℤ) * D)) :
    v (refinedMonomial n j H G J C) ≤ WithZero.exp
      (((n - 1 : ℕ) : ℤ) * B + ((n - 2 : ℕ) : ℤ) * D -
        refinedWeight n j (A - h) (B - g) (D - q)) := by
  have hpow (x : L) (e : ℤ) (hx : v x ≤ WithZero.exp e) (k : ℕ) :
      v x ^ k ≤ WithZero.exp ((k : ℤ) * e) := by
    rw [← nsmul_eq_mul, WithZero.exp_nsmul]
    exact pow_le_pow_left₀ zero_le hx k
  have hsub : ((n - 1 - j : ℕ) : ℤ) + j = ((n - 1 : ℕ) : ℤ) := by omega
  have hmin : ((n - 2 - 2 * j : ℕ) : ℤ) +
      ((min (2 * j) (n - 2) : ℕ) : ℤ) = ((n - 2 : ℕ) : ℤ) := by omega
  unfold refinedMonomial
  simp only [map_mul, map_pow]
  calc
    _ ≤ WithZero.exp ((j : ℤ) * h) *
        WithZero.exp (((n - 1 - j : ℕ) : ℤ) * g) *
        WithZero.exp (((n - 2 - 2 * j : ℕ) : ℤ) * q) *
        WithZero.exp ((j : ℤ) * (B - A) +
          ((min (2 * j) (n - 2) : ℕ) : ℤ) * D) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' (hpow H h hH j)
        (hpow G g hG (n - 1 - j))) (hpow J q hJ (n - 2 - 2 * j))) hC
    _ = _ := by
      rw [← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add]
      congr 1
      unfold refinedWeight
      nlinarith [congrArg (fun t : ℤ => t * B) hsub,
        congrArg (fun t : ℤ => t * D) hmin]

theorem refined_monomial_value_le
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n j : ℕ} (hn : 2 ≤ n) (hj : j < n)
    (H G J C : L) (hH : H ≠ 0) (hG : G ≠ 0) (hJ : J ≠ 0)
    (A B D : ℤ)
    (hC : v C ≤ WithZero.exp
      ((j : ℤ) * (B - A) + ((min (2 * j) (n - 2) : ℕ) : ℤ) * D)) :
    v (refinedMonomial n j H G J C) ≤ WithZero.exp
      (((n - 1 : ℕ) : ℤ) * B + ((n - 2 : ℕ) : ℤ) * D -
        refinedWeight n j (A - (v H).log) (B - (v G).log) (D - (v J).log)) :=
  refined_monomial_value_le_exp v hn hj H G J C _ _ _ A B D
    (WithZero.le_exp_of_log_le (le_refl _))
    (WithZero.le_exp_of_log_le (le_refl _))
    (WithZero.le_exp_of_log_le (le_refl _)) hC

theorem zero_sum_has_no_strictly_dominant_term
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → L) (i : ι)
    (hi : T i ≠ 0) (hsum : ∑ j, T j = 0) :
    ¬ (∀ j, j ≠ i → v (T j) < v (T i)) := by
  intro hlt
  have hsmall : v (∑ j ∈ Finset.univ.erase i, T j) < v (T i) := by
    apply v.map_sum_lt (by simpa using hi)
    intro j hj
    exact hlt j (Finset.mem_erase.mp hj).1
  have hsplit : (∑ j ∈ Finset.univ.erase i, T j) + T i = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hsum
  have hneg : (∑ j ∈ Finset.univ.erase i, T j) = -T i :=
    eq_neg_of_add_eq_zero_left hsplit
  rw [hneg, v.map_neg] at hsmall
  exact lt_irrefl _ hsmall

theorem first_tail_shifted_constraint
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n : ℕ} (hn : 2 ≤ n) (H G J : L)
    (hH : H ≠ 0) (hG : G ≠ 0) (hJ : J ≠ 0)
    (C : Fin n → L) (A B D : ℤ)
    (hD : (v J).log ≤ D)
    (hC : ∀ j, v (C j) ≤ WithZero.exp
      ((j.val : ℤ) * (B - A) + ((min (2 * j.val) (n - 2) : ℕ) : ℤ) * D))
    (hlead : v (C ⟨0, by omega⟩) = 1)
    (hzero : ∑ j, refinedMonomial n j.val H G J (C j) = 0) :
    (A - (v H).log) - (B - (v G).log) ≤ 2 * (D - (v J).log) := by
  classical
  by_contra hgap
  let i : Fin n := ⟨0, by omega⟩
  let T : Fin n → L := fun j => refinedMonomial n j.val H G J (C j)
  let P : ℤ := ((n - 1 : ℕ) : ℤ) * B + ((n - 2 : ℕ) : ℤ) * D
  let a := A - (v H).log
  let b := B - (v G).log
  let c := D - (v J).log
  have hleadval : v (T i) = WithZero.exp
      (P - (((n - 1 : ℕ) : ℤ) * b + ((n - 2 : ℕ) : ℤ) * c)) := by
    have hGv : v G ≠ 0 := (Valuation.ne_zero_iff v).mpr hG
    have hJv : v J ≠ 0 := (Valuation.ne_zero_iff v).mpr hJ
    simp only [T, i, refinedMonomial, pow_zero, one_mul, Nat.sub_zero,
      Nat.mul_zero, map_mul, map_pow, hlead, mul_one]
    rw [← WithZero.exp_log (pow_ne_zero (n - 1) hGv),
      ← WithZero.exp_log (pow_ne_zero (n - 2) hJv), ← WithZero.exp_add]
    congr 1
    simp only [WithZero.log_pow, nsmul_eq_mul, P, b, c]
    ring
  have hi : T i ≠ 0 := by
    intro hz
    have := hleadval
    rw [hz, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  apply zero_sum_has_no_strictly_dominant_term v T i hi hzero
  intro j hji
  have hjpos : 1 ≤ (j.val : ℤ) := by
    have : j.val ≠ 0 := by
      intro hz
      apply hji
      exact Fin.ext hz
    omega
  have hsep := leading_separation
    (n := (n : ℤ)) (j := (j.val : ℤ)) (a := a) (b := b) (c := c)
    (by omega) hjpos (by omega) (by dsimp [c]; omega) (by exact lt_of_not_ge hgap)
  have hvalue := refined_monomial_value_le v hn j.isLt H G J (C j)
    hH hG hJ A B D (hC j)
  change v (T j) ≤ WithZero.exp (P - refinedWeight n j.val a b c) at hvalue
  apply lt_of_le_of_lt hvalue
  rw [hleadval]
  apply WithZero.exp_lt_exp.mpr
  rw [refinedWeight_eq hn j.isLt]
  have hsub1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hsub2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  rw [hsub1, hsub2]
  linarith

theorem later_tail_value_le_exp
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n : ℕ} (hn : 2 ≤ n) (H G J : L)
    (C : Fin n → L) (h g q A B D : ℤ)
    (hH : v H ≤ WithZero.exp h) (hG : v G ≤ WithZero.exp g)
    (hJ : v J ≤ WithZero.exp q)
    (hA : h ≤ A) (hB : g ≤ B) (hD : q ≤ D)
    (hgap : (A - h) - (B - g) ≤ 2 * (D - q))
    (hC : ∀ j, v (C j) ≤ WithZero.exp
      ((j.val : ℤ) * (B - A) + ((min (2 * j.val) (n - 2) : ℕ) : ℤ) * D)) :
    v (∑ j, refinedMonomial n j.val H G J (C j)) ≤ WithZero.exp
      ((2 * (((n - 1 : ℕ) : ℤ) * B + ((n - 2 : ℕ) : ℤ) * D) -
          2 * ((n - 1 : ℕ) : ℤ) * (A - h) +
          (n : ℤ) * max ((A - h) - (B - g)) 0) / 2) := by
  apply v.map_sum_le
  intro j _
  apply le_trans (refined_monomial_value_le_exp v hn j.isLt H G J (C j)
    h g q A B D hH hG hJ (hC j))
  apply WithZero.exp_le_exp.mpr
  apply (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 2)).mpr
  have hweight := weighted_tail_bound
    (n := (n : ℤ)) (j := (j.val : ℤ))
    (a := A - h) (b := B - g) (c := D - q)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hgap
  rw [refinedWeight_eq hn j.isLt]
  have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hsub]
  nlinarith

theorem exists_admissible_exponents
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (H G J : L) (A B D : ℤ) (hH : H ≠ 0) (hAB : A ≤ B)
    (hA : (v H).log ≤ A)
    (hB : G ≠ 0 → (v G).log ≤ B) (hD : J ≠ 0 → (v J).log ≤ D)
    (hfirst : G ≠ 0 → J ≠ 0 →
      (A - (v H).log) - (B - (v G).log) ≤ 2 * (D - (v J).log)) :
    ∃ g q : ℤ,
      v G ≤ WithZero.exp g ∧ v J ≤ WithZero.exp q ∧
      g ≤ B ∧ q ≤ D ∧
      (A - (v H).log) - (B - g) ≤ 2 * (D - q) ∧
      max ((A - (v H).log) - (B - g)) 0 =
        max (max (v (G / H)).log 0 - (B - A)) 0 := by
  have hHv : v H ≠ 0 := (Valuation.ne_zero_iff v).mpr hH
  have hJchoice (g : ℤ)
      (hg : J ≠ 0 → (A - (v H).log) - (B - g) ≤ 2 * (D - (v J).log)) :
      ∃ q : ℤ, v J ≤ WithZero.exp q ∧ q ≤ D ∧
        (A - (v H).log) - (B - g) ≤ 2 * (D - q) := by
    by_cases hz : J = 0
    · refine ⟨D - max ((A - (v H).log) - (B - g)) 0, ?_, ?_, ?_⟩
      · simp only [hz, map_zero]; exact zero_le
      · omega
      · omega
    · exact ⟨(v J).log, WithZero.le_exp_of_log_le (le_refl _), hD hz, hg hz⟩
  by_cases hG : G = 0
  · obtain ⟨q, hqv, hqD, hq⟩ := hJchoice ((v H).log + B - A) (by
      intro hJ
      have := hD hJ
      omega)
    refine ⟨(v H).log + B - A, q, ?_, hqv, ?_, hqD, hq, ?_⟩
    · simp only [hG, map_zero]; exact zero_le
    · omega
    · simp only [hG, zero_div, map_zero, WithZero.log_zero]
      omega
  · obtain ⟨q, hqv, hqD, hq⟩ := hJchoice (v G).log (hfirst hG)
    refine ⟨(v G).log, q, WithZero.le_exp_of_log_le (le_refl _),
      hqv, hB hG, hqD, hq, ?_⟩
    have hGv : v G ≠ 0 := (Valuation.ne_zero_iff v).mpr hG
    rw [map_div₀, WithZero.log_div hGv hHv]
    omega

theorem normalized_tail_pole_le
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n : ℕ} (hn : 2 ≤ n) (H G J : L) (hH : H ≠ 0)
    (C : Fin n → L) (A u t : ℤ) (ht : 0 ≤ t) (htu : t ≤ u) (huA : u ≤ A)
    (hA : (v H).log ≤ A)
    (hB : G ≠ 0 → (v G).log ≤ A + 2 * u - t)
    (hD : J ≠ 0 → (v J).log ≤ A - u)
    (hfirst : G ≠ 0 → J ≠ 0 →
      (A - (v H).log) - (A + 2 * u - t - (v G).log) ≤
        2 * (A - u - (v J).log))
    (hC : ∀ j, v (C j) ≤ WithZero.exp
      ((j.val : ℤ) * (2 * u - t) +
        ((min (2 * j.val) (n - 2) : ℕ) : ℤ) * (A - u))) :
    2 * max (v (H ^ 3 * (∑ j, refinedMonomial n j.val H G J (C j)) /
      H ^ (n - 1))).log 0 ≤
      2 * (((n : ℤ) + 1) * A - ((n : ℤ) - 1) * t) +
        (n : ℤ) * max (2 * u) (t + max (v (G / H)).log 0) := by
  let T := ∑ j, refinedMonomial n j.val H G J (C j)
  let theta := max (2 * u) (t + max (v (G / H)).log 0)
  have htheta0 : 0 ≤ theta := by dsimp [theta]; omega
  have hnormal0 : 0 ≤ ((n : ℤ) + 1) * A - ((n : ℤ) - 1) * t := by
    have hprod := mul_nonneg (show 0 ≤ (n : ℤ) - 1 by omega)
      (show 0 ≤ A - t by omega)
    nlinarith
  have hright0 : 0 ≤ 2 * (((n : ℤ) + 1) * A - ((n : ℤ) - 1) * t) +
      (n : ℤ) * theta := by positivity
  change 2 * max (v (H ^ 3 * T / H ^ (n - 1))).log 0 ≤ _
  by_cases hT : T = 0
  · simpa only [hT, mul_zero, zero_div, map_zero, WithZero.log_zero,
      max_self, mul_zero] using hright0
  obtain ⟨g, q, hg, hq, hgB, hqD, hgap, hr⟩ := exists_admissible_exponents
    v H G J A (A + 2 * u - t) (A - u) hH (by omega) hA hB hD hfirst
  have hc' : ∀ j, v (C j) ≤ WithZero.exp
      ((j.val : ℤ) * ((A + 2 * u - t) - A) +
        ((min (2 * j.val) (n - 2) : ℕ) : ℤ) * (A - u)) := by
    convert hC using 1 <;> ring
  have hvalue := later_tail_value_le_exp v hn H G J C (v H).log g q
    A (A + 2 * u - t) (A - u)
    (WithZero.le_exp_of_log_le (le_refl _)) hg hq hA hgB hqD hgap hc'
  let Q : ℤ := 2 * (((n - 1 : ℕ) : ℤ) * (A + 2 * u - t) +
      ((n - 2 : ℕ) : ℤ) * (A - u)) -
      2 * ((n - 1 : ℕ) : ℤ) * (A - (v H).log) +
      (n : ℤ) * max ((A - (v H).log) - (A + 2 * u - t - g)) 0
  change v T ≤ WithZero.exp (Q / 2) at hvalue
  have hTv : v T ≠ 0 := (Valuation.ne_zero_iff v).mpr hT
  have hlog : (v T).log ≤ Q / 2 := by
    simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hTv WithZero.exp_ne_zero).mpr hvalue
  have htwolog : 2 * (v T).log ≤ Q := by omega
  have htheta := max_shift_identity (u := u) (v := t) (p := (v (G / H)).log) ht htu
  have htheta_ge : 0 ≤ theta - 2 * u := by dsimp [theta]; omega
  change max (theta - 2 * u) 0 = _ at htheta
  rw [max_eq_left htheta_ge] at htheta
  have hdelta : max ((A - (v H).log) - (A + 2 * u - t - g)) 0 = theta - 2 * u := by
    rw [hr, htheta]
    omega
  have hHv : v H ≠ 0 := (Valuation.ne_zero_iff v).mpr hH
  have hlogcut : (v (H ^ 3 * T / H ^ (n - 1))).log =
      (4 - (n : ℤ)) * (v H).log + (v T).log := by
    rw [map_div₀, map_mul, map_pow, map_pow,
      WithZero.log_div (mul_ne_zero (pow_ne_zero 3 hHv) hTv) (pow_ne_zero _ hHv),
      WithZero.log_mul (pow_ne_zero 3 hHv) hTv]
    simp only [WithZero.log_pow, nsmul_eq_mul, Nat.cast_ofNat]
    have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [hsub]
    ring
  rw [hlogcut]
  by_cases hnonneg : 0 ≤ (4 - (n : ℤ)) * (v H).log + (v T).log
  · rw [max_eq_left hnonneg]
    dsimp [Q] at htwolog
    rw [hdelta] at htwolog
    have hsub1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hsub2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    rw [hsub1, hsub2] at htwolog
    nlinarith
  · rw [max_eq_right (by omega), mul_zero]
    exact hright0

end

end ProximityPrize.SubmissionLower.BoundaryTail
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN057 RCN095 RCN136 RCN156 RCN234 RCN313

noncomputable section
variable {K Ω : Type} [Field K] [Field Ω]

def coefficientFlag (m i r v z : ℕ) : FlagDegree :=
  ⟨min (2 * i) m * z, min (2 * i) m * v - i,
    2 * i + min (2 * i) m * (r - 2)⟩

theorem coefficientFlag_sub_safe {m i v : ℕ}
    (hm : 1 ≤ m) (hi : i ≤ m + 1) (hv : 2 ≤ v) : i ≤ min (2 * i) m * v := by
  have h : i ≤ 2 * min (2 * i) m := by
    by_cases hh : 2 * i ≤ m
    · rw [min_eq_left hh]; omega
    · rw [min_eq_right (by omega)]; omega
  have := Nat.mul_le_mul_left (min (2 * i) m) hv
  omega

theorem coefficientFlag_cumulative {m i r v : ℕ} (z : ℕ)
    (hm : 1 ≤ m) (hi : i ≤ m + 1) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    ((coefficientFlag m i r v z).all : ℤ) = coefficientWeight m i r 0 ∧
    (((coefficientFlag m i r v z).yz + (coefficientFlag m i r v z).all : ℕ) : ℤ) =
      coefficientWeight m i (r + v) 1 ∧
    (((coefficientFlag m i r v z).zOnly + (coefficientFlag m i r v z).yz +
      (coefficientFlag m i r v z).all : ℕ) : ℤ) = coefficientWeight m i (r + v + z) 1 := by
  have hsafe := coefficientFlag_sub_safe hm hi hv
  simp only [coefficientFlag, coefficientWeight, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub hr, Nat.cast_sub hsafe, Nat.cast_ofNat]
  constructor
  · ring
  constructor <;> ring

theorem weightBound_nat {w : Fin 4 → ℕ} {P : MvPolynomial (Fin 4) K} {a : ℕ}
    (h : WeightBound w P (a : ℤ)) : wt w P ≤ a := by
  rcases h with rfl | h
  · simp [wt, MvPolynomial.weightedTotalDegree]
  · exact_mod_cast h

theorem weightBounds_surfaceMap_flag (φ : Polynomial K →+* Ω)
    (P : MvPolynomial (Fin 4) K) (p : FlagDegree)
    (hR : WeightBound residualSWeights P (p.all : ℤ))
    (hYR : WeightBound residualYSWeights P ((p.yz + p.all : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights P ((p.zOnly + p.yz + p.all : ℕ) : ℤ)) :
    PolynomialInFlag p (surfaceMap φ P) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset φ P he)
  have hr := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans (weightBound_nat hR)
  have hm := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (weightBound_nat hYR)
  have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans (weightBound_nat hAll)
  simp [RCN081.weight_fin4, residualSWeights] at hr
  simp [RCN081.weight_fin4, residualYSWeights] at hm
  simp [RCN081.weight_fin4, residualTotalWeights] at ht
  exact ⟨hr, hm, ht⟩

theorem refinedCoefficients_surfaceMap_flag (φ : Polynomial K →+* Ω)
    (F : MvPolynomial (Fin 4) K) (m i r v z : ℕ)
    (hm : 1 ≤ m) (hi : i ≤ m + 1) (hr : 2 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ)) :
    PolynomialInFlag (coefficientFlag m i r v z) (surfaceMap φ (refinedCoefficients F m i)) := by
  obtain ⟨hcR, hcYR, hcAll⟩ := coefficientFlag_cumulative z hm hi hr hv
  apply weightBounds_surfaceMap_flag
  · rw [hcR]
    exact refinedCoefficients_weightBound residualSWeights 0 rfl rfl rfl (by omega) F _ hR m i
  · rw [hcYR]
    convert refinedCoefficients_weightBound residualYSWeights 1 rfl rfl rfl (by omega)
      F _ hYR m i using 1 <;> push_cast <;> rfl
  · rw [hcAll]
    convert refinedCoefficients_weightBound residualTotalWeights 1 rfl rfl rfl (by omega)
      F _ hAll m i using 1 <;> push_cast <;> rfl

theorem boundary_surfaceMap_flags (φ : Polynomial K →+* Ω)
    (F : MvPolynomial (Fin 4) K) (r v z : ℕ) (hr : 2 ≤ r) (hv : 1 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ)) :
    PolynomialInFlag ⟨z, v, r - 1⟩ (surfaceMap φ (polyH K F)) ∧
    PolynomialInFlag ⟨z, v - 1, r + 1⟩ (surfaceMap φ (polyG K F)) ∧
    PolynomialInFlag ⟨z, v, r - 2⟩ (surfaceMap φ (boundaryJ F)) := by
  have hR' := boundary_polynomial_bounds residualSWeights 0 rfl rfl rfl (by omega) F _ hR
  have hYR' := boundary_polynomial_bounds residualYSWeights 1 rfl rfl rfl (by omega) F _ hYR
  have hAll' := boundary_polynomial_bounds residualTotalWeights 1 rfl rfl rfl (by omega) F _ hAll
  have hr1 : 1 ≤ r := by omega
  refine ⟨?_, ?_, ?_⟩
  · apply weightBounds_surfaceMap_flag
    · convert hR'.1 using 1 <;> simp only [Nat.cast_sub hr1, Nat.cast_one]
    · convert hYR'.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hr1, Nat.cast_one] <;> ring
    · convert hAll'.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hr1, Nat.cast_one] <;> ring
  · apply weightBounds_surfaceMap_flag
    · convert hR'.2.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    · convert hYR'.2.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hv, Nat.cast_one] <;> ring
    · convert hAll'.2.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hv, Nat.cast_one] <;> ring
  · apply weightBounds_surfaceMap_flag
    · convert hR'.2.2 using 1 <;> simp only [Nat.cast_sub hr, Nat.cast_ofNat]
    · convert hYR'.2.2 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hr, Nat.cast_ofNat] <;> ring
    · convert hAll'.2.2 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hr, Nat.cast_ofNat] <;> ring

theorem coefficientFlag_pole {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L)
    (m i r v z : ℕ) (hm : 1 ≤ m) (hi : i ≤ m + 1) (hv : 2 ≤ v) :
    RCN204.flagPole V x (coefficientFlag m i r v z) =
      (i : ℤ) * (2 * RCN204.flagPole V x unitAllFlag - RCN204.flagPole V x unitYZFlag) +
      ((min (2 * i) m : ℕ) : ℤ) * RCN204.flagPole V x (⟨z, v, r - 2⟩ : FlagDegree) := by
  have hsafe := coefficientFlag_sub_safe hm hi hv
  simp only [RCN204.flagPole, coefficientFlag, unitAllFlag, unitYZFlag,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_sub hsafe]
  ring

theorem refinedCoefficients_value_le {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a, V (coeff a) ≤ 1) (x : Fin 3 → L)
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) (m i r v z : ℕ)
    (hm : 1 ≤ m) (hi : i ≤ m + 1) (hr : 2 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ)) :
    V (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (refinedCoefficients F m i))) ≤
      WithZero.exp ((i : ℤ) * (2 * RCN204.flagPole V x unitAllFlag -
        RCN204.flagPole V x unitYZFlag) + ((min (2 * i) m : ℕ) : ℤ) *
        RCN204.flagPole V x (⟨z, v, r - 2⟩ : FlagDegree)) := by
  rw [← coefficientFlag_pole V x m i r v z hm hi hv]
  exact RCN204.valuation_eval_le_flag V coeff hcoeff x _ _
    (refinedCoefficients_surfaceMap_flag φ F m i r v z hm hi hr hv hR hYR hAll)

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN056 RCN313
open scoped BigOperators

noncomputable section
variable {K : Type*} [CommRing K]
local notation "Poly4" => MvPolynomial (Fin 4) K

theorem refined_monomial_step (F P : Poly4) (m i : ℕ) (hi : i ≤ m + 1) :
    baseStep F m (refinedMonomial F m i P) =
      refinedMonomial F (m + 1) i (contributionA F m i P) +
      refinedMonomial F (m + 1) (i + 1)
        (contributionB F m i P + contributionC F m i P +
          if i = m + 1 then contributionF F P else 0) +
      if i ≤ m then refinedMonomial F (m + 1) (i + 2)
        (contributionD F m i P + contributionE F m i P) else 0 := by
  simp only [baseStep, refinedMonomial]
  rw [expanded_monomial_step]
  by_cases htop : i = m + 1
  · subst i
    have hs0 : sExponent m (m + 1) = 0 := by unfold sExponent; omega
    have hs1 : sExponent (m + 1) (m + 1) = 0 := by unfold sExponent; omega
    have hs2 : sExponent (m + 1) (m + 1 + 1) = 0 := by unfold sExponent; omega
    have hGexp : m + 1 + 1 - (m + 1) = 1 := by omega
    simp only [contributionA, contributionB, contributionC, contributionF,
      hs0, hs1, hs2, hGexp, Nat.lt_irrefl, if_false, Nat.le_add_left, if_true,
      show ¬ m + 1 ≤ m by omega, ↓reduceIte]
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_sub, Nat.zero_add,
      Nat.sub_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_zero, pow_zero, pow_succ, zero_mul, mul_zero, one_mul, mul_one,
      dZero]
    ring
  · have him : i ≤ m := by omega
    have hb0 : m + 1 + 1 - i = (m + 1 - i) + 1 := by omega
    have hb1 : m + 1 + 1 - (i + 1) = m + 1 - i := by omega
    have hb2 : m + 1 + 1 - (i + 2) = m - i := by omega
    have hb3 : m + 1 - i = (m - i) + 1 := by omega
    have hcast : (m + 1 - i : Poly4) = ((m + 1 - i : ℕ) : Poly4) := by
      rw [Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    simp only [if_neg htop, if_pos him, contributionA, contributionB,
      contributionC, contributionD, contributionE, hb0, hb1, hb2, hb3, hcast]
    by_cases hs : 2 * i ≤ m
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
      have he0 : sExponent (2 * i + d) i = d := by unfold sExponent; omega
      have he1 : sExponent (2 * i + d + 1) i = d + 1 := by unfold sExponent; omega
      have he2 : sExponent (2 * i + d + 1) (i + 1) = d - 1 := by unfold sExponent; omega
      have he3 : sExponent (2 * i + d + 1) (i + 2) = d - 3 := by unfold sExponent; omega
      have he4 : 2 * i + d - i = i + d := by omega
      simp only [he0, he1, he2, he3, he4]
      by_cases hd : d < 3
      · interval_cases d <;>
          norm_num [pow_add, pow_succ, dZero] <;> ring
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ d by omega)
        have h1 : 3 + s - 1 = s + 2 := by omega
        have h3 : 3 + s - 3 = s := by omega
        have h4 : 3 + s - (s + 2) = 1 := by omega
        have h5 : 3 + s - 1 - (s + 2) = 0 := by omega
        have h6 : 3 + s - 1 - s = 2 := by omega
        simp only [h1, h3, h4, h5, h6, show 0 < 3 + s by omega, if_true]
        norm_num [pow_add, pow_succ, dZero] <;> ring
    · have he0 : sExponent m i = 0 := by unfold sExponent; omega
      have he1 : sExponent (m + 1) i = 0 := by unfold sExponent; omega
      have he2 : sExponent (m + 1) (i + 1) = 0 := by unfold sExponent; omega
      have he3 : sExponent (m + 1) (i + 2) = 0 := by unfold sExponent; omega
      simp only [he0, he1, he2, he3]
      norm_num [pow_add, pow_succ, dZero] <;> ring

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN056 RCN313
open scoped BigOperators

noncomputable section
variable {K : Type*} [CommRing K]
local notation "Poly4" => MvPolynomial (Fin 4) K

theorem coefficient_selector_eq (m i q : ℕ) (A B D : Poly4) :
    (if q = i then A else if q = i + 1 then B else if q = i + 2 ∧ i ≤ m then D else 0) =
      (if q = i then A else 0) + (if q = i + 1 then B else 0) +
        (if q = i + 2 ∧ i ≤ m then D else 0) := by
  split_ifs <;> simp_all <;> omega

theorem refinedCoefficientStep_represents (F : Poly4) (m : ℕ) (C : ℕ → Poly4) :
    baseStep F m (∑ i ∈ Finset.range (m + 2), refinedMonomial F m i (C i)) =
      ∑ q ∈ Finset.range (m + 3),
        refinedMonomial F (m + 1) q (refinedCoefficientStep F m C q) := by
  rw [baseStep_sum]
  conv_rhs =>
    simp only [refinedCoefficientStep, coefficient_selector_eq,
      refinedMonomial, Finset.mul_sum, mul_add, mul_ite, mul_zero,
      Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m + 1 := by have := Finset.mem_range.mp hi; omega
  rw [refined_monomial_step F (C i) m i him]
  have hi0 : i ∈ Finset.range (m + 3) := by simp only [Finset.mem_range]; omega
  have hi1 : i + 1 ∈ Finset.range (m + 3) := by simp only [Finset.mem_range]; omega
  simp only [Finset.sum_add_distrib]
  by_cases hi2 : i ≤ m
  · have hi2mem : i + 2 ∈ Finset.range (m + 3) := by simp only [Finset.mem_range]; omega
    simp [hi2, hi0, hi1, hi2mem, refinedMonomial, mul_add]
  · simp [hi2, hi0, hi1, refinedMonomial, mul_add]

theorem baseNumerator_refined_sum (F : Poly4) (m : ℕ) :
    baseNumerator F m =
      ∑ i ∈ Finset.range (m + 2), refinedMonomial F m i (refinedCoefficients F m i) := by
  induction m with
  | zero => simp [baseNumerator, refinedMonomial, refinedCoefficients, sExponent]
  | succ m ih =>
    change baseStep F m (baseNumerator F m) = _
    rw [ih, refinedCoefficientStep_represents]
    rfl

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts

open BoundaryTailAlgebra RCN055 RCN313
variable {K : Type*} [Field K]
local notation "Poly4" => MvPolynomial (Fin 4) K
noncomputable section

def signedOddScalar : ℕ → K
  | 0 => 1
  | m + 1 => -(2 * m + 1 : K) * signedOddScalar m

@[simp] theorem signedOddScalar_zero : signedOddScalar (K := K) 0 = 1 := rfl

@[simp] theorem signedOddScalar_succ (m : ℕ) :
    signedOddScalar (K := K) (m + 1) = -(2 * m + 1 : K) * signedOddScalar m := by
  rfl

theorem signedOddScalar_ne_zero {p : ℕ} [CharP K p] (m : ℕ)
    (hm : 2 * m < p) : signedOddScalar (K := K) m ≠ 0 := by
  induction m with
  | zero => simp [signedOddScalar]
  | succ m ih =>
      rw [signedOddScalar_succ]
      apply mul_ne_zero
      · apply neg_ne_zero.mpr
        intro hz
        have hdvd : p ∣ 2 * m + 1 :=
          (CharP.cast_eq_zero_iff K p (2 * m + 1)).mp (by
            simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
              Nat.cast_one] using hz)
        exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
      · apply ih
        omega

theorem refinedCoefficients_zero (F : Poly4) (m : ℕ) :
    refinedCoefficients F m 0 = MvPolynomial.C (signedOddScalar (K := K) m) := by
  induction m with
  | zero => simp [refinedCoefficients]
  | succ m ih =>
      have hC2 : MvPolynomial.C (2 : K) = (2 : Poly4) :=
        map_natCast (MvPolynomial.C : K →+* Poly4) 2
      simp [refinedCoefficients, refinedCoefficientStep, ih, signedOddScalar,
        contributionA, sExponent, Nat.cast_add, Nat.cast_mul, hC2]

end
end ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN057 RCN095 RCN136 RCN156 RCN204 RCN234 RCN313
open BoundaryTailCoefficientFacts
open scoped BigOperators

noncomputable section
variable {K Ω L : Type} [Field K] [Field Ω] [Field L]

theorem map_baseNumerator_refined (ev : MvPolynomial (Fin 4) K →+* L)
    (F : MvPolynomial (Fin 4) K) (m : ℕ) :
    ev (baseNumerator F m) =
      ∑ i : Fin (m + 2), BoundaryTail.refinedMonomial (m + 2) i.val
        (ev (polyH K F)) (ev (polyG K F)) (ev (boundaryJ F))
        (ev (refinedCoefficients F m i.val)) := by
  rw [baseNumerator_refined_sum, map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [refinedMonomial, map_mul, map_pow, BoundaryTail.refinedMonomial,
    sExponent, Nat.max_zero, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega]

theorem boundary_flag_poles (V : Valuation L (WithZero (Multiplicative ℤ)))
    (x : Fin 3 → L) (r v z : ℕ) (hr : 3 ≤ r) (hv : 1 ≤ v) :
    let A := flagPole V x (⟨z, v, r - 1⟩ : FlagDegree)
    let u := flagPole V x unitAllFlag
    let t := flagPole V x unitYZFlag
    0 ≤ t ∧ t ≤ u ∧ u ≤ A ∧
      flagPole V x (⟨z, v, r - 2⟩ : FlagDegree) = A - u ∧
      flagPole V x (⟨z, v - 1, r + 1⟩ : FlagDegree) = A + 2 * u - t := by
  dsimp
  have hr1 : 1 ≤ r := by omega
  have hr2 : 2 ≤ r := by omega
  have hu0 := flagPole_nonneg V x unitAllFlag
  have ht0 := flagPole_nonneg V x unitYZFlag
  have hz0 : 0 ≤ RCN187.poleOrder V (x 2) := le_max_left _ _
  simp only [flagPole, unitAllFlag, unitYZFlag, Nat.cast_add, Nat.cast_sub hr1,
    Nat.cast_sub hr2, Nat.cast_sub hv, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat,
    zero_mul, one_mul, zero_add, add_zero] at *
  refine ⟨ht0, le_max_right _ _, ?_, ?_, ?_⟩
  · have := mul_nonneg (show 0 ≤ (r : ℤ) - 2 by omega) hu0
    have := mul_nonneg (show 0 ≤ (v : ℤ) by omega) ht0
    have := mul_nonneg (show 0 ≤ (z : ℤ) by omega) hz0
    nlinarith
  · ring
  · ring

theorem actual_tail_normalized_pole_le
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a : Ω, a ≠ 0 → V (coeff a) = 1)
    (x : Fin 3 → L) (φ : Polynomial K →+* Ω)
    (F : MvPolynomial (Fin 4) K) (m₀ m r v z p : ℕ) [CharP K p]
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) (hchar : 2 * m₀ < p)
    (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (hH : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)) ≠ 0)
    (hfirst : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (baseNumerator F m₀)) = 0) :
    let ev := (MvPolynomial.eval₂Hom coeff x).comp (surfaceMap φ)
    let A := flagPole V x (⟨z, v, r - 1⟩ : FlagDegree)
    let t := flagPole V x unitYZFlag
    let u := flagPole V x unitAllFlag
    2 * max (V (ev (polyH K F) ^ 3 * ev (baseNumerator F m) /
      ev (polyH K F) ^ (m + 1))).log 0 ≤
      2 * (((m : ℤ) + 3) * A - ((m : ℤ) + 1) * t) +
        ((m : ℤ) + 2) * max (2 * u) (t + max (V (ev (polyG K F) / ev (polyH K F))).log 0) := by
  classical
  let ev := (MvPolynomial.eval₂Hom coeff x).comp (surfaceMap φ)
  let H := ev (polyH K F)
  let G := ev (polyG K F)
  let J := ev (boundaryJ F)
  let A := flagPole V x (⟨z, v, r - 1⟩ : FlagDegree)
  let u := flagPole V x unitAllFlag
  let t := flagPole V x unitYZFlag
  have hc : ∀ a : Ω, V (coeff a) ≤ 1 := by
    intro a
    letI : Decidable (a = 0) := Classical.propDecidable _
    by_cases ha : a = 0
    · simp [ha]
    · rw [hcoeff a ha]
  obtain ⟨ht0, htu, huA, hJcap, hGcap⟩ := boundary_flag_poles V x r v z hr (by omega)
  obtain ⟨hHF, hGF, hJF⟩ := boundary_surfaceMap_flags φ F r v z (by omega) (by omega) hR hYR hAll
  have log_cap (P : MvPolynomial (Fin 3) Ω) (cap : FlagDegree)
      (hP : PolynomialInFlag cap P) (hne : MvPolynomial.eval₂Hom coeff x P ≠ 0) :
      (V (MvPolynomial.eval₂Hom coeff x P)).log ≤ flagPole V x cap := by
    have hh := valuation_eval_le_flag V coeff hc x cap P hP
    simpa only [WithZero.log_exp] using
      (WithZero.log_le_log ((Valuation.ne_zero_iff V).mpr hne) WithZero.exp_ne_zero).mpr hh
  have hA : (V H).log ≤ A := log_cap _ _ hHF hH
  have hB : G ≠ 0 → (V G).log ≤ A + 2 * u - t := by
    intro hn
    rw [← hGcap]
    exact log_cap _ _ hGF hn
  have hD : J ≠ 0 → (V J).log ≤ A - u := by
    intro hn
    rw [← hJcap]
    exact log_cap _ _ hJF hn
  have hcoeffs (k : ℕ) (hk : 1 ≤ k) (i : Fin (k + 2)) :
      V (ev (refinedCoefficients F k i.val)) ≤ WithZero.exp
        ((i.val : ℤ) * (2 * u - t) +
          ((min (2 * i.val) k : ℕ) : ℤ) * (A - u)) := by
    rw [← hJcap]
    exact refinedCoefficients_value_le V coeff hc x φ F k i.val r v z hk
      (by omega) (by omega) hv hR hYR hAll
  have hconstraint : G ≠ 0 → J ≠ 0 →
      (A - (V H).log) - (A + 2 * u - t - (V G).log) ≤ 2 * (A - u - (V J).log) := by
    intro hG hJ
    apply BoundaryTail.first_tail_shifted_constraint V (n := m₀ + 2) (by omega)
      H G J hH hG hJ (fun i => ev (refinedCoefficients F m₀ i.val)) A (A + 2 * u - t) (A - u) (hD hJ)
    · intro i
      simpa only [show m₀ + 2 - 2 = m₀ by omega,
        show A + 2 * u - t - A = 2 * u - t by ring] using hcoeffs m₀ hm₀ i
    · simp only [ev, RingHom.comp_apply, refinedCoefficients_zero,
        surfaceMap_C, MvPolynomial.eval₂Hom_C]
      apply hcoeff
      have hn := signedOddScalar_ne_zero (K := K) m₀ hchar
      intro hz
      apply hn
      apply (φ.comp Polynomial.C).injective
      simpa using hz
    · rw [← map_baseNumerator_refined ev F m₀]
      exact hfirst
  have hresult := BoundaryTail.normalized_tail_pole_le V (n := m + 2) (by omega) H G J hH
    (fun i => ev (refinedCoefficients F m i.val)) A u t ht0 htu huA hA hB hD hconstraint
    (by intro i; simpa only [Nat.add_sub_cancel] using hcoeffs m hm i)
  rw [← map_baseNumerator_refined ev F m] at hresult
  simp only [show m + 2 - 1 = m + 1 by omega] at hresult
  convert hresult using 1 <;> push_cast <;> ring

def normalFlag (m r v z : ℕ) : FlagDegree :=
  ⟨(m + 3) * z, (m + 3) * v - (m + 1), (m + 3) * (r - 1)⟩

theorem normalFlag_pole (V : Valuation L (WithZero (Multiplicative ℤ)))
    (x : Fin 3 → L) (m r v z : ℕ) (hv : 1 ≤ v) :
    flagPole V x (normalFlag m r v z) =
      ((m : ℤ) + 3) * flagPole V x (⟨z, v, r - 1⟩ : FlagDegree) -
        ((m : ℤ) + 1) * flagPole V x unitYZFlag := by
  have hsub : m + 1 ≤ (m + 3) * v := by nlinarith
  simp only [normalFlag, flagPole, unitYZFlag, Nat.cast_sub hsub,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  ring

theorem global_tail_value (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a : Ω, a ≠ 0 → V (coeff a) = 1)
    (x : Fin 3 → L) (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (m : ℕ) :
    V (MvPolynomial.eval₂Hom coeff x (RCN086.globalTailCut φ F (m + 2)) /
      (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F))) ^ (m + 1)) =
    V ((MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F))) ^ 3 *
      MvPolynomial.eval₂Hom coeff x (surfaceMap φ (baseNumerator F m)) /
      (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F))) ^ (m + 1)) := by
  have hunit := hcoeff _ (RCN086.tail_scalar_ne_zero φ hφ (m + 2))
  simp only [map_pow] at hunit
  rw [RCN086.globalTailCut_eq, numerator_eq_H_cube]
  simp only [map_mul, map_pow, MvPolynomial.eval₂Hom_C, map_div₀, hunit, mul_one]

theorem global_tail_normalized_pole_le
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a : Ω, a ≠ 0 → V (coeff a) = 1)
    (x : Fin 3 → L) (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (m₀ m r v z p : ℕ) [CharP K p]
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) (hchar : 2 * m₀ < p)
    (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (hH : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)) ≠ 0)
    (hfirst : MvPolynomial.eval₂Hom coeff x (RCN086.globalTailCut φ F (m₀ + 2)) = 0) :
    2 * RCN187.poleOrder V
      (MvPolynomial.eval₂Hom coeff x (RCN086.globalTailCut φ F (m + 2)) /
        (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F))) ^ (m + 1)) ≤
      2 * flagPole V x (normalFlag m r v z) + ((m : ℤ) + 2) *
        max (2 * flagPole V x unitAllFlag) (flagPole V x unitYZFlag +
          RCN187.poleOrder V (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyG K F)) /
            MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)))) := by
  have hscalar : coeff ((-φ Polynomial.X) ^ (m₀ + 2)) ≠ 0 := by
    intro hz
    have hh := hcoeff _ (RCN086.tail_scalar_ne_zero φ hφ (m₀ + 2))
    rw [hz, map_zero] at hh
    exact zero_ne_one hh
  simp only [map_pow] at hscalar
  have hbase : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (baseNumerator F m₀)) = 0 := by
    rw [RCN086.globalTailCut_eq, numerator_eq_H_cube] at hfirst
    simp only [map_mul, map_pow, MvPolynomial.eval₂Hom_C] at hfirst
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hfirst).resolve_right hscalar)).resolve_left
      (pow_ne_zero 3 hH)
  have h := actual_tail_normalized_pole_le V coeff hcoeff x φ F m₀ m r v z p
    hm₀ hm hchar hr hv hR hYR hAll hH hbase
  rw [normalFlag_pole V x m r v z (by omega)]
  simp only [RCN187.poleOrder, global_tail_value V coeff hcoeff x φ hφ F m, max_comm]
  simpa only [max_comm, RingHom.comp_apply] using h

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.RCN199
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN341 RCN095 RCN114 RCN295 RCN187 RCN207 RCN064 RCN204 RCN271 RCN257
noncomputable section
set_option autoImplicit false
variable {K : Type} [Field K]
variable {P : Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
variable {H G : MvPolynomial (Fin 3) K}

namespace MovingPoleBudget

theorem zero_le_of_doubled_pole [IsAlgClosed K]
    (budget : MovingPoleBudget P H G)
    (base : SeparableLiteralCoordinate P)
    (T : MvPolynomial (Fin 3) K) (denom factor : ℕ) (q : FlagDegree)
    (hH : H ∉ P) (hT : T ∉ P)
    (hpole : ∀ v : Place K (CoordinateField K P),
      2 * poleOrder v.val
          (coordinateEvaluation K P T /
            (coordinateEvaluation K P H)^denom) ≤
        2 * flagPole v.val (coordinate K P) q +
          (2 * factor : ℕ) * movingPoleTarget P H G v) :
    FiniteRegularZeroSetBound P H T
      (budget.weightedCost q + factor * budget.movingCost) := by
  apply finite_regular_zero_bound_of_separator K P base H T denom _ hT hH
  intro W
  have hlocal : ∀ v ∈ W,
      (2 * poleOrder v.val
          (coordinateEvaluation K P T /
            (coordinateEvaluation K P H)^denom) : ℤ) ≤
        2 * flagPole v.val (coordinate K P) q +
          (2 * factor : ℤ) * movingPoleTarget P H G v := by
    intro v hv
    exact hpole v
  have hsum := Finset.sum_le_sum hlocal
  have hflag := budget.sum_flagPole_le q W
  have hmove := budget.movingPole W
  have hbound :
      (2 : ℤ) * (∑ v ∈ W, poleOrder v.val
        (coordinateEvaluation K P T /
          (coordinateEvaluation K P H)^denom)) ≤
      (2 : ℤ) * (budget.weightedCost q + factor * budget.movingCost) := by
    calc
      _ = ∑ v ∈ W, (2 * poleOrder v.val
          (coordinateEvaluation K P T /
            (coordinateEvaluation K P H)^denom) : ℤ) := by
            simp only [Finset.mul_sum]
      _ ≤ ∑ v ∈ W, (2 * flagPole v.val (coordinate K P) q +
          (2 * factor : ℤ) * movingPoleTarget P H G v) := hsum
      _ = (2 : ℤ) * ((∑ v ∈ W, flagPole v.val (coordinate K P) q) +
          (factor : ℤ) * ∑ v ∈ W, movingPoleTarget P H G v) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
            push_cast
            ring
      _ ≤ (2 : ℤ) * (budget.weightedCost q + factor * budget.movingCost) := by
            gcongr
  have hfinal :
      (∑ v ∈ W, poleOrder v.val
        (coordinateEvaluation K P T /
          (coordinateEvaluation K P H)^denom) : ℤ) ≤
        (budget.weightedCost q + factor * budget.movingCost : ℤ) := by
    linarith
  simpa only [RCN346.poleOrder, coordinateEvaluation_eq_aeval,
    Nat.cast_add, Nat.cast_mul] using hfinal

end MovingPoleBudget
end
end ProximityPrize.SubmissionLower.RCN199
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN002 RCN055 RCN057 RCN064 RCN086 RCN095 RCN114 RCN136 RCN156
open RCN187 RCN199 RCN204 RCN234 RCN257 RCN271 RCN295 RCN313 RCN341 RCN344

noncomputable section
variable {K Ω : Type} [Field K] [Field Ω]

theorem coordinate_eval₂ (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (Q : MvPolynomial (Fin 3) Ω) :
    MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω P)) (coordinate Ω P) Q =
      coordinateEvaluation Ω P Q := by
  rw [coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm

theorem coordinate_global_tail_pole_le
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (V : Place Ω (CoordinateField Ω P))
    (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (m₀ m r v z p : ℕ) [CharP K p]
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) (hchar : 2 * m₀ < p)
    (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (hH : surfaceMap φ (polyH K F) ∉ P)
    (hfirst : globalTailCut φ F (m₀ + 2) ∈ P) :
    2 * poleOrder V.val (coordinateEvaluation Ω P (globalTailCut φ F (m + 2)) /
      coordinateEvaluation Ω P (surfaceMap φ (polyH K F)) ^ (m + 1)) ≤
      2 * flagPole V.val (coordinate Ω P) (normalFlag m r v z) +
        ((m : ℤ) + 2) * movingPoleTarget P
          (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F)) V := by
  have hHne : coordinateEvaluation Ω P (surfaceMap φ (polyH K F)) ≠ 0 := by
    intro hz
    apply hH
    rw [← coordinateEvaluation_ker Ω P]
    exact hz
  have hfirstzero : coordinateEvaluation Ω P (globalTailCut φ F (m₀ + 2)) = 0 := by
    change globalTailCut φ F (m₀ + 2) ∈ RingHom.ker (coordinateEvaluation Ω P).toRingHom
    rw [coordinateEvaluation_ker]
    exact hfirst
  have hcoeff : ∀ a : Ω, a ≠ 0 → V.val (algebraMap Ω (CoordinateField Ω P) a) = 1 := by
    letI : V.val.IsTrivialOn Ω := V.property.2
    exact Valuation.IsTrivialOn.eq_one
  have h := global_tail_normalized_pole_le V.val (algebraMap Ω (CoordinateField Ω P))
    hcoeff (coordinate Ω P) φ hφ F m₀ m r v z p hm₀ hm hchar hr hv hR hYR hAll
    (by rwa [coordinate_eval₂]) (by rwa [coordinate_eval₂])
  simpa only [coordinate_eval₂, movingPoleTarget, movingRatio, flagPole_unitAll,
    flagPole_unitYZ] using h

theorem global_tail_zero_count [IsAlgClosed Ω]
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (m₀ m r v z p factor : ℕ) [CharP K p]
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) (hchar : 2 * m₀ < p)
    (hr : 3 ≤ r) (hv : 2 ≤ v) (hfactor : m + 2 ≤ 2 * factor)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (budget : MovingPoleBudget P (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F)))
    (base : SeparableLiteralCoordinate P)
    (hH : surfaceMap φ (polyH K F) ∉ P)
    (hfirst : globalTailCut φ F (m₀ + 2) ∈ P)
    (hlater : globalTailCut φ F (m + 2) ∉ P) :
    FiniteRegularZeroSetBound P (surfaceMap φ (polyH K F)) (globalTailCut φ F (m + 2))
      (budget.weightedCost (normalFlag m r v z) + factor * budget.movingCost) := by
  apply budget.zero_le_of_doubled_pole base _ (m + 1) factor _ hH hlater
  intro V
  apply (coordinate_global_tail_pole_le P V φ hφ F m₀ m r v z p hm₀ hm hchar
    hr hv hR hYR hAll hH hfirst).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hfactor)
  simp only [movingPoleTarget, poleOrder]
  positivity

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra
end MergedPart7
