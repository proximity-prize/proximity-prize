import ProximityPrize.SubmissionLower.Fast058
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_2_3_6
set_option maxRecDepth 50000
set_option maxHeartbeats 0
open K1_13_2_3
open private       sumFrom from ProximityPrize.SubmissionLower.Numeric6AuxCert
end K1_13_2_3_6
end
section
namespace K1_13_2_3_5
open K1_13_2_3
open private unpack   from ProximityPrize.SubmissionLower.Numeric5Certificate
section
set_option maxHeartbeats 0
set_option maxRecDepth 50000
end
end K1_13_2_3_5
end
section
namespace K1_13_2_3_6
open K1_13_2_3
open private   sumFrom    from ProximityPrize.SubmissionLower.Numeric6AuxCert
end K1_13_2_3_6
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open private   sumFrom    from ProximityPrize.SubmissionLower.Numeric6AuxCert
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
end
end K1_13_2_3_6
end
section
namespace K1_13_2_3_6
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
end
end K1_13_2_3_6
end
section
namespace K1_13_2_3_7
open K1_13_2 K1_13_2_3
open scoped BigOperators
private theorem twice_half (q : ℤ) : 2 * (q * (q - 1) / 2) = q * (q - 1) := by
  have h : (2 : ℤ) ∣ q * (q - 1) := by
    rcases Int.emod_two_eq_zero_or_one q with h | h
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ q) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ q - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem fastDen_eq (u : ℤ) : fastDen u = denominator u := by
  by_cases hu : u < 0
  · simp [fastDen, denominator, hu]
  simp only [fastDen, denominator, hu, ite_false]
  let q := u / 6
  let r := u % 6
  let p := u * (u * (2 * u + 21) + 66)
  let v := 1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)
  change p / 72 + 1 = v
  suffices p + 47 ≤ 72 * v ∧ 72 * v ≤ p + 72 by omega
  have he : u = 6 * q + r := by dsimp [q, r]; omega
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
    dsimp [r]
    omega
  have hq := twice_half q
  unfold p v
  rw [he]
  rcases hr with h | h | h | h | h | h <;> rw [h] <;> norm_num <;>
    constructor <;> nlinarith only [hq]
private theorem den_neg {u : ℤ} (h : u < 0) : denominator u = 0 := by
  simp only [denominator, ite_eq_left h]
private theorem fastCum_eq (d u : ℤ) : fastCum d u = cumulative d u := by
  by_cases hd : d < 0
  · simp [fastCum, cumulative, hd]
  by_cases hu : u < 0
  · simp [fastCum, cumulative, hu]
  simp only [fastCum, cumulative, fastDen_eq, hd, hu, decide_false, Bool.false_or, Bool.false_eq_true,
    ite_false]
  let v := min u (3 * d)
  have hv : v ≤ 3 * d := min_le_right _ _
  rw [den_neg (show v - 3 * d - 6 < 0 by omega), sub_zero]
  by_cases h₁ : v ≤ d
  · rw [ite_eq_left h₁, den_neg (show v - d - 1 < 0 by omega),
      den_neg (show v - d - 2 < 0 by omega), den_neg (show v - d - 3 < 0 by omega),
      den_neg (show v - 2 * d - 3 < 0 by omega), den_neg (show v - 2 * d - 4 < 0 by omega),
      den_neg (show v - 2 * d - 5 < 0 by omega)]
    simp only [sub_zero, add_zero]
  · rw [ite_eq_right h₁]
    by_cases h₂ : v ≤ 2 * d + 2
    · rw [ite_eq_left h₂, den_neg (show v - 2 * d - 3 < 0 by omega),
        den_neg (show v - 2 * d - 4 < 0 by omega), den_neg (show v - 2 * d - 5 < 0 by omega)]
      simp only [add_zero]
    · rw [ite_eq_right h₂]
private theorem cumulative_neg_right (d u : ℤ) (hu : u < 0) : cumulative d u = 0 := by
  simp [cumulative, hu]
private theorem cap_inactive (d u : ℤ) (hu : u ≤ 1650) :
    cappedCount d u 550 = fastCum d u := by
  unfold cappedCount
  rw [ite_eq_right (by decide : ¬ (550 : ℤ) < 0), cumulative_neg_right (d - 550 - 1) _ (by omega),
    sub_zero, fastCum_eq]
private def chart (d j h : ℤ) : Flag := ⟨d, 1650 - j, 1650, 550, h + 1⟩
private theorem oldCount_eq (d j h : ℤ) (hj : 0 ≤ j) :
    oldCount (chart d j h) = fastCum d 1650 - fastCum d (1649 - j) := by
  have hl : min (1650 : ℤ) (1650 - j - 1) = 1649 - j := by
    rw [min_eq_right (by omega)]
    omega
  simp only [oldCount, chart, hl, cap_inactive _ _ (le_refl _),
    cap_inactive _ _ (show 1649 - j ≤ 1650 by omega)]
private theorem kernel_eq (d j h : ℤ) (hd : 0 ≤ d) (hj : 0 ≤ j) :
    kernelLower (chart d j h) = signedKernel d j h := by
  unfold kernelLower
  simp only [chart, show ¬ d < 0 by omega, decide_false, Bool.false_or, Bool.false_eq_true,
    ite_false, show ¬ (1650 : ℤ) < 0 by decide, show ¬ (550 : ℤ) < 0 by decide]
  change oldCount (chart d j h) - targetCount (chart d j h) = _
  rw [oldCount_eq _ _ _ hj]
  unfold targetCount signedKernel
  simp only [chart, add_sub_cancel_right, show (1650 : ℤ) - j - 1 = 1649 - j by ring]
  by_cases hb : h - (1650 - j) + d < 0
  · simp only [ite_eq_left hb, sub_zero]
  · simp only [ite_eq_right hb, fastCum_eq]
    ring
private theorem residual_eq (d j h : ℤ) (v : ℕ) :
    residualFlag (chart d j h) (Powers.expand ⟨v, 0, 0⟩) = chart (d - v) j h := by
  rw [residualFlag_expand]
  simp [chart]
end K1_13_2_3_7
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3
noncomputable section
open K1_13 MvPolynomial
abbrev Exponent := Fin 4 →₀ ℕ
abbrev Jets (k : Type) [Field k] := MvPolynomial (Fin 4) k
def lattice (p : Shape) : Set Exponent :=
  {e | e 0 + e 1 + e 2 + e 3 ≤ p.b ∧
    e 1 + 2 * e 2 + 3 * e 3 ≤ p.j ∧ e 3 ≤ p.t}
theorem lattice_finite (p : Shape) : (lattice p).Finite :=
  (Finsupp.finite_of_degree_le p.b).subset fun e he => by
    simpa only [Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Fin.sum_univ_four]
      using (show e 0 + e 1 + e 2 + e 3 ≤ p.b from he.1)
abbrev CutIdeal {k : Type} [Field k] (f : Fin 4 → Jets k) : Ideal (Jets k) :=
  Ideal.span (Set.range f)
abbrev CutAlgebra {k : Type} [Field k] (f : Fin 4 → Jets k) :=
  Jets k ⧸ CutIdeal f
abbrev CoefficientRing (k : Type) [Field k] (P : Fin 4 → Shape) :=
  MvPolynomial (Σ i : Fin 4, lattice (P i)) k
abbrev CoefficientField (k : Type) [Field k] (P : Fin 4 → Shape) :=
  FractionRing (CoefficientRing k P)
def genericEquation (k : Type) [Field k] (P : Fin 4 → Shape) (i : Fin 4) :
    Jets (CoefficientField k P) := by
  classical
  letI := (lattice_finite (P i)).fintype
  exact ∑ e : lattice (P i), monomial e.val
    (algebraMap (CoefficientRing k P) (CoefficientField k P) (MvPolynomial.X ⟨i, e⟩))
abbrev GenericAlgebra (k : Type) [Field k] (P : Fin 4 → Shape) :=
  CutAlgebra (genericEquation k P)
def shapeDifference (f : Shape → ℝ) (p R : Shape) : ℝ :=
  f (R.plus p) - f R
def fourDifference (f : Shape → ℝ) (P : Fin 4 → Shape) : Shape → ℝ :=
  shapeDifference (shapeDifference (shapeDifference (shapeDifference f (P 0)) (P 1))
    (P 2)) (P 3)
end
end K1_13_6_1_4_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_2
noncomputable section
open K1_13_5_4_2_4_1 MvPolynomial
def specialIdeal {L : Type} [Field L] (g : Fin 4 → Total L) : Ideal (Total L) :=
  equationsIdeal g ⊔ Ideal.span {C Polynomial.X}
end
end K1_13_6_1_4_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_1
def otherIdeal {R : Type*} [CommRing R] (f : Fin 4 → R) (i : Fin 4) : Ideal R :=
  Ideal.span (f '' {j | j ≠ i})
end K1_13_6_1_4_3_3_1
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_3
noncomputable section
open K1_13_5_4_2_4 K1_13_5_4_2_4_2
abbrev Chart (A : Fin 4 → Finset Exponent) := ∀ i, ↥(A i)
def chartPower {A : Fin 4 → Finset Exponent} (a : Chart A) (m : ℕ) : Row A :=
  MvPolynomial.monomial (m • ∑ i, (a i).val) 1
def ChartLifting (A : Fin 4 → Finset Exponent) : Prop :=
  ∀ (i : Fin 4) (d : Degree) (p : Row A),
    p ∈ piece A (shift d i 1) → p ∈ prefixIdeal A (i.val + 1) →
    ∀ a : Chart A, ∃ (m : ℕ) (r : Row A),
      r ∈ piece A (d + fun _ => m) ∧
        chartPower a m * p - genericEquation A i * r ∈ prefixIdeal A i.val
end
end K1_13_7_5_3_3_3
end
