import ProximityPrize.SubmissionLower.KoalaCutMultiplicity
import ProximityPrize.SubmissionLower.KoalaPointCount
import ProximityPrize.SubmissionLower.HighCore82229Family

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SplitCut.TwoCutCoverage

open MvPolynomial
open K1_13_6_3_5 (boundaryWeight)
open CutMultiplicity
open scoped BigOperators

/-- The ordinary node incidence bound fits two copies of the second-cut quota
    for a repeated first-cut component. The common sites shorten its node curves. -/
theorem repeated_tariff {s ell k L : ℕ} (hs : s ≤ 133510) (he₀ : 128632 ≤ ell)
    (he₁ : ell ≤ L) (he₂ : L ≤ 128715) (hk : k ≤ 4878) :
    (262144-s)*(ell-s+k) ≤ (179915-s)*(2*(L+2+k)) := by
  have ha : s ≤ 179915 := by omega
  by_cases hse : s ≤ ell
  · have hsmall : 179915*(ell-s+k) ≤ (179915-s)*(ell+k) := by
      zify [hse, ha]
      nlinarith only [mul_nonneg (show (0 : ℤ) ≤ s by positivity)
        (show (0 : ℤ) ≤ 179915-ell-k by omega)]
    refine Nat.le_of_mul_le_mul_left ?_ (by decide : 0 < 179915)
    calc
      179915*((262144-s)*(ell-s+k)) = (262144-s)*(179915*(ell-s+k)) := by ring
      _ ≤ (262144-s)*((179915-s)*(ell+k)) := Nat.mul_le_mul_left _ hsmall
      _ = (179915-s)*((262144-s)*(ell+k)) := by ring
      _ ≤ (179915-s)*((179915*2)*(L+2+k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _ = 179915*((179915-s)*(2*(L+2+k))) := by ring
  · rw [Nat.sub_eq_zero_of_le (by omega : ell ≤ s), zero_add]
    have hn : 262144-s ≤ 6*(179915-s) := by omega
    calc
      _ ≤ (6*(179915-s))*k := Nat.mul_le_mul_right _ hn
      _ = (179915-s)*(6*k) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

theorem stable_tariff {s L k : ℕ} (hs : s ≤ 133510) (hL : 128632 ≤ L) :
    (262144-s)*129 ≤ (179915-s)*(L+2+k) := by
  have hn : 262144-s ≤ 6*(179915-s) := by omega
  calc
    _ ≤ (6*(179915-s))*129 := Nat.mul_le_mul_right _ hn
    _ = (179915-s)*(6*129) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

open P1 (I K node)
open HighCore82229 (FixedWord agreement blockLength persistent_card_le section_incidence)
open P1_7_3 (persistentNodes)

theorem repeated_marks {word : I → K} {U : Finset K} {S : K → Polynomial K} {d : ℕ}
    (hword : FixedWord word U S d) (hd : d ≤ 133510)
    {ell L k δ : ℕ} (he₀ : 128632 ≤ ell) (he₁ : ell ≤ L) (he₂ : L ≤ 128715)
    (hk : k ≤ 4878) (hδ : 0 < δ)
    (hcuts : ∀ x : I, (∃ γ ∈ U, (S γ).eval (node x) ≠ word x) →
      (U.filter fun γ => (S γ).eval (node x) = word x).card ≤
        (ell-(persistentNodes word U S).card+k)*δ) :
    U.card ≤ (2*(L+2+k))*δ := by
  classical
  by_cases hlarge : 1 < U.card
  · let s := (persistentNodes word U S).card
    have hs := (persistent_card_le hword hlarge).trans hd
    have hh := repeated_tariff (s:=s) hs he₀ he₁ he₂ hk
    have hpos : 0 < 179915-s := by omega
    have h := section_incidence hword ((ell-s+k)*δ) hcuts
    change (179915-s)*U.card ≤ (262144-s)*((ell-s+k)*δ) at h
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [← mul_assoc]
    rw [← mul_assoc] at h
    exact h.trans (Nat.mul_le_mul_right δ hh)
  · exact (show U.card ≤ 1 by omega).trans (Nat.succ_le_of_lt (Nat.mul_pos (by omega) hδ))

theorem stable_marks {word : I → K} {U : Finset K} {S : K → Polynomial K} {d : ℕ}
    (hword : FixedWord word U S d) (hd : d ≤ 133510)
    {L k δ : ℕ} (hL : 128632 ≤ L) (hδ : 0 < δ)
    (hcuts : ∀ x : I, (∃ γ ∈ U, (S γ).eval (node x) ≠ word x) →
      (U.filter fun γ => (S γ).eval (node x) = word x).card ≤ 129*δ) :
    U.card ≤ (L+2+k)*δ := by
  classical
  by_cases hlarge : 1 < U.card
  · let s := (persistentNodes word U S).card
    have hs := (persistent_card_le hword hlarge).trans hd
    have hh := stable_tariff (s:=s) (k:=k) hs hL
    have hpos : 0 < 179915-s := by omega
    have h := section_incidence hword (129*δ) hcuts
    change (179915-s)*U.card ≤ (262144-s)*(129*δ) at h
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [← mul_assoc]
    rw [← mul_assoc] at h
    exact h.trans (Nat.mul_le_mul_right δ hh)
  · exact (show U.card ≤ 1 by omega).trans (Nat.succ_le_of_lt (Nat.mul_pos (by omega) hδ))

section

variable {F E σ α : Type} [Field F] [Field E] [Algebra F E] [Finite σ]

/-- Cover a marked family by first-cut components. Simple components spend one
    local degree and repeated components can spend two. -/
theorem weighted_cover (I : Ideal (MvPolynomial σ F)) (T : Finset α) (x : α → σ → E)
    (hI : (affineHilbertPolynomial I).natDegree ≤ 1)
    (hT : ∀ a ∈ T, x a ∈ zeroLocus E I) (q : ℕ)
    [DecidableRel (fun (i : α) (P : Ideal (MvPolynomial σ F)) => x i ∈ zeroLocus E P)]
    (hsimple : ∀ P, I.IsMinimalPrime P → boundaryWeight I P = 1 →
      ((T.filter (fun i => x i ∈ zeroLocus E P)).card : ℚ) ≤
        q*(affineHilbertPolynomial P).coeff 1)
    (hrepeat : ∀ P, I.IsMinimalPrime P → 2 ≤ boundaryWeight I P →
      ((T.filter (fun i => x i ∈ zeroLocus E P)).card : ℚ) ≤
        (2*q)*(affineHilbertPolynomial P).coeff 1) :
    (T.card : ℚ) ≤ q*(affineHilbertPolynomial I).coeff 1 := by
  classical
  obtain ⟨hfin, hsum⟩ := coefficient_budget I 1 hI
  have hc := PointCount.cover I T hT
  have hc' : (T.card : ℚ) ≤ ∑ P ∈ I.minimalPrimesFinset,
      ((T.filter (fun i => x i ∈ zeroLocus E P)).card : ℚ) := by exact_mod_cast hc
  refine hc'.trans ?_
  calc
    _ ≤ ∑ P ∈ I.minimalPrimesFinset,
        (q : ℚ)*((boundaryWeight I P : ℚ)*(affineHilbertPolynomial P).coeff 1) := by
      apply Finset.sum_le_sum
      intro P hP
      have hm := Ideal.mem_minimalPrimesFinset.mp hP
      let _ : P.IsPrime := hm.isPrime
      have hp := weight_pos hm.le (hfin P hm)
      by_cases hw : boundaryWeight I P = 1
      · simpa only [hw, Nat.cast_one, one_mul] using hsimple P hm hw
      · have htwo : 2 ≤ boundaryWeight I P := by omega
        have hn : 0 ≤ (affineHilbertPolynomial P).coeff 1 :=
          Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
            ((natDegree_affineHilbertPolynomial_le_of_le hm.le).trans hI)
            (eventually_eval_affineHilbertPolynomial_nonneg P)
        calc
          _ ≤ (2*q)*(affineHilbertPolynomial P).coeff 1 := hrepeat P hm htwo
          _ ≤ (q * (boundaryWeight I P : ℚ))*(affineHilbertPolynomial P).coeff 1 := by
            rw [mul_comm (2 : ℚ) q]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by exact_mod_cast htwo) (Nat.cast_nonneg q)) hn
          _ = _ := by rw [mul_assoc]
    _ = (q : ℚ) * ∑ P ∈ I.minimalPrimesFinset,
        (boundaryWeight I P : ℚ)*(affineHilbertPolynomial P).coeff 1 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg q)

end
end SplitCut.TwoCutCoverage

#print axioms SplitCut.TwoCutCoverage.repeated_tariff
#print axioms SplitCut.TwoCutCoverage.stable_tariff
#print axioms SplitCut.TwoCutCoverage.repeated_marks
#print axioms SplitCut.TwoCutCoverage.stable_marks
#print axioms SplitCut.TwoCutCoverage.weighted_cover
