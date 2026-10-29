import ProximityPrize.SubmissionBinaryLower.P64C7Parameters

/-!
# The two single-line weighted estimates

Matched curves use the flat auxiliary and missing curves use the residual
auxiliary. The weights clear `2*N` symbolically, including all rounding costs.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7SingleLine

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Bessel
  P64C7Parameters BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F] [Fintype ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

theorem missing_bound (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (D w q d C : ℕ) (hd : 1 ≤ d) (hqh : q * R.natDegree ≤ d) (hC : 0 < C)
    (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (ω : ι ↪ F) (y : ι → F[X]) (i : ι) (hy : (y i).natDegree ≤ q)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (τ : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ j ∈ A z, 1 ≤ lineOrd R (ω j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j ∈ A z, (P z).eval (ω j) = (y j).eval z)
    (hmiss : ∀ z ∈ S, (P z).eval (ω i) ≠ (y i).eval z)
    (hτ : ∀ z ∈ S, 2 * (τ z : ℤ) * normalDefect R ω y (A z) w D ≤ C) :
    ∑ z ∈ S, τ z * lineOrd R (ω i) (y i) ^ 2 ≤ 5 * C * R.natDegree ^ 2 * d := by
  classical
  let h := R.natDegree
  let μ := lineOrd R (ω i) (y i)
  change ∑ z ∈ S, τ z * μ ^ 2 ≤ 5 * C * h ^ 2 * d
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  have hμpos : 0 < μ := Nat.pos_of_ne_zero hμ0
  have hμh : μ ≤ h := lineOrd_le_natDegree_of_irreducible hirr hh (ω i) (y i)
  have hqd : q * μ ≤ d := (Nat.mul_le_mul_left q hμh).trans hqh
  obtain ⟨ν, R'', _, hR0, hu⟩ := P64C7Slice.exists_slice R hirr hh (ω i) (y i)
  let E := negativeParameter h d μ
  have hc := P64C7Bessel.weighted_orders_le R hirr D w q d (2 * h - μ) E (2 * h) (C * μ) ν
    hRw hRyz ω y i hy R'' hR0 hu hμh hqd (by omega) (by exact Nat.succ_pos _)
    (Nat.mul_pos hC hμpos) (by omega) (negative_leading h q d μ (by omega) hμpos hμh)
    S P A (fun z => τ z * μ ^ 2) hP hcurve hderiv hμ hmatch hmiss (fun z hz => ?_)
  · have hn := negative_numerical h d μ hμh hd
    apply hc.trans
    calc h * (C * μ) * E = (C * h) * (μ * E) := by ring
      _ ≤ (C * h) * (5 * h * d) := Nat.mul_le_mul_left _ hn
      _ = _ := by ring
  · have he : ((2 * h : ℕ) : ℤ) - (2 * h - μ : ℕ) = μ := by
      rw [Nat.cast_sub (by omega : μ ≤ 2 * h)]
      omega
    rw [he]
    have ht := mul_le_mul_of_nonneg_right (hτ z hz) (show 0 ≤ (μ : ℤ) ^ 2 by positivity)
    push_cast
    nlinarith only [ht]

theorem matched_bound (R : Tri) (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (D w q d C : ℕ) (hd : 1 ≤ d) (hqh : q * R.natDegree ≤ d) (hC : 0 < C)
    (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ j, (y j).natDegree ≤ q) (i : ι)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (τ : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ j ∈ A z, 1 ≤ lineOrd R (ω j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j ∈ A z, (P z).eval (ω j) = (y j).eval z)
    (hi : ∀ z ∈ S, i ∈ A z)
    (hτ : ∀ z ∈ S, 2 * (τ z : ℤ) * normalDefect R ω y (A z) w D ≤ C) :
    ∑ z ∈ S, τ z * (R.natDegree - lineOrd R (ω i) (y i)) ^ 2 ≤
      5 * C * R.natDegree ^ 2 * d := by
  classical
  let h := R.natDegree
  let μ := lineOrd R (ω i) (y i)
  change ∑ z ∈ S, τ z * (h - μ) ^ 2 ≤ 5 * C * h ^ 2 * d
  have hμh : μ ≤ h := lineOrd_le_natDegree_of_irreducible hirr hh (ω i) (y i)
  by_cases hfull : μ = h
  · simp [hfull]
  have hμlt : μ < h := by omega
  let σ : ι → ℕ := fun j => if j = i then 2 * h else 0
  let U := h + μ
  let E := positiveParameter h q d μ
  have hσ : ∀ j, q * σ j < E := by
    intro j
    by_cases hj : j = i
    · simpa [σ, hj] using positive_weight h q d μ
    · simp only [σ, if_neg hj, Nat.mul_zero]
      exact Nat.succ_pos _
  have hlead : (∑ j, P64C6Scale.quadraticCost q d E (σ j) (lineOrd R (ω j) (y j))) <
      6 * (h : ℤ) * U * E := by
    have he : (∑ j, P64C6Scale.quadraticCost q d E (σ j) (lineOrd R (ω j) (y j))) =
        P64C6Scale.quadraticCost q d E (2 * h) μ := by
      have ht : ∀ j, P64C6Scale.quadraticCost q d E (σ j) (lineOrd R (ω j) (y j)) =
          if j = i then P64C6Scale.quadraticCost q d E (2 * h) μ else 0 := by
        intro j
        by_cases hj : j = i <;> simp [σ, hj, μ, P64C6Scale.quadraticCost]
      simp_rw [ht]
      simp
    rw [he]
    exact positive_leading h q d μ (by omega) hμlt
  have hb : ∀ z ∈ S, bias σ (A z) U = (h - μ : ℕ) := by
    intro z hz
    have hs : ∑ j ∈ A z, σ j = 2 * h := by simp [σ, hi z hz]
    have hs' : ∑ j ∈ A z, (σ j : ℤ) = 2 * h := by exact_mod_cast hs
    unfold bias
    rw [hs', Nat.cast_sub hμh]
    dsimp [U]
    push_cast
    ring
  have hc := P64C6Bessel.weighted_orders_le R hirr D w q d U E (C * (h - μ)) hRw hRyz
    ω y hy σ (by dsimp [U, h]; omega) (by exact Nat.succ_pos _)
    (Nat.mul_pos hC (Nat.sub_pos_of_lt hμlt)) hσ hlead S P A
    (fun z => τ z * (h - μ) ^ 2) hP hcurve hderiv hμ hmatch (fun z hz => ?_) (fun z hz => ?_)
  · have hn := positive_numerical h q d μ hqh hd
    apply hc.trans
    calc h * (C * (h - μ)) * E = (C * h) * ((h - μ) * E) := by ring
      _ ≤ (C * h) * (5 * h * d) := Nat.mul_le_mul_left _ hn
      _ = _ := by ring
  · rw [hb z hz]
    exact_mod_cast Nat.sub_pos_of_lt hμlt
  · rw [hb z hz]
    have ht := mul_le_mul_of_nonneg_right (hτ z hz)
      (show 0 ≤ ((h - μ : ℕ) : ℤ) ^ 2 by positivity)
    push_cast
    nlinarith only [ht]

end P64C7SingleLine
end ProximityPrize.SubmissionBinaryLower
