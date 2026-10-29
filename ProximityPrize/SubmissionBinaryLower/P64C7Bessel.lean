import ProximityPrize.SubmissionBinaryLower.P64C7Scale

/-!
# An integral weighted order bound for residual auxiliaries

The denominator-clearing constant is symbolic. Arbitrarily large integral
scales remove the fixed resultant cost by a finite contradiction.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Bessel

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Finite P64C6Bessel
  P64C7Scale BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F] [Fintype ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

theorem weighted_orders_le (R : Tri) (hirr : Irreducible R)
    (D w q d U E σ C ν : ℕ) (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (ω : ι ↪ F) (y : ι → F[X]) (i : ι) (hy : (y i).natDegree ≤ q)
    (R'' : Polynomial (Polynomial F))
    (hR0 : (lineShift R (ω i) (y i)).map (Polynomial.constantCoeff (R := Polynomial F)) =
      Polynomial.X ^ ν * R'')
    (hu : R''.coeff 0 ≠ 0) (hμh : lineOrd R (ω i) (y i) ≤ R.natDegree)
    (hqd : q * lineOrd R (ω i) (y i) ≤ d)
    (hU : 0 < U) (hE : 0 < E) (hC : 0 < C) (hσU : U < σ)
    (hlead : quadraticCost R.natDegree q d (lineOrd R (ω i) (y i)) E σ <
      R.natDegree * U * E)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (a : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ j ∈ A z, 1 ≤ lineOrd R (ω j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j ∈ A z, (P z).eval (ω j) = (y j).eval z)
    (hmiss : ∀ z ∈ S, (P z).eval (ω i) ≠ (y i).eval z)
    (hslope : ∀ z ∈ S, 2 * (a z : ℤ) * normalDefect R ω y (A z) w D ≤ C * ((σ : ℤ) - U)) :
    ∑ z ∈ S, a z ≤ R.natDegree * C * E := by
  classical
  let μ := lineOrd R (ω i) (y i)
  have hscaled : quadraticCost R.natDegree q d μ (C * E) (C * σ) <
      R.natDegree * (C * U) * (C * E) := by
    have he : quadraticCost R.natDegree q d μ (C * E) (C * σ) =
        C ^ 2 * quadraticCost R.natDegree q d μ E σ := by
      unfold quadraticCost
      ring
    rw [he]
    have hh := Nat.mul_lt_mul_of_pos_left hlead (show 0 < C ^ 2 by positivity)
    convert hh using 1 <;> ring
  let B := (R.natDegree - 1) * d
  obtain ⟨T, hTB, hT, hμs, hνs, hdim⟩ := exists_dimension_scale D q d R.natDegree μ ν
    (C * U) (C * E) (C * σ) (B + 1) (Nat.mul_pos hC hU) (Nat.mul_pos hC hE)
    (Nat.mul_pos hC (by omega)) hscaled
  let m := T * ∑ z ∈ S, a z
  have hN : ∀ z ∈ S, 0 ≤ normalDefect R ω y (A z) w D := by
    intro z hz
    exact normal_defect_nonneg R (P z) z D w hRw (hP z hz) (hderiv z hz) ω y (A z)
      (fun j => lineOrd R (ω j) (y j)) (fun j _ => ordGE_lineOrd R (ω j) (y j)) (hmatch z hz)
  have hc := P64C7Step.forced_orders_of_dimension R hirr D w (T * (C * U)) q (T * (C * E)) d m
    (T * (C * σ)) ν hRw hRyz ω y i hy R'' hR0 hu hμh hμs hνs hqd hdim S P A
    (fun z => T * a z) hP hcurve hderiv (fun z hz => ?_) hμ hmatch hmiss (fun z hz ρ hρ => ?_)
  · rw [← Finset.mul_sum] at hc
    change T * (∑ z ∈ S, a z) ≤ B + R.natDegree * (T * (C * E)) at hc
    rw [show R.natDegree * (T * (C * E)) = T * (R.natDegree * C * E) by ring] at hc
    by_contra hn
    have hstep : R.natDegree * C * E + 1 ≤ ∑ z ∈ S, a z := by omega
    have hmul := Nat.mul_le_mul_left T hstep
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · have hsingle : a z ≤ ∑ z ∈ S, a z := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz
    have hh := Nat.mul_le_mul_left T hsingle
    dsimp [m]
    omega
  · have he : ((T * (C * σ) : ℕ) : ℤ) - (T * (C * U) : ℕ) =
        (T : ℤ) * C * ((σ : ℤ) - U) := by push_cast; ring
    rw [he]
    exact scaled_forcing (normalDefect R ω y (A z) w D) ((σ : ℤ) - U)
      C T (a z) ρ (hN z hz) (sub_pos.mpr (by exact_mod_cast hσU))
      hC hT (hslope z hz) hρ

end P64C7Bessel
end ProximityPrize.SubmissionBinaryLower
