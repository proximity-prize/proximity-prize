import ProximityPrize.SubmissionLower.BCHKSHenselBaseZAlignment
import ProximityPrize.SubmissionLower.BCHKSHenselSetup

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Filtering a coarse base-`Z` fibre by the nonvanishing of `W = H.leadingCoeff`
still leaves the sharp number of points required by the affine root count. -/
theorem coarse_fiber_filter_leadingCoeff_card_exact
    (H : F[X][Y]) (D DX dR dH : ℕ)
    (hdH : H.natDegree = dH) (hDX : 1 ≤ DX) (hdR : 1 ≤ dR) (hdHpos : 1 ≤ dH)
    (hHD : Bivariate.totalDegree H ≤ D) (Fib : Finset F)
    (hcoarse : 2*DX*dR*D*dH < Fib.card) :
    let Good := Fib.filter (fun z => ¬ H.leadingCoeff.eval z = 0)
    (((2*(DX-1)+1)*dR*D)+1)*dH < Good.card ∧
      ∀ z ∈ Good, H.leadingCoeff.eval z ≠ 0 := by
  dsimp
  have hWdeg : H.leadingCoeff.natDegree ≤ D - dH := by
    rw [← hdH]
    exact RationalFunctions.HenselNumerators.leadingCoeff_natDegree_le_of_totalDegree_le hHD
  have hHne : H ≠ 0 := by
    intro h
    rw [h] at hdH
    simp at hdH
    omega
  have hWne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHne
  let Bad := Fib.filter (fun z => H.leadingCoeff.eval z = 0)
  have hBad : Bad.card ≤ D - dH := by
    calc
      Bad.card ≤ H.leadingCoeff.roots.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        have hz0 := (Finset.mem_filter.mp hz).2
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hWne]
        simpa using hz0
      _ ≤ H.leadingCoeff.roots.card := Multiset.toFinset_card_le _
      _ ≤ H.leadingCoeff.natDegree := Polynomial.card_roots' _
      _ ≤ D - dH := hWdeg
  have hpartition :
      (Fib.filter (fun z => ¬ H.leadingCoeff.eval z = 0)).card + Bad.card = Fib.card := by
    simpa [Bad, add_comm] using Finset.filter_card_add_filter_neg_card_eq_card
      (s := Fib) (p := fun z => H.leadingCoeff.eval z ≠ 0)
  constructor
  · have hD : dH ≤ D := by
      have hHin : H.natDegree ∈ H.support :=
        Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHne)
      have hc := Bivariate.coeff_totalDegree_le H hHin
      omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : DX ≠ 0)
    simp only [Nat.succ_sub_one]
    have hloss : Fib.card ≤
        (Fib.filter (fun z => ¬ H.leadingCoeff.eval z = 0)).card + (D-dH) := by
      omega
    have hprod : dH ≤ dR * D * dH := by
      calc dH = 1 * 1 * dH := by simp
        _ ≤ dR * D * dH := Nat.mul_le_mul (Nat.mul_le_mul hdR (by omega)) (le_refl dH)
    have hDprod : D ≤ dR * D * dH := by
      calc D = 1 * D * 1 := by simp
        _ ≤ dR * D * dH := Nat.mul_le_mul (Nat.mul_le_mul hdR (le_refl D)) hdHpos
    have hgap : D - dH ≤ dR * D * dH - dH := Nat.sub_le_sub_right hDprod dH
    have hid : 2 * (n+1) * dR * D * dH =
        (((2*n+1)*dR*D)+1)*dH + (dR*D*dH-dH) := by
      rw [← Nat.add_sub_assoc hprod]
      ring_nf
      omega
    have hcoarse' : 2*(n+1)*dR*D*dH < Fib.card := by
      simpa [Nat.succ_eq_add_one] using hcoarse
    have hbudget : (((2*n+1)*dR*D)+1)*dH + (D-dH) ≤
        2*(n+1)*dR*D*dH := by
      rw [hid]
      omega
    omega
  · intro z hz
    exact (Finset.mem_filter.mp hz).2

end ProximityPrize.SubmissionLower
