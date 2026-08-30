import ProximityPrize.SubmissionLower.LocatorContact

/-!
Research extension of the locator collar to irreducible factors whose
R degree is greater than half the interpolation R cap.

This module reuses the actual contact-to-kernel restoration theorem. No regular
selected seed or nonzero specialization of a factor derivative is assumed.

For Q = F * P in the kernel, enough weighted slack makes N * Q_R another
kernel polynomial. Primality of F, F not dividing N, and F not dividing F_R
then force F to divide P. A nonzero Q would have R degree at least twice
that of F, contradicting the original slope cap.

Only degree_R(F) < characteristic is needed; there is no assumption that
the whole kernel polynomial has degree below the characteristic, nor that
its R derivative is nonzero.
-/
namespace ProximityPrize.SubmissionLower.LocatorIrreducibleContact

open RCN081 RCN100 RCN156 RCN180 RCN234 RCN313

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048

variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq _

abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- A positive-R-degree polynomial cannot divide the X-only node locator. -/
theorem not_dvd_locator_of_pos_degreeR
    {I : Type*} [Fintype I] (nodes : I → K) (F : Poly4 K)
    (hpos : 0 < F.degreeOf (2 : Fin 4)) :
    ¬ F ∣ LocatorContact.locator nodes := by
  intro hdiv
  have hdegree := RCN081.degreeOf_le_of_dvd (2 : Fin 4) F
    (LocatorContact.locator nodes) hdiv (LocatorContact.locator_ne_zero nodes)
  rw [LocatorContact.locator_degreeR] at hdegree
  omega

/-- Characteristic is used only here: F_R is nonzero and has lower R degree. -/
theorem not_dvd_pderivR_of_degree_lt_char
    (F : Poly4 K) (p : ℕ) [CharP K p]
    (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hlt : F.degreeOf (2 : Fin 4) < p) :
    ¬ F ∣ MvPolynomial.pderiv (2 : Fin 4) F := by
  intro hdiv
  have hder := LocatorContact.pderiv_R_ne_zero_of_degree_lt_char F p hpos hlt
  have hlower := RCN081.degreeOf_le_of_dvd (2 : Fin 4) F
    (MvPolynomial.pderiv (2 : Fin 4) F) hdiv hder
  have hupper := RCN313.pderiv_same_degree_bound
    (2 : Fin 4) F (F.degreeOf (2 : Fin 4)) le_rfl
  omega

/-- Differential saturation for an irreducible factor. This algebraic
lemma does not require a kernel, a slope cap, or nonzeroness of P or Q_R. -/
theorem irreducible_dvd_quotient_of_dvd_locator_pderiv
    {I : Type*} [Fintype I] (nodes : I → K)
    (F P : Poly4 K) (hF : Irreducible F) (p : ℕ) [CharP K p]
    (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hlt : F.degreeOf (2 : Fin 4) < p)
    (hdiv : F ∣ LocatorContact.locator nodes *
      MvPolynomial.pderiv (2 : Fin 4) (F * P)) : F ∣ P := by
  have hprime : Prime F := hF.prime
  have hder : F ∣ MvPolynomial.pderiv (2 : Fin 4) (F * P) :=
    (hprime.dvd_or_dvd hdiv).resolve_left
      (not_dvd_locator_of_pos_degreeR nodes F hpos)
  have hsum : F ∣ MvPolynomial.pderiv (2 : Fin 4) F * P +
      F * MvPolynomial.pderiv (2 : Fin 4) P := by
    simpa only [MvPolynomial.pderiv_mul] using hder
  have hterm : F ∣ F * MvPolynomial.pderiv (2 : Fin 4) P :=
    dvd_mul_right F _
  have hproduct : F ∣ MvPolynomial.pderiv (2 : Fin 4) F * P := by
    have h := dvd_sub hsum hterm
    simpa only [add_sub_cancel_right] using h
  exact (hprime.dvd_or_dvd hproduct).resolve_left
    (not_dvd_pderivR_of_degree_lt_char F p hpos hlt)

section WholeKernel

variable {I : Type*} [Fintype I]
local instance : DecidableEq I := Classical.decEq _

/-- Enough weighted slack is impossible for a nonzero kernel element if
an irreducible whole-kernel divisor has more than half the allowed R degree.
The additive margin avoids all assumptions about truncated degree cuts. -/
theorem irreducible_half_slope_kernel_eq_zero_of_margin
    (D w L s m p : ℕ) [CharP K p] (nodes u0 u1 : I → K)
    (F : Poly4 K) (hF : Irreducible F)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hlt : F.degreeOf (2 : Fin 4) < p)
    (hhalf : s < 2 * F.degreeOf (2 : Fin 4)) (hm : 1 ≤ m)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hmargin : wt (contactWeights w) (reconstruct K D w L s v.1) +
      Fintype.card I < D + (w - 1)) :
    reconstruct K D w L s v.1 = 0 := by
  classical
  by_contra hQ
  obtain ⟨P, hprod⟩ := hdiv v
  have hP : P ≠ 0 := by
    intro hz
    apply hQ
    rw [hprod, hz, mul_zero]
  obtain ⟨b, hb, hbeq⟩ := LocatorContact.exists_kernel_array_locator_pderiv
    D w L s m nodes u0 u1 v.1 v.2 hm hmargin
  have hderDiv : F ∣ LocatorContact.locator nodes *
      MvPolynomial.pderiv (2 : Fin 4) (F * P) := by
    have h := hdiv ⟨b, hb⟩
    simpa only [hbeq, hprod] using h
  have hFP : F ∣ P := irreducible_dvd_quotient_of_dvd_locator_pderiv
    nodes F P hF p hpos hlt hderDiv
  have hPdegree : F.degreeOf (2 : Fin 4) ≤ P.degreeOf (2 : Fin 4) :=
    RCN081.degreeOf_le_of_dvd (2 : Fin 4) F P hFP hP
  have hQdegree : (reconstruct K D w L s v.1).degreeOf (2 : Fin 4) ≤ s := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (reconstruct_mem_globalCoefficientBox K D w L s v.1 hd).2.1
  have hdegreeAdd : (reconstruct K D w L s v.1).degreeOf (2 : Fin 4) =
      F.degreeOf (2 : Fin 4) + P.degreeOf (2 : Fin 4) := by
    rw [hprod, MvPolynomial.degreeOf_mul_eq hF.ne_zero hP]
  omega

/-- The corresponding zero-array statement, useful when proving a
coefficient projection injective on the original kernel. -/
theorem irreducible_half_slope_array_eq_zero_of_margin
    (D w L s m p : ℕ) [CharP K p] (nodes u0 u1 : I → K)
    (F : Poly4 K) (hF : Irreducible F)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hlt : F.degreeOf (2 : Fin 4) < p)
    (hhalf : s < 2 * F.degreeOf (2 : Fin 4)) (hm : 1 ≤ m)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hmargin : wt (contactWeights w) (reconstruct K D w L s v.1) +
      Fintype.card I < D + (w - 1)) : v = 0 := by
  apply Subtype.ext
  apply reconstruct_injective K D w L s
  simpa only [ZeroMemClass.coe_zero, reconstruct_zero] using
    irreducible_half_slope_kernel_eq_zero_of_margin
      D w L s m p nodes u0 u1 F hF hdiv hpos hlt hhalf hm v hmargin

/-- Quotient-prefix version for a collar of width c. The quotient may have
positive residual R degree; neither Lq nor sq needs a positive lower bound.
In application use the actual differences D-wt(F), L-total(F), and s-r. -/
theorem irreducible_half_slope_quotient_eq_zero_of_mem_prefix
    (D w L s m c p : ℕ) [CharP K p] (nodes u0 u1 : I → K)
    (F : Poly4 K) (hF : Irreducible F)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hlt : F.degreeOf (2 : Fin 4) < p)
    (hhalf : s < 2 * F.degreeOf (2 : Fin 4)) (hm : 1 ≤ m)
    (hcost : Fintype.card I ≤ c + (w - 1))
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (P : Poly4 K) (hprod : reconstruct K D w L s v.1 = F * P)
    {Lq sq : ℕ}
    (hprefix : P ∈ globalCoefficientBox K
      (D - wt (contactWeights w) F - c) w Lq sq) : P = 0 := by
  classical
  by_contra hP
  have hprefixPos : 0 < D - wt (contactWeights w) F - c := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hP
    have h := (hprefix hd).2.2
    omega
  have hpcaps := (mem_flagGlobalCoefficientBox_iff P
    (D - wt (contactWeights w) F - c) w Lq sq hprefixPos).mp hprefix
  have hmargin : wt (contactWeights w) (reconstruct K D w L s v.1) +
      Fintype.card I < D + (w - 1) := by
    rw [hprod]
    have hmul := wt_mul_le (contactWeights w) F P
    have hPwt := hpcaps.2.2
    omega
  have hzero := irreducible_half_slope_kernel_eq_zero_of_margin
    D w L s m p nodes u0 u1 F hF hdiv hpos hlt hhalf hm v hmargin
  have hQ : reconstruct K D w L s v.1 ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hF.ne_zero hP
  exact hQ hzero

end WholeKernel

/- Intended next application: for an irreducible whole-kernel divisor of
   an A48/s13 profile, r=12 and r=11 both satisfy 13 < 2*r. The coefficient
   collar has the single-locator width c=n-(w-1), but now residual slope
   s-r is respectively 1 or 2. A general-slope retained-coordinate map is
   still required to turn the last theorem into the numerical finrank
   certificate; it is not assumed in this file. -/

end
end ProximityPrize.SubmissionLower.LocatorIrreducibleContact
