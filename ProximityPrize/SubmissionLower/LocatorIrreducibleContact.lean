import ProximityPrize.SubmissionLower.LocatorContact
namespace ProximityPrize.SubmissionLower.LocatorIrreducibleContact
open RCN081 RCN100 RCN156 RCN180 RCN234 RCN313
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq _
abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K
theorem not_dvd_locator_of_pos_degreeR
    {I : Type*} [Fintype I] (nodes : I → K) (F : Poly4 K)
    (hpos : 0 < F.degreeOf (2 : Fin 4)) :
    ¬ F ∣ LocatorContact.locator nodes := by
  intro hdiv
  have hdegree := RCN081.degreeOf_le_of_dvd (2 : Fin 4) F
    (LocatorContact.locator nodes) hdiv (LocatorContact.locator_ne_zero nodes)
  rw [LocatorContact.locator_degreeR] at hdegree
  omega
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
end
end ProximityPrize.SubmissionLower.LocatorIrreducibleContact
