import ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps6543Research
import ProximityPrize.SubmissionLower.ContactRegularComponentCover
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedProjection6600Research

namespace ProximityPrize.SubmissionLower.ContactTerminalTrapezoidProjection6622Research

open scoped Classical
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.ContactFlagBezout6543Research
open ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch
open ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps6543Research
open ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
open ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
open ProximityPrize.SubmissionLower.ActualPlaneCoordinateCaps
open ProximityPrize.SubmissionLower.ActualPlanePositiveOrder
open ProximityPrize.SubmissionLower.ContactRegularComponentCover
open ProximityPrize.SubmissionLower.ContactAdaptiveNestedProjection6600Research
open ProximityPrize.SubmissionLower.ActualCurveCoordinateField
open ProximityPrize.SubmissionLower.ActualCurveRationalProjection

noncomputable section

variable {Omega : Type} [Field Omega]

abbrev trapezoidPrime : ℕ := 2130706433
abbrev trapezoidW : ℕ := 131071

theorem finite_separable_at_Y_of_trapezoid
    [CharP Omega trapezoidPrime]
    {p : ProximityPrize.SubmissionLower.ContactFlagBezout6543Research.FlagDegree}
    {G T H : MvPolynomial (Fin 3) Omega}
    (C : RegularComponent Omega G T H)
    (hG : Irreducible G)
    (hproper : ¬ G ∣ T)
    (hGflag : ProximityPrize.SubmissionLower.ContactFlagBezout6543Research.PolynomialInFlag p G)
    (hGAll : p.all ≤ 8)
    (hGTotal : p.zOnly + p.yz + p.all ≤ 528)
    (hTflag : ProximityPrize.SubmissionLower.ContactFlagBezout6543Research.PolynomialInFlag ⟨970 * trapezoidW, 1 + 70 * trapezoidW, 15 * trapezoidW⟩ T) :
    LiteralProjectionGate C 0 := by
  intro htr
  have hTne : T ≠ 0 := by
    intro hzero
    apply hproper
    rw [hzero]
    exact dvd_zero G
  have gCaps := flagTrapezoidCaps_of_inFlag (K := Omega) p G hGflag
  have tCaps := flagTrapezoidCaps_of_inFlag (K := Omega)
    ⟨970 * trapezoidW, 1 + 70 * trapezoidW, 15 * trapezoidW⟩ T hTflag
  have hGZ : G.degreeOf 2 ≤ 528 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have h := (hGflag d hd).2.2
    omega
  have hTR : T.degreeOf 1 ≤ 15 * trapezoidW := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hTflag d hd).1
  have hGswapOuter :
      (planeMap Omega (swapOtherOrder uOrder) G).natDegree ≤ 528 := by
    exact (planeMap_natDegree_le Omega (swapOtherOrder uOrder) G).trans
      (by simpa [uOrder, swapOtherOrder, Equiv.swap_apply_def] using hGZ)
  have hTswapInner : Polynomial.Bivariate.degreeX
      (planeMap Omega (swapOtherOrder uOrder) T) ≤ 15 * trapezoidW := by
    exact (planeMap_degreeX_le Omega (swapOtherOrder uOrder) T).trans
      (by simpa [uOrder, swapOtherOrder, Equiv.swap_apply_def] using hTR)
  have hcertificate : JointOrderCertificate Omega uOrder G T trapezoidPrime := by
    exact jointOrderCertificate_of_projection_data Omega uOrder C.1 G T trapezoidPrime
      8 (15 * trapezoidW) 528 (1 + 1055 * trapezoidW) 2128593048 528 (15 * trapezoidW)
      hG (regularComponent_G_mem Omega G T H C) htr hTne
      (gCaps.uOuter.trans hGAll) tCaps.uOuter
      (fun d hd ↦ (gCaps.uTotal d hd).trans hGTotal)
      (by
        intro d hd
        have h := tCaps.uTotal d hd
        norm_num [trapezoidW] at h ⊢
        exact h)
      hGswapOuter hTswapInner
      (by norm_num [trapezoidPrime]) (by norm_num [trapezoidPrime])
      (by norm_num [trapezoidPrime]) (by norm_num [trapezoidPrime, trapezoidW])
      (by intro m hm; norm_num [trapezoidW] at hm ⊢; omega)
  have hresult := finite_separable_finrank_bound_of_joint_certificate
    Omega uOrder C.1 htr trapezoidPrime G T hG
    (regularComponent_G_mem Omega G T H C)
    (regularComponent_T_mem Omega G T H C) hproper hcertificate
  exact ⟨hresult.1, hresult.2.1⟩

end
end ProximityPrize.SubmissionLower.ContactTerminalTrapezoidProjection6622Research

#print axioms ProximityPrize.SubmissionLower.ContactTerminalTrapezoidProjection6622Research.finite_separable_at_Y_of_trapezoid
