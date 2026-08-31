import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch
import ProximityPrize.SubmissionLower.ActualPlaneJointProjection
namespace ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps6543Research
open scoped Classical
open ContactFlagBezout6543Research
open ContactFlagTriangularProjectionResearch
open TrivariateRationalCollection ActualPlaneCoordinateKernel
  ActualPlaneCoordinateCaps ActualPlaneJointProjection
noncomputable section
variable {K:Type} [Field K]
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
structure FlagTrapezoidCaps (p:FlagDegree) (F:Poly3 K):Prop where
  uOuter:(planeMap K uOrder F).natDegree ≤ p.all
  uTotal:∀ d∈(rationalMap K uOrder F).support,
    d 0+d 1 ≤ p.zOnly+p.yz+p.all
  vOuter:(planeMap K vOrder F).natDegree ≤ p.yz+p.all
  vTotal:∀ d∈(rationalMap K vOrder F).support,
    d 0+d 1 ≤ p.zOnly+p.yz+p.all
  zOuter:(planeMap K zOrder F).natDegree ≤ p.all
  zTotal:∀ d∈(rationalMap K zOrder F).support,
    d 0+d 1 ≤ p.yz+p.all
private theorem degreeOf_s_le
    {p:FlagDegree} {F:Poly3 K}
    (hF:ContactFlagTriangularProjectionResearch.PolynomialInFlag p F):
    F.degreeOf 1 ≤ p.all:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  exact (hF d hd).1
private theorem degreeOf_y_le
    {p:FlagDegree} {F:Poly3 K}
    (hF:ContactFlagTriangularProjectionResearch.PolynomialInFlag p F):
    F.degreeOf 0 ≤ p.yz+p.all:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  exact (Nat.le_add_right (d 0) (d 1)).trans (hF d hd).2.1
theorem flagTrapezoidCaps_of_inFlag
    (p:FlagDegree) (F:Poly3 K)
    (hF:ContactFlagTriangularProjectionResearch.PolynomialInFlag p F):
    FlagTrapezoidCaps p F:=by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact (planeMap_natDegree_le K uOrder F).trans
      (by simpa [uOrder] using degreeOf_s_le hF)
  · apply rationalMap_joint_support_of_original K uOrder F _
    intro d hd
    have h:=(hF d hd).2.2
    have h':d 1+d 2 ≤ p.zOnly+p.yz+p.all:=by omega
    simpa [uOrder] using h'
  · exact (planeMap_natDegree_le K vOrder F).trans
      (by simpa [vOrder,Equiv.swap_apply_def] using degreeOf_y_le hF)
  · apply rationalMap_joint_support_of_original K vOrder F _
    intro d hd
    have h:=(hF d hd).2.2
    have h':d 0+d 2 ≤ p.zOnly+p.yz+p.all:=by omega
    simpa [vOrder,Equiv.swap_apply_def] using h'
  · exact (planeMap_natDegree_le K zOrder F).trans
      (by simpa [zOrder,Equiv.swap_apply_def] using degreeOf_s_le hF)
  · apply rationalMap_joint_support_of_original K zOrder F _
    intro d hd
    have h:=(hF d hd).2.1
    simpa [zOrder,Equiv.swap_apply_def,Nat.add_comm] using h
theorem flagTrapezoidCaps_flagAlgHom
    (p:FlagDegree) (F:Poly3 K) (lam mu nu:K)
    (hF:F.support ⊆ flagSupport p):
    FlagTrapezoidCaps p (flagAlgHom lam mu nu F):=by
  apply flagTrapezoidCaps_of_inFlag
  apply polynomialInFlag_flagAlgHom p F lam mu nu
  intro d hd
  exact (mem_flagSupport_iff p d).mp (hF hd)
theorem u_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 1179639):
    m*376+5*98434322-m*5 ≤ flagYZMixedCap:=by
  rw [flag_mixed_values.2.2.1]
  omega
theorem v_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 6684622):
    m*376+26*98434322-m*26 ≤ flagAllMixedCap:=by
  rw [flag_mixed_values.2.2.2]
  omega
theorem z_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 1179639):
    m*26+5*6684622-m*5 ≤ flagZMixedCap:=by
  rw [flag_mixed_values.2.1]
  omega
end
end ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps6543Research
