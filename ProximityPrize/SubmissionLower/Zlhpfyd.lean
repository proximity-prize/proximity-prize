import ProximityPrize.SubmissionLower.BI
set_option Elab.async false
set_option autoImplicit true
namespace Dr
noncomputable section
open aR dN vS
open scoped BigOperators
private lemma eMr {J:Ideal GeoJets} (hJ:dimension J=0)
    (x :oe) (hx :J≤oF x) :J.IsMinimalPrime (oF x) := by
  have :Module.Finite GeoField (GeoJets ⧸ J) :=
    MvPolynomial.natDegree_affineHilbertPolynomial_eq_zero_iff.mp hJ
  have :IsArtinianRing (GeoJets ⧸ J) :=IsArtinianRing.of_finite GeoField _
  have :Ring.KrullDimLE 0 (GeoJets ⧸ J) :=isArtinianRing_iff_krullDimLE_zero.mp ‹_›
  have hp:=c4m x
  change oF x∈J.minimalPrimes
  rw [Ideal.minimalPrimes_eq_comap]
  refine ⟨(oF x).map (Ideal.Quotient.mk J),?_,Ideal.comap_map_mk hx⟩
  have :=Ideal.isPrime_map_quotientMk_of_isPrime hx
  exact Ideal.mem_minimalPrimes_of_krullDimLE_zero _
end
end Dr
