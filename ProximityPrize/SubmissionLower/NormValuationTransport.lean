import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.NormValuation
namespace ProximityPrize.SubmissionLower.NormValuationTransport
open scoped BigOperators Classical
open IsDedekindDomain
noncomputable section
section OneRing
variable (A F:Type*) [CommRing A] [IsDedekindDomain A] [Field F]
variable [Algebra A F] [IsFractionRing A F]
def fieldOrder (v:HeightOneSpectrum A) (x:F):ℤ:=
  -(v.valuation F x).log
theorem valuation_transport (v:HeightOneSpectrum A) (x:F):
    v.valuation F x=v.valuation (FractionRing A)
      ((FractionRing.algEquiv A F).symm x):=by
  obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=A) x
  simp only [map_div₀,AlgEquiv.commutes,
    HeightOneSpectrum.valuation_of_algebraMap]
theorem fieldOrder_transport (v:HeightOneSpectrum A) (x:F):
    fieldOrder A F v x=NormValuation.orderAt v
      ((FractionRing.algEquiv A F).symm x):=by
  rw [fieldOrder,valuation_transport]
  rfl
end OneRing
section TwoRings
variable (R S:Type*) [CommRing R] [CommRing S]
variable [IsDedekindDomain R] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
local instance:Algebra (FractionRing R) (FractionRing S):=
  FractionRing.liftAlgebra _ _
def placeAbove (v:HeightOneSpectrum R)
    (P:{P:Ideal S//P∈IsDedekindDomain.primesOverFinset v.asIdeal S}):
    HeightOneSpectrum S:=
  ⟨P.1,((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S).mp P.2).1,
    Ideal.ne_bot_of_mem_primesOver v.ne_bot
      ((IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S).mp P.2)⟩
variable (F L:Type*) [Field F] [Field L]
variable [Algebra R F] [IsFractionRing R F]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra F L] [Algebra R L]
variable [IsScalarTower R F L] [IsScalarTower R S L]
theorem norm_transport (x:L):
    Algebra.norm (FractionRing R) ((FractionRing.algEquiv S L).symm x)=
      (FractionRing.algEquiv R F).symm (Algebra.norm F x):=by
  have h:=Algebra.norm_eq_of_equiv_equiv
    (FractionRing.algEquiv R F).toRingEquiv
    (FractionRing.algEquiv S L).toRingEquiv
    (by
      ext y
      exact IsFractionRing.algEquiv_commutes
        (FractionRing.algEquiv R F) (FractionRing.algEquiv S L) y)
    ((FractionRing.algEquiv S L).symm x)
  change Algebra.norm (FractionRing R) ((FractionRing.algEquiv S L).symm x)=
    (FractionRing.algEquiv R F).symm
      (Algebra.norm F ((FractionRing.algEquiv S L)
        ((FractionRing.algEquiv S L).symm x))) at h
  simpa only [AlgEquiv.apply_symm_apply] using h
variable [Algebra.IsSeparable F L]
include F L in
theorem canonical_separable:
    Algebra.IsSeparable (FractionRing R) (FractionRing S):=by
  apply Algebra.IsSeparable.of_equiv_equiv
    (A₁:=F) (B₁:=L) (A₂:=FractionRing R) (B₂:=FractionRing S)
    (FractionRing.algEquiv R F).symm.toRingEquiv
    (FractionRing.algEquiv S L).symm.toRingEquiv
  ext y
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R F).symm (FractionRing.algEquiv S L).symm y
theorem fieldOrder_norm (v:HeightOneSpectrum R) (x:L) (hx:x≠0):
    fieldOrder R F v (Algebra.norm F x)=
      ∑ P∈(IsDedekindDomain.primesOverFinset v.asIdeal S).attach,
        (P.1.inertiaDeg R:ℤ)*fieldOrder S L (placeAbove R S v P) x:=by
  letI:Algebra.IsSeparable (FractionRing R) (FractionRing S):=
    canonical_separable R S F L
  have h:=NormValuation.orderAt_fieldNorm R S v
    ((FractionRing.algEquiv S L).symm x) (by simpa using hx)
  calc
    fieldOrder R F v (Algebra.norm F x)=
        NormValuation.orderAt v
          ((FractionRing.algEquiv R F).symm (Algebra.norm F x)):=
      fieldOrder_transport R F v (Algebra.norm F x)
    _=∑ P∈(IsDedekindDomain.primesOverFinset v.asIdeal S).attach,
        (P.1.inertiaDeg R:ℤ)*NormValuation.orderAt (placeAbove R S v P)
          ((FractionRing.algEquiv S L).symm x):=by
      simpa only [norm_transport R S F L x,NormValuation.primeFiber,
        NormValuation.fiberPlace,placeAbove] using h
    _=_:=by
      apply Finset.sum_congr rfl
      intro P _
      congr 1
      exact (fieldOrder_transport S L (placeAbove R S v P) x).symm
end TwoRings
end
end ProximityPrize.SubmissionLower.NormValuationTransport
