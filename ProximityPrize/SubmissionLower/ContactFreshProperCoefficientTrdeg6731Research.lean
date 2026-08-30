import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactCoefficientFieldTrdeg6731Research
import ProximityPrize.SubmissionLower.ContactTrivariateTrdeg6731Research
import ProximityPrize.SubmissionLower.ContactGaussLocalization
namespace ProximityPrize.SubmissionLower.ContactFreshProperCoefficientTrdeg6731Research
open ContactDifferentialRing ContactTranslation ContactGenericSurface
  ContactGaussLocalization ContactFreshCoefficientFieldGenerationResearch
  ContactCoefficientFieldTrdeg6731Research
  ContactTrivariateTrdeg6731Research ContactFunctionFieldTrdeg6731Research
  ArbitraryRationalProjectionResearch
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
private def freshJet (P:Polynomial L) (γ:L) (i:Fin 4):
    jetField (k:=k) P γ:=
  ⟨freshPoint P γ i,IntermediateField.subset_adjoin k _ ⟨i,rfl⟩⟩
@[simp] private theorem freshJet_val (P:Polynomial L) (γ:L) (i:Fin 4):
    ((freshJet (k:=k) P γ i:jetField (k:=k) P γ):RatFunc L)=
      freshPoint P γ i:=rfl
private def freshOtherJet (P:Polynomial L) (γ:L) (i:Fin 3):
    jetField (k:=k) P γ:=freshJet (k:=k) P γ i.succ
private theorem freshTau_transcendental (P:Polynomial L) (γ:L):
    Transcendental k (freshJet (k:=k) P γ 0):=by
  intro h
  have h':IsAlgebraic k (RatFunc.X:RatFunc L):=by
    exact IntermediateField.isAlgebraic_iff.mp h
  exact (RatFunc.transcendental_X.restrictScalars
    (algebraMap k L).injective) h'
set_option maxHeartbeats 1000000 in
theorem baseCoefficientField_trdeg_le_one_of_fresh_proper_relations
    (F T:Poly4 k) (P:Polynomial L) (γ:L)
    (hF:Irreducible F)
    (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
    (hproper:¬ F∣T)
    (hFsolution:specialization L P γ
      (MvPolynomial.map (algebraMap k L) F)=0)
    (hTsolution:specialization L P γ
      (MvPolynomial.map (algebraMap k L) T)=0)
    (hreg:specialization L P γ
      (MvPolynomial.pderiv (2:Fin 4)
        (MvPolynomial.map (algebraMap k L) F))≠0)
    (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
    Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
  classical
  let E:=jetField (k:=k) P γ
  let full:Fin 4 → E:=freshJet (k:=k) P γ
  let v:Fin 3 → E:=freshOtherJet (k:=k) P γ
  let τ:E:=freshJet (k:=k) P γ 0
  have hτ:Transcendental k τ:=freshTau_transcendental P γ
  let rawEquiv:=FractionRing.algEquiv (Polynomial k) (RatFunc k)
  let coeffEquiv:RationalCoefficients k ≃ₐ[k] RatFunc k:=rawEquiv.restrictScalars k
  let baseRat:RatFunc k →ₐ[k] E:=elementEmbedding k E τ hτ
  let base:RationalCoefficients k →ₐ[k] E:=baseRat.comp coeffEquiv.toAlgHom
  letI:Algebra (RationalCoefficients k) E:=base.toRingHom.toAlgebra
  letI:IsScalarTower k (RationalCoefficients k) E:=
    IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
  have hbaseX:base
      (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)=τ:=by
    change baseRat (rawEquiv
      (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X))=τ
    rw [rawEquiv.commutes,elementEmbedding_variable]
  have hfull:IntermediateField.adjoin k (Set.range full)=⊤:=by
    apply IntermediateField.map_injective E.val
    rw [IntermediateField.adjoin_map, ←AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    have himage:E.val '' Set.range full=Set.range (freshPoint P γ):=by
      ext x
      simp [full,freshJet]
    rw [himage]
    rfl
  have hgen:IntermediateField.adjoin (RationalCoefficients k) (Set.range v)=⊤:=by
    let S:=IntermediateField.adjoin (RationalCoefficients k) (Set.range v)
    have hcoords:Set.range full ⊆ S.restrictScalars k:=by
      rintro x ⟨i,rfl⟩
      refine Fin.cases ?_ (fun j↦?_) i
      · have hm:=S.algebraMap_mem
          (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)
        change base
          (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)∈S at hm
        rw [hbaseX] at hm
        exact hm
      · exact IntermediateField.subset_adjoin (RationalCoefficients k) _ ⟨j,rfl⟩
    have htop:S.restrictScalars k=⊤:=by
      apply top_unique
      rw [←hfull]
      exact IntermediateField.adjoin_le_iff.mpr hcoords
    exact (IntermediateField.restrictScalars_eq_top_iff (K:=k)).mp htop
  have hsurface:∀ G:Poly4 k,
      MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
          (rationalSurfaceMap k G)=
        MvPolynomial.eval₂Hom (algebraMap k E) full G:=by
    intro G
    have heq:(MvPolynomial.eval₂Hom
          (algebraMap (RationalCoefficients k) E) v).comp (rationalSurfaceMap k)=
        MvPolynomial.eval₂Hom (algebraMap k E) full:=by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_C,
          MvPolynomial.eval₂Hom_C]
        change base
          (algebraMap (Polynomial k) (RationalCoefficients k) (Polynomial.C a))=
            algebraMap k E a
        calc
          _=base (algebraMap k (RationalCoefficients k) a):=by
            congr 1
          _=algebraMap k E a:=base.commutes a
      · intro i
        refine Fin.cases ?_ (fun j↦?_) i
        · simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_X_zero,
            MvPolynomial.eval₂Hom_C,
            MvPolynomial.eval₂Hom_X']
          change base
            (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)=full 0
          exact hbaseX
        · simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_X_succ,
            MvPolynomial.eval₂Hom_X']
          rfl
    exact RingHom.congr_fun heq G
  have hcoeffcomp:E.val.toRingHom.comp
        (MvPolynomial.eval₂Hom (algebraMap k E) full)=
      (MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ)).comp
        (MvPolynomial.map (algebraMap k L)):=by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
        MvPolynomial.eval₂Hom_C,
        MvPolynomial.map_C]
      change algebraMap k (RatFunc L) a=
        algebraMap L (RatFunc L) (algebraMap k L a)
      exact IsScalarTower.algebraMap_apply k L (RatFunc L) a
    · intro i
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
        MvPolynomial.eval₂Hom_X',
        MvPolynomial.map_X]
      change E.val (full i)=freshPoint P γ i
      rfl
  have hfullroot (G:Poly4 k)
      (hG:specialization L P γ (MvPolynomial.map (algebraMap k L) G)=0):
      MvPolynomial.eval₂Hom (algebraMap k E) full G=0:=by
    apply E.val.injective
    change (E.val.toRingHom.comp
      (MvPolynomial.eval₂Hom (algebraMap k E) full)) G=E.val 0
    rw [hcoeffcomp,RingHom.comp_apply,fresh_eval_eq,hG,map_zero,map_zero]
  have hFroot:MvPolynomial.aeval v (rationalSurfaceMap k F)=0:=by
    change MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
      (rationalSurfaceMap k F)=0
    rw [hsurface]
    exact hfullroot F hFsolution
  have hTroot:MvPolynomial.aeval v (rationalSurfaceMap k T)=0:=by
    change MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
      (rationalSurfaceMap k T)=0
    rw [hsurface]
    exact hfullroot T hTsolution
  have hirr:Irreducible (rationalSurfaceMap k F):=
    rationalSurfaceMap_irreducible k F hF hpos
  have hproperRat:¬ rationalSurfaceMap k F∣rationalSurfaceMap k T:=by
    intro h
    exact hproper ((rationalSurfaceMap_dvd_iff k F T hF hpos).mp h)
  have hrelative:Algebra.trdeg (RationalCoefficients k) E ≤ 1:=
    trdeg_le_one_of_generated_relations (RationalCoefficients k) E v hgen
      (rationalSurfaceMap k F) (rationalSurfaceMap k T)
      hirr hproperRat hFroot hTroot
  have hbaseRat:Algebra.trdeg k (RatFunc k) ≤ 1:=
    trdeg_le_one_of_functionField k (RatFunc k)
  have hbase:Algebra.trdeg k (RationalCoefficients k) ≤ 1:=by
    rw [coeffEquiv.trdeg_eq]
    exact hbaseRat
  have hsum:Algebra.trdeg k (RationalCoefficients k)+
      Algebra.trdeg (RationalCoefficients k) E=Algebra.trdeg k E:=
    trdeg_add_eq k (RationalCoefficients k)
  have hjet:Algebra.trdeg k E ≤ 2:=by
    rw [←hsum]
    exact (add_le_add hbase hrelative).trans_eq (by norm_num)
  have hfield:=fresh_jetField_eq_coefficientField F P γ hFsolution hreg p w hw hP
  change Algebra.trdeg k (jetField (k:=k) P γ) ≤ 2 at hjet
  rw [hfield] at hjet
  exact baseCoefficientField_trdeg_le_one P γ hjet
end
end ProximityPrize.SubmissionLower.ContactFreshProperCoefficientTrdeg6731Research
