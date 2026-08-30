import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch
import ProximityPrize.SubmissionLower.ContactSeedlessProperCutResearch
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.ContactSingularDegreeBounds
import ProximityPrize.SubmissionLower.ContactImplicitContactLift
import ProximityPrize.SubmissionLower.ContactTaylorNumerators
import ProximityPrize.SubmissionLower.ContactExceptionalSeedCount
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
namespace ProximityPrize.SubmissionLower.ContactSeedlessListBoundResearch
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation ContactInterpolation ContactPolynomialSolutions
open ContactFactorCaps ContactImplicitContactLift ContactTaylorNumerators
open ContactGenericSurface ContactGenericInitialPoint ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount ContactSingularAuxiliary
open ContactSingularDegreeBounds
open ContactSelectedSeedDecomposition
open ContactSeedlessInterpolationResearch
open ContactSeedlessPrimeIncidenceResearch ContactSeedlessProperCutResearch
open ActualCoordinateDegreeSum
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
def prime:ℕ:=2130706433
def gap:ℕ:=agreements-w
def capY:ℕ:=1+2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap-1)
def agreementCap:Fin 3 → ℕ:=![capY,capR,1]
def regularListNumerator:ℕ:=
  (n-w)*(capY*slopeCap+capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap-1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator+singularListCap*gap
def listBudget:ℕ:=600000000
theorem numeric_values:
    gap=51207∧capY=13369243∧capR=2228207∧
      regularListNumerator=30666067671312∧
      singularListCap=867∧listNumerator=30666112067781:=by
  norm_num [gap,capY,capR,regularListNumerator,singularListCap,
    listNumerator,agreements,n,errors,w,yTotalCap,slopeCap]
theorem list_numerator_fits:listNumerator < listBudget*gap:=by
  norm_num [listNumerator,regularListNumerator,singularListCap,listBudget,
    gap,capY,capR,agreements,n,errors,w,yTotalCap,slopeCap]
theorem list_strict_ceiling_exact:
    listNumerator/gap+1=598865626∧
      listNumerator < 598865626*gap∧
      598865626 < listBudget:=by
  norm_num [listNumerator,regularListNumerator,singularListCap,listBudget,
    gap,capY,capR,agreements,n,errors,w,yTotalCap,slopeCap]
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
theorem seedless_degree_caps
    (Q:MvPolynomial (Fin 4) K)
    (hbox:Q∈ContactSeedlessInterpolationResearch.globalCoefficientBox K
      weightedCap w yTotalCap slopeCap):
    Q.degreeOf 1 ≤ yTotalCap∧Q.degreeOf 2 ≤ slopeCap∧
      Q.degreeOf 3=0:=by
  refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
    MvPolynomial.degreeOf_le_iff.mpr ?_,?_⟩
  · intro d hd
    exact (Nat.le_add_right (d 1) (d 2)).trans (hbox hd).1
  · intro d hd
    exact (hbox hd).2.1
  · apply Nat.eq_zero_of_le_zero
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.2.1.le
theorem agreement_cap
    (phi:Polynomial K →+*GenericField K)
    (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1 ≤ yTotalCap)
    (hR:F.degreeOf 2 ≤ slopeCap)
    (hZ:F.degreeOf 3=0) (x u:K):
    ∀ j,(agreementPolynomial phi F w x u 0).degreeOf j ≤ agreementCap j:=by
  have hb:=agreementNumerator_degree_bounds F yTotalCap slopeCap 0
    (by norm_num [slopeCap]) hY hR hZ.le w
      (fun j => (j.factorial:K)⁻¹) x u 0
  intro j
  fin_cases j
  · exact (surfaceMap_degreeOf_le phi _ 0).trans
      (hb.1.trans (by simp [agreementCap,capY]))
  · exact (surfaceMap_degreeOf_le phi _ 1).trans
      (hb.2.1.trans (by simp [agreementCap,capR]))
  · exact (surfaceMap_degreeOf_le phi _ 2).trans
      (hb.2.2.trans (by simp [agreementCap]))
abbrev GeometricFactor (F:MvPolynomial (Fin 4) K):=
  ContactOriginalRegularSeedCount.GeometricFactor K F
def geometricPolynomials (F:MvPolynomial (Fin 4) K)
    (Gamma:Finset (Polynomial K)) (g:GeometricFactor K F):
    Finset (Polynomial K):=by
  classical
  exact Gamma.filter (fun S =>
    MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S) g.1=0)
theorem geometricPolynomials_subset
    (F:MvPolynomial (Fin 4) K) (Gamma:Finset (Polynomial K))
    (g:GeometricFactor K F):geometricPolynomials K F Gamma g ⊆ Gamma:=by
  classical
  exact Finset.filter_subset _ _
theorem card_le_sum_geometricPolynomials
    (F:MvPolynomial (Fin 4) K) (hF:F≠0)
    (Gamma:Finset (Polynomial K))
    (hsolutions:∀ S∈Gamma,specialization K S 0 F=0):
    Gamma.card ≤ ∑ g:GeometricFactor K F,
      (geometricPolynomials K F Gamma g).card:=by
  classical
  have hcover:Gamma ⊆ Finset.univ.biUnion (geometricPolynomials K F Gamma):=by
    intro S hS
    have hz:MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S)
        (surfaceMap (polynomialEmbedding K) F)=0:=by
      rw [seedlessPoint_surface_evaluation,
        eval_polynomialPoint_eq_specialization,hsolutions S hS]
      simp
    obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero (polynomialEmbedding K)
      (polynomialEmbedding_injective K) F hF
      (seedlessPoint (polynomialEmbedding K) S) hz
    exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hS,hzg⟩⟩
  exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
theorem geometric_seedless_cut_proper
    (g:MvPolynomial (Fin 3) (GenericField K))
    (hR:0 < g.degreeOf 1):
    ¬ g∣(seedlessCut:MvPolynomial (Fin 3) (GenericField K)):=by
  intro hdvd
  have hle:=coordinate_degree_le_of_dvd 1 g seedlessCut hdvd
    (by simp [seedlessCut])
  have hx:(seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1=0:=by
    simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2)]
  rw [hx] at hle
  omega
theorem original_regular_seedless_bound
    [CharP K prime]
    (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
    (hRpos:0 < F.degreeOf 2)
    (hbox:F∈ContactInterpolation.globalCoefficientBox K
      weightedCap w yTotalCap slopeCap)
    (hY:F.degreeOf 1 ≤ yTotalCap)
    (hR:F.degreeOf 2 ≤ slopeCap)
    (hZ:F.degreeOf 3=0)
    (Gamma:Finset (Polynomial K))
    (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
    (hsolutions:∀ S∈Gamma,specialization K S 0 F=0)
    (hregular:∀ S∈Gamma,
      specialization K S 0 (MvPolynomial.pderiv (2:Fin 4) F)≠0)
    {Iota:Type} [Fintype Iota] [DecidableEq Iota]
    (nodes:Finset Iota) (x received:Iota → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hagreement:∀ S∈Gamma,agreements ≤
      (nodes.filter (fun i => S.eval (x i)=received i)).card):
    Gamma.card*gap ≤
      (n-w)*(capY*F.degreeOf 2+capR*F.degreeOf 1):=by
  classical
  letI:CharP (GenericField K) prime:=genericField_charP K prime
  have hsmall:F.degreeOf 2 < prime:=hR.trans_lt (by
    norm_num [slopeCap,prime])
  have hcount (g:GeometricFactor K F):
      (geometricPolynomials K F Gamma g).card*gap ≤
        (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0):=by
    obtain ⟨hgirred,hgdiv⟩:=
      surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
    have hgate:=geometric_factor_regular_gate K (GenericField K) F hF
      prime hRpos hsmall g.1 hgirred
      (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
    have hproper:=geometric_seedless_cut_proper K g.1 hgate.1
    have hgY:=(geometricFactor_degree_le K F hF.ne_zero g 0).trans hY
    have hgR:=(geometricFactor_degree_le K F hF.ne_zero g 1).trans hR
    have hgZ:g.1.degreeOf 2=0:=Nat.eq_zero_of_le_zero
      ((geometricFactor_degree_le K F hF.ne_zero g 2).trans_eq hZ)
    have hGdegree:∀ j:Fin 3,g.1.degreeOf j < prime:=by
      intro j
      fin_cases j
      · exact hgY.trans_lt (by norm_num [yTotalCap,prime])
      · exact hgR.trans_lt (by norm_num [slopeCap,prime])
      · simp [hgZ,prime]
    have hcutDegree:∀ j k:Fin 3,j≠k →
        (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf j*
            g.1.degreeOf k+
          g.1.degreeOf j*
            (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf k < prime:=by
      intro j k hjk
      have h0:=hGdegree 0
      have h1:=hGdegree 1
      have h2:=hGdegree 2
      fin_cases j <;> fin_cases k <;>
        simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne] at hjk ⊢ <;>
        omega
    have hsub:=geometricPolynomials_subset K F Gamma g
    have hraw:=seedless_proper_cut_bound (polynomialEmbedding K)
      (polynomialEmbedding_injective K) F g.1 hgirred hgdiv hproper
      (geometricPolynomials K F Gamma g) nodes x received hinj prime w agreements
      (by norm_num [w])
      (by norm_num [w,prime])
      (by norm_num [agreements,w,n,errors])
      (by rw [hnodes];norm_num [agreements,n,errors])
      hGdegree hcutDegree
      (fun S hS => hdegree S (hsub hS))
      (fun S hS => hsolutions S (hsub hS))
      (fun S hS => selectedPoint_regular_of_specialization K F
        (fun _:K => S) 0 (hregular S (hsub hS)))
      (fun S hS => (Finset.mem_filter.mp hS).2)
      (fun S hS => hagreement S (hsub hS)) agreementCap
      (fun i hi => agreement_cap K (polynomialEmbedding K) F hY hR hZ
        (x i) (received i))
    have hx0:
        (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 0=0:=by
      simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(0:Fin 3)≠2)]
    have hx1:
        (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1=0:=by
      simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2)]
    have hx2:
        (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 2=1:=by
      simp [seedlessCut]
    have hm0:coordinateMixedDegree (GenericField K) g.1 seedlessCut 0=
        g.1.degreeOf 1:=by
      rw [ActualCoordinateDegreeSum.coordinateMixedDegree_zero,hx1,hx2]
      omega
    have hm1:coordinateMixedDegree (GenericField K) g.1 seedlessCut 1=
        g.1.degreeOf 0:=by
      rw [ActualCoordinateDegreeSum.coordinateMixedDegree_one,hx0,hx2]
      omega
    have hm2:coordinateMixedDegree (GenericField K) g.1 seedlessCut 2=0:=by
      rw [ActualCoordinateDegreeSum.coordinateMixedDegree_two,hx0,hx1]
      omega
    have hcost:
        (∑ i:Fin 3,agreementCap i*
          coordinateMixedDegree (GenericField K) g.1 seedlessCut i)=
        capY*g.1.degreeOf 1+capR*g.1.degreeOf 0:=by
      simp [Fin.sum_univ_succ,agreementCap,hm0,hm1,hm2]
    rw [hnodes,hcost] at hraw
    change (geometricPolynomials K F Gamma g).card*(agreements-w) ≤
      (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0)
    exact hraw
  calc
    Gamma.card*gap ≤
        (∑ g:GeometricFactor K F,
          (geometricPolynomials K F Gamma g).card)*gap:=
      Nat.mul_le_mul_right _
        (card_le_sum_geometricPolynomials K F hF.ne_zero Gamma hsolutions)
    _=∑ g:GeometricFactor K F,
        (geometricPolynomials K F Gamma g).card*gap:=by
      rw [Finset.sum_mul]
    _ ≤ ∑ g:GeometricFactor K F,
        (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0):=
      Finset.sum_le_sum (fun g _ => hcount g)
    _=(n-w)*(capY*(∑ g:GeometricFactor K F,g.1.degreeOf 1)+
        capR*(∑ g:GeometricFactor K F,g.1.degreeOf 0)):=by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,
        ←Finset.mul_sum, ←Finset.mul_sum]
    _ ≤ (n-w)*(capY*F.degreeOf 2+capR*F.degreeOf 1):=by
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add
        (Nat.mul_le_mul_left capY (geometricFactor_sum_degree_le K F hF.ne_zero 1))
        (Nat.mul_le_mul_left capR (geometricFactor_sum_degree_le K F hF.ne_zero 0))
def yProjection (T:Type*) [Field T]:
    MvPolynomial (Fin 3) T →+*Polynomial T:=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,0,0]
def yEmbedding (T:Type*) [Field T]:
    Polynomial T →+*MvPolynomial (Fin 3) T:=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)
theorem y_only_vars {T:Type*} [Field T]
    (S:MvPolynomial (Fin 3) T)
    (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0)
    (i:Fin 3) (hi:i∈S.vars):i=0:=by
  fin_cases i
  · rfl
  · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
  · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hZ)
theorem yProjection_reconstruct {T:Type*} [Field T]
    (S:MvPolynomial (Fin 3) T)
    (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0):
    yEmbedding T (yProjection T S)=S:=by
  change ((yEmbedding T).comp (yProjection T)) S=(RingHom.id _) S
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp [yEmbedding,yProjection]
  · intro i hi _
    rw [y_only_vars S hR hZ i hi]
    simp [yEmbedding,yProjection]
  · rfl
theorem yProjection_nonzero {T:Type*} [Field T]
    (S:MvPolynomial (Fin 3) T) (hS:S≠0)
    (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0):
    yProjection T S≠0:=by
  intro hz
  apply hS
  rw [←yProjection_reconstruct S hR hZ,hz,map_zero]
theorem yProjection_natDegree_le {T:Type*} [Field T]
    (S:MvPolynomial (Fin 3) T):
    (yProjection T S).natDegree ≤ S.degreeOf 0:=by
  classical
  have hsum:yProjection T S=
      ∑ d∈S.support,yProjection T (MvPolynomial.monomial d (S.coeff d)):=by
    rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
  rw [hsum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hmono:(yProjection T (MvPolynomial.monomial d (S.coeff d))).natDegree ≤
      d 0:=by
    have heq:MvPolynomial.monomial d (S.coeff d)=
        MvPolynomial.C (S.coeff d)*MvPolynomial.X 0^d 0*
          MvPolynomial.X 1^d 1*MvPolynomial.X 2^d 2:=by
      exact ContactExceptionalSeedCount.monomial_fin3 d (S.coeff d)
    rw [heq]
    by_cases h1:d 1=0 <;> by_cases h2:d 2=0 <;>
      simp [yProjection,h1,h2]
    have hc:(Polynomial.C (S.coeff d)).natDegree ≤ 0:=by simp
    have hx:((Polynomial.X:Polynomial T)^d 0).natDegree ≤ d 0:=by simp
    simpa only [Nat.zero_add] using Polynomial.natDegree_mul_le_of_le hc hx
  exact hmono.trans (MvPolynomial.monomial_le_degreeOf 0 hd)
theorem yProjection_eval {T:Type*} [Field T]
    (S:MvPolynomial (Fin 3) T)
    (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0)
    (v:Fin 3 → T):
    (yProjection T S).eval (v 0)=MvPolynomial.eval v S:=by
  change ((Polynomial.evalRingHom (v 0)).comp (yProjection T)) S=
    (MvPolynomial.eval v) S
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp [yProjection]
  · intro i hi _
    rw [y_only_vars S hR hZ i hi]
    simp [yProjection]
  · rfl
def yWeights:Fin 4 → ℕ:=![0,1,0,0]
def zWeights:Fin 4 → ℕ:=![0,0,0,1]
theorem degreeY_le_yWeight (Q:MvPolynomial (Fin 4) K):
    Q.degreeOf 1 ≤ MvPolynomial.weightedTotalDegree yWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree yWeights hd
  rw [weight_fin4] at h
  simpa [yWeights] using h
theorem degreeZ_le_zWeight (Q:MvPolynomial (Fin 4) K):
    Q.degreeOf 3 ≤ MvPolynomial.weightedTotalDegree zWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree zWeights hd
  rw [weight_fin4] at h
  simpa [zWeights] using h
theorem singular_seedless_card_le
    [CharP K prime]
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    (hbox:Q∈ContactSeedlessInterpolationResearch.globalCoefficientBox K
      weightedCap w yTotalCap slopeCap)
    (Gamma:Finset (Polynomial K))
    (hsolutions:∀ S∈Gamma,
      specialization K S 0 (singularAuxiliary Q)=0):
    Gamma.card ≤ singularListCap:=by
  classical
  let phi:=polynomialEmbedding K
  let J:=singularAuxiliary Q
  have hcaps:=seedless_degree_caps K Q hbox
  have hJne:J≠0:=singularAuxiliary_nonzero Q hQ prime
    (hcaps.2.1.trans_lt (by norm_num [slopeCap,prime]))
  have hJR:J.degreeOf 2=0:=singularAuxiliary_R_degree Q hQ prime
    (hcaps.2.1.trans_lt (by norm_num [slopeCap,prime]))
  have hQY:MvPolynomial.weightedTotalDegree yWeights Q ≤ yTotalCap:=by
    apply (weightedTotalDegree_le_iff yWeights Q yTotalCap).mpr
    intro d hd
    have hh:=(hbox hd).1
    rw [weight_fin4]
    simpa [yWeights] using (Nat.le_add_right (d 1) (d 2)).trans hh
  have hQZ:MvPolynomial.weightedTotalDegree zWeights Q ≤ 0:=by
    apply (weightedTotalDegree_le_iff zWeights Q 0).mpr
    intro d hd
    have hh:=(hbox hd).2.2.1
    rw [weight_fin4]
    simpa [zWeights,hh]
  have hJYw:=singularAuxiliary_weight_le yWeights Q hQ slopeCap
    (by norm_num [slopeCap]) hcaps.2.1
  have hJZw:=singularAuxiliary_weight_le zWeights Q hQ slopeCap
    (by norm_num [slopeCap]) hcaps.2.1
  have hJY:J.degreeOf 1 ≤ singularListCap:=
    (degreeY_le_yWeight K J).trans (hJYw.trans (by
      unfold singularListCap
      exact Nat.mul_le_mul_left _ hQY))
  have hJZ:J.degreeOf 3=0:=Nat.eq_zero_of_le_zero
    ((degreeZ_le_zWeight K J).trans (hJZw.trans (by
      simpa only [Nat.mul_zero] using Nat.mul_le_mul_left (2*slopeCap-1) hQZ)))
  let A:MvPolynomial (Fin 3) (GenericField K):=surfaceMap phi J
  have hAne:A≠0:=surfaceMap_ne_zero phi (polynomialEmbedding_injective K) J hJne
  have hAR:A.degreeOf 1=0:=Nat.eq_zero_of_le_zero
    ((surfaceMap_degreeOf_le phi J 1).trans_eq hJR)
  have hAZ:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero
    ((surfaceMap_degreeOf_le phi J 2).trans_eq hJZ)
  let q:Polynomial (GenericField K):=yProjection (GenericField K) A
  have hq:q≠0:=yProjection_nonzero A hAne hAR hAZ
  have hroots:∀ z∈Gamma.image phi,z∈q.roots:=by
    intro z hz
    obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hz
    apply (Polynomial.mem_roots hq).mpr
    change q.eval (phi S)=0
    have hv:seedlessPoint phi S 0=phi S:=by
      simp [seedlessPoint_value]
    change (yProjection (GenericField K) A).eval (phi S)=0
    rw [←hv,yProjection_eval A hAR hAZ (seedlessPoint phi S)]
    rw [seedlessPoint_surface_evaluation,eval_polynomialPoint_eq_specialization,
      hsolutions S hS]
    simp
  have hcard:(Gamma.image phi).card=Gamma.card:=
    Finset.card_image_of_injective _ (polynomialEmbedding_injective K)
  rw [←hcard]
  calc
    (Gamma.image phi).card ≤ q.roots.toFinset.card:=by
      apply Finset.card_le_card
      intro z hz
      exact Multiset.mem_toFinset.mpr (hroots z hz)
    _ ≤ q.roots.card:=Multiset.toFinset_card_le _
    _ ≤ q.natDegree:=Polynomial.card_roots' q
    _ ≤ A.degreeOf 0:=yProjection_natDegree_le A
    _ ≤ J.degreeOf 1:=surfaceMap_degreeOf_le phi J 0
    _ ≤ singularListCap:=hJY
def singularPolynomials (Q:MvPolynomial (Fin 4) K)
    (Gamma:Finset (Polynomial K)):Finset (Polynomial K):=by
  classical
  exact Gamma.filter (fun S => specialization K S 0 (singularAuxiliary Q)=0)
def regularPolynomials (Q:MvPolynomial (Fin 4) K)
    (Gamma:Finset (Polynomial K)) (F:↥(positiveRFactors Q)):
    Finset (Polynomial K):=by
  classical
  exact Gamma.filter (fun S => RegularSolution F.1 S 0)
theorem seedless_solution_cover
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    (Gamma:Finset (Polynomial K))
    (hsolutions:∀ S∈Gamma,specialization K S 0 Q=0):
    Gamma.card ≤ (singularPolynomials K Q Gamma).card+
      ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card:=by
  classical
  let regularUnion:=Finset.univ.biUnion (regularPolynomials K Q Gamma)
  have hcover:Gamma ⊆ singularPolynomials K Q Gamma ∪ regularUnion:=by
    intro S hS
    obtain hsing | ⟨F,hF,hreg⟩:=solution_regular_or_auxiliary
      Q hQ S 0 (hsolutions S hS)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hsing⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨F,hF⟩,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hS,hreg⟩⟩
  calc
    Gamma.card ≤ (singularPolynomials K Q Gamma ∪ regularUnion).card:=
      Finset.card_le_card hcover
    _ ≤ (singularPolynomials K Q Gamma).card+regularUnion.card:=
      Finset.card_union_le _ _
    _ ≤ (singularPolynomials K Q Gamma).card+
        ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card:=
      Nat.add_le_add_left Finset.card_biUnion_le _
theorem seedless_list_card_le
    [CharP K prime]
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    (hbox:Q∈ContactSeedlessInterpolationResearch.globalCoefficientBox K
      weightedCap w yTotalCap slopeCap)
    (hlegacy:Q∈ContactInterpolation.globalCoefficientBox K
      weightedCap w yTotalCap slopeCap)
    (Gamma:Finset (Polynomial K))
    {Iota:Type} [Fintype Iota] [DecidableEq Iota]
    (nodes:Finset Iota) (x received:Iota → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
    (hsolutions:∀ S∈Gamma,specialization K S 0 Q=0)
    (hagreement:∀ S∈Gamma,agreements ≤
      (nodes.filter (fun i => S.eval (x i)=received i)).card):
    Gamma.card ≤ listBudget:=by
  classical
  have hcaps:=seedless_degree_caps K Q hbox
  have hsing:(singularPolynomials K Q Gamma).card ≤ singularListCap:=
    singular_seedless_card_le K Q hQ hbox (singularPolynomials K Q Gamma)
      (fun S hS => (Finset.mem_filter.mp hS).2)
  have hreg (F:↥(positiveRFactors Q)):
      (regularPolynomials K Q Gamma F).card*gap ≤
        (n-w)*(capY*F.1.degreeOf 2+capR*F.1.degreeOf 1):=by
    have hdata:=directFactor_data Q F.1 hQ weightedCap w yTotalCap slopeCap
      hlegacy F.2
    have hdivF:=(positiveRFactors_spec Q F.1 F.2).2.1
    have hFZ:F.1.degreeOf 3=0:=Nat.eq_zero_of_le_zero
      ((degreeOf_le_of_dvd 3 F.1 Q hdivF hQ).trans_eq hcaps.2.2)
    have hsub:regularPolynomials K Q Gamma F ⊆ Gamma:=Finset.filter_subset _ _
    exact original_regular_seedless_bound K F.1 hdata.1 hdata.2.1 hdata.2.2
      ((degreeOf_le_of_dvd 1 F.1 Q hdivF hQ).trans hcaps.1)
      ((degreeOf_le_of_dvd 2 F.1 Q hdivF hQ).trans hcaps.2.1)
      hFZ (regularPolynomials K Q Gamma F)
      (fun S hS => hdegree S (hsub hS))
      (fun S hS => (Finset.mem_filter.mp hS).2.1)
      (fun S hS => (Finset.mem_filter.mp hS).2.2)
      nodes x received hinj hnodes (fun S hS => hagreement S (hsub hS))
  have hsumY:=sum_coordinate_degrees_le_of_prod_dvd
    (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 1
  have hsumR:=sum_coordinate_degrees_le_of_prod_dvd
    (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 2
  have hsumY':(∑ F:↥(positiveRFactors Q),F.1.degreeOf 1) ≤ Q.degreeOf 1:=by
    simpa only [Finset.sum_coe_sort,id_eq] using hsumY
  have hsumR':(∑ F:↥(positiveRFactors Q),F.1.degreeOf 2) ≤ Q.degreeOf 2:=by
    simpa only [Finset.sum_coe_sort,id_eq] using hsumR
  have hregularScaled:
      (∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap ≤
        regularListNumerator:=by
    calc
      _=∑ F:↥(positiveRFactors Q),
          (regularPolynomials K Q Gamma F).card*gap:=by rw [Finset.sum_mul]
      _ ≤ ∑ F:↥(positiveRFactors Q),
          (n-w)*(capY*F.1.degreeOf 2+capR*F.1.degreeOf 1):=
        Finset.sum_le_sum (fun F _ => hreg F)
      _=(n-w)*(capY*(∑ F:↥(positiveRFactors Q),F.1.degreeOf 2)+
          capR*(∑ F:↥(positiveRFactors Q),F.1.degreeOf 1)):=by
        rw [←Finset.mul_sum,Finset.sum_add_distrib,
          ←Finset.mul_sum, ←Finset.mul_sum]
      _ ≤ (n-w)*(capY*slopeCap+capR*yTotalCap):=by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add (Nat.mul_le_mul_left capY (hsumR'.trans hcaps.2.1))
          (Nat.mul_le_mul_left capR (hsumY'.trans hcaps.1))
      _=regularListNumerator:=rfl
  have hcover:=seedless_solution_cover K Q hQ Gamma hsolutions
  have hscaled:=Nat.mul_le_mul_right gap hcover
  have htotal:Gamma.card*gap ≤ listNumerator:=by
    calc
      Gamma.card*gap ≤
          ((singularPolynomials K Q Gamma).card+
            ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap:=
        hscaled
      _=(singularPolynomials K Q Gamma).card*gap+
          (∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap:=by
        ring
      _ ≤ singularListCap*gap+regularListNumerator:=
        Nat.add_le_add (Nat.mul_le_mul_right gap hsing) hregularScaled
      _=listNumerator:=by simp only [listNumerator];ring
  by_contra hnot
  have hlarge:listBudget < Gamma.card:=Nat.lt_of_not_ge hnot
  have hgap:0 < gap:=by norm_num [gap,agreements,n,errors,w]
  have hmul:=Nat.mul_lt_mul_of_pos_right hlarge hgap
  have hcontra:listBudget*gap < listNumerator:=hmul.trans_le htotal
  exact (Nat.not_lt_of_ge hcontra.le) list_numerator_fits
end
end ProximityPrize.SubmissionLower.ContactSeedlessListBoundResearch
