import ProximityPrize.SubmissionLower.ContactMovingSeedlessGeometry6733Research
import ProximityPrize.SubmissionLower.ContactSeedlessLambdaResearch
namespace ProximityPrize.SubmissionLower.ContactMovingSeedlessGeometry6733Research
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
open ContactSeedlessListBoundResearch
open AlignmentMomentCurveProjection AlignmentInterleavedLambda
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
section
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
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
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:CharP IRSProfile.Field prime:=by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem exists_seedless_vanishing_interpolant
    (received:IRSProfile.Index → IRSProfile.Field):
    ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
      Q≠0∧
      Q∈ContactSeedlessInterpolationResearch.globalCoefficientBox IRSProfile.Field
        weightedCap w yTotalCap slopeCap∧
      Q∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        weightedCap w yTotalCap slopeCap∧
      ∀ (P:Polynomial IRSProfile.Field)
        (support:Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i∈support,P.eval (IRSProfile.domain i)=received i) →
        ContactTranslation.specialization IRSProfile.Field P 0 Q=0:=by
  classical
  obtain ⟨Q,hQ,hbox,hcontact⟩:=
    ContactMovingSeedless6733Research.exists_seedless_interpolant received
  change Q∈ContactSeedlessInterpolationResearch.globalCoefficientBox IRSProfile.Field
    weightedCap w yTotalCap slopeCap at hbox
  have hlegacy:Q∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
      weightedCap w yTotalCap slopeCap:=by
    intro d hd
    obtain ⟨hYR,hR,hZ,hweight⟩:=hbox hd
    exact ⟨by omega,hR,hweight⟩
  refine ⟨Q,hQ,hbox,hlegacy,?_⟩
  intro P support hdegree hcard hvalues
  apply ContactTranslation.specialization_eq_zero_of_contact_and_degree
    IRSProfile.Field Q P 0 IRSProfile.domain received (fun _ => 0)
      support multiplicity
  · intro i hi r
    exact hcontact i r
  · intro i hi
    simpa only [mul_zero,add_zero] using hvalues i hi
  · have hdeg:=ContactTranslation.specialization_natDegree_lt
      IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
      (by norm_num [weightedCap,multiplicity,agreements,n,errors])
      hlegacy hdegree
    have hbound:weightedCap ≤ multiplicity*support.card:=by
      rw [weightedCap]
      exact Nat.mul_le_mul_left multiplicity hcard
    exact hdeg.trans_le hbound
theorem irs_scalar_finite_list_card_le
    (received:IRSProfile.Index → IRSProfile.Field)
    (L:Finset (IRSProfile.Index → IRSProfile.Field))
    (hcode:∀ c∈L,c∈IRSProfile.baseCode)
    (hclose:∀ c∈L,agreements ≤
      (Finset.univ.filter (fun i => c i=received i)).card):
    L.card ≤ listBudget:=by
  classical
  let D:=↥L
  let codeword:D → IRSProfile.baseCode:=fun c => ⟨c.1,hcode c.1 c.2⟩
  let selected:D → Polynomial IRSProfile.Field:=fun c => ReedSolomon.toPolynomial (codeword c)
  let Gamma:Finset (Polynomial IRSProfile.Field):=Finset.univ.image selected
  have hselected:Function.Injective selected:=by
    intro c d h
    apply Subtype.ext
    funext i
    have hh:=congrArg (fun P:Polynomial IRSProfile.Field =>
      P.eval (IRSProfile.domain i)) h
    simpa only [selected,ReedSolomon.toPolynomial_eval_at_domain] using hh
  have hcard:Gamma.card=L.card:=by
    rw [show Gamma=Finset.univ.image selected by rfl,
      Finset.card_image_of_injective _ hselected,Finset.card_univ,
      Fintype.card_coe]
  obtain ⟨Q,hQ,hbox,hlegacy,hvanish⟩:=
    exists_seedless_vanishing_interpolant received
  have hdegree:∀ P∈Gamma,P.natDegree ≤ w:=by
    intro P hP
    obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
    have hp:=ReedSolomon.toPolynomial_mem_lt_deg (codeword c)
    have hdeg:(selected c).degree < ((w+1:ℕ):WithBot ℕ):=by
      have hh:=Polynomial.mem_degreeLT.mp hp
      change (selected c).degree <
        ((IRSProfile.baseDimension:ℕ):WithBot ℕ) at hh
      rw [show IRSProfile.baseDimension=w+1 by
        norm_num [IRSProfile.baseDimension,w]] at hh
      exact hh
    by_cases hz:selected c=0
    · simp [hz]
    · rw [←Polynomial.natDegree_lt_iff_degree_lt hz] at hdeg
      omega
  have hsolution:∀ P∈Gamma,specialization IRSProfile.Field P 0 Q=0:=by
    intro P hP
    obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
    let A:=Finset.univ.filter (fun i => c.1 i=received i)
    apply hvanish (selected c) A (hdegree (selected c)
      (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩))
      (hclose c.1 c.2)
    intro i hi
    have hcval:=ReedSolomon.toPolynomial_eval_at_domain (c:=codeword c) (i:=i)
    exact hcval.trans (Finset.mem_filter.mp hi).2
  have hagreement:∀ P∈Gamma,agreements ≤
      (Finset.univ.filter (fun i => P.eval (IRSProfile.domain i)=received i)).card:=by
    intro P hP
    obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
    have heq:Finset.univ.filter
        (fun i => (selected c).eval (IRSProfile.domain i)=received i)=
        Finset.univ.filter (fun i => c.1 i=received i):=by
      apply Finset.filter_congr
      intro i hi
      rw [ReedSolomon.toPolynomial_eval_at_domain]
    rw [heq]
    exact hclose c.1 c.2
  have hbound:=seedless_list_card_le IRSProfile.Field Q hQ hbox hlegacy Gamma
    (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain received
    IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index,n]) hdegree hsolution hagreement
  rwa [hcard] at hbound
end
end ProximityPrize.SubmissionLower.ContactMovingSeedlessGeometry6733Research
