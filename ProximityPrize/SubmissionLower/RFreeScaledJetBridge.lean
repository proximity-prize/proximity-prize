import ProximityPrize.SubmissionLower.RFreeJetCodimension

set_option autoImplicit true

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
    ContactMovingSeedless6735Research.exists_seedless_interpolant received
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
end ProximityPrize.SubmissionLower.ContactMovingSeedlessGeometry6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactMovingProtocol6735Research
open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open AlignmentMomentCurveProjection AlignmentInterleavedLambda
open scoped Classical NNReal
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
def n:ℕ:=262144
def errors:ℕ:=80161
def agreements:ℕ:=n-errors
def listBudget:ℕ:=967448892
def mcaBudget:ℕ:=274980727143946195
def radius:ℝ≥0:=ContactMovingSeedless6735Research.radius
theorem field_capacity_split:
    2^(128:ℕ)*(mcaBudget+listBudget) ≤ Fintype.card IRSProfile.Field:=
  ContactMovingSeedless6735Research.field_capacity_split
theorem irs_interleaved_finite_list_card_le
    {r:ℕ}
    (received:IRSProfile.Index → Fin r → IRSProfile.Field)
    (L:Finset (IRSProfile.Index → Fin r → IRSProfile.Field))
    (hrows:∀ v∈L,∀ j:Fin r,
      (fun i => v i j)∈IRSProfile.baseCode)
    (hclose:∀ v∈L,agreements ≤
      (Finset.univ.filter (fun i => v i=received i)).card)
    (hseparation:(r-1)*(listBudget+1).choose 2 <
      Fintype.card IRSProfile.Field):
    L.card ≤ listBudget:=by
  classical
  letI:DecidableEq (IRSProfile.Index → Fin r → IRSProfile.Field):=Classical.decEq _
  letI:DecidableEq (IRSProfile.Index → IRSProfile.Field):=Classical.decEq _
  by_contra hnot
  obtain ⟨D,hDL,hDcard⟩:=
    Finset.exists_subset_card_eq (show listBudget+1 ≤ L.card by omega)
  have hsepD:(r-1)*D.card.choose 2 < Fintype.card IRSProfile.Field:=by
    rw [hDcard]
    exact hseparation
  obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
  let projected:Finset (IRSProfile.Index → IRSProfile.Field):=
    D.image (momentProjection (ι:=IRSProfile.Index) (r:=r) t)
  have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
  have hcode:∀ c∈projected,c∈IRSProfile.baseCode:=by
    intro c hc
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
    exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
  have hnear:∀ c∈projected,agreements ≤
      (Finset.univ.filter (fun i => c i=momentProjection t received i)).card:=by
    intro c hc
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
    exact (hclose v (hDL hv)).trans
      (Finset.card_le_card (momentProjection_preserves_agreements t v received))
  have hbound:=ContactMovingSeedlessGeometry6735Research.irs_scalar_finite_list_card_le (momentProjection t received)
    projected hcode hnear
  change projected.card ≤ listBudget at hbound
  rw [hprojcard,hDcard] at hbound
  omega
theorem sixteen_row_separation:
    15*(listBudget+1).choose 2 < Fintype.card IRSProfile.Field:=by
  rw [show Fintype.card IRSProfile.Field=(2130706433:ℕ)^6 by
    norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize],
    Nat.choose_eq_descFactorial_div_factorial]
  norm_num [listBudget,Nat.descFactorial_succ,Nat.factorial_succ]
theorem squared_eight_lambda_new
    (delta:ℝ)
    (hcell:(delta:ℝ)*(Fintype.card IRSProfile.Index:ℝ) <
      ((errors+1:ℕ):ℝ)):
    Code.Lambda
      (((IRSProfile.baseCode^⋈ (Fin 8))^⋈ (Fin 2):
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin 8 → IRSProfile.Field)):
        Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))
      delta ≤ (listBudget:ℕ∞):=by
  apply ContactSeedlessLambdaResearch.squared_eight_lambda_le_of_interleaved_list
    IRSProfile.baseCode errors listBudget ?_ delta hcell
  intro received L hrows hclose
  have hclose':∀ v∈L,agreements ≤
      (Finset.univ.filter (fun i => v i=received i)).card:=by
    intro v hv
    simpa [agreements,n,errors,IRSProfile.Index] using hclose v hv
  classical
  letI:DecidableEq (IRSProfile.Index → Fin 16 → IRSProfile.Field):=Classical.decEq _
  letI:DecidableEq (IRSProfile.Index → IRSProfile.Field):=Classical.decEq _
  by_contra hnot
  obtain ⟨D,hDL,hDcard⟩:=
    Finset.exists_subset_card_eq (show listBudget+1 ≤ L.card by omega)
  have hsepD:15*D.card.choose 2 < Fintype.card IRSProfile.Field:=by
    rw [hDcard]
    exact sixteen_row_separation
  obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
  let projected:Finset (IRSProfile.Index → IRSProfile.Field):=
    D.image (momentProjection (ι:=IRSProfile.Index) (r:=16) t)
  have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
  have hcode:∀ c∈projected,c∈IRSProfile.baseCode:=by
    intro c hc
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
    exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
  have hnear:∀ c∈projected,agreements ≤
      (Finset.univ.filter (fun i => c i=momentProjection t received i)).card:=by
    intro c hc
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
    exact (hclose' v (hDL hv)).trans
      (Finset.card_le_card (momentProjection_preserves_agreements t v received))
  have hbound:=ContactMovingSeedlessGeometry6735Research.irs_scalar_finite_list_card_le
    (momentProjection t received) projected hcode hnear
  change projected.card ≤ listBudget at hbound
  rw [hprojcard,hDcard] at hbound
  omega
theorem lambda_le:
    Code.Lambda
      ((IRSProfile.code^⋈ (Fin 2):
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (radius:ℝ) ≤ (listBudget:ℕ∞):=by
  rw [irs_squared_carrier_eq]
  apply squared_eight_lambda_new (radius:ℝ)
  norm_num [radius,ContactMovingSeedless6735Research.radius,claimedRadius,
    errors,IRSProfile.Index]
theorem base_mca_le_of_alignment
    (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius:ℝ) ≤
      ENNReal.ofReal ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius:ℝ) errors mcaBudget
  · intro A hA
    have hcomp:=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0:ℝ) ≤ (radius:ℝ) by positivity)).mp hA
    rw [show ⌊(radius:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=errors by
      simpa only [radius,errors,ContactMovingSeedless6735Research.errors] using
        ContactMovingSeedless6735Research.radius_floor] at hcomp
    have hn:Fintype.card IRSProfile.Index=262144:=by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors,ContactMovingSeedless6735Research.errors] at hcomp ⊢
    omega
  · exact halign
theorem mca_le_of_alignment
    (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (radius:ℝ) ≤
      (mcaBudget:ENNReal)/
        (Fintype.card IRSProfile.Field:ENNReal):=by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius:ℝ):=by
      rw [ContactSeedlessProtocolResearch.irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius,ContactMovingSeedless6735Research.radius,
          claimedRadius])
        (by norm_num [radius,ContactMovingSeedless6735Research.radius,
          claimedRadius])
    _ ≤ ENNReal.ofReal
        ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=
      base_mca_le_of_alignment halign
    _=(mcaBudget:ENNReal)/
        (Fintype.card IRSProfile.Field:ENNReal):=by
      rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
theorem certifiedGammaError_le_of_alignment
    (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
    certifiedGammaError IRSProfile.code radius ≤
      (1:ℝ≥0)/2^(128:ℕ):=by
  rw [←ENNReal.coe_le_coe,coe_certifiedGammaError]
  push_cast
  have hLambdaNat:=ENat.toNat_le_of_le_coe lambda_le
  have hList:
      ((Code.Lambda
        ((IRSProfile.code^⋈ (Fin 2):
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
            IRSProfile.Field))
        (radius:ℝ)).toNat:ENNReal)/
          (Fintype.card IRSProfile.Field:ENNReal) ≤
        (listBudget:ENNReal)/
          (Fintype.card IRSProfile.Field:ENNReal):=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (mcaBudget:ENNReal)/
          (Fintype.card IRSProfile.Field:ENNReal)+
        (listBudget:ENNReal)/
          (Fintype.card IRSProfile.Field:ENNReal):=
      add_le_add (mca_le_of_alignment halign) hList
    _=((mcaBudget+listBudget:ℕ):ENNReal)/
        (Fintype.card IRSProfile.Field:ENNReal):=by
      rw [←ENNReal.add_div,Nat.cast_add]
    _ ≤ (1:ENNReal)/2^(128:ℕ):=by
      apply ContactSeedlessProtocolResearch.nat_div_le_inv_pow
      · norm_num [mcaBudget,listBudget]
      · simpa only [Nat.mul_comm] using field_capacity_split
theorem protocolClaim6735_of_alignment
    (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
    ProtocolClaim 6740 10260735 33554432 where
  admissible:=ContactMovingSeedless6735Research.radius_admissible
  reduction:=by
    change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
    exact (certifiedGammaError_le_of_alignment halign).trans
      (by norm_num [reductionTarget,ProximityGap.prizeThreshold,div_le_iff₀])
  score:=ContactMovingSeedless6735Research.radius_score
end
end ProximityPrize.SubmissionLower.ContactMovingProtocol6735Research
end
