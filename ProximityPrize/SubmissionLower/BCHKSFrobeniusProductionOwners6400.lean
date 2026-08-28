import ProximityPrize.SubmissionLower.BCHKSFrobeniusCoordinateOwners6400

/-!
# Production coordinate-owner data

This module connects a concrete sparse Reed--Solomon MCA witness to the
coordinate-owner mechanism.  For a slope outside the two checked coprimality
exceptions, its witness polynomial factors as

`P = (direct₀ + w*direct₁) * M`,

and the multiplier `M` satisfies one fixed global semilinear polynomial
identity.  The original chosen agreement set and its failure of simultaneous
pair explanation are retained; they are essential for selecting a genuine
defect coordinate downstream.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

abbrev Score6400Field := IRSProfile.Field
abbrev Score6400Index := IRSProfile.Index

/-- All data retained from one nonexceptional sparse MCA witness. -/
structure Score6400FactoredWitness
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (w : Score6400Field) where
  agreementSet : Finset Score6400Index
  witnessPolynomial : Score6400Field[X]
  outsideLocator : Score6400Field[X]
  cofactor : Score6400Field[X]
  quotient : Score6400Field[X]
  multiplier : Score6400Field[X]
  agreementSet_large : 185364 ≤ agreementSet.card
  witness_degree : witnessPolynomial.natDegree ≤ 131071
  agreement : ∀ i ∈ agreementSet,
    witnessPolynomial.eval (IRSProfile.domain i) = e₀ i + w * e₁ i
  not_explained : ¬ExplainedPair IRSProfile.baseCode e₀ e₁ agreementSet
  outsideLocator_eq : outsideLocator =
    outsideAgreementLocator IRSProfile.domain agreementSet (pairSupport e₀ e₁)
  cofactor_factor : outsideLocator * cofactor = witnessPolynomial
  cofactor_ne_zero : cofactor ≠ 0
  direct_factor :
    affinePolynomial atom.direct₀ atom.direct₁ w * quotient = cofactor
  multiplier_eq : multiplier = outsideLocator * quotient
  semilinear_identity :
    atom.denominator * multiplier.map koalaSexticFrobenius.toRingHom =
      atom.amplitudeMultiplier * multiplier

/-- A concrete noncancelling MCA witness outside the two cofactor exceptions
produces the full factored data, including the global quotient identity. -/
theorem exists_score6400FactoredWitness_of_good_sparse_mcaBad
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (w : Score6400Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hbad : MCABad IRSProfile.baseCode e₀ e₁ 185364 w)
    (hnoncancel : w ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁))
    (hlarge : 54292 < (pairSupport e₀ e₁).card)
    (hcoprimeAmplitude :
      IsCoprime (affinePolynomial atom.direct₀ atom.direct₁ w)
        atom.amplitudeMultiplier)
    (hcoprimeConjugate :
      IsCoprime (affinePolynomial atom.direct₀ atom.direct₁ w)
        ((affinePolynomial atom.direct₀ atom.direct₁ w).map
          koalaSexticFrobenius.toRingHom)) :
    Nonempty (Score6400FactoredWitness e₀ e₁ atom w) := by
  classical
  let T := pairSupport e₀ e₁
  let S := T.map IRSProfile.domain
  let hh := T.card - 54292
  have hbadRS : MCABad
      (ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension)
      e₀ e₁ 185364 w := by
    simpa only [IRSProfile.baseCode] using hbad
  rcases hbadRS with ⟨Aset, hAcard, ⟨c, hcCode, hcAgree⟩, hnotPair⟩
  change c ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension at hcCode
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcCode
  obtain ⟨P, hPdegree, rfl⟩ := hcCode
  have hPagree : ∀ i ∈ Aset,
      P.eval (IRSProfile.domain i) = e₀ i + w * e₁ i := by
    intro i hi
    simpa [ReedSolomon.evalOnPoints] using hcAgree i hi
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  have hintersects : ∃ i, i ∈ Aset ∧ i ∈ T := by
    by_contra hnone
    push Not at hnone
    apply hnotPair
    refine ⟨0, (ReedSolomon.code IRSProfile.domain
      IRSProfile.baseDimension).zero_mem,
      0, (ReedSolomon.code IRSProfile.domain
        IRSProfile.baseDimension).zero_mem, ?_, ?_⟩
    · intro i hi
      have hz := (pairSupport_values_eq_zero_of_not_mem e₀ e₁
        (show i ∉ pairSupport e₀ e₁ by exact hnone i hi)).1
      simpa only [Pi.zero_apply] using hz.symm
    · intro i hi
      have hz := (pairSupport_values_eq_zero_of_not_mem e₀ e₁
        (show i ∉ pairSupport e₀ e₁ by exact hnone i hi)).2
      simpa only [Pi.zero_apply] using hz.symm
  have hPne : P ≠ 0 := by
    obtain ⟨i, hiA, hiT⟩ := hintersects
    have hlineNe : e₀ i + w * e₁ i ≠ 0 :=
      affine_error_ne_zero_on_support_of_not_cancellation
        e₀ e₁ T (fun _ hi ↦ hi) w hnoncancel i hiT
    intro hPzero
    have hi := hPagree i hiA
    rw [hPzero, Polynomial.eval_zero] at hi
    exact hlineNe hi.symm
  have hzero : ∀ i ∈ Aset, i ∉ T →
      P.eval (IRSProfile.domain i) = 0 := by
    intro i hiA hiT
    obtain ⟨hi₀, hi₁⟩ := pairSupport_values_eq_zero_of_not_mem e₀ e₁ hiT
    rw [hPagree i hiA, hi₀, hi₁, mul_zero, add_zero]
  obtain ⟨Cof, hCofFactor, hCofNe, hCofDegree⟩ :=
    exists_outsideAgreementCofactor IRSProfile.domain Aset T P hPne hzero
  let L := outsideAgreementLocator IRSProfile.domain Aset T
  let Raw := (Aset ∩ T).map IRSProfile.domain
  let E := Raw ∩ atom.valid
  have hPdegreeRoom : P.natDegree + 54292 < Aset.card := by omega
  have hCofRoomIndex : Cof.natDegree + 54292 < (Aset ∩ T).card :=
    outsideAgreementCofactor_degree_room IRSProfile.domain Aset T P Cof
      54292 hCofFactor hCofNe hPdegreeRoom
  have hCofRoom : Cof.natDegree + 54292 < Raw.card := by
    simpa only [Raw, Finset.card_map] using hCofRoomIndex
  have hRawSubset : Raw ⊆ S := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr ⟨i, (Finset.mem_inter.mp hi).2, rfl⟩
  have hEsubset : E ⊆ atom.valid := Finset.inter_subset_right
  have hEcoverage : Raw.card ≤
      E.card + (atom.baseLoss + atom.gcdLoss) := by
    simpa only [E] using card_le_inter_add_of_coverage Raw atom.valid S
      (atom.baseLoss + atom.gcdLoss) hRawSubset atom.valid_subset atom.coverage
  have hfixed : ∀ x ∈ E, koalaSexticFrobenius x = x := by
    intro x hx
    have hxS : x ∈ S := atom.valid_subset (hEsubset hx)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hxS
    exact koalaSexticFrobenius_fixed_domain i
  have hLfixed : L.map koalaSexticFrobenius.toRingHom = L := by
    simpa only [L] using outsideAgreementLocator_map IRSProfile.domain
      koalaSexticFrobenius koalaSexticFrobenius_fixed_domain Aset T
  have hLne : ∀ x ∈ E, L.eval x ≠ 0 := by
    intro x hx
    have hxRaw := (Finset.mem_inter.mp hx).1
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hxRaw
    exact outsideAgreementLocator_eval_ne_zero_of_mem
      IRSProfile.domain Aset T (Finset.mem_inter.mp hi).2
  have hagreementE : ∀ x ∈ E,
      (L * Cof).eval x = score6400ErrorSource e₀ x +
        w * score6400ErrorSource e₁ x := by
    intro x hx
    have hxRaw := (Finset.mem_inter.mp hx).1
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hxRaw
    rw [show L * Cof = P by simpa only [L] using hCofFactor]
    simpa only [score6400ErrorSource_domain] using
      hPagree i (Finset.mem_inter.mp hi).1
  have hTcap : T.card ≤ 76780 := by
    change T.card ≤ Fintype.card Score6400Index - 185364 at hsparse
    norm_num [IRSProfile.Index] at hsparse
    exact hsparse
  have htwo : 2 * hh ≤ 54292 := by
    dsimp only [hh]
    omega
  have hidentity : atom.cofactorRelation w Cof = 0 := by
    apply atom.cofactorRelation_eq_zero w L Cof E Raw.card 54292
    · exact hEsubset
    · exact hfixed
    · exact hLfixed
    · exact hLne
    · exact hagreementE
    · exact hEcoverage
    · exact hCofRoom
    · simpa only [hh, T] using htwo
  have hdiv : affinePolynomial atom.direct₀ atom.direct₁ w ∣ Cof :=
    affinePolynomial_dvd_cofactor_of_cofactorRelation_eq_zero atom w Cof
      hidentity hcoprimeAmplitude hcoprimeConjugate
  obtain ⟨Q, hQFactor'⟩ := hdiv
  have hQFactor : affinePolynomial atom.direct₀ atom.direct₁ w * Q = Cof :=
    hQFactor'.symm
  have hCwNe : affinePolynomial atom.direct₀ atom.direct₁ w ≠ 0 := by
    intro hzeroC
    have hmapzero :
        (affinePolynomial atom.direct₀ atom.direct₁ w).map
          koalaSexticFrobenius.toRingHom = 0 := by rw [hzeroC, Polynomial.map_zero]
    exact hcoprimeConjugate.ne_zero_or_ne_zero.elim
      (fun hleft ↦ hleft hzeroC) (fun hright ↦ hright hmapzero)
  have hQsemi : atom.denominator * Q.map koalaSexticFrobenius.toRingHom =
      atom.amplitudeMultiplier * Q :=
    quotient_semilinear_identity_of_cofactorRelation_eq_zero atom w Cof Q
      hQFactor hCwNe hidentity
  let M := L * Q
  have hMsemi : atom.denominator * M.map koalaSexticFrobenius.toRingHom =
      atom.amplitudeMultiplier * M := by
    simpa only [M] using locator_mul_quotient_semilinear_identity
      koalaSexticFrobenius atom.denominator atom.amplitudeMultiplier L Q
      hQsemi hLfixed
  exact ⟨
    { agreementSet := Aset
      witnessPolynomial := P
      outsideLocator := L
      cofactor := Cof
      quotient := Q
      multiplier := M
      agreementSet_large := hAcard
      witness_degree := hPnat
      agreement := hPagree
      not_explained := by simpa only [IRSProfile.baseCode] using hnotPair
      outsideLocator_eq := rfl
      cofactor_factor := by simpa only [L] using hCofFactor
      cofactor_ne_zero := hCofNe
      direct_factor := hQFactor
      multiplier_eq := rfl
      semilinear_identity := hMsemi }⟩

theorem Score6400FactoredWitness.witness_factor
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    {atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292)}
    {w : Score6400Field}
    (data : Score6400FactoredWitness e₀ e₁ atom w) :
    affinePolynomial atom.direct₀ atom.direct₁ w * data.multiplier =
      data.witnessPolynomial := by
  rw [data.multiplier_eq]
  calc
    affinePolynomial atom.direct₀ atom.direct₁ w *
        (data.outsideLocator * data.quotient) =
      data.outsideLocator *
        (affinePolynomial atom.direct₀ atom.direct₁ w * data.quotient) := by ring
    _ = data.outsideLocator * data.cofactor := by rw [data.direct_factor]
    _ = data.witnessPolynomial := data.cofactor_factor

theorem Score6400FactoredWitness.multiplier_ne_zero
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    {atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292)}
    {w : Score6400Field}
    (data : Score6400FactoredWitness e₀ e₁ atom w) :
    data.multiplier ≠ 0 := by
  have hQ : data.quotient ≠ 0 := by
    intro hzero
    have hfactor := data.direct_factor
    rw [hzero, mul_zero] at hfactor
    exact data.cofactor_ne_zero hfactor.symm
  have hL : data.outsideLocator ≠ 0 := by
    rw [data.outsideLocator_eq]
    exact outsideAgreementLocator_ne_zero IRSProfile.domain
      data.agreementSet (pairSupport e₀ e₁)
  rw [data.multiplier_eq]
  exact mul_ne_zero hL hQ

/-- Evaluation of a retained production multiplier satisfies the fixed
normalized Frobenius equation at every base-domain point. -/
theorem Score6400FactoredWitness.multiplier_eval_semilinear_eq
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    {atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292)}
    {w : Score6400Field}
    (data : Score6400FactoredWitness e₀ e₁ atom w)
    (normalized : NormalizedPolynomialPair
      atom.denominator atom.amplitudeMultiplier
      ((pairSupport e₀ e₁).card - 54292) atom.baseLoss)
    (x : Score6400Field) (hfixed : koalaSexticFrobenius x = x) :
    normalized.first.eval x *
        koalaSexticFrobenius (data.multiplier.eval x) =
      normalized.second.eval x * data.multiplier.eval x := by
  have hsemi : normalized.first *
        data.multiplier.map koalaSexticFrobenius.toRingHom =
      normalized.second * data.multiplier :=
    normalized.semilinear_identity atom.denominator
      atom.amplitudeMultiplier data.multiplier
      ((pairSupport e₀ e₁).card - 54292) atom.baseLoss
      koalaSexticFrobenius data.semilinear_identity
  have heval := congrArg
    (fun P : Score6400Field[X] ↦ P.eval x) hsemi
  rw [Polynomial.eval_mul, Polynomial.eval_mul,
    polynomial_map_eval_of_fixed koalaSexticFrobenius
      data.multiplier x hfixed] at heval
  exact heval

private theorem degree_lt_baseDimension_of_natDegree_le_owner
    {P : Score6400Field[X]} (hP : P.natDegree ≤ 131071) :
    P.degree < (IRSProfile.baseDimension : WithBot ℕ) := by
  by_cases hzero : P = 0
  · simp [hzero]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hzero]
    norm_num [IRSProfile.baseDimension]
    omega

/-- If the affine direct member has the generic direct degree, multiplying
either endpoint by `M` stays in the production RS message degree. -/
theorem Score6400FactoredWitness.direct_multiplier_degree
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    {atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292)}
    {w : Score6400Field}
    (data : Score6400FactoredWitness e₀ e₁ atom w)
    (hdegree : (affinePolynomial atom.direct₀ atom.direct₁ w).natDegree =
      max atom.direct₀.natDegree atom.direct₁.natDegree) :
    (atom.direct₀ * data.multiplier).natDegree ≤ 131071 ∧
      (atom.direct₁ * data.multiplier).natDegree ≤ 131071 := by
  have hCw : affinePolynomial atom.direct₀ atom.direct₁ w ≠ 0 := by
    intro hzero
    have hwitness := data.witness_factor e₀ e₁
    rw [hzero, zero_mul] at hwitness
    have hPne : data.witnessPolynomial ≠ 0 := by
      intro hPzero
      have hLne : data.outsideLocator ≠ 0 := by
        rw [data.outsideLocator_eq]
        exact outsideAgreementLocator_ne_zero IRSProfile.domain
          data.agreementSet (pairSupport e₀ e₁)
      have hproduct : data.outsideLocator * data.cofactor = 0 :=
        data.cofactor_factor.trans hPzero
      exact data.cofactor_ne_zero
        ((mul_eq_zero.mp hproduct).resolve_left hLne)
    exact hPne hwitness.symm
  have hM := data.multiplier_ne_zero e₀ e₁
  have hPdegree :
      (affinePolynomial atom.direct₀ atom.direct₁ w).natDegree +
          data.multiplier.natDegree = data.witnessPolynomial.natDegree := by
    calc
      _ = (affinePolynomial atom.direct₀ atom.direct₁ w *
          data.multiplier).natDegree :=
        (Polynomial.natDegree_mul hCw hM).symm
      _ = data.witnessPolynomial.natDegree :=
        congrArg Polynomial.natDegree data.witness_factor
  constructor
  · calc
      (atom.direct₀ * data.multiplier).natDegree ≤
          atom.direct₀.natDegree + data.multiplier.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ max atom.direct₀.natDegree atom.direct₁.natDegree +
          data.multiplier.natDegree := Nat.add_le_add_right (Nat.le_max_left _ _) _
      _ = data.witnessPolynomial.natDegree := by rw [← hdegree, hPdegree]
      _ ≤ 131071 := data.witness_degree
  · calc
      (atom.direct₁ * data.multiplier).natDegree ≤
          atom.direct₁.natDegree + data.multiplier.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ max atom.direct₀.natDegree atom.direct₁.natDegree +
          data.multiplier.natDegree := Nat.add_le_add_right (Nat.le_max_right _ _) _
      _ = data.witnessPolynomial.natDegree := by rw [← hdegree, hPdegree]
      _ ≤ 131071 := data.witness_degree

/-- A genuinely MCA-bad factored witness must contain a chosen agreement
coordinate where the normalized direct ratio is defective. -/
theorem Score6400FactoredWitness.exists_defect_owner
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    {atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292)}
    {w : Score6400Field}
    (data : Score6400FactoredWitness e₀ e₁ atom w)
    (hdegree : (affinePolynomial atom.direct₀ atom.direct₁ w).natDegree =
      max atom.direct₀.natDegree atom.direct₁.natDegree)
    (hCwDomain : ∀ i : Score6400Index,
      (affinePolynomial atom.direct₀ atom.direct₁ w).eval
        (IRSProfile.domain i) ≠ 0) :
    ∃ i ∈ data.agreementSet,
      IRSProfile.domain i ∈ atom.defect ∧
      data.multiplier.eval (IRSProfile.domain i) =
        (e₀ i + w * e₁ i) /
          (atom.direct₀.eval (IRSProfile.domain i) +
            w * atom.direct₁.eval (IRSProfile.domain i)) := by
  classical
  have hdegrees := data.direct_multiplier_degree e₀ e₁ hdegree
  let p₀ := atom.direct₀ * data.multiplier
  let p₁ := atom.direct₁ * data.multiplier
  have hp₀Code : ReedSolomon.evalOnPoints IRSProfile.domain p₀ ∈
      IRSProfile.baseCode := by
    change ReedSolomon.evalOnPoints IRSProfile.domain p₀ ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    exact degree_lt_baseDimension_of_natDegree_le_owner hdegrees.1
  have hp₁Code : ReedSolomon.evalOnPoints IRSProfile.domain p₁ ∈
      IRSProfile.baseCode := by
    change ReedSolomon.evalOnPoints IRSProfile.domain p₁ ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    exact degree_lt_baseDimension_of_natDegree_le_owner hdegrees.2
  have hcomponent : ∀ i ∈ data.agreementSet,
      IRSProfile.domain i ∉ atom.defect →
      (atom.direct₀ * data.multiplier).eval (IRSProfile.domain i) = e₀ i ∧
      (atom.direct₁ * data.multiplier).eval (IRSProfile.domain i) = e₁ i := by
    intro i hi hxNot
    let x := IRSProfile.domain i
    have hCw : atom.direct₀.eval x + w * atom.direct₁.eval x ≠ 0 := by
      simpa only [affinePolynomial_eval] using hCwDomain i
    have hfactorEval :
        (atom.direct₀.eval x + w * atom.direct₁.eval x) *
            data.multiplier.eval x = e₀ i + w * e₁ i := by
      have hP := data.agreement i hi
      rw [← data.witness_factor e₀ e₁, Polynomial.eval_mul,
        affinePolynomial_eval] at hP
      exact hP
    have hcross : atom.direct₀.eval x * e₁ i =
        atom.direct₁.eval x * e₀ i := by
      by_cases hiT : i ∈ pairSupport e₀ e₁
      · have hxS : x ∈ (pairSupport e₀ e₁).map IRSProfile.domain :=
          Finset.mem_map.mpr ⟨i, hiT, rfl⟩
        have hextended :
            atom.direct₀.eval x * score6400ErrorSource e₁ x =
              atom.direct₁.eval x * score6400ErrorSource e₀ x := by
          by_contra hneq
          apply hxNot
          simpa only [FrobeniusAmplitudeAtom.defect] using
            (Finset.mem_filter.mpr ⟨hxS, hneq⟩)
        simpa only [x, score6400ErrorSource_domain] using hextended
      · obtain ⟨h₀, h₁⟩ := pairSupport_values_eq_zero_of_not_mem e₀ e₁ hiT
        simp only [h₀, h₁, mul_zero]
    have hpair := direct_pair_eq_of_cross_and_affine
      (atom.direct₀.eval x) (atom.direct₁.eval x)
      (e₀ i) (e₁ i) w (data.multiplier.eval x)
      hCw hcross hfactorEval
    constructor
    · simpa only [Polynomial.eval_mul, x] using hpair.1
    · simpa only [Polynomial.eval_mul, x] using hpair.2
  have hexists : ∃ i ∈ data.agreementSet,
      IRSProfile.domain i ∈ atom.defect := by
    by_contra hnone
    push Not at hnone
    apply data.not_explained
    refine ⟨ReedSolomon.evalOnPoints IRSProfile.domain p₀, hp₀Code,
      ReedSolomon.evalOnPoints IRSProfile.domain p₁, hp₁Code, ?_, ?_⟩
    · intro i hi
      have hpair := hcomponent i hi (hnone i hi)
      change (atom.direct₀ * data.multiplier).eval
        (IRSProfile.domain i) = e₀ i
      exact hpair.1
    · intro i hi
      have hpair := hcomponent i hi (hnone i hi)
      change (atom.direct₁ * data.multiplier).eval
        (IRSProfile.domain i) = e₁ i
      exact hpair.2
  obtain ⟨i, hiA, hiDefect⟩ := hexists
  refine ⟨i, hiA, hiDefect, ?_⟩
  have hP := data.agreement i hiA
  rw [← data.witness_factor e₀ e₁, Polynomial.eval_mul,
    affinePolynomial_eval] at hP
  have hden : atom.direct₀.eval (IRSProfile.domain i) +
      w * atom.direct₁.eval (IRSProfile.domain i) ≠ 0 := by
    simpa only [affinePolynomial_eval] using hCwDomain i
  apply (eq_div_iff hden).2
  calc
    data.multiplier.eval (IRSProfile.domain i) *
        (atom.direct₀.eval (IRSProfile.domain i) +
          w * atom.direct₁.eval (IRSProfile.domain i)) =
      (atom.direct₀.eval (IRSProfile.domain i) +
          w * atom.direct₁.eval (IRSProfile.domain i)) *
        data.multiplier.eval (IRSProfile.domain i) := by ring
    _ = e₀ i + w * e₁ i := hP

end ProximityPrize.SubmissionLower
