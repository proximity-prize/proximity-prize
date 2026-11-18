/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Adapted from the frontier FactorWhole.lean. First-order squarefree pricing is due to Quang Dao and the ArkLib contributors (Apache 2.0). -/
import ProximityPrize.SubmissionLower.Mid6833JetArity
import ProximityPrize.SubmissionLower.Mid6833CappedSolutions
import ProximityPrize.SubmissionLower.Mid6833BiSource
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.DirectJetList

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.TailBound

namespace KoalaFactorResultant
open ReedSolomon.FirstOrder.Squarefree Frontier.SeedFreeze
open ProximityPrize.SubmissionLower RCN082 RCN136 RCN290 RCN293
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F

/-- Every second-order regular factor is charged once; the joint singular
locus is counted as a single first-order equation. -/
theorem capped_whole {p U s n A k V a b c τ : ℕ} [CharP F p]
    (hs : 1 ≤ s) (hsp : s < p) (hk : 2 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : max (k-1) ((2*s-1)*U) < ringChar F)
    (hτ : TaylorExponentSufficient 2 k τ) (hV : 2≤V) (ha : 0<a) (hb : 0<b)
    (hUa : s≤a) (hUb : U≤b) (hbmax : 1+τ*(U-1)≤b) (hamax : (τ*(V-2)+(k-1))/2≤a)
    (hc : 0<c) (hVc : V≤c) (hcmax : τ*(V-2)+(k-1)≤c)
    (Q : MvPolynomial (Fin 4) F) (hQ : Q ≠ 0) (hT : Q.degreeOf 2 ≤ s)
    (hU : weightedTotalDegree weights Q ≤ U)
    (hIndex : weightedTotalDegree jetIndexWt Q ≤ V)
    (x : Fin n ↪ F) (v : Fin n → F) (Γ : Finset (Polynomial F))
    (close : ∀ P ∈ Γ, P ∈ ReedSolomon.closePolynomialSet x v k A)
    (sol : ∀ P ∈ Γ, differentialSpecialization (rename twoSlot Q) P = 0) :
    (Γ.card : ℚ) ≤ (((n-k+1:ℕ):ℚ)/((A-k+1:ℕ):ℚ))^2 * (cappedBidegreeMixedVolume s U V a b c : ℕ) + ((firstOrderCurveFiberStageOne k ((2*s-1)*U) ((2*s-1)*U) (regularTaylorExponent (k-1)) : ℚ) *
       ((n-(k-1):ℕ):ℚ) / ((A-(k-1):ℕ):ℚ) + ordinaryDegreeEnvelope ((2*s-1)*U) ((2*s-1)*U)) := by
  classical
  let E := FractionRing (Polynomial F)
  let φ : Polynomial F →+* E := algebraMap _ _
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  obtain ⟨S,hnz,ht,hw,hsum,hcover⟩ :=
    eliminate_singular_and_account_factors (E:=E) p U s hs hsp Q hQ hT hU
  obtain ⟨B,hB⟩ := onePresentation S ht
  have hnB : B ≠ 0 := by rintro rfl; simp_all
  have hwB : jetTotalDegree B ≤ (2*s-1)*U := by rwa [← oneWeight, hB]
  let singular := Γ.filter (fun P => differentialSpecialization B P = 0)
  let regular (H : MvPolynomial (Fin 4) F) := Γ.filter (fun P =>
    0 < H.degreeOf 2 ∧ differentialSpecialization (rename twoSlot H) P = 0 ∧
      differentialSpecialization (separant (rename twoSlot H) 2) P ≠ 0)
  have covers : Γ ⊆ singular ∪ (activeFactors Q).biUnion regular := by
    intro P mem
    have zero : eval (coords φ P) (surfaceMap φ Q) = 0 := by
      rw [evaluation_two,sol P mem,map_zero]
    rcases hcover φ hφ _ zero with h | ⟨H,hH,_,pos,z,nz⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨mem,?_⟩
      rw [← hB,evaluation_two,evaluation_one] at h
      exact hφ (h.trans (map_zero φ).symm)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨H,hH,Finset.mem_filter.mpr ⟨mem,pos,?_,?_⟩⟩
      · rw [evaluation_two] at z
        exact hφ (z.trans (map_zero φ).symm)
      · rw [twoSeparant]
        rw [evaluation_two] at nz
        exact fun bad => nz (by rw [bad,map_zero])
  have keq : k-1+1=k := by omega
  have degEq : (↑(k-1) : WithBot ℕ)+1 = k := by exact_mod_cast keq
  have sr := finite_squarefree_agreement_solutions_card_le (D:=k-1) x v B hnB (by omega)
    (by omega) hAn le_rfl hwB ((jetDegree_le_total B 1).trans hwB) (Or.inr hchar) singular
    (fun _ mem => (Finset.mem_filter.mp mem).2) (by
      intro P mem
      have c := close P (Finset.mem_filter.mp mem).1
      exact ⟨degEq ▸ c.1, c.2⟩)
  rw [keq] at sr
  have sh : (singular.card : ℚ) ≤
    ((firstOrderCurveFiberStageOne k ((2*s-1)*U) ((2*s-1)*U) (regularTaylorExponent (k-1)) : ℚ) *
       ((n-(k-1):ℕ):ℚ) / ((A-(k-1):ℕ):ℚ) + ordinaryDegreeEnvelope ((2*s-1)*U) ((2*s-1)*U)) := by
    apply (Rat.cast_le (K:=ℝ)).mp
    push_cast
    exact sr
  have bin : ∀ r, r ≤ 2 → ∀ i, r < i → i < k → (i.choose r : F) ≠ 0 := by
    intro r _ i hir hik
    have hv := natCast_choose_ne_zero_of_ringChar (F:=F) (D:=k-1) (s:=r)
      (Or.inr ((Nat.le_max_left _ _).trans_lt hchar)) (i-r) (by omega) (by omega)
    simpa only [Nat.sub_add_cancel hir.le] using hv
  let inc := (((n-k+1:ℕ):ℚ)/((A-k+1:ℕ):ℚ))^2
  let deg (H : MvPolynomial (Fin 4) F) := weightedTotalDegree weights H
  let last (H : MvPolynomial (Fin 4) F) := H.degreeOf 2
  have lastsum : (∑ H ∈ activeFactors Q, last H) ≤ s := by
    have h := sum_weighted_degrees_le_of_prod_dvd (Pi.single 2 1) (activeFactors Q) id Q hQ
      (activeFactors_product_dvd Q hQ)
    simpa only [weightedTotalDegree_piSingle,id_eq] using h.trans (by simpa using hT)
  have idxsum := (sum_weighted_degrees_le_of_prod_dvd jetIndexWt (activeFactors Q) id Q hQ
    (activeFactors_product_dvd Q hQ)).trans hIndex
  let idg (H : MvPolynomial (Fin 4) F) := weightedTotalDegree jetIndexWt H
  have reg (H : MvPolynomial (Fin 4) F) (hh : H∈activeFactors Q) : ((regular H).card : ℚ) ≤
      inc * (cappedBidegreeMixedVolume (last H) (deg H) (idg H) a b c : ℕ) := by
    have dcap : deg H ≤ U := (Finset.single_le_sum (f:=deg) (fun _ _ => Nat.zero_le _) hh).trans hsum
    have lcap : last H ≤ s := (Finset.single_le_sum (f:=last) (fun _ _ => Nat.zero_le _) hh).trans lastsum
    have icap : weightedTotalDegree jetIndexWt H ≤ V :=
      (Finset.single_le_sum (f:=fun H => weightedTotalDegree jetIndexWt H) (fun _ _ => Nat.zero_le _) hh).trans idxsum
    have actual : weightedTotalDegree (indexWeight 3) (rename twoSlot H) ≤ V := by
      rw [weightedTotalDegree_rename_of_injective twoSlot_injective]
      rw [show indexWeight 3 ∘ twoSlot = jetIndexWt by funext i; fin_cases i <;> rfl]
      exact icap
    have locald : jetDegree (rename twoSlot H) 1 ≤ idg H := by
      apply (degreeOf_le_weightedTotalDegree (indexWeight 3) (some 1) (by decide) _).trans
      rw [weightedTotalDegree_rename_of_injective twoSlot_injective]
      rw [show indexWeight 3 ∘ twoSlot = jetIndexWt by funext i; fin_cases i <;> rfl]
    have regb := KoalaBiJet.capped_solutions (rename twoSlot H) hk hkA hτ hV ha hb hc (icap.trans hVc) locald actual
      (twoWeight H).le (twoDegree H).le (dcap.trans hUb) (lcap.trans hUa)
      (by
        rw [rationalTaylorCutDegreeBound,twoWeight]
        exact (Nat.add_le_add_left (Nat.mul_le_mul_left τ (Nat.sub_le_sub_right dcap 1)) _).trans hbmax)
      hamax hcmax x v (regular H)
      (fun P mem => (close P (Finset.mem_filter.mp mem).1).1)
      (fun P mem => (Finset.mem_filter.mp mem).2.2.1)
      (fun P mem => (Finset.mem_filter.mp mem).2.2.2)
      (bin 2 le_rfl)
      (fun P mem => (close P (Finset.mem_filter.mp mem).1).2)
    rw [mul_comm]
    exact regb
  have inc0 : 0 ≤ inc := by dsimp [inc]; positivity
  have pooled : (∑ H ∈ activeFactors Q, ((regular H).card : ℚ)) ≤
      inc*(cappedBidegreeMixedVolume s U V a b c : ℕ) := by
    calc
      _ ≤ ∑ H ∈ activeFactors Q, inc*(cappedBidegreeMixedVolume (last H) (deg H) (idg H) a b c : ℕ) := Finset.sum_le_sum reg
      _ = inc*((∑ H ∈ activeFactors Q, cappedBidegreeMixedVolume (last H) (deg H) (idg H) a b c) : ℕ) := by
        rw [Nat.cast_sum,Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ inc0
        apply Nat.cast_le.mpr
        simp only [cappedBidegreeMixedVolume,cappedDegreeMixedVolume,Nat.mul_add,Finset.sum_add_distrib,
          ← Finset.sum_mul,← Finset.mul_sum,Nat.mul_assoc]
        gcongr
        exact idxsum
  have card := (Finset.card_le_card covers).trans (Finset.card_union_le _ _)
  have unionB := Finset.card_biUnion_le (s:=activeFactors Q) (t:=regular)
  have all : Γ.card ≤ singular.card + ∑ H ∈ activeFactors Q, (regular H).card :=
    card.trans (Nat.add_le_add_left unionB _)
  have rat : (Γ.card : ℚ) ≤ singular.card + ∑ H ∈ activeFactors Q, ((regular H).card : ℚ) := by
    exact_mod_cast all
  simpa [inc,add_comm] using rat.trans (add_le_add sh pooled)
#print axioms capped_whole
end
end KoalaFactorResultant
