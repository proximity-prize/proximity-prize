import ProximityPrize.SubmissionLower.ZGa2w7a
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qPQ4nYa
noncomputable section
open aR (ao)
open jA

open Rj (Flat Exp BU indexWeight topWeight J6 oH)
open qlc9qed (Bank ays bsz)
open ReedSolomon.HiddenDerivative MvPolynomial
open scoped Polynomial
open private Ky aob ec6 normalize eE1 dPj from ProximityPrize.SubmissionLower.S
private theorem flat_capped {b:Bank} {F:jK} (hF:Jn b.box F) (n:ℕ) :
    aob n F∈apR b:= by
  intro e he
  change e∈(aob n F).support at he
  have hc:=MvPolynomial.mem_support_iff.mp he
  rw [ec6] at hc
  have hs :e.some.optionElim n∈F.support :=
    MvPolynomial.mem_support_iff.mpr (fun h=>hc (by rw [h,Polynomial.coeff_zero]))
  have hb:=(le_weightedTotalDegree BU hs).trans hF.1
  have hj:=(le_weightedTotalDegree indexWeight hs).trans hF.2.1
  have ht:=(degreeOf_le_iff.mp hF.2.2.1) _ hs
  have hg (i:ℕ) : (e.some.optionElim i).weight BU=e.some.weight (fun _=>1) := by
    unfold BU
    rw [Finsupp.weight_optionElim,zero_mul,zero_add]
  have hi (i:ℕ) : (e.some.optionElim i).weight indexWeight=e.some.weight Fin.val := by
    unfold indexWeight
    rw [Finsupp.weight_optionElim,zero_mul,zero_add]
  change e.weight BU≤b.box.b∧e.weight indexWeight≤b.box.j∧e (some 2)≤b.box.t
  have heq :=Finsupp.optionElim_some e
  rw [hg] at hb
  rw [hi] at hj
  refine ⟨?_,?_,?_⟩
  · exact (congrArg (Finsupp.weight BU) heq).symm.le.trans ((hg (e none)).le.trans hb)
  · exact (congrArg (Finsupp.weight indexWeight) heq).symm.le.trans ((hi (e none)).le.trans hj)
  · simpa using ht
private theorem normalize_capped {b:Bank} {Q:Flat} (h:Q∈apR b) (x v :ao) :
    normalize x v Q∈apR b:= by
  have preserve (w:Option (Fin 3)→ℕ) (a :ℕ)
      (hQ : ∀ e∈Q.support,e.weight w≤a) :
      ∀ e∈(normalize x v Q).support,e.weight w≤a :=
    mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x v (mem_restrictWeightAtMost.mpr hQ))
  have htop (e :Exp) :e.weight topWeight=e (some 2) := by
    conv_lhs=>rw [← Finsupp.optionElim_some e]
    unfold topWeight
    rw [Finsupp.weight_optionElim,zero_mul,zero_add,Finsupp.weight_single_one_apply]
    simp
  intro e he
  exact ⟨preserve BU _ (fun t ht=>(h ht).1) e he,
    preserve indexWeight _ (fun t ht=>(h ht).2.1) e he,
    htop e ▸ preserve topWeight _ (fun t ht=>(htop t).symm ▸ (h ht).2.2) e he⟩
private theorem contact_of_origin_zero (b:Bank) (x v :ao) (F:jK)
    (h : ∀ n:ℕ,origin b (normalize x v (aob n F))=0) :F∈ays b.m x v := by
  apply (bsz b.m x v F).mpr
  intro e
  let E :=Polynomial.taylorEquiv x
  have hX:E (Polynomial.X-Polynomial.C x)=Polynomial.X:= by
    rw [map_sub]
    change Polynomial.taylor x Polynomial.X-Polynomial.taylor x (Polynomial.C x)= _
    simp
  rw [← map_dvd_iff E,map_pow,hX,Polynomial.X_pow_dvd_iff]
  intro i hi
  have hc:E ((aCk x v F).coeff e) =
      (Ky (J6 (normalize x v (aob (e none) F)))).coeff e.some := by
    rw [eE1,Finsupp.optionElim_some]
    rfl
  rw [hc]
  change ((optionEquivRight ao (Fin 3) _).coeff e.some).coeff i=0
  rw [optionEquivRight_coeff_coeff]
  have hz :=congrArg (fun Q:Flat=>Q.coeff (e.some.optionElim i)) (h (e none))
  change (weightedTruncation oH b.m
    (J6 (normalize x v (aob (e none) F)))).coeff (e.some.optionElim i)=0 at hz
  have hlt: (e.some.optionElim i).weight oH<b.m:= by
    rw [dPj]
    change i+3*e (some 0)<b.m
    omega
  rw [coeff_weightedTruncation] at hz
  simpa only [hlt,ite_true] using hz
end
end qPQ4nYa
