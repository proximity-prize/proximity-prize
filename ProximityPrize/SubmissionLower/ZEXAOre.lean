import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 12
namespace qHEUR1a
noncomputable section
open Polynomial Finset UniqueFactorizationMonoid




open cu (Equation)
open Qt (Qc)


open scoped Classical BigOperators


private theorem lift_factor {f :Equation} (hf :Irreducible f) :
    ∃ F:Raw,Irreducible F∧Associated (embed F) f := by
  obtain ⟨Q,a,ha,hQ,_,_,_⟩:=Y3.normalize f _ _ hf.ne_zero le_rfl
    ((Qc f _).mp le_rfl)
  have hu:IsUnit (Y3.constant a) :=(isUnit_iff_ne_zero.mpr ha).map _
  have haQ:Associated (embed Q) f :=hQ ▸ (associated_unit_mul_left _ _ hu)
  have hn:Q≠0:= by
    intro h
    rw [h,map_zero] at haQ
    exact hf.ne_zero ((associated_zero_iff_eq_zero _).mp haQ.symm)
  have find (N :Multiset Raw) (h:Associated (embed N.prod) f) :
      ∃ F∈N,Associated (embed F) f := by
    induction N using Multiset.induction_on with
    | empty =>
      rw [Multiset.prod_zero,map_one] at h
      exact (hf.not_isUnit (h.isUnit isUnit_one)).elim
    | cons F N ih =>
      rw [Multiset.prod_cons,map_mul] at h
      rcases (h.symm.irreducible hf).isUnit_or_isUnit rfl with huF | huN
      · obtain ⟨G,hG,ha⟩:=ih ((associated_unit_mul_right _ _ huF).trans h)
        exact ⟨G,Multiset.mem_cons_of_mem hG,ha⟩
      · exact ⟨F,Multiset.mem_cons_self _ _,(associated_mul_unit_right _ _ huN).trans h⟩
  let _:StrongNormalizationMonoid Raw:=UniqueFactorizationMonoid.strongNormalizationMonoid
  obtain ⟨F,hF,ha⟩:=find (normalizedFactors Q) (((prod_normalizedFactors hn).map embed).trans haQ)
  exact ⟨F,irreducible_of_normalized_factor F hF,ha⟩
end
end qHEUR1a
