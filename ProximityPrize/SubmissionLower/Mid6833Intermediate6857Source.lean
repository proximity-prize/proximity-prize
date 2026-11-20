/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Extend the frontier SeedFreeze source with its original index cap. The interpolation method credits BitWonka and Lucieno. -/
import ProximityPrize.SubmissionLower.Mid6833BiSource
import ProximityPrize.SubmissionLower.Mid6833Intermediate6857Profile
namespace Frontier.SeedFreeze
open MvPolynomial PolynomialDifferential ProximityPrize.SubmissionLower
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F]

private theorem singleWeightHigh (w : Fin 4 → ℕ) (i : Fin 4) :
    weightedTotalDegree w (MvPolynomial.X i : MvPolynomial (Fin 4) F) = w i := by
  change weightedTotalDegree w (monomial (Finsupp.single i 1) (1 : F)) = _
  rw [weightedTotalDegree_monomial _ _ _ one_ne_zero, Finsupp.weight_single]
  simp


private theorem freezeIndexHigh (z:F) (P : MvPolynomial (Fin 5) F)
    (cap : ∀e∈P.support, 2*e 1+e 3 ≤ 12) :
    (freeze z P).weightedTotalDegree jetIndexWt ≤ 12 := by
  let w : Fin 5 → ℕ := ![0,2,0,1,0]
  apply le_trans (weightedTotalDegree_aeval_le_of_le w jetIndexWt (assign z) P ?_)
  · rw [weightedTotalDegree,Finset.sup_le_iff]
    intro e he
    rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)]
    simpa [w,Fin.sum_univ_succ,nsmul_eq_mul,Nat.mul_comm] using cap e he
  · intro i
    fin_cases i <;> simp [assign,w,jetIndexWt,singleWeightHigh]
private theorem getIntermediate6857 [Fintype F] {N : Type*} [Fintype N] (nodes : N ↪ F) (u : N → F) (A s U : ℕ)
    (P : MvPolynomial (Fin 5) F) (hp : P≠0)
    (hc : ∀ e ∈ P.support, e 1≤s ∧ e 1+e 2+e 3≤U)
    (indexcap : ∀ e ∈ P.support, 2*e 1+e 3 ≤ 12)
    (sizes : ∀ e ∈ P.support, ∀ i, e i < Fintype.card F)
    (hv : ∀ f : Polynomial F, f.natDegree≤131071 → ∀ z : F, ∀ S : Finset N, A≤S.card →
      (∀ i∈S, f.eval (nodes i)=u i) → SecondJetSpecialize.specialize f z P=0) :
    ∃ Q : MvPolynomial (Fin 4) F, Q≠0 ∧ Q.degreeOf 2 ≤ s ∧ weightedTotalDegree wt Q ≤ U ∧ weightedTotalDegree jetIndexWt Q ≤ 12 ∧
      ∀ f : Polynomial F, f.natDegree≤131071 → ∀ S : Finset N, A≤S.card →
      (∀ i∈S, f.eval (nodes i)=u i) → differentialSpecialization (rename slot Q) f=0 := by
  classical
  obtain ⟨v,hv0⟩ : ∃ v, eval v P ≠ 0 := by
    by_contra! h
    apply hp
    apply MvPolynomial.eq_zero_of_eval_eq_zero (Fin 5) F P h
    rw [MvPolynomial.mem_restrictDegree]
    exact fun e he i => Nat.le_sub_one_of_lt (sizes e he i)
  refine ⟨freeze (v 4) P, ?_, (preserve _ _ _ _ hc).1,(preserve _ _ _ _ hc).2,?_,?_⟩
  · intro h
    exact hv0 (by rw [← reconstruct v P,h,map_zero])
  · exact freezeIndexHigh _ P indexcap
  · intro f hf S hs hi
    rw [specializes]
    exact hv f hf (v 4) S hs hi

theorem intermediate6857_index {N : Type*} [Fintype N] (hn : Fintype.card N≤262144)
    (nodes : N ↪ KoalaBear.Ext6) (u : N → KoalaBear.Ext6) :
    ∃ Q : MvPolynomial (Fin 4) KoalaBear.Ext6, Q≠0 ∧ Q.degreeOf 2 ≤ 5 ∧ weightedTotalDegree wt Q ≤ 41 ∧ weightedTotalDegree jetIndexWt Q ≤ 12 ∧
      ∀ f : Polynomial KoalaBear.Ext6, f.natDegree≤131071 → ∀ S : Finset N, 180833≤S.card →
      (∀ i∈S, f.eval (nodes i)=u i) → differentialSpecialization (rename slot Q) f=0 := by
  obtain ⟨P,hp,hcaps,-,hvan⟩ := Intermediate6857Profile.exists_profile_interpolant 0 hn nodes u (fun _ => 0)
  apply getIntermediate6857 nodes u 180833 5 41 P hp
  · intro e he
    exact ⟨(hcaps e he).2.1,(hcaps e he).2.2.1⟩
  · exact fun e he => (hcaps e he).1
  · intro e he i
    obtain ⟨_,_,_,ht,hx⟩ := hcaps e he
    change e 1+e 2+e 3+e 4 ≤ 102467 at ht
    change e 0+131071*e 2+131070*e 3+131069*e 1 < _ at hx
    have hcut : Intermediate6857Profile.profileCutoff (Intermediate6857Profile.jetProfile 0) (e 1) ≤ 180833*30 := Nat.sub_le _ _
    rw [KoalaBear.card_ext6]
    change e i < (2130706433 : ℕ)^6
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> norm_num1 <;> omega
  · intro f hf z S hs hi
    simpa using hvan 0 (Nat.zero_le _) f hf z S hs (by simpa using hi)

#print axioms intermediate6857_index
end
end Frontier.SeedFreeze
