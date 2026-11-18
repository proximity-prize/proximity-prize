/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833Compact180589
import ProximityPrize.SubmissionLower.Mid6833Compact180100
import ProximityPrize.SubmissionLower.Mid6833Compact179739
import ArkLib.Data.Polynomial.Differential.JetDegree
import Mathlib.FieldTheory.Finite.Polynomial
import CompPoly.Fields.KoalaBear.Ext6

namespace Frontier.SeedFreeze
open MvPolynomial PolynomialDifferential
open ProximityPrize.SubmissionLower
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F]
abbrev slot : Fin 4 → JetVariable 2 := ![none,some 0,some 2,some 1]
abbrev wt : Fin 4 → ℕ := ![0,1,1,1]
def assign (z : F) : Fin 5 → MvPolynomial (Fin 4) F := ![MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 1,MvPolynomial.X 3,MvPolynomial.C z]
def freeze (z : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 4) F := aeval (assign z)

theorem reconstruct (v : Fin 5 → F) (P : MvPolynomial (Fin 5) F) :
    eval ![v 0,v 2,v 1,v 3] (freeze (v 4) P) = eval v P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [freeze]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    simp only [map_mul,hp,freeze,aeval_X,eval_X]
    congr 1
    fin_cases i <;> simp [assign]

private theorem singleWeight (w : Fin 4 → ℕ) (i : Fin 4) :
    weightedTotalDegree w (MvPolynomial.X i : MvPolynomial (Fin 4) F) = w i := by
  change weightedTotalDegree w (monomial (Finsupp.single i 1) (1 : F)) = _
  rw [weightedTotalDegree_monomial _ _ _ one_ne_zero, Finsupp.weight_single]
  simp

theorem preserve (z : F) (P : MvPolynomial (Fin 5) F) (s U : ℕ)
    (caps : ∀ e ∈ P.support, e 1≤s ∧ e 1+e 2+e 3≤U) :
    (freeze z P).degreeOf 2 ≤ s ∧ weightedTotalDegree wt (freeze z P) ≤ U := by
  constructor
  · rw [← weightedTotalDegree_piSingle]
    apply le_trans (weightedTotalDegree_aeval_le_of_le (Pi.single 1 1) (Pi.single 2 1) (assign z) P ?_)
    · rw [weightedTotalDegree_piSingle,degreeOf_le_iff]
      exact fun e he => (caps e he).1
    · intro i
      fin_cases i <;> simp [assign,weightedTotalDegree_piSingle,degreeOf_X,Pi.single_apply]
  · let w : Fin 5 → ℕ := ![0,1,1,1,0]
    apply le_trans (weightedTotalDegree_aeval_le_of_le w wt (assign z) P ?_)
    · rw [weightedTotalDegree, Finset.sup_le_iff]
      intro e he
      rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)]
      simpa [w,Fin.sum_univ_succ, nsmul_eq_mul,add_assoc] using (caps e he).2
    · intro i
      fin_cases i <;> simp [assign,w,wt,singleWeight]

theorem specializes (z : F) (f : Polynomial F) (P : MvPolynomial (Fin 5) F) :
    differentialSpecialization (rename slot (freeze z P)) f = SecondJetSpecialize.specialize f z P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [freeze,differentialSpecialization,differentialSpecializationHom,SecondJetSpecialize.specialize]
  | add p q hp hq => simpa only [map_add,differentialSpecialization] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    change (differentialSpecializationHom f) _ = _ at hp ⊢
    simp only [map_mul,hp]
    congr 1
    fin_cases i <;> simp [freeze,assign,slot,differentialSpecializationHom,SecondJetSpecialize.specialize]

theorem get [Fintype F] {N : Type*} [Fintype N] (nodes : N ↪ F) (u : N → F) (A s U : ℕ)
    (P : MvPolynomial (Fin 5) F) (hp : P≠0)
    (hc : ∀ e ∈ P.support, e 1≤s ∧ e 1+e 2+e 3≤U)
    (sizes : ∀ e ∈ P.support, ∀ i, e i < Fintype.card F)
    (hv : ∀ f : Polynomial F, f.natDegree≤131071 → ∀ z : F, ∀ S : Finset N, A≤S.card →
      (∀ i∈S, f.eval (nodes i)=u i) → SecondJetSpecialize.specialize f z P=0) :
    ∃ Q : MvPolynomial (Fin 4) F, Q≠0 ∧ Q.degreeOf 2 ≤ s ∧ weightedTotalDegree wt Q ≤ U ∧
      ∀ f : Polynomial F, f.natDegree≤131071 → ∀ S : Finset N, A≤S.card →
      (∀ i∈S, f.eval (nodes i)=u i) → differentialSpecialization (rename slot Q) f=0 := by
  classical
  obtain ⟨v,hv0⟩ : ∃ v, eval v P ≠ 0 := by
    by_contra! h
    apply hp
    apply MvPolynomial.eq_zero_of_eval_eq_zero (Fin 5) F P h
    rw [MvPolynomial.mem_restrictDegree]
    exact fun e he i => Nat.le_sub_one_of_lt (sizes e he i)
  refine ⟨freeze (v 4) P, ?_, (preserve _ _ _ _ hc).1,(preserve _ _ _ _ hc).2,?_⟩
  · intro h
    exact hv0 (by rw [← reconstruct v P,h,map_zero])
  · intro f hf S hs hi
    rw [specializes]
    exact hv f hf (v 4) S hs hi

theorem scalar180589 {N : Type*} [Fintype N] (hn : Fintype.card N≤262144)
    (nodes : N ↪ KoalaBear.Ext6) (u : N → KoalaBear.Ext6) :
    ∃ Q : MvPolynomial (Fin 4) KoalaBear.Ext6, Q≠0 ∧ Q.degreeOf 2 ≤ 7 ∧ weightedTotalDegree wt Q ≤ 46 ∧
      ∀ f : Polynomial KoalaBear.Ext6, f.natDegree≤131071 → ∀ S : Finset N, 180589≤S.card →
      (∀ i∈S, f.eval (nodes i)=u i) → differentialSpecialization (rename slot Q) f=0 := by
  obtain ⟨P,hp,hcaps,-,hvan⟩ := Compact180589.exists_profile_interpolant 0 hn nodes u (fun _ => 0)
  apply get nodes u 180589 7 46 P hp
  · intro e he
    exact ⟨(hcaps e he).2.1,(hcaps e he).2.2.1⟩
  · intro e he i
    obtain ⟨_,_,_,ht,hx⟩ := hcaps e he
    change e 1+e 2+e 3+e 4 ≤ 19893 at ht
    change e 0+131071*e 2+131070*e 3+131069*e 1 < _ at hx
    have hcut : Compact180589.profileCutoff (Compact180589.jetProfile 0) (e 1) ≤ 180589*34 := Nat.sub_le _ _
    rw [KoalaBear.card_ext6]
    change e i < (2130706433 : ℕ)^6
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> norm_num1 <;> omega
  · intro f hf z S hs hi
    simpa using hvan 0 (Nat.zero_le _) f hf z S hs (by simpa using hi)

#print axioms scalar180589

theorem scalar180100 {N : Type*} [Fintype N] (hn : Fintype.card N≤262144)
    (nodes : N ↪ KoalaBear.Ext6) (u : N → KoalaBear.Ext6) :
    ∃ Q : MvPolynomial (Fin 4) KoalaBear.Ext6, Q≠0 ∧ Q.degreeOf 2 ≤ 9 ∧ weightedTotalDegree wt Q ≤ 62 ∧
      ∀ f : Polynomial KoalaBear.Ext6, f.natDegree≤131071 → ∀ S : Finset N, 180100≤S.card →
      (∀ i∈S, f.eval (nodes i)=u i) → differentialSpecialization (rename slot Q) f=0 := by
  obtain ⟨P,hp,hcaps,-,hvan⟩ := Compact180100.exists_profile_interpolant 0 hn nodes u (fun _ => 0)
  apply get nodes u 180100 9 62 P hp
  · intro e he
    exact ⟨(hcaps e he).2.1,(hcaps e he).2.2.1⟩
  · intro e he i
    obtain ⟨_,_,_,ht,hx⟩ := hcaps e he
    change e 1+e 2+e 3+e 4 ≤ 29010 at ht
    change e 0+131071*e 2+131070*e 3+131069*e 1 < _ at hx
    have hcut : Compact180100.profileCutoff (Compact180100.jetProfile 0) (e 1) ≤ 180100*46 := Nat.sub_le _ _
    rw [KoalaBear.card_ext6]
    change e i < (2130706433 : ℕ)^6
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> norm_num1 <;> omega
  · intro f hf z S hs hi
    simpa using hvan 0 (Nat.zero_le _) f hf z S hs (by simpa using hi)

#print axioms scalar180100

theorem scalar179739 {N : Type*} [Fintype N] (hn : Fintype.card N≤262144)
    (nodes : N ↪ KoalaBear.Ext6) (u : N → KoalaBear.Ext6) :
    ∃ Q : MvPolynomial (Fin 4) KoalaBear.Ext6, Q≠0 ∧ Q.degreeOf 2 ≤ 12 ∧ weightedTotalDegree wt Q ≤ 82 ∧
      ∀ f : Polynomial KoalaBear.Ext6, f.natDegree≤131071 → ∀ S : Finset N, 179739≤S.card →
      (∀ i∈S, f.eval (nodes i)=u i) → differentialSpecialization (rename slot Q) f=0 := by
  obtain ⟨P,hp,hcaps,-,hvan⟩ := Compact179739.exists_profile_interpolant 0 hn nodes u (fun _ => 0)
  apply get nodes u 179739 12 82 P hp
  · intro e he
    exact ⟨(hcaps e he).2.1,(hcaps e he).2.2.1⟩
  · intro e he i
    obtain ⟨_,_,_,ht,hx⟩ := hcaps e he
    change e 1+e 2+e 3+e 4 ≤ 610923 at ht
    change e 0+131071*e 2+131070*e 3+131069*e 1 < _ at hx
    have hcut : Compact179739.profileCutoff (Compact179739.jetProfile 0) (e 1) ≤ 179739*61 := Nat.sub_le _ _
    rw [KoalaBear.card_ext6]
    change e i < (2130706433 : ℕ)^6
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> norm_num1 <;> omega
  · intro f hf z S hs hi
    simpa using hvan 0 (Nat.zero_le _) f hf z S hs (by simpa using hi)

#print axioms scalar179739
end
end Frontier.SeedFreeze
