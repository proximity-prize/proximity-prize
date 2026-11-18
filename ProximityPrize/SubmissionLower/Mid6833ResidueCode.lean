/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833LinearKernel
namespace Frontier.LinearKernel
open Polynomial Finset
open scoped Polynomial Classical
noncomputable section
variable {K I : Type*} [Field K]

/-- Exact reformulation of the rational-slope family on fixed evaluation nodes.
One symbol g controls a prescribed constant residue; the same supports work both ways. -/
theorem residue_iff (σ : K →+* K) (x : I ↪ K) (word : I → K) (D : K[X])
    (d w : ℕ) (g : K) (S : Finset I) (fixed : ∀ i∈S, σ (x i)=x i)
    (base : ∀ i∈S, σ (word i)=word i) (degree : D.natDegree=d) (hn : D≠0)
    (nonzero : ∀ i∈S, D.eval (x i)≠0) (enough : w+d<S.card) :
    (∃ P : K[X], P.natDegree≤w ∧ ∀ i∈S, P.eval (x i)=(word i+g)/D.eval (x i)) ↔
    (∃ T : K[X], T.natDegree≤w+d ∧ T.map σ=T ∧ D ∣ T+C g ∧ ∀ i∈S, T.eval (x i)=word i) := by
  constructor
  · rintro ⟨P,deg,fit⟩
    let T := D*P-C g
    have dT : T.natDegree≤w+d := by
      apply (natDegree_sub_le ..).trans
      have dp : (D*P).natDegree ≤ D.natDegree+P.natDegree := natDegree_mul_le
      rw [natDegree_C]
      omega
    have good (i : I) (hi : i∈S) : T.eval (x i)=word i := by
      simp only [T,eval_sub,eval_mul,eval_C,fit i hi]
      field_simp [nonzero i hi]
      <;> ring
    refine ⟨T,dT,?_,⟨P,by simp [T]⟩,good⟩
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun i : S => x i.val) (x.injective.comp Subtype.val_injective)
    · intro i
      have e := eval_map_apply (p:=T) σ (x i.val)
      rw [fixed i.val i.property,good i.val i.property, base i.val i.property] at e
      rw [good i.val i.property]
      exact e
    · rw [Fintype.card_coe]
      have m := natDegree_map_le (p:=T) (f:=σ)
      omega
  · rintro ⟨T,dt,_,⟨P,quot⟩,fit⟩
    refine ⟨P,?_,?_⟩
    · by_cases hp : P=0
      · simp [hp]
      have md : (T+C g).natDegree ≤ max T.natDegree (C g).natDegree := natDegree_add_le _ _
      rw [quot,natDegree_mul hn hp,degree,natDegree_C] at md
      omega
    · intro i hi
      apply (eq_div_iff (nonzero i hi)).mpr
      have v := congrArg (Polynomial.eval (x i)) quot
      simp only [eval_add,eval_C,eval_mul,fit i hi] at v
      linear_combination -v

theorem conjugate_residue (σ : K →+* K) (D T : K[X]) (g : K)
    (fixed : T.map σ=T) (dv : D∣T+C g) : D.map σ ∣ T+C (σ g) := by
  have h := map_dvd (Polynomial.mapRingHom σ) dv
  change D.map σ ∣ (T+C g).map σ at h
  simpa [Polynomial.map_add,Polynomial.map_C,fixed] using h

#print axioms residue_iff
#print axioms conjugate_residue
end
end Frontier.LinearKernel
