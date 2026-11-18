/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833LinearKernel
import ProximityPrize.Benchmark.TargetLower
import Mathlib.FieldTheory.Finite.GaloisField
namespace Frontier.LinearKernel.Saturation
open Polynomial Finset KoalaBear CompPoly.Extension
open scoped Polynomial Classical BigOperators
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
abbrev F := KoalaBear.Field
abbrev K := KoalaBear.Ext6

def σ : K →+* K := (FiniteField.frobeniusAlgHom F K).toRingHom

def rep (g : K) : K[X] :=
  ∑ i : Fin 6, C (algebraMap F K (Ext.coeff g i))*(Polynomial.X : K[X])^(i:ℕ)

theorem rep_value (g : K) : (rep g).eval ext6Gen=g := by
  apply Ext.toQuot_injective
  simp only [rep,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,Ext.toQuot_sum,Ext.toQuot_mul,
    Ext.toQuot_pow,Ext.algebraMap_eq_ofBase,Ext.toQuot_ofBase, ext6Gen,Ext.toQuot_gen]
  rfl

theorem rep_deg (g : K) : (rep g).natDegree≤5 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le ..).trans ((natDegree_X_pow_le _).trans (by have := i.isLt; omega))

theorem rep_fixed (g : K) : (rep g).map σ=rep g := by
  simp only [rep,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X]
  apply Finset.sum_congr rfl
  intro i _
  rw [show σ (algebraMap F K (Ext.coeff g i)) = _ from (FiniteField.frobeniusAlgHom F K).commutes _]

def D (d : ℕ) : K[X] := (Polynomial.X : K[X])^d-C ext6Gen

/-- Every challenge admits a low-degree formal polynomial solution for a proper
rational slope of degree d. These witnesses may fall short of enough agreements. -/
theorem all_seeds (d : ℕ) (hd : 0<d) (g : K) :
    ∃ P : K[X], P.natDegree ≤ 5*d ∧
      D d*P - (D d).map σ * P.map σ = C g - C (σ g) ∧
      ∀ x : K, (D d).eval x * P.eval x = g - (rep g).eval (x^d) := by
  have dv : (Polynomial.X : K[X])-C ext6Gen ∣ C g - rep g := dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot,rep_value])
  obtain ⟨H,hH⟩ := dv
  let P := H.comp ((Polynomial.X : K[X])^d)
  have prod : D d*P = C g-(rep g).comp ((Polynomial.X : K[X])^d) := by
    have h := congrArg (fun q : K[X] => q.comp ((Polynomial.X : K[X])^d)) hH
    simpa [P,D,sub_comp,mul_comp] using h.symm
  have neD : D d ≠ 0 := by
    have high : (C ext6Gen).natDegree < ((Polynomial.X : K[X])^d : K[X]).natDegree := by simp [hd]
    exact sub_ne_zero.mpr (fun h => (ne_of_gt high) (congrArg natDegree h))
  have dg : (rep g).natDegree ≤ 5 := rep_deg g
  have diff : (C g-(rep g).comp ((Polynomial.X : K[X])^d)).natDegree ≤ 5*d := by
    apply (natDegree_sub_le ..).trans
    rw [natDegree_C, max_eq_right (Nat.zero_le _)]
    exact (natDegree_comp_le ..).trans (Nat.mul_le_mul dg (natDegree_X_pow_le _))
  have pdeg : P.natDegree ≤ 5*d := by
    by_cases hp : P=0
    · simp [hp]
    · rw [← prod,natDegree_mul neD hp] at diff
      omega
  refine ⟨P,pdeg,?_,?_⟩
  · have conjugate := congrArg (Polynomial.map σ) prod
    simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_C,Polynomial.map_comp,
      Polynomial.map_pow,Polynomial.map_X,rep_fixed] at conjugate
    rw [prod,conjugate]
    ring
  · intro x
    simpa [eval_mul,eval_sub,eval_C,eval_comp] using congrArg (Polynomial.eval x) prod

theorem actual_obstruction :
  ∀ g : K, ∃ P : K[X], P.natDegree≤131071 ∧
    D 9554*P-(D 9554).map σ * P.map σ=C g-C (σ g) := by
  intro g
  obtain ⟨P,deg,row,_⟩ := all_seeds 9554 (by decide) g
  exact ⟨P,deg.trans (by decide),row⟩
private theorem gen_not_base (c : F) : algebraMap F K c ≠ ext6Gen := by
  intro eq
  let n : Fin ext6Params.d := ⟨1,by decide⟩
  have ce := congrArg (fun z : K => Ext.coeff z n) eq
  change Ext.coeff (Ext.ofBase c : K) n = Ext.coeff (Ext.gen : K) n at ce
  rw [Ext.coeff_ofBase,Ext.coeff_gen] at ce
  simp [n] at ce

open ProximityPrize.Benchmark.IRSProfile in
theorem actual_domain_nonzero (i : Index) : (D 9554).eval (domain i) ≠ 0 := by
  simp only [D,eval_sub,eval_pow,eval_X,eval_C,sub_ne_zero]
  change (algebraMap F K (baseNttDomain.node i))^9554 ≠ ext6Gen
  rw [← map_pow]
  exact gen_not_base _

open ProximityPrize.Benchmark.IRSProfile in
theorem actual_agreement_iff (g : K) :
  (∃ (P : K[X]) (S : Finset Index), P.natDegree≤131071 ∧ 179740≤S.card ∧
    ∀ i∈S, P.eval (domain i)=g/(D 9554).eval (domain i)) ↔ g=0 := by
  constructor
  · rintro ⟨P,S,deg,ag,fit⟩
    have dd : (D 9554).natDegree=9554 := by
      unfold D
      rw [natDegree_sub_eq_left_of_natDegree_lt (by simp : (C ext6Gen).natDegree < ((Polynomial.X:K[X])^9554).natDegree),natDegree_X_pow]
    have id : D 9554*P=C g := by
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun i : S => domain i.val) (domain.injective.comp Subtype.val_injective)
      · intro i
        simpa [eval_mul,fit i.val i.property,eval_C] using
          (show (D 9554).eval (domain i.val)*(g/(D 9554).eval (domain i.val))=g by field_simp [actual_domain_nonzero])
      · rw [Fintype.card_coe,natDegree_C]
        have d : (D 9554*P).natDegree ≤ (D 9554).natDegree+P.natDegree := natDegree_mul_le
        omega
    by_contra nz
    have hn : P≠0 := by intro e; rw [e,mul_zero] at id; exact nz (C_eq_zero.mp id.symm)
    have dn : D 9554≠0 := fun e => by rw [e,natDegree_zero] at dd; contradiction
    have di := congrArg natDegree id
    rw [natDegree_mul dn hn,dd,natDegree_C] at di
    omega
  · rintro rfl
    exact ⟨0,univ,by simp,by simp [Index],by simp⟩
#print axioms actual_agreement_iff
#print axioms all_seeds
#print axioms actual_obstruction
end
end Frontier.LinearKernel.Saturation
