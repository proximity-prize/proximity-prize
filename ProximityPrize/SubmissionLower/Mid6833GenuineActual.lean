/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833GenuineLinearData
import ProximityPrize.SubmissionLower.Mid6833Global
import ProximityPrize.SubmissionLower.Mid6833LinearKernel
namespace ProximityPrize.SubmissionLower.GenuineLinearData
open Polynomial Finset Koala6831Comparison K6969Global
open Koala6831BenchmarkPrimitive (Received SelectionMap badNodes agreementSet eval_eq_of_mem_agreementSet)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K I : Type} [Field K] [Fintype I]

theorem actual_coefficients (x : I ↪ K) (σ : K →+* K) (fixed : ∀ i, σ (x i)=x i)
    (card : Fintype.card I=262144) (U : Received K I) (E : Finset K) (P : SelectionMap K)
    (q : SymbolicRow (SeedRing K)) (h : RetainedComparison x σ U E P q) (linear : combinedDegree q≤1) :
    let δ := primitiveExcess 131071 q
    ∃ a b B L R : K[X], a≠0 ∧ b≠0 ∧ a.natDegree≤δ ∧ b.natDegree≤δ ∧
      L.natDegree≤131071+δ ∧ a.map σ*R=b*L.map σ ∧
      (∀ g∈E, a*P g+b*(P g).map σ=B+C g*L+C (σ g)*R) ∧
      ∀ g∈E, ∀ i∈agreementSet x U P g, (a.eval (x i)≠0 ∨ b.eval (x i)≠0) ∧
        a.eval (x i)*U 1 i=L.eval (x i) ∧ b.eval (x i)*σ (U 1 i)=R.eval (x i) := by
  let δ := primitiveExcess 131071 q
  let S := univ \ badNodes x σ U q
  have cap : δ + (badNodes x σ U q).card ≤ 33735 := h.excess_bad
  have sz : S.card=262144-(badNodes x σ U q).card := by
    simp only [S,card_sdiff_of_subset (subset_univ _),card_univ,card]
  have β : q.beta.natDegree-131071≤δ := le_max_left _ _
  have da : q.first.natDegree≤δ := (le_max_left _ _).trans (le_max_right _ _)
  have db : q.second.natDegree≤δ := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨a,b,B,L,R,na,nb,ha,hb,hB,hL,hR,values,data⟩ := extract q 131071 δ h.first_ne h.second_ne
    da db (by omega) linear
  have atNode (i : I) (hi : i∈S) := data (x i) (U 0 i) (U 1 i) (σ (U 0 i)) (σ (U 1 i))
    (Koala6831BenchmarkResidual.good_node_identity (mem_sdiff.mp hi).2)
  have core (g : K) (hg : g∈E) (i : I) (hi : i∈agreementSet x U P g) : i∈S := by
    exact mem_sdiff.mpr ⟨mem_univ _,fun bad => disjoint_left.mp (h.good g hg).2 hi bad⟩
  have cp := Frontier.LinearKernel.compatibility σ x S (U 1) a b L R 131071 δ ha hb hL hR
     (by omega) (fun i _ => fixed i) (fun i hi => (atNode i hi).2.1) (fun i hi => (atNode i hi).2.2)
  refine ⟨a,b,B,L,R,na,nb,ha,hb,hL,cp,?_,?_⟩
  swap
  · intro g hg i hi
    have good := Koala6831BenchmarkResidual.good_node_identity (mem_sdiff.mp (core g hg i hi)).2
    have active := primitive_active_at_good_node q h.primitive (x i) _ _ good
    rw [(values (x i)).1,(values (x i)).2] at active
    exact ⟨active.imp (fun nz eq => nz (by rw [eq,MvPolynomial.C_0]))
      (fun nz eq => nz (by rw [eq,MvPolynomial.C_0])),(atNode i (core g hg i hi)).2⟩
  intro g hg
  let T := agreementSet x U P g
  have enough : 179740≤T.card := h.selection.agreement g hg
  have pg := h.selection.degree_le g hg
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun i:T => x i.val) (x.injective.comp Subtype.val_injective)
  · intro i
    have f := eval_eq_of_mem_agreementSet (x:=x) (received:=U) (selected:=P) (g:=g) i.property
    have mf := eval_map_apply (p:=P g) σ (x i.val)
    rw [fixed,f,map_add,map_mul] at mf
    obtain ⟨e₀,e₁,e₂⟩ := atNode i.val (core g hg i.val i.property)
    simp only [eval_add,eval_mul,eval_C,f,mf]
    linear_combination e₀ + g*e₁ + (σ g)*e₂
  · rw [Fintype.card_coe]
    have hd₁ : (a*P g).natDegree≤a.natDegree+(P g).natDegree := natDegree_mul_le
    have hd₂ : (b*(P g).map σ).natDegree≤b.natDegree+((P g).map σ).natDegree := natDegree_mul_le
    have hd₃ := natDegree_map_le (f:=σ) (p:=P g)
    have hleft := natDegree_add_le (a*P g) (b*(P g).map σ)
    have hl := natDegree_C_mul_le g L
    have hr := natDegree_C_mul_le (σ g) R
    have hmid := natDegree_add_le B (C g*L)
    have hright := natDegree_add_le (B+C g*L) (C (σ g)*R)
    omega
#print axioms actual_coefficients
end
end ProximityPrize.SubmissionLower.GenuineLinearData
