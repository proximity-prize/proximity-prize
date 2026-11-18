/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833ProtocolResidual
import ProximityPrize.SubmissionLower.Koala6831Cramer
namespace Frontier6969.GenuineMoving

open Polynomial Finset ProximityPrize.SubmissionLower
open Koala6831Separation (NormalForm Seeds pairDegree)
open Koala6831Comparison (SymbolicRow primitiveExcess)
open K6969Global (RetainedComparison budget)
open Koala6831BenchmarkPrimitive (Received SelectionMap badNodes agreementSet eval_eq_of_mem_agreementSet)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 2000000
variable {K I : Type} [Field K] [Fintype I]

def twist (σ : K →+* K) (A B : Fin 2 → K[X]) : K[X] :=
  (A 0).map σ * B 1 - (A 1).map σ * B 0

def offset (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (j : Fin 2) :=
  N.d₁ * (N.C j).map σ + N.d₀.map σ * N.D j

private def V (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) := N.d₀.map σ * twist σ N.A N.B

private def J (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) := (N.A 1).map σ * offset σ N 0 - (N.A 0).map σ * offset σ N 1

private def rationalValue (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (j : Fin 2) := N.A j * J σ N - V σ N * N.C j

private theorem map_at_fixed (σ : K →+* K) (p : K[X]) {x : K} (hx : σ x = x) :
    (p.map σ).eval x = σ (p.eval x) := by
  simpa only [hx] using (eval_map_apply (p:=p) σ x)

/-- The two receiver coordinates give two semilinear equations on one common value. -/
theorem node_equations (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (x : K) (fixed : σ x=x) (U : Fin 2 → K)
    (good : q.atNode (MvPolynomial.C x) (Koala6831SeparationFactors.affine 0 (U 0) (U 1))
      (Koala6831SeparationFactors.affine 1 (σ (U 0)) (σ (U 1)))=0) :
    ∃ t : K, (∀ j, N.d₀.eval x * U j + (N.C j).eval x = t * (N.A j).eval x) ∧
      ∀ j, N.d₁.eval x * ((N.A j).map σ).eval x * σ t -
        (N.d₀.map σ).eval x * (N.B j).eval x * t = (offset σ N j).eval x := by
  obtain ⟨t,left,right⟩ := N.fixedWord x U (σ ∘ U) good
  refine ⟨t,left,?_⟩
  intro j
  have hj := congrArg σ (left j)
  have hr := right j
  simp only [map_add,map_mul] at hj
  simp only [Function.comp_apply] at hr
  simp only [offset,eval_add,eval_mul,map_at_fixed σ _ fixed]
  linear_combination -(N.d₁.eval x)*hj+(σ (N.d₀.eval x))*hr

private theorem node_rational (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (x : K) (fixed : σ x=x) (U : Fin 2 → K)
    (good : q.atNode (MvPolynomial.C x) (Koala6831SeparationFactors.affine 0 (U 0) (U 1))
      (Koala6831SeparationFactors.affine 1 (σ (U 0)) (σ (U 1)))=0) :
    ∀ j, (N.d₀ * V σ N).eval x * U j = (rationalValue σ N j).eval x := by
  obtain ⟨t,left,eq⟩ := node_equations σ N x fixed U good
  have vt : (V σ N).eval x * t = (J σ N).eval x := by
    simp only [V,J,twist,eval_mul,eval_sub]
    linear_combination ((N.A 1).map σ).eval x * eq 0 - ((N.A 0).map σ).eval x * eq 1
  intro j
  simp only [rationalValue,eval_mul,eval_sub]
  linear_combination (V σ N).eval x * left j + (N.A j).eval x * vt

private theorem deg_pair (A : Fin 2 → K[X]) (i : Fin 2) : (A i).natDegree ≤ pairDegree A := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _
private theorem mul_bound {a b : K[X]} {s t : ℕ} (ha : a.natDegree ≤ s) (hb : b.natDegree ≤ t) :
    (a*b).natDegree ≤ s+t := natDegree_mul_le.trans (Nat.add_le_add ha hb)
private theorem add_bound {a b : K[X]} {s : ℕ} (ha : a.natDegree ≤ s) (hb : b.natDegree ≤ s) :
    (a+b).natDegree ≤ s := (natDegree_add_le _ _).trans (max_le ha hb)
private theorem sub_bound {a b : K[X]} {s : ℕ} (ha : a.natDegree ≤ s) (hb : b.natDegree ≤ s) :
    (a-b).natDegree ≤ s := (natDegree_sub_le _ _).trans (max_le ha hb)

private theorem degrees (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) :
    (N.d₀ * V σ N).natDegree ≤ 4*δ ∧ ∀ j, (rationalValue σ N j).natDegree ≤ w+4*δ := by
  have h0 := N.first_degree
  have h1 := N.second_degree
  have h2 := N.left_degree
  have h3 := N.right_degree
  have da (j) : ((N.A j).map σ).natDegree ≤ δ :=
    natDegree_map_le.trans ((deg_pair _ j).trans (by omega))
  have db (j) : (N.B j).natDegree ≤ δ := (deg_pair _ j).trans (by omega)
  have dc (j) : (N.C j).natDegree ≤ w+δ := (deg_pair _ j).trans (by omega)
  have dd (j) : (N.D j).natDegree ≤ w+δ := (deg_pair _ j).trans (by omega)
  have d0 : (N.d₀.map σ).natDegree ≤ δ := natDegree_map_le.trans (by omega)
  have dt : (twist σ N.A N.B).natDegree ≤ δ+δ := sub_bound (mul_bound (da 0) (db 1)) (mul_bound (da 1) (db 0))
  have dv : (V σ N).natDegree ≤ δ+(δ+δ) := mul_bound d0 dt
  have dz (j) : (offset σ N j).natDegree ≤ δ+(w+δ) := add_bound
    (mul_bound (by omega : N.d₁.natDegree ≤ δ) (natDegree_map_le.trans (dc j))) (mul_bound d0 (dd j))
  have dj : (J σ N).natDegree ≤ δ+(δ+(w+δ)) :=
    sub_bound (mul_bound (da 1) (dz 0)) (mul_bound (da 0) (dz 1))
  constructor
  · exact (mul_bound (by omega : N.d₀.natDegree ≤ δ) dv).trans (by omega)
  · intro j
    apply sub_bound
    · exact (mul_bound ((deg_pair N.A j).trans (show pairDegree N.A ≤ δ by omega)) dj).trans (by omega)
    · exact (mul_bound dv (dc j)).trans (by omega)

/-- Entire retained set, before any normalization cleanup, lies on one rational pencil. -/
theorem transverse_count (x : I ↪ K) (σ : K →+* K) (fixed : ∀ i, σ (x i)=x i)
    (U : Received K I) (S : Finset K) (P : SelectionMap K) (q : SymbolicRow (Seeds K))
    (h : RetainedComparison x σ U S P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (short : primitiveExcess 131071 q ≤ 12136) (tr : twist σ N.A N.B ≠ 0) :
    S.card ≤ 82405 := by
  classical
  let δ := primitiveExcess 131071 q
  have bounds := degrees σ N
  have dne : N.d₀ * V σ N ≠ 0 := mul_ne_zero N.d₀_ne
    (mul_ne_zero (fun bad => N.d₀_ne ((Polynomial.map_injective σ σ.injective) (by simpa using bad))) tr)
  apply Koala6831Cramer.card_le_of_common_denominator S P (N.d₀*V σ N)
    (rationalValue σ N 0) (rationalValue σ N 1) dne 131071 82404 h.selection.degree_le
  · intro g hg
    let T := agreementSet x U P g
    have enough : 179740 ≤ T.card := h.selection.agreement g hg
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun i:T => x i.val)
      (x.injective.comp Subtype.val_injective)
    · intro i
      have hi := i.property
      have ng := fun bad => Finset.disjoint_left.mp (h.good g hg).2 hi bad
      have orig := Koala6831BenchmarkResidual.good_node_identity ng
      have fits := node_rational σ N (x i.val) (fixed i.val) (fun j => U j i.val)
        (by simpa only [Koala6831SeparationFactors.affine,mul_comm] using orig)
      have ag := eval_eq_of_mem_agreementSet (x:=x) (received:=U) (selected:=P) (g:=g) hi
      simp only [eval_mul,eval_add,eval_C,ag]
      simp only [eval_mul] at fits
      linear_combination fits 0 + g * fits 1
    · rw [Fintype.card_coe]
      have degreeP := mul_bound bounds.1 (h.selection.degree_le g hg)
      have degreeR := add_bound (bounds.2 0) ((natDegree_C_mul_le g _).trans (bounds.2 1))
      omega
  · exact h.selection.pencil

#print axioms node_equations
#print axioms transverse_count
end
end Frontier6969.GenuineMoving
