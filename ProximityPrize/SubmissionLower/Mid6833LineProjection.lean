/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Koala6831Cramer
import Mathlib.Tactic
namespace Frontier6969.Projection
open Polynomial
open scoped Polynomial
variable {K I : Type*} [Field K]
noncomputable section

def proj (σ : K →+* K) (t : K) (P : K[X]) := C t*P.map σ-C (σ t)*P

theorem degree_proj (σ : K →+* K) (t : K) (P : K[X]) :
    (proj σ t P).natDegree ≤ P.natDegree :=
  (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans natDegree_map_le)
    (natDegree_C_mul_le _ _))

private theorem ev (σ : K →+* K) (P : K[X]) (x : K) (h : σ x=x) :
    (P.map σ).eval x=σ (P.eval x) := by
  rw [Polynomial.eval_map, ← h, Polynomial.eval₂_at_apply]
  rw [h]

/-- A varying contribution taking values in one fixed-field line is annihilated
by this seed-dependent semilinear projection. The remaining proper rational
intercept leaves a coefficient restriction independent of which sites agree. -/
theorem residual_zero (σ : K →+* K) (dom : I ↪ K) (S : Finset I) (b : I → K)
    (D R P : K[X]) (t : K) (w : ℕ)
    (hfix : D.map σ=D) (hR : R.natDegree<D.natDegree) (hP : P.natDegree≤w)
    (hA : w+D.natDegree<S.card)
    (hx : ∀ i∈S, σ (dom i)=dom i) (hb : ∀ i∈S, σ (b i)=b i)
    (hf : ∀ i∈S, D.eval (dom i)*(P.eval (dom i)-t*b i)=R.eval (dom i)) :
    proj σ t R=0 := by
  have h : D*proj σ t P=proj σ t R := by
    have he := ProximityPrize.SubmissionLower.Koala6831Cramer.equation_of_node_agreement
      dom S D (proj σ t P) (proj σ t R) 0 (0:K) w D.natDegree le_rfl
      ((degree_proj _ _ _).trans hP) ((degree_proj _ _ _).trans (by omega))
      (by simp) hA
    simp only [map_zero,zero_mul,add_zero] at he
    apply he
    intro i hi
    have hden : σ (D.eval (dom i))=D.eval (dom i) := by
      rw [← ev σ D (dom i) (hx i hi),hfix]
    have e0 := hf i hi
    have e1 := congrArg σ e0
    simp only [map_sub,map_mul,hden,hb i hi] at e1
    simp only [proj,eval_sub,eval_mul,eval_C,ev _ _ _ (hx i hi)]
    linear_combination t*e1-σ t*e0
  by_contra nz
  have deg := Polynomial.natDegree_le_of_dvd (show D ∣ proj σ t R from ⟨_,h.symm⟩) nz
  exact Nat.not_le_of_lt hR (deg.trans (degree_proj _ _ _))

theorem all_coefficients (σ : K →+* K) (t : K) (R : K[X]) (h : proj σ t R=0) (j : ℕ) :
    t*σ (R.coeff j)=σ t*R.coeff j := by
  have hc := congrArg (fun f : K[X] => f.coeff j) h
  simpa [proj,sub_eq_zero] using hc

theorem prime_line [DecidableEq K] (σ : K →+* K) (p : ℕ) (hp : 1<p)
    (hσ : ∀ a, σ a=a^p) (seeds : Finset K) (V r : K) (hv : V≠0) (hr : r≠0)
    (h : ∀ g∈seeds, (g*V)*σ r=σ (g*V)*r) : seeds.card≤p := by
  let Q : K[X] := C (V^p*r)*X^p-C (V*r^p)*X
  have hh : (C (V^p*r)*X^p : K[X]).natDegree=p := by
    rw [natDegree_C_mul (mul_ne_zero (pow_ne_zero _ hv) hr)]
    simp
  have hl : (C (V*r^p)*X : K[X]).natDegree<p := by
    apply (natDegree_C_mul_le _ _).trans_lt
    simpa using hp
  have deg : Q.natDegree=p := by
    unfold Q
    rw [natDegree_sub_eq_left_of_natDegree_lt (hh.symm ▸ hl),hh]
  have nz : Q≠0 := fun eq => by rw [eq,natDegree_zero] at deg;omega
  rw [← deg]
  apply card_le_degree_of_subset_roots
  intro g hg
  apply (mem_roots nz).mpr
  change Q.eval g=0
  simp only [Q,eval_sub,eval_mul,eval_C,eval_pow,eval_X]
  have e := h g hg
  rw [hσ,hσ,mul_pow] at e
  linear_combination -e

/-- A uniform count under the rational-intercept and prime-line hypotheses.
S may depend on the seed. P may be shifted by any globally known polynomial pencil
before this theorem is applied. -/
theorem uniform [DecidableEq K] (σ : K →+* K) (p : ℕ) (hp : 1<p)
    (hσ : ∀ a, σ a=a^p) (dom : I ↪ K) (seeds : Finset K) (ag : K → Finset I)
    (b : I → K) (D R : K[X]) (P : K → K[X]) (V : K) (w j : ℕ)
    (hv : V≠0) (hr : R.coeff j≠0) (hfix : D.map σ=D) (hR : R.natDegree<D.natDegree)
    (hP : ∀ g∈seeds, (P g).natDegree≤w) (hA : ∀ g∈seeds, w+D.natDegree<(ag g).card)
    (hx : ∀ g∈seeds, ∀ i∈ag g, σ (dom i)=dom i)
    (hb : ∀ g∈seeds, ∀ i∈ag g, σ (b i)=b i)
    (hf : ∀ g∈seeds, ∀ i∈ag g, D.eval (dom i)*((P g).eval (dom i)-(g*V)*b i)=R.eval (dom i)) :
    seeds.card≤p := by
  apply prime_line σ p hp hσ seeds V _ hv hr
  intro g hg
  exact all_coefficients _ _ _ (residual_zero σ dom (ag g) b D R (P g) (g*V) w
    hfix hR (hP g hg) (hA g hg) (hx g hg) (hb g hg) (hf g hg)) j

#print axioms residual_zero
#print axioms uniform
end
end Frontier6969.Projection
