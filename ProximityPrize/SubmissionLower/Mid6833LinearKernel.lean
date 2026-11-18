/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
namespace Frontier.LinearKernel
open Polynomial Finset
open scoped Polynomial Classical
noncomputable section
variable {K I : Type*} [Field K] [DecidableEq I]

def conjugateProduct (σ : K →+* K) (a : K[X]) (n : ℕ) : K[X] :=
  ∏ j ∈ Finset.range n, (Polynomial.mapRingHom σ)^[j] a

/-- Iterate an equation in the polynomial ring; no splitting of the
denominator or assumption on its roots is needed. -/
theorem iterate_row (σ : K →+* K) (a b r : K[X]) (row : a*r=b*r.map σ) (n : ℕ) :
    conjugateProduct σ a n * r = conjugateProduct σ b n * (Polynomial.mapRingHom σ)^[n] r := by
  induction n with
  | zero => simp [conjugateProduct]
  | succ n ih =>
    let M := Polynomial.mapRingHom σ
    have hiter (j : ℕ) (A B : K[X]) : M^[j] (A*B) = M^[j] A * M^[j] B := by
      induction j with
      | zero => rfl
      | succ j hh => simp only [Function.iterate_succ_apply',hh,map_mul]
    have step := congrArg (M^[n]) row
    change M^[n] (a*r)=M^[n] (b*M r) at step
    rw [hiter,hiter,← Function.iterate_succ_apply] at step
    simp only [conjugateProduct,Finset.prod_range_succ] at ih ⊢
    change (conjugateProduct σ a n * M^[n] a)*r =
      (conjugateProduct σ b n * M^[n] b)*M^[n+1] r
    calc
      _ = M^[n] a * (conjugateProduct σ a n*r) := by ring
      _ = M^[n] a * (conjugateProduct σ b n*M^[n] r) := by exact congrArg (fun k => M^[n] a*k) ih
      _ = conjugateProduct σ b n * (M^[n] a * M^[n] r) := by ring
      _ = _ := by rw [step]; ring

theorem norm_no_kernel (σ : K →+* K) (a b : K[X]) (n : ℕ)
    (period : ∀ r : K[X], (Polynomial.mapRingHom σ)^[n] r = r)
    (different : conjugateProduct σ a n ≠ conjugateProduct σ (-b) n)
    (r : K[X]) (zero : a*r+b*r.map σ=0) : r=0 := by
  have eq := iterate_row σ a (-b) r (by linear_combination zero) n
  rw [period] at eq
  exact (mul_eq_zero.mp (show (conjugateProduct σ a n-conjugateProduct σ (-b) n)*r=0 by linear_combination eq)).resolve_left (sub_ne_zero.mpr different)

private theorem eval_map_fixed (σ : K →+* K) (f : K[X]) (v : K) (hv : σ v=v) :
    (f.map σ).eval v=σ (f.eval v) := by
  conv_lhs => arg 1; rw [← hv]
  exact eval_map_apply .. 

/-- The two separately recovered rational slopes agree globally once the good
node count exceeds w+2δ. This inequality holds on the full tested excess window. -/
theorem compatibility (σ : K →+* K) (x : I ↪ K) (S : Finset I) (v : I → K)
    (a b L R : K[X]) (w δ : ℕ) (ha : a.natDegree≤δ) (hb : b.natDegree≤δ)
    (hL : L.natDegree≤w+δ) (hR : R.natDegree≤w+δ)
    (size : w+2*δ < S.card) (fixed : ∀ i∈S, σ (x i)=x i)
    (left : ∀ i∈S, a.eval (x i)*v i=L.eval (x i))
    (right : ∀ i∈S, b.eval (x i)*σ (v i)=R.eval (x i)) :
    a.map σ * R = b * L.map σ := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun i : S => x i.val) (x.injective.comp Subtype.val_injective)
  · intro j
    simp only [eval_mul,eval_map_fixed σ _ _ (fixed j.val j.property),← left j.val j.property,
      ← right j.val j.property,map_mul]
    ring
  · rw [Fintype.card_coe]
    have s₁ : (a.map σ * R).natDegree ≤ (a.map σ).natDegree + R.natDegree := natDegree_mul_le
    have s₂ : (b*L.map σ).natDegree ≤ b.natDegree+(L.map σ).natDegree := natDegree_mul_le
    have m₁ := natDegree_map_le (p:=a) (f:=σ)
    have m₂ := natDegree_map_le (p:=L) (f:=σ)
    omega

/-- With trivial homogeneous semilinear kernel, any two witness polynomials
determine the entire selected graph, even for excess beyond the Cramer range. -/
theorem affine_graph (σ : K →+* K) (a b B L R : K[X]) (E : Finset K) (P : K → K[X])
    (ha : a≠0) (compatible : a.map σ*R=b*L.map σ)
    (noKernel : ∀ r : K[X], (a.map σ)*r+b*r.map σ=0 → r=0)
    (row : ∀ g∈E, a*P g+b*(P g).map σ=B+C g*L+C (σ g)*R)
    (g₀ g₁ : K) (h₀ : g₀∈E) (h₁ : g₁∈E) (ne : g₁≠g₀) :
    let V := C (g₁-g₀)⁻¹*(P g₁-P g₀)
    ∀ g∈E, P g=P g₀-C g₀*V+C g*V := by
  let V := C (g₁-g₀)⁻¹*(P g₁-P g₀)
  have diff (g : K) (hg : g∈E) : a*(P g-P g₀) = C (g-g₀)*L := by
    apply sub_eq_zero.mp
    apply noKernel
    simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,map_sub]
    linear_combination (a.map σ)*(row g hg) - (a.map σ)*(row g₀ h₀) + (C (σ g)-C (σ g₀))*compatible
  have hinv : C (g₁-g₀)⁻¹*C (g₁-g₀) = (1:K[X]) := by rw [← C_mul,inv_mul_cancel₀ (sub_ne_zero.mpr ne),C_1]
  have hV : a*V=L := by
    dsimp [V]
    rw [mul_left_comm a _ _,diff g₁ h₁,← mul_assoc,hinv,one_mul]
  dsimp only
  intro g hg
  change P g = P g₀-C g₀*V+C g*V
  apply mul_left_cancel₀ ha
  have hh := diff g hg
  rw [← hV,C_sub] at hh
  linear_combination hh
#print axioms norm_no_kernel
#print axioms compatibility
#print axioms affine_graph
end
end Frontier.LinearKernel
