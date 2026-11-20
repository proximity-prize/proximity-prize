/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Roots
namespace Frontier6969.GenuineMoving
open Polynomial Finset
open scoped Polynomial Classical
noncomputable section
variable {K L : Type} [Field K] [Field L]

/-- A fractional-linear constraint and its pth-power conjugate leave at most
p+1 seeds, including the pole reserved as the reference seed. -/
theorem mobius_count (c : K →+* L) (p : ℕ) (hp : 1<p) (S : Finset K) (r : K) (hr : r∈S)
    (u v u' v' c₀ c₁ : L) (anchor : u+c r*v≠0) (nc : c₁≠0)
    (eq : ∀g∈S, c₀*(u'+c g*v')*(c g-c r)^p=c₁*(c g-c r)*(u+c g*v)^p) :
    S.card≤p+1 := by
  classical
  let U₀ : L[X] := C u+Polynomial.X*C v
  let U₁ : L[X] := C u'+Polynomial.X*C v'
  let F : L[X] := C c₀*(Polynomial.X-C (c r))^(p-1)*U₁-C c₁*U₀^p
  have ev0 (x : L) : U₀.eval x=u+x*v := by simp only [U₀,eval_add,eval_C,eval_mul,eval_X]
  have ev1 (x : L) : U₁.eval x=u'+x*v' := by simp only [U₁,eval_add,eval_C,eval_mul,eval_X]
  have nz : F≠0 := by
    intro ez
    have e := congrArg (Polynomial.eval (c r)) ez
    simp only [F,eval_sub,eval_mul,eval_pow,eval_X,eval_C,sub_self,ev0,ev1,eval_zero] at e
    rw [zero_pow (by omega : p-1≠0),mul_zero,zero_mul,zero_sub,neg_eq_zero] at e
    exact mul_ne_zero nc (pow_ne_zero _ anchor) e
  have d0 : U₀.natDegree≤1 := (natDegree_add_le ..).trans (max_le (by simp) ((natDegree_mul_C_le ..).trans (by simp)))
  have d1 : U₁.natDegree≤1 := (natDegree_add_le ..).trans (max_le (by simp) ((natDegree_mul_C_le ..).trans (by simp)))
  have dg : F.natDegree≤p := by
    have subD : ((Polynomial.X-C (c r) : L[X])^(p-1)).natDegree≤p-1 := by simp
    have cd := natDegree_C_mul_le c₀ ((Polynomial.X-C (c r) : L[X])^(p-1))
    have pd := @natDegree_mul_le _ _ (C c₀*(Polynomial.X-C (c r))^(p-1)) U₁
    have last := (natDegree_C_mul_le c₁ (U₀^p)).trans ((natDegree_pow_le).trans (Nat.mul_le_mul_left p d0))
    have endD := natDegree_sub_le (C c₀*(Polynomial.X-C (c r))^(p-1)*U₁) (C c₁*U₀^p)
    dsimp only [F]
    omega
  have num : ((S.erase r).image c).card ≤ p := by
    apply (Polynomial.card_le_degree_of_subset_roots (p:=F) ?_).trans dg
    intro t ht
    obtain ⟨g,hg,rfl⟩ := mem_image.mp ht
    obtain ⟨ne,inS⟩ := mem_erase.mp hg
    have id := eq g inS
    have cn : c g-c r≠0 := sub_ne_zero.mpr (c.injective.ne ne)
    have pe : (c g-c r)^p=(c g-c r)^(p-1)*(c g-c r) := by
      rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤p)]
    rw [pe] at id
    apply (Polynomial.mem_roots nz).mpr
    change F.eval (c g)=0
    simp only [F,eval_sub,eval_mul,eval_pow,eval_C,eval_X,ev0,ev1]
    exact (mul_eq_zero.mp (show _*(c g-c r)=0 by linear_combination id)).resolve_right cn
  rw [card_image_of_injective _ c.injective] at num
  rw [←card_erase_add_one hr]
  exact Nat.add_le_add_right num 1
#print axioms mobius_count
end
end Frontier6969.GenuineMoving
