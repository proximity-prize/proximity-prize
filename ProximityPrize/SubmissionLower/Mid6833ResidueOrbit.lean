/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- A virtual pole congruence and one coefficientwise conjugate bound the
number of seeds even when the two poles do not lie on the evaluation domain. -/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
namespace Frontier.ResidueOrbit
open Polynomial Finset
open scoped Polynomial Classical
noncomputable section
variable {K : Type*} [Field K]

/-- Every pair of allowed seed offsets is proportional to its coefficientwise
conjugate when the two residue conditions meet at a visible common divisor. -/
theorem direction (σ : K →+* K) (D G H L : K[X]) (g₀ : K)
    (E : Finset K) (T : K → K[X]) (common : G∣D) (overlap : G∣D.map σ)
    (visible : ¬G∣(H.map σ)*L)
    (fixed : ∀ g∈E, (T g).map σ=T g)
    (residue : ∀ g∈E, D ∣ H*T g+C (g-g₀)*L) :
    ∀ g∈E, ∀ h∈E, (g-g₀)*σ (h-g₀) - (h-g₀)*σ (g-g₀) = 0 := by
  let β := (H.map σ)*L
  let γ := H*(L.map σ)
  have rel (g : K) (hg : g ∈ E) : G ∣ C (g-g₀)*β - C (σ (g-g₀))*γ := by
    have r1 := common.trans (residue g hg)
    have r2 := overlap.trans (Polynomial.map_dvd σ (residue g hg))
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,fixed g hg] at r2
    convert dvd_sub (dvd_mul_of_dvd_right r1 (H.map σ)) (dvd_mul_of_dvd_right r2 H) using 1
    dsimp [β,γ]
    ring
  intro g hg h hh
  by_contra bad
  apply visible
  apply (Polynomial.dvd_C_mul bad).mp
  change G ∣ C ((g-g₀)*σ (h-g₀)-(h-g₀)*σ (g-g₀))*β
  convert dvd_sub (dvd_mul_of_dvd_right (rel g hg) (C (σ (h-g₀))))
    (dvd_mul_of_dvd_right (rel h hh) (C (σ (g-g₀)))) using 1
  rw [map_sub,map_mul,map_mul]
  ring

/-- A Frobenius overlap cuts the seed set to at most q, with no factor for
the code length, number of errors, or polynomial degrees. -/
theorem count (σ : K →+* K) (q : ℕ) (hq : 1 < q) (frob : ∀t, σ t=t^q)
    (D G H L : K[X]) (g₀ : K) (E : Finset K) (T : K → K[X])
    (common : G∣D) (overlap : G∣D.map σ) (visible : ¬G∣(H.map σ)*L)
    (fixed : ∀ g∈E, (T g).map σ=T g) (residue : ∀ g∈E, D∣H*T g+C (g-g₀)*L) :
    E.card ≤ q := by
  classical
  by_cases single : ∀ g∈E, g=g₀
  · have sub : E⊆{g₀} := fun g hg => mem_singleton.mpr (single g hg)
    exact (card_le_card sub).trans (by simpa using hq.le)
  push_neg at single
  obtain ⟨h,hh,ne⟩ := single
  let d := h-g₀
  have hd : d ≠ 0 := sub_ne_zero.mpr ne
  let P : K[X] := C d * X^q - C (σ d) * X
  have top : (C d * X^q).natDegree=q := by rw [natDegree_C_mul hd,natDegree_X_pow]
  have lt : (C (σ d)*X).natDegree < (C d * X^q).natDegree := by
    rw [top]
    exact (natDegree_C_mul_le _ _).trans_lt (by simpa using hq)
  have dp : P.natDegree = q := (natDegree_sub_eq_left_of_natDegree_lt lt).trans top
  have nz : P≠0 := by intro z; rw [z,natDegree_zero] at dp;omega
  let shift (x:K) := x-g₀
  have hi : Function.Injective shift := fun _ _ h => sub_left_inj.mp h
  have sub : E.image shift ⊆ P.roots.toFinset := by
    intro z hz
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hz
    apply Multiset.mem_toFinset.mpr ((mem_roots nz).mpr ?_)
    have eq := direction σ D G H L g₀ E T common overlap visible fixed residue g hg h hh
    change P.eval (g-g₀)=0
    simp only [P,eval_sub,eval_mul,eval_pow,eval_X,eval_C,d]
    rw [← frob]
    linear_combination -eq
  simpa [card_image_of_injective _ hi,dp] using
    (card_le_card sub).trans (Multiset.toFinset_card_le _ |>.trans (card_roots' P))

#print axioms direction
#print axioms count
end
end Frontier.ResidueOrbit
