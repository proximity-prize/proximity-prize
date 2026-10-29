import ProximityPrize.SubmissionBinaryLower.P64C6Step
import ProximityPrize.SubmissionBinaryLower.P64FoundSupp

/-!
# The flat auxiliary kernel and uniqueness of its local cofactors

The unknowns are the global auxiliary coefficients and one bounded cofactor
per line. Cofactor uniqueness makes every nonzero kernel vector have a
nonzero global auxiliary component.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Flat

open Polynomial P64Found P64LineOrder Module

variable {F : Type*} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

noncomputable def lineShiftLM (x : F) (y : F[X]) : Tri →ₗ[F] Tri where
  toFun R := lineShift R x y
  map_add' R H := by simp [lineShift, Polynomial.Bivariate.shift]
  map_smul' a R := by simp [lineShift, Polynomial.Bivariate.shift, Algebra.smul_def]

section Kernel

variable {ι : Type*} [Fintype ι]

noncomputable def constraints (R : Tri) (B : Finset (ℕ × ℕ × ℕ))
    (C T : ι → Finset (ℕ × ℕ × ℕ)) (x : ι → F) (y : ι → F[X]) :
    ((B → F) × (∀ i, C i → F)) →ₗ[F] (∀ i, T i → F) :=
  LinearMap.pi fun i =>
    let first : ((B → F) × (∀ i, C i → F)) →ₗ[F] Tri :=
      (lineShiftLM (x i) (y i)).comp
        ((comb3 B).comp (LinearMap.fst F (B → F) (∀ i, C i → F)))
    let second : ((B → F) × (∀ i, C i → F)) →ₗ[F] Tri :=
      (LinearMap.mulLeft F (lineShift R (x i) (y i))).comp
        ((comb3 (C i)).comp
          ((LinearMap.proj i : (∀ i, C i → F) →ₗ[F] (C i → F)).comp
            (LinearMap.snd F (B → F) (∀ i, C i → F))))
    (extr3 (T i)).comp
      ((first + second) : ((B → F) × (∀ i, C i → F)) →ₗ[F] Tri)

lemma constraints_apply (R : Tri) (B : Finset (ℕ × ℕ × ℕ))
    (C T : ι → Finset (ℕ × ℕ × ℕ)) (x : ι → F) (y : ι → F[X])
    (v : (B → F) × (∀ i, C i → F)) (i : ι) :
    constraints R B C T x y v i = extr3 (T i)
      (lineShift (comb3 B v.1) (x i) (y i) + lineShift R (x i) (y i) * comb3 (C i) (v.2 i)) := rfl

/-- More unknowns than equations, together with cofactor uniqueness, gives a nonzero auxiliary. -/
theorem exists_flat_coefficients (R : Tri) (B : Finset (ℕ × ℕ × ℕ))
    (C T : ι → Finset (ℕ × ℕ × ℕ)) (x : ι → F) (y : ι → F[X])
    (hcard : (∑ i, (T i).card) < B.card + ∑ i, (C i).card)
    (huniq : ∀ i (c : C i → F),
      extr3 (T i) (lineShift R (x i) (y i) * comb3 (C i) c) = 0 → c = 0) :
    ∃ (c : B → F) (g : ∀ i, C i → F), c ≠ 0 ∧
      ∀ i, extr3 (T i) (lineShift (comb3 B c) (x i) (y i) +
        lineShift R (x i) (y i) * comb3 (C i) (g i)) = 0 := by
  classical
  have hdim : finrank F (∀ i, T i → F) < finrank F ((B → F) × (∀ i, C i → F)) := by
    simpa [Module.finrank_prod, Module.finrank_pi_fintype] using hcard
  have hk := LinearMap.ker_ne_bot_of_finrank_lt
    (f := constraints R B C T x y) hdim
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  change constraints R B C T x y v = 0 at hv
  have hvi : ∀ i, extr3 (T i) (lineShift (comb3 B v.1) (x i) (y i) +
      lineShift R (x i) (y i) * comb3 (C i) (v.2 i)) = 0 :=
    fun i => congrFun hv i
  refine ⟨v.1, v.2, ?_, hvi⟩
  intro hzero
  have hg : v.2 = 0 := by
    funext i
    apply huniq i
    have hi := hvi i
    rw [hzero, map_zero, show lineShift 0 (x i) (y i) = 0 by
      simp [lineShift, Polynomial.Bivariate.shift], zero_add] at hi
    exact hi
  exact hv0 (Prod.ext hzero hg)

end Kernel

/-- A supported cofactor cannot disappear in the truncated product constraints. -/
theorem cofactor_unique (S : Tri) (hS : S ≠ 0) (s q d g : ℕ)
    (hSw : WtLE 0 q 1 d S) (C T : Finset (ℕ × ℕ × ℕ))
    (hCo : ∀ p ∈ C, p.1 + p.2.1 < s - tord S)
    (hCw : ∀ p ∈ C, q * p.2.1 + p.2.2 ≤ g)
    (hT : ∀ a b l, a + b < s → q * b + l ≤ d + g → (a, b, l) ∈ T)
    (c : C → F) (hc : extr3 T (S * comb3 C c) = 0) : c = 0 := by
  classical
  let G := comb3 C c
  have hGmem : G ∈ supp C := comb3_mem_supp C c
  by_cases hG : G = 0
  · apply comb3_injective C
    simpa [G] using hG
  have hGw : WtLE 0 q 1 g G := by
    intro a b l hn
    have hp : (a, b, l) ∈ C := by
      by_contra hnot
      exact hn (hGmem a b l hnot)
    simpa using hCw _ hp
  have hSGw := hSw.mul hGw
  have hSG : S * G ≠ 0 := mul_ne_zero hS hG
  have ho : s ≤ tord (S * G) := by
    apply (le_tord_iff hSG).mpr
    intro a b hab
    ext l
    change c3 (S * G) a b l = 0
    by_cases hp : (a, b, l) ∈ T
    · exact congrFun hc ⟨(a, b, l), hp⟩
    · by_contra hn
      apply hp
      apply hT a b l hab
      simpa using hSGw a b l hn
  rw [tord_mul hS hG] at ho
  have hGo := (le_tord_iff hG).mp (show s - tord S ≤ tord G by omega)
  funext p
  have hpair := hGo p.1.1 p.1.2.1 (hCo p.1 p.2)
  have hentry := c3_comb3 C c p.1.1 p.1.2.1 p.1.2.2
  rw [dite_eq_left p.2] at hentry
  have hz : c3 G p.1.1 p.1.2.1 p.1.2.2 = 0 := by simp [c3, hpair]
  exact hentry.symm.trans hz

end P64C6Flat
end ProximityPrize.SubmissionBinaryLower
