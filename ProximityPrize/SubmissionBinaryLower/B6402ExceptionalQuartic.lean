import ProximityPrize.SubmissionBinaryLower.B6402LocalInput

/-! On every exceptional fibre use the same w³ and two-degree quotient
allowance. The local recursion only requires a nonzero remaining factor. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ExceptionalQuartic
open Polynomial P64Found B6402ExceptionalSystem B6402ExceptionalSupport B6402LocalSupport
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K]
noncomputable local instance : CommRing (Polynomial K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial K)) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Fibre K) := AddMonoidAlgebra.commRing

theorem ordinate_cube : Bounds ((Polynomial.X : Fibre K)^3) 0 5 0 := by
  have h := ((ordinate (K:=K)).pow 3) 0
  change Bounds (((Polynomial.C (Polynomial.X : Fibre K))^3).coeff 0) _ _ _ at h
  rw [←map_pow,coeff_C_zero] at h
  exact h.mono (by decide) (by decide) (by decide)

noncomputable def tail (p : Fibre K) := p.divX.divX.divX

theorem factor (p : Fibre K) (H : ℕ) (hn : p≠0) (support : Bounds p 0 5 H)
    (low : ∀ j<3,p.coeff j=0) :
    p=(Polynomial.X : Fibre K)^3 * tail p ∧ tail p≠0 ∧ Bounds (tail p) 0 2 H := by
  have ident : p=(Polynomial.X : Fibre K)^3*tail p := by
    apply Polynomial.ext
    intro j
    rw [coeff_X_pow_mul']
    by_cases hj : 3≤j
    · rw [if_pos hj]
      simp only [tail,coeff_divX]
      congr 1; omega
    · rw [if_neg hj]
      exact low _ (by omega)
  refine ⟨ident,fun hp => hn (by rw [ident,hp,mul_zero]),?_⟩
  apply (in_box _ _ _ _).mp
  intro a b l outside
  by_contra hz
  have hc : c3 p a (b+3) l≠0 := by
    simpa only [tail,c3,coeff_divX,Nat.add_assoc] using hz
  have hr := support.slope a (b+3) l hc
  have hw := support.ordinate a (b+3) l hc
  have ht := support.seed a (b+3) l hc
  simp at hr hw ht
  exact outside (by simp [box]; omega)

#print axioms factor
end ProximityPrize.SubmissionBinaryLower.B6402ExceptionalQuartic
