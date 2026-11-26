import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-! The recursion at an order-two fibre with zero quartic coefficient.
The local variable of this polynomial ring represents (X-x)^2. Its
coefficient ring contains the other local coordinates and the seed. -/

namespace ProximityPrize.SubmissionBinaryLower.B6402ExceptionalFibres
open Polynomial
set_option autoImplicit false

variable {S : Type*} [CommRing S]

/-- One remainder test at each spatial layer. Only division by the fixed
ordinate polynomial L is tested. The factors discarded at a miss are in d. -/
def remainderConditions (F : S[X]) (d L : S) : ℕ → S[X] → Prop
  | 0, _ => True
  | n+1, G => ∃ q : S, G.coeff 0 = L*q ∧
      remainderConditions F d L n ((C d*G - F*C q).divX)

theorem cleared_identity (F : S[X]) (d L : S) (hF : F.coeff 0 = d*L)
    (n : ℕ) (G : S[X]) (h : remainderConditions F d L n G) :
    ∃ U V : S[X], C d^n * G = F*U + X^n * V := by
  induction n generalizing G with
  | zero => exact ⟨0,G,by simp⟩
  | succ n ih =>
    obtain ⟨q,hq,hrest⟩ := h
    let B := C d*G-F*C q
    have h0 : B.coeff 0 = 0 := by simp [B,hF,hq]; ring
    have hdiv : B = X * B.divX := by
      simpa [h0,mul_comm] using (B.divX_mul_X_add).symm
    obtain ⟨U,V,hUV⟩ := ih B.divX hrest
    refine ⟨C d^n*C q + X*U,V,?_⟩
    calc C d^(n+1)*G = C d^n*(F*C q+B) := by dsimp [B]; rw [pow_succ]; ring
      _ = C d^n*(F*C q) + X*(C d^n*B.divX) := by linear_combination C d^n * hdiv
      _ = _ := by rw [hUV,pow_succ]; ring

/-- A regular multiplier at a miss permits cancellation after evaluation on
the witness. No choice or factorization of individual ordinate roots is needed. -/
theorem miss_dvd {T : Type*} [CommRing T] (ev : S[X] →+* T) (π : T)
    (F G : S[X]) (d L : S) (hF : F.coeff 0 = d*L) (n : ℕ)
    (rows : remainderConditions F d L n G)
    (hf : ev F=0) (ht : ev X=π^2) (hu : IsCoprime π (ev (C d))) :
    π^(2*n) ∣ ev G := by
  obtain ⟨U,V,h⟩ := cleared_identity F d L hF n G rows
  have hv := congrArg ev h
  simp only [map_mul,map_pow,map_add,hf,zero_mul,zero_add,ht,←pow_mul] at hv
  have hcop : IsCoprime (π^(2*n)) (ev (C d)^n) := hu.pow
  exact hcop.dvd_of_dvd_mul_left ⟨_,hv⟩

#print axioms cleared_identity
#print axioms miss_dvd
end ProximityPrize.SubmissionBinaryLower.B6402ExceptionalFibres
