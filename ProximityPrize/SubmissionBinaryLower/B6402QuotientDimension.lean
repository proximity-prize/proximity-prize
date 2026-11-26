import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace ProximityPrize.SubmissionBinaryLower.B6402QuotientDimension
open scoped BigOperators
set_option autoImplicit false

/-- The column map includes both the coefficients of G and its local auxiliary
variables. Uniqueness of those auxiliary variables on the kernel makes the
projection injective there. Genuine multiples have a separately bounded space. -/
theorem exists_outside_multiples {K U E Z C : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup Z] [Module K Z]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    (rows : U →ₗ[K] E) (output : U →ₗ[K] Z) (multiples : C →ₗ[K] Z)
    (unique : ∀ u, rows u=0 → output u=0 → u=0)
    (surplus : Module.finrank K E + Module.finrank K C < Module.finrank K U) :
    ∃ u : U, rows u=0 ∧ output u ∉ LinearMap.range multiples := by
  classical
  by_contra! closed
  let embed : LinearMap.ker rows →ₗ[K] LinearMap.range multiples :=
    (output.comp (LinearMap.ker rows).subtype).codRestrict _ (fun x => closed x.1 x.2)
  have hinj : Function.Injective embed := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h0 : embed x=0 := hx
    have hz : output x.1=0 := congrArg Subtype.val h0
    exact Subtype.ext (unique x.1 x.2 hz)
  have hsize := LinearMap.finrank_le_finrank_of_injective hinj
  have hnull := LinearMap.finrank_range_add_finrank_ker rows
  have h1 := LinearMap.finrank_range_le multiples
  have h2 := Submodule.finrank_le (LinearMap.range rows)
  omega

/-- Equations minus quotient variables at one exceptional spatial layer. -/
theorem exceptional_layer (K J d T i b H : ℕ) (dmax : d≤2) (dk : d≤K)
    (base : H≤T) (ib : i≤b) (width : K≤J+5*i) :
    (K+1)*(T+i*H+1) ≤ (K-d+1)*(T+i*H-H+1) + 2*(T+1+(J+16*b+2)*H) := by
  have uh : H≤T+i*H := by omega
  have rect : (K+1)*(T+i*H+1) =
      (K-d+1)*(T+i*H-H+1)+d*(T+i*H+1)+(K-d+1)*H := by
    zify [dk,uh]; ring
  rw [rect]
  have hd := Nat.mul_le_mul_right (T+i*H+1) dmax
  have hw := Nat.mul_le_mul_right H (show K-d+1≤J+5*i+1 by omega)
  have hi := Nat.mul_le_mul_right H ib
  nlinarith only [hd,hw,hi]

/-- Number of even spatial slices and ordinate coefficients to test at a
regular fibre under the resultant line-order estimate. -/
theorem regular_layers (J s m b : ℕ) (hm : 2*m≤J+s) (hb : b≤m) :
    (∑ i ∈ Finset.range b, (J+4*s-(2*m+3*s-2*i)+1)) =
      b*(J+s-2*m+1)+b*(b-1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ,ih (by omega)]
    have h0 : b+1≤m := hb
    have h1 : 2*b≤2*m+3*s := by omega
    have h2 : 2*m+3*s-2*b≤J+4*s := by omega
    cases b with
    | zero => simp; omega
    | succ b =>
      simp only [Nat.add_sub_cancel]
      zify [hm,h1,h2]; ring

end ProximityPrize.SubmissionBinaryLower.B6402QuotientDimension
