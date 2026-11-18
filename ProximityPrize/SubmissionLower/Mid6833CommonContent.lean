/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Koala6831MovingExceptionsNormalForm
import Mathlib.Tactic
namespace Frontier6969.Content
open Polynomial ProximityPrize.SubmissionLower
open Koala6831Separation (NormalForm Seeds primitive_regroup)
open Koala6831SeparationFactors (affine)
open Koala6831Comparison (SymbolicRow IsPrimitiveRow)
open scoped Polynomial
noncomputable section
variable {K : Type*} [Field K]

theorem repeated_coeffs (d a₀ a₁ c₀ c₁ P Q L : K[X]) (g h : K) (ne : g≠h)
    (hg : d*P+(c₀+C g*c₁)=(a₀+C g*a₁)*L)
    (hh : d*Q+(c₀+C h*c₁)=(a₀+C h*a₁)*L) :
    ∃ U V : K[X], a₀*L-c₀=d*U ∧ a₁*L-c₁=d*V := by
  let V := C ((g-h)⁻¹)*(P-Q)
  have e : C (g-h)*(a₁*L-c₁)=d*(P-Q) := by rw [map_sub];linear_combination hh-hg
  have hn : g-h≠0 := sub_ne_zero.mpr ne
  have z := congrArg ((C ((g-h)⁻¹)) * ·) e
  rw [←mul_assoc,←map_mul,inv_mul_cancel₀ hn,map_one,one_mul] at z
  have hs : a₁*L-c₁=d*V := by rw [z];unfold V;ring
  refine ⟨P-C g*V,V,?_,hs⟩
  linear_combination -hg-C g*hs

/-- Simultaneous repetition forces the two field-polynomial denominator contents
to be relatively prime, by primitivity of all three components of the original row. -/
theorem coprime_of_repetition {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (prim : IsPrimitiveRow q) (L : K[X])
    (left : ∃ U V : K[X], N.A 0*L-N.C 0=N.d₀*U ∧ N.A 1*L-N.C 1=N.d₀*V)
    (right : ∃ U V : K[X], N.B 0*L+N.D 0=N.d₁*U ∧ N.B 1*L+N.D 1=N.d₁*V) :
    IsCoprime N.d₀ N.d₁ := by
  obtain ⟨u,v,hu,hv⟩ := left
  obtain ⟨s,t,hs,ht⟩ := right
  apply isRelPrime_iff_isCoprime.mp
  intro p p0 p1
  obtain ⟨j,hj⟩ := p0
  obtain ⟨k,hk⟩ := p1
  let c : K[X] →+* MvPolynomial (Fin 2) K[X] := MvPolynomial.C
  have cp : IsUnit (c p) := by
    apply primitive_regroup q.beta q.first q.second prim
    · refine ⟨c k*affine 0 (N.A 0) (N.A 1)*affine 1 s t-c j*affine 0 u v*affine 1 (N.B 0) (N.B 1),?_⟩
      rw [N.beta_eq]
      have ee₁ := congrArg c hu
      have ee₂ := congrArg c hv
      have ee₃ := congrArg c hs
      have ee₄ := congrArg c ht
      simp only [map_sub,map_add,map_mul,hj,hk] at ee₁ ee₂ ee₃ ee₄
      dsimp only [affine,c] at *
      linear_combination
        -(MvPolynomial.C (N.B 0)+MvPolynomial.C (N.B 1)*MvPolynomial.X 1)*ee₁
        -MvPolynomial.X 0*(MvPolynomial.C (N.B 0)+MvPolynomial.C (N.B 1)*MvPolynomial.X 1)*ee₂
        +(MvPolynomial.C (N.A 0)+MvPolynomial.C (N.A 1)*MvPolynomial.X 0)*ee₃
        +MvPolynomial.X 1*(MvPolynomial.C (N.A 0)+MvPolynomial.C (N.A 1)*MvPolynomial.X 0)*ee₄
    · refine ⟨c j*affine 1 (N.B 0) (N.B 1),?_⟩
      rw [N.first_eq,hj,map_mul];ring
    · refine ⟨-(c k*affine 0 (N.A 0) (N.A 1)),?_⟩
      rw [N.second_eq,hk,map_mul];ring
  simpa only [c,MvPolynomial.eval_C] using cp.map (MvPolynomial.eval (fun _ => 0))

#print axioms repeated_coeffs
#print axioms coprime_of_repetition
end
end Frontier6969.Content
