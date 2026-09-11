import ProximityPrize.SubmissionLower.PartG015


section Compact_SecondJetLocal
/-! The explicit local substitution A = R - epsilon*S + epsilon^2*T.
Here S is the second Hasse derivative, and T records the remaining contact. -/
namespace ProximityPrize.SubmissionLower.SecondJetLocal
open scoped BigOperators
open SecondJetBasis SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]
abbrev Base := MvPolynomial (Fin 3) K
abbrev Target := Polynomial (MvPolynomial (Fin 4) K)

def baseEval : Base (K := K) →ₐ[K] Target (K := K) :=
  MvPolynomial.aeval ![
    Polynomial.C (MvPolynomial.X 2)-Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
      Polynomial.X^2*Polynomial.C (MvPolynomial.X 1),
    Polynomial.C (MvPolynomial.X 2), Polynomial.C (MvPolynomial.X 3)]

def innerEval : Polynomial (Base (K := K)) →ₐ[K] Target (K := K) :=
  Polynomial.eval₂AlgHom baseEval (Polynomial.C (MvPolynomial.X 0)) (fun _ => Commute.all _ _)

def contact : Jet (Base (K := K)) →ₐ[K] Target (K := K) :=
  Polynomial.eval₂AlgHom innerEval Polynomial.X (fun _ => Commute.all _ _)

@[simp] theorem contact_X : contact (K := K) Polynomial.X = Polynomial.X := by
  simp [contact]

@[simp] theorem contact_C_C (p : Base (K := K)) :
    contact (K := K) (Polynomial.C (Polynomial.C p)) = baseEval (K := K) p := by
  simp [contact, innerEval]

@[simp] theorem contact_C_X :
    contact (K := K) (Polynomial.C Polynomial.X) = Polynomial.C (MvPolynomial.X 0) := by
  simp [contact, innerEval]

def v : Base (K := K) := MvPolynomial.X 0-MvPolynomial.X 1

theorem v_ne_zero : v (K := K) ≠ 0 := by
  unfold v
  apply sub_ne_zero.mpr
  intro h
  have hh := MvPolynomial.X_injective h
  exact (by decide : (0 : Fin 3) ≠ 1) hh

theorem contact_v : contact (K := K) (Polynomial.C (Polynomial.C v)) =
    (Polynomial.X : Target (K := K)) * (-(Polynomial.C (MvPolynomial.X (0 : Fin 4)) : Target (K := K))+
      Polynomial.X*Polynomial.C (MvPolynomial.X 1)) := by
  rw [contact_C_C]
  simp only [v, map_sub, baseEval, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem contact_u : contact (K := K)
    (Polynomial.C (Polynomial.C v)+Polynomial.X*Polynomial.C Polynomial.X) =
      Polynomial.X^2*Polynomial.C (MvPolynomial.X 1) := by
  rw [map_add, map_mul, contact_v, contact_X, contact_C_X]
  ring

theorem term_vanishes (m r h a b : ℕ) (p : Base (K := K))
    (horder : m ≤ r+2*a+b) :
    Polynomial.X^m ∣ contact (K := K) (term (K := K) v r h a b p) := by
  apply (pow_dvd_pow Polynomial.X horder).trans
  apply term_contact (K := K) (contact (K := K)).toRingHom Polynomial.X v p r h a b
  · exact contact_X
  · exact ⟨Polynomial.C (MvPolynomial.X 1), contact_u⟩
  · exact ⟨(-(Polynomial.C (MvPolynomial.X (0 : Fin 4)) : Target (K := K))+Polynomial.X*Polynomial.C (MvPolynomial.X 1) : Target (K := K)), contact_v⟩


end
end ProximityPrize.SubmissionLower.SecondJetLocal

end Compact_SecondJetLocal
