import ProximityPrize.SubmissionLower.Part.G065


section Compact_SecondJetWeightedContact
/-! A second contact-two generator for weighted second-jet spaces.
The generator J = R*(A-R) + epsilon*A*S has the same contact as U, but
its leading coefficient contains an additional R. This checks the algebraic
ingredient found by the weighted-space matrix experiments. It does not assert
a new interpolation rank receipt or a stronger protocol claim. -/
namespace ProximityPrize.SubmissionLower.SecondJetWeightedContact
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {B C : Type*} [CommRing B] [CommRing C]

def V (a r : B) : Polynomial B := Polynomial.C (a-r)
def U (a r s : B) : Polynomial B :=
  V a r + Polynomial.X*Polynomial.C s
def J (a r s : B) : Polynomial B :=
  Polynomial.C r*V a r + Polynomial.X*Polynomial.C (a*s)

theorem J_eq (a r s : B) :
    J a r s = Polynomial.C r*U a r s +
      Polynomial.X*Polynomial.C s*V a r := by
  simp only [J, U, V, map_sub, map_mul]
  ring

theorem contact_J (a r s : B) (φ : Polynomial B →+* C) (ε : C)
    (hε : φ Polynomial.X = ε)
    (hU : ε^2 ∣ φ (U a r s)) (hV : ε ∣ φ (V a r)) :
    ε^2 ∣ φ (J a r s) := by
  obtain ⟨u, hu⟩ := hU
  obtain ⟨v, hv⟩ := hV
  refine ⟨φ (Polynomial.C r)*u + φ (Polynomial.C s)*v, ?_⟩
  rw [J_eq, map_add, map_mul, map_mul, map_mul, hε, hu, hv]
  ring

/-- Higher powers of R give further contact-two generators. For the global
source condition `A-degree ≤ epsilon-degree`, powers above two require extra
epsilon reserve; this theorem asserts contact only. -/
def JPower (a r s : B) (n : ℕ) : Polynomial B :=
  Polynomial.C (r^n)*V a r + Polynomial.X*Polynomial.C (a^n*s)





/-- A contact-four generator filling the weight-5/2 gap between J_1 and J_2.
Its low-weight expansion uses one extra unit of the A/epsilon source reserve. -/
def KFour (a r s : B) : Polynomial B :=
  J a r s*JPower a r s 2 -
    Polynomial.X*Polynomial.C (a*s)*V a r^3




/-- Higher contact generators extending JPower at power two and KFour.
The support bounds used in exploratory counts are separate obligations. -/
def GFamily (a r s : B) : ℕ → Polynomial B
  | 0 => Polynomial.C r
  | n+1 => J a r s*GFamily a r s n +
      Polynomial.C ((-1:B)^n)*Polynomial.X*Polynomial.C (a*s)*V a r^(2*n+1)



def family (a r s z : B) (ρ h u v i j ℓ : ℕ) : Polynomial B :=
  Polynomial.X^ρ * (Polynomial.C (s^h) *
    U a r s^(u-ℓ) * J a r s^ℓ * V a r^v *
    Polynomial.C (a^i*r^(j-ℓ)*z))

theorem family_contact (a r s z : B) (ρ h u v i j ℓ : ℕ)
    (hℓ : ℓ ≤ u) (φ : Polynomial B →+* C) (ε : C)
    (hε : φ Polynomial.X = ε)
    (hU : ε^2 ∣ φ (U a r s)) (hV : ε ∣ φ (V a r)) :
    ε^(ρ+2*u+v) ∣ φ (family a r s z ρ h u v i j ℓ) := by
  have hJ := contact_J a r s φ ε hε hU hV
  obtain ⟨cu, hu⟩ := hU
  obtain ⟨cv, hv⟩ := hV
  obtain ⟨cj, hj⟩ := hJ
  refine ⟨φ (Polynomial.C (s^h))*cu^(u-ℓ)*cj^ℓ*cv^v*
    φ (Polynomial.C (a^i*r^(j-ℓ)*z)), ?_⟩
  simp only [family, map_mul, map_pow, hε, hu, hv, hj, mul_pow]
  have he : ρ+2*u+v = ρ+2*(u-ℓ)+2*ℓ+v := by omega
  rw [he]
  simp only [pow_add, pow_mul]
  ring

theorem family_coeff_lt (a r s z : B) (ρ h u v i j ℓ d : ℕ)
    (hd : d < ρ) : (family a r s z ρ h u v i j ℓ).coeff d = 0 := by
  simp [family, Polynomial.coeff_X_pow_mul', Nat.not_le.mpr hd]

theorem family_coeff_self (a r s z : B) (ρ h u v i j ℓ : ℕ)
    (hu : ℓ ≤ u) (hj : ℓ ≤ j) :
    (family a r s z ρ h u v i j ℓ).coeff ρ =
      s^h*(a-r)^(u+v)*(a^i*r^j*z) := by
  obtain ⟨u', rfl⟩ := Nat.exists_eq_add_of_le hu
  obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj
  simp only [family, Polynomial.coeff_X_pow_mul', Nat.sub_self, if_pos (le_refl ρ)]
  simp [Polynomial.coeff_zero_eq_eval_zero, U, J, V, pow_add]
  rw [mul_pow]
  ring

end
end ProximityPrize.SubmissionLower.SecondJetWeightedContact

end Compact_SecondJetWeightedContact
