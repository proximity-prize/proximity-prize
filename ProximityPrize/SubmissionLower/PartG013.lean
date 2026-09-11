import ProximityPrize.SubmissionLower.PartG012


section Compact_SecondJetBasis
/-! A triangular polynomial family for second-jet interpolation. The outer
polynomial variable is epsilon; the inner one is the second Hasse derivative.
This module checks independence before imposing the finite support bounds. -/
namespace ProximityPrize.SubmissionLower.SecondJetBasis
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
abbrev Jet (B : Type*) [CommRing B] := Polynomial (Polynomial B)

def lift : B →ₐ[K] Jet B :=
  (Polynomial.CAlgHom (R := K) (A := Polynomial B)).comp
    (Polynomial.CAlgHom (R := K) (A := B))

def factor (v : B) (r h a b : ℕ) : Jet B :=
  Polynomial.X^r *
    (Polynomial.C (Polynomial.X^h) *
      (Polynomial.C (Polynomial.C v) +
        Polynomial.X * Polynomial.C Polynomial.X)^a *
      Polynomial.C (Polynomial.C v)^b)

def term (v : B) (r h a b : ℕ) : B →ₗ[K] Jet B :=
  (LinearMap.mulLeft K (factor v r h a b)).comp lift.toLinearMap

theorem term_apply (v p : B) (r h a b : ℕ) :
    term (K := K) v r h a b p = factor v r h a b * Polynomial.C (Polynomial.C p) := rfl

theorem term_coeff_lt (v p : B) (r h a b d : ℕ) (hd : d < r) :
    (term (K := K) v r h a b p).coeff d = 0 := by
  rw [term_apply]
  simp [factor, mul_assoc, Polynomial.coeff_X_pow_mul', Nat.not_le.mpr hd]

theorem term_coeff_self (v p : B) (r h a b : ℕ) :
    (term (K := K) v r h a b p).coeff r =
      Polynomial.X^h * Polynomial.C (v^(a+b)*p) := by
  rw [term_apply]
  simp [factor, mul_assoc, Polynomial.coeff_X_pow_mul',
    Polynomial.coeff_zero_eq_eval_zero, pow_add]

variable {m s : ℕ}

def pack (v : B) (a b : Fin m → Fin s → ℕ) :
    (Fin m → Fin s → B) →ₗ[K] Jet B :=
  ∑ r, ∑ h, (term (K := K) v r.val h.val (a r h) (b r h)).comp
    ((LinearMap.proj h : (Fin s → B) →ₗ[K] B).comp
      (LinearMap.proj r : (Fin m → Fin s → B) →ₗ[K] (Fin s → B)))

theorem pack_apply (v : B) (a b : Fin m → Fin s → ℕ)
    (p : Fin m → Fin s → B) :
    pack (K := K) v a b p = ∑ r, ∑ h, term (K := K) v r.val h.val (a r h) (b r h) (p r h) := by
  simp [pack]

def truncate : Jet B →ₗ[K] (Fin m → Fin s → B) :=
  LinearMap.pi (fun r => LinearMap.pi (fun h =>
    ((Polynomial.lcoeff B h.val).restrictScalars K).comp
      ((Polynomial.lcoeff (Polynomial B) r.val).restrictScalars K)))

theorem truncate_apply (P : Jet B) (r : Fin m) (h : Fin s) :
    truncate (K := K) P r h = (P.coeff r.val).coeff h.val := rfl

theorem pack_initial_coeff (v : B) (a b : Fin m → Fin s → ℕ)
    (p : Fin m → Fin s → B) (r : Fin m)
    (hp : ∀ j, j.val < r.val → p j = 0) :
    (pack (K := K) v a b p).coeff r.val =
      ∑ h, Polynomial.X^h.val * Polynomial.C (v^(a r h+b r h)*p r h) := by
  rw [pack_apply, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single r]
  · simp_rw [Polynomial.finsetSum_coeff, term_coeff_self]
  · intro j _ hj
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro h _
    by_cases hlt : j.val < r.val
    · simp [hp j hlt]
    · exact term_coeff_lt v (p j h) j.val h.val (a j h) (b j h) r.val (by
        have hne : j.val ≠ r.val := fun he => hj (Fin.ext he)
        omega)
  · simp

theorem truncate_pack_initial (v : B) (a b : Fin m → Fin s → ℕ)
    (p : Fin m → Fin s → B) (r : Fin m)
    (hp : ∀ j, j.val < r.val → p j = 0) :
    truncate (K := K) (pack (K := K) v a b p) r =
      fun h => v^(a r h+b r h)*p r h := by
  funext h
  rw [truncate_apply, pack_initial_coeff v a b p r hp, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
  simp only [Fin.val_inj]
  simp

theorem truncate_pack_injective (v : B) (hv : v ≠ 0)
    (a b : Fin m → Fin s → ℕ) :
    Function.Injective ((truncate (K := K) (m := m) (s := s)).comp (pack (K := K) v a b)) := by
  let D : Fin m → (Fin s → B) →ₗ[K] (Fin s → B) := fun r =>
    LinearMap.pi (fun h => (LinearMap.mulLeft K (v^(a r h+b r h))).comp (LinearMap.proj h))
  apply TriangularKernel.injective_of_triangular _ D
  · intro r p q he
    funext h
    have hh := congrFun he h
    exact mul_left_cancel₀ (pow_ne_zero _ hv) hh
  · intro p r hp
    exact truncate_pack_initial v a b p r hp


/-- Contact orders of the two factors add, over any target commutative ring. -/
theorem term_contact {C : Type*} [CommRing C]
    (φ : Jet B →+* C) (t : C) (v p : B) (r h a b : ℕ)
    (hε : φ Polynomial.X = t)
    (hU : t^2 ∣ φ (Polynomial.C (Polynomial.C v) +
      Polynomial.X * Polynomial.C Polynomial.X))
    (hV : t ∣ φ (Polynomial.C (Polynomial.C v))) :
    t^(r+2*a+b) ∣ φ (term (K := K) v r h a b p) := by
  obtain ⟨u, hu⟩ := hU
  obtain ⟨w, hw⟩ := hV
  refine ⟨φ (Polynomial.C (Polynomial.X^h)) * u^a * w^b *
    φ (Polynomial.C (Polynomial.C p)), ?_⟩
  simp only [term_apply, factor, map_mul, map_pow, hε, hu, hw, pow_mul, pow_add]
  ring

/-- The chosen exponents attain the requested contact without exceeding the
available second-derivative degree. -/
theorem exponent_budget (m r s h : ℕ) (hr : r ≤ m) (hh : h ≤ s) :
    let q := max ((m-r+1)/2) (m-r-(s-h))
    let a := min q (s-h)
    let b := q-a
    a+b = q ∧ h+a ≤ s ∧ m ≤ r+2*a+b := by
  dsimp
  omega

end
end ProximityPrize.SubmissionLower.SecondJetBasis

end Compact_SecondJetBasis
