import ProximityPrize.SubmissionLower.PartG013


section Compact_SecondJetTruncate
/-! Truncation preserves the triangular kernel construction and its contact.
The concrete finite monomial support bounds are still separate obligations. -/
namespace ProximityPrize.SubmissionLower.SecondJetBasis
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]

def truncateOuter (m : ℕ) : Jet B →ₗ[K] Jet B :=
  (Polynomial.modByMonicHom (Polynomial.X^m : Jet B)).restrictScalars K

theorem truncateOuter_coeff (m : ℕ) (P : Jet B) (r : ℕ) (hr : r < m) :
    (truncateOuter (K := K) m P).coeff r = P.coeff r := by
  change (P %ₘ Polynomial.X^m).coeff r = P.coeff r
  have heq := Polynomial.modByMonic_add_div P (Polynomial.X^m)
  have hc := congrArg (fun Q : Jet B => Q.coeff r) heq
  simpa only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hr), add_zero] using hc


theorem truncateOuter_coeff_high (m : ℕ) (P : Jet B) (r : ℕ) (hr : m ≤ r) :
    (truncateOuter (K := K) m P).coeff r = 0 := by
  change (P %ₘ Polynomial.X^m).coeff r = 0
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply (Polynomial.degree_modByMonic_lt P (Polynomial.monic_X_pow m)).trans_le
  simp only [Polynomial.degree_X_pow]
  exact_mod_cast hr

theorem truncate_truncateOuter {m s : ℕ} (P : Jet B) :
    truncate (K := K) (m := m) (s := s) (truncateOuter (K := K) m P) =
      truncate (K := K) (m := m) (s := s) P := by
  funext r h
  exact congrArg (fun Q : Polynomial B => Q.coeff h.val)
    (truncateOuter_coeff (K := K) m P r.val r.isLt)

theorem truncateOuter_pack_injective {m s : ℕ} (v : B) (hv : v ≠ 0)
    (a b : Fin m → Fin s → ℕ) :
    Function.Injective ((truncateOuter (K := K) m).comp (pack (K := K) v a b)) := by
  intro p q hpq
  apply truncate_pack_injective (K := K) v hv a b
  have h := congrArg (truncate (K := K) (m := m) (s := s)) hpq
  simpa only [LinearMap.comp_apply, truncate_truncateOuter] using h

theorem truncateOuter_contact {C : Type*} [CommRing C]
    (φ : Jet B →+* C) (t : C) (m : ℕ) (P : Jet B)
    (hε : φ Polynomial.X = t) (hP : t^m ∣ φ P) :
    t^m ∣ φ (truncateOuter (K := K) m P) := by
  have hd : t^m ∣ φ ((Polynomial.X^m : Jet B) * (P /ₘ Polynomial.X^m)) := by
    simp only [map_mul, map_pow, hε]
    exact dvd_mul_right _ _
  have heq := congrArg φ (Polynomial.modByMonic_add_div P (Polynomial.X^m))
  rw [map_add] at heq
  have hsub := dvd_sub hP hd
  rwa [← heq, add_sub_cancel_right] at hsub


/-- A finite family of these vectors gives a rank saving once its support and
vanishing under the concrete contact map have been verified. -/
theorem finite_source_rank {m s : ℕ}
    {V T : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup T] [Module K T]
    (W : Submodule K (Jet B)) [FiniteDimensional K W]
    (f : W →ₗ[K] T) (v : B) (hv : v ≠ 0)
    (a b : Fin m → Fin s → ℕ)
    (e : V →ₗ[K] (Fin m → Fin s → B)) (he : Function.Injective e)
    (hW : ∀ p, truncateOuter (K := K) m (pack (K := K) v a b (e p)) ∈ W)
    (hzero : ∀ p, f ⟨truncateOuter (K := K) m (pack (K := K) v a b (e p)), hW p⟩ = 0) :
    Module.finrank K f.range + Module.finrank K V ≤ Module.finrank K W := by
  let g := ((truncateOuter (K := K) m).comp (pack (K := K) v a b)).comp e
  have hg : Function.Injective g := (truncateOuter_pack_injective (K := K) v hv a b).comp he
  let gw : V →ₗ[K] W := g.codRestrict W hW
  let gk : V →ₗ[K] f.ker := gw.codRestrict f.ker hzero
  have hi : Function.Injective gk := by
    intro p q hpq
    apply hg
    exact congrArg (fun x : f.ker => (x.val : Jet B)) hpq
  letI : AddCommGroup W := inferInstance
  letI : Module K W := W.module
  letI : FiniteDimensional K f.ker := inferInstance
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hsum := f.finrank_range_add_finrank_ker
  omega

end
end ProximityPrize.SubmissionLower.SecondJetBasis

end Compact_SecondJetTruncate
