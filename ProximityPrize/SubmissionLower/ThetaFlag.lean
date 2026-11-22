import ProximityPrize.SubmissionLower.ThetaCore

/-!
The theta rank bound for one contact block.

A space of polynomials of degree `d` with index between `l` and `u`, mapped by the shear and
truncated at contact order `R ≤ u + 1`, has rank at most the number of monomials of degree `d`
with index between `l - 3 (u + 1 - R)` and `R - 1`.
-/

namespace ThetaCore
open MvPolynomial ThetaDeriv

section Flag
variable {k : Type*} [Field k]

theorem finrank_range_le_of_ker_le {V W W' : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W'] [Module.Finite k V]
    [Module.Finite k W'] (f : V →ₗ[k] W) (g : V →ₗ[k] W')
    (h : LinearMap.ker g ≤ LinearMap.ker f) :
    Module.finrank k (LinearMap.range f) ≤ Module.finrank k W' := by
  have h1 := f.finrank_range_add_finrank_ker
  have h2 := g.finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_mono h
  have h4 := (LinearMap.range g).finrank_le
  omega

/-- Exponents of the image of the theta operator. -/
def window (d l u R : ℤ) : Set (Fin 4 →₀ ℕ) :=
  { e | ((e.weight ωg : ℕ) : ℤ) = d ∧ l - 3 * (u + 1 - R) ≤ ((e.weight ωo : ℕ) : ℤ) ∧
    ((e.weight ωo : ℕ) : ℤ) ≤ R - 1 }

theorem theta_rank {s : Set (Fin 4 →₀ ℕ)} (d l u R : ℤ)
    [Module.Finite k (restrictSupport k s)]
    [Module.Finite k (restrictSupport k (window d l u R))]
    (hsub : ∀ e ∈ s, ((e.weight ωg : ℕ) : ℤ) = d ∧ l ≤ ((e.weight ωo : ℕ) : ℤ) ∧
      ((e.weight ωo : ℕ) : ℤ) ≤ u)
    (hu : 0 ≤ u) (hR0 : 0 ≤ R) (hR : R ≤ u + 1)
    (hchar : ∀ n : ℕ, 0 < n → (n : ℤ) ≤ u → ((n : ℕ) : k) ≠ 0)
    (f : restrictSupport k s →ₗ[k] MvPolynomial (Fin 4) k)
    (hf : ∀ x : restrictSupport k s, f x =
      weightedTruncation ωc R.toNat (bind₁ shear (x : MvPolynomial (Fin 4) k))) :
    Module.finrank k (LinearMap.range f) ≤
      Module.finrank k (restrictSupport k (window d l u R)) := by
  have hu' : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu
  have hδ' : (((u + 1 - R).toNat : ℕ) : ℤ) = u + 1 - R := Int.toNat_of_nonneg (by omega)
  have hδu : (u + 1 - R).toNat ≤ u.toNat + 1 := by omega
  have hchar' : ∀ n : ℕ, 0 < n → n ≤ u.toNat → ((n : ℕ) : k) ≠ 0 :=
    fun n h0 hn => hchar n h0 (by omega)
  have hmem : ∀ x : restrictSupport k s,
      desc (Do (k := k)) u.toNat (u + 1 - R).toNat (x : MvPolynomial (Fin 4) k) ∈
        restrictSupport k (window d l u R) := by
    intro x
    have h1 : (x : MvPolynomial (Fin 4) k) ∈ upper (R := k) ωo ((u.toNat : ℕ) : ℤ) :=
      mem_upper.mpr fun e he => by
        have h := (hsub e (x.2 he)).2.2
        omega
    have h2 : (x : MvPolynomial (Fin 4) k) ∈ restrictWeightedOrder (R := k) ωo l.toNat :=
      mem_restrictWeightedOrder.mpr fun e he => by
        have h := (hsub e (x.2 he)).2.1
        omega
    have h3 : (x : MvPolynomial (Fin 4) k) ∈ restrictWeightedOrder (R := k) ωg d.toNat :=
      mem_restrictWeightedOrder.mpr fun e he => by
        have h := (hsub e (x.2 he)).1
        omega
    have h4 : (x : MvPolynomial (Fin 4) k) ∈ upper (R := k) ωg d :=
      mem_upper.mpr fun e he => by
        have h := (hsub e (x.2 he)).1
        omega
    have y1 := desc_upper (k := k) u.toNat (u + 1 - R).toNat hδu _ h1
    have y2 := desc_order (k := k) u.toNat (u + 1 - R).toNat _ h2
    have y3 := desc_mem (Do (k := k)) u.toNat (restrictWeightedOrder (R := k) ωg d.toNat)
      (fun p hp => Do_grade_order hp) (u + 1 - R).toNat _ h3
    have y4 := desc_mem (Do (k := k)) u.toNat (upper (R := k) ωg d)
      (fun p hp => Do_grade_upper hp) (u + 1 - R).toNat _ h4
    intro e he
    have a1 := mem_upper.mp y1 e he
    have a2 := mem_restrictWeightedOrder.mp y2 e he
    have a3 := mem_restrictWeightedOrder.mp y3 e he
    have a4 := mem_upper.mp y4 e he
    exact ⟨by omega, by omega, by omega⟩
  let T : restrictSupport k s →ₗ[k] restrictSupport k (window d l u R) :=
    LinearMap.codRestrict _ ((desc (Do (k := k)) u.toNat (u + 1 - R).toNat).comp
      (restrictSupport k s).subtype) hmem
  refine finrank_range_le_of_ker_le f T fun x hx => ?_
  have h0 : desc (Do (k := k)) u.toNat (u + 1 - R).toNat (x : MvPolynomial (Fin 4) k) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  rw [LinearMap.mem_ker, hf]
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  have h := shear_order_of_desc_eq_zero (k := k) u.toNat (u + 1 - R).toNat hδu hchar' _ h0
  have he : u.toNat + 1 - (u + 1 - R).toNat = R.toNat := by omega
  rw [he] at h
  exact h


end Flag

end ThetaCore
