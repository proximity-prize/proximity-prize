import ProximityPrize.SubmissionBinaryLower.P64C7Boxes

/-!
# Lifting independent monomials from the fraction field

The WS/HS basis is chosen over `F(Z)`. Its independence implies that the
bounded `F[Z]`-span of the same monomials meets `(U^s,V^s,S)` only at zero.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Lift

open Polynomial P64Found P64C7 P64C7Boxes

variable {F : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "Frac" => FractionRing (Polynomial F)

noncomputable def toFrac : Tri →+* Polynomial (Polynomial Frac) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) Frac))

lemma toFrac_mem_boxIdeal (s : ℕ) (S R : Tri) (hR : R ∈ boxIdeal s S) :
    toFrac R ∈ boxIdeal s (toFrac S) := by
  classical
  have hmap : Ideal.map toFrac (boxIdeal s S) ≤ boxIdeal s (toFrac S) := by
    rw [boxIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨r, hr, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · simpa [toFrac] using U_pow_mem s (toFrac S)
    · simpa [toFrac] using V_pow_mem s (toFrac S)
    · exact S_mem _ _
  exact hmap (Ideal.mem_map_of_mem toFrac hR)

lemma toFrac_atU0 (S : Tri) :
    (toFrac S).map (Polynomial.constantCoeff (R := Frac)) =
      (S.map (Polynomial.constantCoeff (R := Polynomial F))).map (algebraMap (Polynomial F) Frac) := by
  ext b
  simp [toFrac, Polynomial.coeff_map]

lemma toFrac_order (S : Tri) (μ : ℕ) (hS : OrdAtLeast μ S) : OrdAtLeast μ (toFrac S) := by
  intro a b hab
  simp [toFrac, Polynomial.coeff_map, hS a b hab]

lemma toFrac_eq_sum (R : Tri) (Λ : Finset (ℕ × ℕ))
    (hR : ∀ a b, (a, b) ∉ Λ → (R.coeff b).coeff a = 0) :
    toFrac R = ∑ p ∈ Λ, algebraMap (Polynomial F) Frac ((R.coeff p.2).coeff p.1) •
      mono (K := Frac) p.1 p.2 := by
  classical
  rw [← Finset.sum_coe_sort]
  apply Polynomial.ext
  intro b
  apply Polynomial.ext
  intro a
  rw [coeff_sum_mono]
  simp only [toFrac, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  by_cases hp : (a, b) ∈ Λ
  · simp [hp]
  · simp [hp, hR a b hp]

theorem exists_lifted_independent (s μ ν : ℕ) (S : Tri) (R'' : Polynomial (Polynomial F))
    (hS : OrdAtLeast μ S)
    (hS0 : S.map (Polynomial.constantCoeff (R := Polynomial F)) = Polynomial.X ^ ν * R'')
    (hu : R''.coeff 0 ≠ 0) :
    ∃ Λ : Finset (ℕ × ℕ), (∀ p ∈ Λ, p.1 < s ∧ p.2 < min ν s) ∧
      (tri s).card - (tri (s - μ)).card ≤ Λ.card ∧
      ∀ q E (R : Tri), R ∈ supp (lifted Λ q E) → R ∈ boxIdeal s S → R = 0 := by
  classical
  let f : Polynomial F →+* Frac := algebraMap (Polynomial F) Frac
  have hf : Function.Injective f := IsFractionRing.injective (Polynomial F) Frac
  have hS0' : (toFrac S).map (Polynomial.constantCoeff (R := Frac)) =
      Polynomial.X ^ ν * R''.map f := by
    rw [toFrac_atU0, hS0, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  have hu' : (R''.map f).coeff 0 ≠ 0 := by
    intro hz
    apply hu
    apply hf
    simpa using hz
  obtain ⟨Λ, hΛ, hcard, hind⟩ := exists_indep_monomials s μ ν (toFrac S) (R''.map f)
    (toFrac_order S μ hS) hS0' hu'
  refine ⟨Λ, hΛ, hcard, ?_⟩
  intro q E R hRT hRJ
  have hm := toFrac_mem_boxIdeal s S R hRJ
  rw [toFrac_eq_sum R Λ (lifted_support Λ q E R hRT)] at hm
  have hz := hind (fun p => f ((R.coeff p.2).coeff p.1)) hm
  apply Polynomial.ext
  intro b
  apply Polynomial.ext
  intro a
  by_cases hp : (a, b) ∈ Λ
  · apply hf
    simpa using hz (a, b) hp
  · exact lifted_support Λ q E R hRT a b hp

end P64C7Lift
end ProximityPrize.SubmissionBinaryLower
