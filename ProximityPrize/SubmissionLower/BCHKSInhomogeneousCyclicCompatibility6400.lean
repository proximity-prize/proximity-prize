import ProximityPrize.SubmissionLower.BCHKSCyclicNormMultiplicative6400

/-!
# Six-cycle compatibility for an inhomogeneous semilinear equation

If `R = A * D + B * sigma(D)`, eliminating the six Frobenius conjugates of
`D` leaves a single linear expression in the six conjugates of `R`.  When
the cyclic norms of `A` and `B` agree, that expression vanishes.  Unlike the
homogeneous norm identity, this retains information about an owner-independent
forcing term such as the reduced global quotient.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSInhomogeneousCyclicCompatibility6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSCyclicNormErrorEvaluator6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The obstruction obtained after eliminating an unknown from the six
conjugates of `R = A*D + B*sigma(D)`. -/
noncomputable def koalaCyclicCompatibilitySix
    (A B R : IRSProfile.Field[X]) : IRSProfile.Field[X] :=
  koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 B *
      koalaFrobeniusConjugate 2 B *
      koalaFrobeniusConjugate 3 B *
      koalaFrobeniusConjugate 4 B *
      koalaFrobeniusConjugate 5 R -
    koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 B *
      koalaFrobeniusConjugate 2 B *
      koalaFrobeniusConjugate 3 B *
      koalaFrobeniusConjugate 4 R +
    koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 4 A *
      koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 B *
      koalaFrobeniusConjugate 2 B *
      koalaFrobeniusConjugate 3 R -
    koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 4 A *
      koalaFrobeniusConjugate 3 A *
      koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 B *
      koalaFrobeniusConjugate 2 R +
    koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 4 A *
      koalaFrobeniusConjugate 3 A *
      koalaFrobeniusConjugate 2 A *
      koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 R -
    koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 4 A *
      koalaFrobeniusConjugate 3 A *
      koalaFrobeniusConjugate 2 A *
      koalaFrobeniusConjugate 1 A *
      koalaFrobeniusConjugate 0 R

/-- Pure commutative-ring elimination identity underlying the compatibility
operator.  It is kept independent of the finite-field implementation. -/
theorem cyclicCompatibilitySix_algebra
    {R : Type} [CommRing R]
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ b₅ : R)
    (d₀ d₁ d₂ d₃ d₄ d₅ d₆ r₀ r₁ r₂ r₃ r₄ r₅ : R)
    (h₀ : r₀ = a₀ * d₀ + b₀ * d₁)
    (h₁ : r₁ = a₁ * d₁ + b₁ * d₂)
    (h₂ : r₂ = a₂ * d₂ + b₂ * d₃)
    (h₃ : r₃ = a₃ * d₃ + b₃ * d₄)
    (h₄ : r₄ = a₄ * d₄ + b₄ * d₅)
    (h₅ : r₅ = a₅ * d₅ + b₅ * d₆)
    (hcycle : d₆ = d₀) :
    b₀ * b₁ * b₂ * b₃ * b₄ * r₅ -
        a₅ * b₀ * b₁ * b₂ * b₃ * r₄ +
        a₅ * a₄ * b₀ * b₁ * b₂ * r₃ -
        a₅ * a₄ * a₃ * b₀ * b₁ * r₂ +
        a₅ * a₄ * a₃ * a₂ * b₀ * r₁ -
        a₅ * a₄ * a₃ * a₂ * a₁ * r₀ =
      (b₀ * b₁ * b₂ * b₃ * b₄ * b₅ -
        a₀ * a₁ * a₂ * a₃ * a₄ * a₅) * d₀ := by
  rw [h₀, h₁, h₂, h₃, h₄, h₅, hcycle]
  ring

theorem koalaFrobeniusConjugate_six
    (P : IRSProfile.Field[X]) :
    koalaFrobeniusConjugate 6 P = P := by
  apply Polynomial.ext
  intro n
  simp only [koalaFrobeniusConjugate, Polynomial.coeff_map]
  have hcoe (x : IRSProfile.Field) :
      koalaSexticFrobenius.toRingHom x = koalaSexticFrobenius x := rfl
  simp only [hcoe]
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
    koalaSexticFrobenius_six_apply (P.coeff n)

theorem koalaFrobeniusConjugate_add
    (P Q : IRSProfile.Field[X]) (n : Nat) :
    koalaFrobeniusConjugate n (P + Q) =
      koalaFrobeniusConjugate n P + koalaFrobeniusConjugate n Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate, koalaFrobeniusConjugate,
        koalaFrobeniusConjugate, ih, Polynomial.map_add]

theorem koalaFrobeniusConjugate_comp_one
    (P : IRSProfile.Field[X]) (n : Nat) :
    koalaFrobeniusConjugate n
        (P.map koalaSexticFrobenius.toRingHom) =
      koalaFrobeniusConjugate (n + 1) P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate, koalaFrobeniusConjugate, ih]

/-- Applying the compatibility operator to an actual semilinear image gives
the norm difference times the original unknown. -/
theorem koalaCyclicCompatibilitySix_semilinear
    (A B D : IRSProfile.Field[X]) :
    koalaCyclicCompatibilitySix A B
        (A * D + B * D.map koalaSexticFrobenius.toRingHom) =
      (koalaCyclicNormSix B - koalaCyclicNormSix A) * D := by
  let R := A * D + B * D.map koalaSexticFrobenius.toRingHom
  have hconj (n : Nat) :
      koalaFrobeniusConjugate n R =
        koalaFrobeniusConjugate n A *
            koalaFrobeniusConjugate n D +
          koalaFrobeniusConjugate n B *
            koalaFrobeniusConjugate (n + 1) D := by
    dsimp only [R]
    rw [koalaFrobeniusConjugate_add,
      koalaFrobeniusConjugate_mul,
      koalaFrobeniusConjugate_mul,
      koalaFrobeniusConjugate_comp_one]
  have h := cyclicCompatibilitySix_algebra
    (koalaFrobeniusConjugate 0 A)
    (koalaFrobeniusConjugate 1 A)
    (koalaFrobeniusConjugate 2 A)
    (koalaFrobeniusConjugate 3 A)
    (koalaFrobeniusConjugate 4 A)
    (koalaFrobeniusConjugate 5 A)
    (koalaFrobeniusConjugate 0 B)
    (koalaFrobeniusConjugate 1 B)
    (koalaFrobeniusConjugate 2 B)
    (koalaFrobeniusConjugate 3 B)
    (koalaFrobeniusConjugate 4 B)
    (koalaFrobeniusConjugate 5 B)
    (koalaFrobeniusConjugate 0 D)
    (koalaFrobeniusConjugate 1 D)
    (koalaFrobeniusConjugate 2 D)
    (koalaFrobeniusConjugate 3 D)
    (koalaFrobeniusConjugate 4 D)
    (koalaFrobeniusConjugate 5 D)
    (koalaFrobeniusConjugate 6 D)
    (koalaFrobeniusConjugate 0 R)
    (koalaFrobeniusConjugate 1 R)
    (koalaFrobeniusConjugate 2 R)
    (koalaFrobeniusConjugate 3 R)
    (koalaFrobeniusConjugate 4 R)
    (koalaFrobeniusConjugate 5 R)
    (hconj 0) (hconj 1) (hconj 2) (hconj 3) (hconj 4) (hconj 5)
    (koalaFrobeniusConjugate_six D)
  have hDzero : koalaFrobeniusConjugate 0 D = D := rfl
  simpa only [koalaCyclicCompatibilitySix, koalaCyclicNormSix, R,
    hDzero] using h

/-- Equal cyclic norms are exactly the condition under which every
semilinear image obeys the six-cycle compatibility equation. -/
theorem koalaCyclicCompatibilitySix_eq_zero_of_norm_eq
    (A B D : IRSProfile.Field[X])
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B) :
    koalaCyclicCompatibilitySix A B
        (A * D + B * D.map koalaSexticFrobenius.toRingHom) = 0 := by
  rw [koalaCyclicCompatibilitySix_semilinear, hnorm, sub_self, zero_mul]

theorem koalaFrobeniusConjugate_eq_of_map_eq
    (G : IRSProfile.Field[X])
    (hG : G.map koalaSexticFrobenius.toRingHom = G) (n : Nat) :
    koalaFrobeniusConjugate n G = G := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate, ih, hG]

/-- Multiplication of the forcing term by a Frobenius-fixed polynomial pulls
straight through the compatibility operator. -/
theorem koalaCyclicCompatibilitySix_mul_fixed
    (A B G R : IRSProfile.Field[X])
    (hG : G.map koalaSexticFrobenius.toRingHom = G) :
    koalaCyclicCompatibilitySix A B (G * R) =
      G * koalaCyclicCompatibilitySix A B R := by
  simp only [koalaCyclicCompatibilitySix,
    koalaFrobeniusConjugate_mul,
    koalaFrobeniusConjugate_eq_of_map_eq G hG]
  ring

/-- A fixed-scalar multiple of an inhomogeneous forcing has zero
compatibility whenever it equals another fixed-scalar multiple of a genuine
semilinear image and the two coefficient norms agree. -/
theorem koalaCyclicCompatibilitySix_eq_zero_of_fixed_factorization
    (A B D R G H : IRSProfile.Field[X])
    (hGfixed : G.map koalaSexticFrobenius.toRingHom = G)
    (hHfixed : H.map koalaSexticFrobenius.toRingHom = H)
    (hG : G ≠ 0)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hfactor :
      G * R = H *
        (A * D + B * D.map koalaSexticFrobenius.toRingHom)) :
    koalaCyclicCompatibilitySix A B R = 0 := by
  have hcompat := congrArg (koalaCyclicCompatibilitySix A B) hfactor
  rw [koalaCyclicCompatibilitySix_mul_fixed A B G R hGfixed,
    koalaCyclicCompatibilitySix_mul_fixed A B H
      (A * D + B * D.map koalaSexticFrobenius.toRingHom) hHfixed,
    koalaCyclicCompatibilitySix_eq_zero_of_norm_eq A B D hnorm,
    mul_zero] at hcompat
  exact (mul_eq_zero.mp hcompat).resolve_left hG

theorem score6400_nodal_map_frobenius
    (E : Finset IRSProfile.Index) :
    (Lagrange.nodal E (fun i ↦ IRSProfile.domain i)).map
        koalaSexticFrobenius.toRingHom =
      Lagrange.nodal E (fun i ↦ IRSProfile.domain i) := by
  simpa only [outsideAgreementLocator, Finset.sdiff_empty] using
    outsideAgreementLocator_map IRSProfile.domain koalaSexticFrobenius
      koalaSexticFrobenius_fixed_domain E ∅

/-- Nodal locators in the production evaluation domain are fixed by
Frobenius, so they can be cancelled from a scaled owner equation before
testing compatibility. -/
theorem score6400_koalaCyclicCompatibilitySix_eq_zero_of_nodal_keyEquation
    (E Fixed : Finset IRSProfile.Index)
    (A B D R : IRSProfile.Field[X])
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hkey :
      Lagrange.nodal E (fun i ↦ IRSProfile.domain i) * R =
        Lagrange.nodal Fixed (fun i ↦ IRSProfile.domain i) *
          (A * D + B * D.map koalaSexticFrobenius.toRingHom)) :
    koalaCyclicCompatibilitySix A B R = 0 := by
  exact koalaCyclicCompatibilitySix_eq_zero_of_fixed_factorization
    A B D R
    (Lagrange.nodal E (fun i ↦ IRSProfile.domain i))
    (Lagrange.nodal Fixed (fun i ↦ IRSProfile.domain i))
    (score6400_nodal_map_frobenius E)
    (score6400_nodal_map_frobenius Fixed)
    Lagrange.nodal_ne_zero hnorm hkey

end BCHKSInhomogeneousCyclicCompatibility6400
end ProximityPrize.SubmissionLower
