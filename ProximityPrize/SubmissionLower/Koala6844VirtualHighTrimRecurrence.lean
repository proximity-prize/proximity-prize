import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Function

section Derivation

variable {K R A : Type*} [CommSemiring K]
  [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]

def clearedTail (D : Derivation K R R) (H f : R) : ℕ → R
  | 0 => D f
  | n + 1 => H * D (clearedTail D H f n) -
    ((2*n+1 : ℕ) : R) * clearedTail D H f n * D H




def trimmedNumerator (D : Derivation K R R) (H V W : R) : ℕ → R
  | 0 => V * D W - W * D V
  | n + 1 => V * H * D (trimmedNumerator D H V W n) -
    ((((n+2 : ℕ) : R) * H * D V) + (((2*n+1 : ℕ) : R) * V * D H)) *
      trimmedNumerator D H V W n

theorem map_trimmedNumerator (D : Derivation K R R) (δ : Derivation K A A)
    (H V W : R) (φ : R →+* A) (hφ : ∀ a : R, φ (D a) = φ H * δ (φ a))
    (s Q : A) (hs : δ s = 0) (hW : φ W = s * φ V * Q) (n : ℕ) :
    φ (trimmedNumerator D H V W n) =
      s * φ V^(n+2) * φ H^(2*n+1) * (δ^[n+1]) Q := by
  have powerDerivative (a : A) (k : ℕ) :
      δ (a^(k+1)) = ((k+1 : ℕ) : A) * a^k * δ a := by
    rw [δ.leibniz_pow]
    simp [nsmul_eq_mul, mul_assoc]
  induction n with
  | zero =>
    simp only [trimmedNumerator, map_sub, map_mul, hφ, hW, iterate_one, zero_add, mul_zero,
      pow_one, δ.leibniz, hs, smul_eq_mul, add_zero, pow_two]
    ring
  | succ n ih =>
    simp only [trimmedNumerator, map_sub, map_mul, map_add, map_natCast, hφ, ih,
      iterate_succ_apply' δ (n+1) Q]
    rw [show 2*(n+1)+1 = (2*n+1)+2 by omega,
      show n+1+2 = (n+2)+1 by omega]
    simp only [δ.leibniz, hs, smul_eq_mul,
      show n+2 = (n+1)+1 by omega, powerDerivative]
    simp only [pow_add, pow_one, pow_two]
    ring

theorem map_trimmedNumerator_eq_zero (D : Derivation K R R) (δ : Derivation K A A)
    (H V W : R) (φ : R →+* A) (hφ : ∀ a : R, φ (D a) = φ H * δ (φ a))
    (s Q : A) (hs : δ s = 0) (hW : φ W = s * φ V * Q) (n : ℕ)
    (vanishes : (δ^[n+1]) Q = 0) :
    φ (trimmedNumerator D H V W n) = 0 := by
  rw [map_trimmedNumerator D δ H V W φ hφ s Q hs hW, vanishes, mul_zero]

end Derivation

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
