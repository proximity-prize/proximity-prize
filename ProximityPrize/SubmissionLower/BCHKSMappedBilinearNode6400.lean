import ProximityPrize.SubmissionLower.BCHKSLocatorAffineLaneNodes6400

/-! # Ring-generic transport of a bilinear node equation -/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Mapping coefficients commutes with evaluation at a mapped node and with
a bilinear value equation. -/
theorem mapped_bilinear_eval_eq
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (C A B : R[X]) (x r s : R)
    (h : C.eval x = A.eval x * r + B.eval x * s) :
    (C.map f).eval (f x) =
      (A.map f).eval (f x) * f r +
        (B.map f).eval (f x) * f s := by
  rw [Polynomial.eval_map_apply, Polynomial.eval_map_apply,
    Polynomial.eval_map_apply]
  rw [h, map_add, map_mul, map_mul]

/-- The value-level ring-homomorphism calculation used when the polynomial
evaluation transports are kept as separate opaque steps. -/
theorem map_bilinear_value_eq
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (a b r s : R) :
    f (a * r + b * s) = f a * f r + f b * f s := by
  rw [map_add, map_mul, map_mul]

/-- Two bilinear node equations are compatible with a common polynomial
multiplier on their homogeneous lanes.  This value-level interface keeps
large concrete interpolation terms out of ring normalization. -/
theorem bilinear_node_eq_multiplier
    {F : Type} [CommRing F]
    (C₁ A₁ B₁ M A B C : F[X]) (x r s : F)
    (hraw : C₁.eval x = A₁.eval x * r + B₁.eval x * s)
    (hnormalized : C.eval x = A.eval x * r + B.eval x * s)
    (hA : A₁ = M * A) (hB : B₁ = M * B) :
    C₁.eval x = (M * C).eval x := by
  rw [hraw, hA, hB, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_mul, hnormalized]
  ring

/-- Mapping an inhomogeneous polynomial factorization preserves its exact
shape. -/
theorem map_inhomogeneous_factorization
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (L K A B C W V : R[X])
    (h : L * K = A * W + B * V - C) :
    L.map f * K.map f =
      A.map f * W.map f + B.map f * V.map f - C.map f := by
  simpa only [Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_sub] using congrArg (Polynomial.map f) h

/-- Injective coefficient maps preserve a nonzero polynomial evaluation,
even across two nested coefficient rings. -/
theorem mapped_twice_eval_ne_zero
    {F R S : Type} [CommRing F] [CommRing R] [CommRing S]
    (g : F →+* R) (f : R →+* S)
    (hg : Function.Injective g) (hf : Function.Injective f)
    (P : F[X]) (x : F) (h : P.eval x ≠ 0) :
    ((P.map g).map f).eval (f (g x)) ≠ 0 := by
  rw [Polynomial.eval_map_apply, Polynomial.eval_map_apply]
  simpa only [map_zero] using hf.ne (hg.ne h)

/-- A raw affine node relation which is a common multiplier of a normalized
one forces that multiplier times the global quotient to vanish at any node
where the complementary locator is nonzero. -/
theorem multiplier_quotient_eval_eq_zero
    {F : Type} [Field F]
    (L K A B C W V C₁ A₁ B₁ M : F[X]) (x w v : F)
    (hglobal : L * K = A * W + B * V - C)
    (hW : W.eval x = w) (hV : V.eval x = v)
    (hraw : C₁.eval x = A₁.eval x * w + B₁.eval x * v)
    (hC : C₁ = M * C) (hA : A₁ = M * A) (hB : B₁ = M * B)
    (hL : L.eval x ≠ 0) :
    (M * K).eval x = 0 := by
  have hglobalEval := congrArg (fun P : F[X] ↦ P.eval x) hglobal
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_mul, hW, hV] at hglobalEval
  have hCEval := congrArg (fun P : F[X] ↦ P.eval x) hC
  have hAEval := congrArg (fun P : F[X] ↦ P.eval x) hA
  have hBEval := congrArg (fun P : F[X] ↦ P.eval x) hB
  rw [Polynomial.eval_mul] at hCEval hAEval hBEval
  have hscaled :
      M.eval x * (L.eval x * K.eval x) = 0 := by
    calc
      M.eval x * (L.eval x * K.eval x) =
          M.eval x * (A.eval x * w + B.eval x * v - C.eval x) := by
            rw [hglobalEval]
      _ = (M.eval x * A.eval x) * w +
            (M.eval x * B.eval x) * v - M.eval x * C.eval x := by ring
      _ = A₁.eval x * w + B₁.eval x * v - C₁.eval x := by
            rw [← hAEval, ← hBEval, ← hCEval]
      _ = 0 := by rw [← hraw, sub_self]
  have hreassociated :
      L.eval x * (M.eval x * K.eval x) = 0 := by
    calc
      L.eval x * (M.eval x * K.eval x) =
          M.eval x * (L.eval x * K.eval x) := by ring
      _ = 0 := hscaled
  rw [Polynomial.eval_mul]
  exact (mul_eq_zero.mp hreassociated).resolve_left hL

end ProximityPrize.SubmissionLower
