import Mathlib.Algebra.MvPolynomial.Eval
import ProximityPrize.SubmissionLower.Koala6844VirtualHighContact
import ProximityPrize.SubmissionLower.Koala6844NormalizationData



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial Koala6844Normalization

variable {K : Type*} [Field K]

abbrev GermCarrier (K : Type*) [Field K] := Polynomial (MvPolynomial (Fin 3) K)

noncomputable def liftPolynomial : Polynomial K →+* GermCarrier K :=
  Polynomial.mapRingHom MvPolynomial.C

noncomputable def coordinatePolynomial (i : Fin 3) : GermCarrier K :=
  Polynomial.C (MvPolynomial.X i)

noncomputable def specializeGerm (P : Polynomial K) (s t : K) :
    GermCarrier K →+* Polynomial K :=
  Polynomial.eval₂RingHom (MvPolynomial.eval₂Hom Polynomial.C ![P, Polynomial.C s, Polynomial.C t])
    Polynomial.X

@[simp] theorem specialize_liftPolynomial (P Q : Polynomial K) (s t : K) :
    specializeGerm P s t (liftPolynomial Q) = Q := by
  have h : (specializeGerm P s t).comp liftPolynomial = RingHom.id (Polynomial K) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [specializeGerm, liftPolynomial]
    · simp [specializeGerm, liftPolynomial]
  exact DFunLike.congr_fun h Q

@[simp] theorem specialize_value (P : Polynomial K) (s t : K) :
    specializeGerm P s t (coordinatePolynomial 0) = P := by
  simp [specializeGerm, coordinatePolynomial]

@[simp] theorem specialize_first_seed (P : Polynomial K) (s t : K) :
    specializeGerm P s t (coordinatePolynomial 1) = Polynomial.C s := by
  simp [specializeGerm, coordinatePolynomial]

@[simp] theorem specialize_second_seed (P : Polynomial K) (s t : K) :
    specializeGerm P s t (coordinatePolynomial 2) = Polynomial.C t := by
  simp [specializeGerm, coordinatePolynomial]

noncomputable def virtualEquation (A : Fin 2 → Polynomial K) (B : Polynomial K)
    (z : Fin 3) : GermCarrier K :=
  (liftPolynomial (A 0) + coordinatePolynomial z * liftPolynomial (A 1)) *
    coordinatePolynomial 0 - coordinatePolynomial z * liftPolynomial B

noncomputable def ordinaryIdeal (x u : K) : Ideal (GermCarrier K) :=
  Ideal.span ({liftPolynomial (X - Polynomial.C x),
    coordinatePolynomial 0 - liftPolynomial (Polynomial.C u)} : Set (GermCarrier K))

noncomputable def divisorIdeal (d : Polynomial K) (q : GermCarrier K) :
    Ideal (GermCarrier K) :=
  Ideal.span ({liftPolynomial d,q} : Set (GermCarrier K))

variable {I : Type*} [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}


end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
