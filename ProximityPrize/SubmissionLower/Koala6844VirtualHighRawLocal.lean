import ProximityPrize.SubmissionLower.Koala6844VirtualHighLocalOrder
import ProximityPrize.SubmissionLower.Koala6844VirtualHighRawTail


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic RCN135 RCN136 RCN219 RCN218
open MvPolynomial

noncomputable section

variable {K : Type} [Field K]

theorem rawTrimmedTail_succ (F V W : Carrier K) (j : ℕ) :
    rawTrimmedTail F V W (j+1) =
      V * implicitRegularity F * clearedImplicit F (rawTrimmedTail F V W j) -
        ((((j+2 : ℕ) : Carrier K) * implicitRegularity F * clearedImplicit F V) +
          (((2*j+1 : ℕ) : Carrier K) * V * clearedImplicit F (implicitRegularity F))) *
          rawTrimmedTail F V W j := by
  unfold rawTrimmedTail
  rw [trimmedNumerator]
  simp only [trimDerivation_apply]

theorem localOrder_rawTrimmedTail (F V W : Carrier K) (first pchar : ℕ) [CharP K pchar]
    (hpchar : pchar.Prime)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (height : C.height ≤ 2) (hirr : Irreducible F)
    (carrier_mem : surfaceMap (polynomialEmbedding K) F ∈ C)
    (separant_avoids : surfaceMap (polynomialEmbedding K) (implicitRegularity F) ∉ C)
    (divisor_avoids : surfaceMap (polynomialEmbedding K) V ∉ C)
    (first_mem : surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W first) ∈ C)
    (first_proper : ¬ F ∣ rawTrimmedTail F V W first) :
    ∃ μ : ℕ, 1 ≤ μ ∧
      (∃ s : Carrier K, s ∉ originalPrime C ∧
        s * rawTrimmedTail F V W first ∈ factorIdeal F ⊔ (originalPrime C)^μ) ∧
      ((∃ delay, 1 ≤ delay ∧ delay ≤ μ ∧
        surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W (first+delay)) ∉ C) ∨
        (∀ delay, surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W (first+delay)) ∈ C)) := by
  let H := implicitRegularity F
  let A (j : ℕ) := ((((first+j+2 : ℕ) : Carrier K) * H) * clearedImplicit F V) +
    ((((2*(first+j)+1 : ℕ) : Carrier K) * V) * clearedImplicit F H)
  let lead := V*H
  let T (j : ℕ) := rawTrimmedTail F V W (first+j)
  have proper : ∀ j, T (j+1) = lead * clearedImplicit F (T j) - A j * T j := by
    intro j
    dsimp only [T, H, lead, A]
    rw [← Nat.add_assoc, rawTrimmedTail_succ]
  have hlead : surfaceMap (polynomialEmbedding K) lead ∉ C := by
    rw [show lead = V * implicitRegularity F by rfl, map_mul]
    exact (inferInstance : C.IsPrime).mul_notMem divisor_avoids separant_avoids
  exact residual_local_order F lead A T pchar hpchar C height hirr carrier_mem separant_avoids
    first_mem first_proper hlead proper

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
