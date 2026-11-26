import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_ReedSolomon_MutualCorrelatedAgreement_Pairs_Family
set_option Elab.async false
/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/




/-!
# Exact correlated-pair witnesses under field extensions

An exact correlated-pair witness consists of two base-field message polynomials whose affine
specialization is a given candidate and whose full common agreement set is the candidate's
agreement set. Injectivity of a field homomorphism lets this witness descend from an extension.

## Main definitions

* `ReedSolomon.HasExactCorrelatedPair`: an exact witness for a challenge and candidate polynomial.

## Main statements

* `ReedSolomon.HasExactCorrelatedPair.descend`: exact witnesses descend to the base field.

## References

* [DKT26]
-/

section

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n : ℕ}

/-- A pair of degree-bounded base-field polynomials exactly explains a candidate polynomial and
its full agreement set at one affine-line challenge. -/
def HasExactCorrelatedPair (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (k : ℕ) (z : E) (P : (Polynomial E)) : Prop :=
  ∃ pair : (Polynomial F) × (Polynomial F),
    pair.1.degree < k ∧ pair.2.degree < k ∧
      P = correlatedPairSpecialization ι z pair ∧
      polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι (f i) + z * ι (g i)) P =
          commonPolynomialAgreementSet domain f g pair.1 pair.2

/-- An exact correlated-pair witness for a mapped candidate descends to the base field. -/
theorem HasExactCorrelatedPair.descend (domain : Fin n ↪ F) (f g : Fin n → F)
    (ι : F →+* E) (k : ℕ) (z : F) (P : (Polynomial F))
    (h : HasExactCorrelatedPair domain f g ι k (ι z) (P.map ι)) :
    HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨pair, hleft, hright, heq, hagree⟩ := h
  refine ⟨pair, hleft, hright, ?_, ?_⟩
  · apply Polynomial.map_injective ι ι.injective
    simpa [correlatedPairSpecialization] using heq
  · have hline : (fun i ↦ ι (f i) + ι z * ι (g i)) =
        (fun i ↦ ι (f i + z * g i)) := by
      funext i
      simp
    rw [hline, polynomialAgreementSet_map] at hagree
    simpa [RingHom.id_apply] using hagree

end ReedSolomon
