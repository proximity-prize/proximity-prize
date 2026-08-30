import ProximityPrize.SubmissionLower.ContactAlignmentParameters
import ProximityPrize.SubmissionLower.ContactFlagRankKernel

namespace ProximityPrize.SubmissionLower.ContactInterpolation

open ProximityPrize.Benchmark
open scoped BigOperators

noncomputable section

variable (K : Type*) [Field K]

abbrev Poly := MvPolynomial (Fin 3) K

def seedAffine (u₀ u₁ : K) : Poly K :=
  MvPolynomial.C u₀ + MvPolynomial.monomial (Finsupp.single 2 1) u₁

def globalExponents (D w L s : ℕ) : Set (Fin 4 →₀ ℕ) :=
  {d | d 1 + d 3 ≤ L ∧ d 2 ≤ s ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D}

def globalCoefficientBox (D w L s : ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K (globalExponents D w L s)

end

end ProximityPrize.SubmissionLower.ContactInterpolation
