import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false

namespace StructuralList

open CJ0

/-- Number of separant factors that clears all the shortened Taylor coefficients. -/
def exponent (length : ℕ) : ℕ := max (2 * length - 7) (length - 2)

/-- Total degree of a numerator or common denominator. -/
def totalCap (s : Source) (length : ℕ) : ℕ :=
  1 + exponent length * (s.B - 1)

/-- Weighted derivative degree of a numerator or common denominator. -/
def indexCap (s : Source) (length : ℕ) : ℕ :=
  exponent length * (s.J - 2) + length - 1

/-- Degree in the highest derivative of a numerator or common denominator. -/
def topCap (s : Source) (length : ℕ) : ℕ :=
  min (exponent length * (s.C - 1) + length - 2) (indexCap s length / 2)

def InBand (s : Source) (length : ℕ) (P : InitialRing 2) : Prop :=
  P.totalDegree ≤ totalCap s length ∧
    P.weightedTotalDegree Fin.val ≤ indexCap s length ∧
    P.degreeOf (Fin.last 2) ≤ topCap s length

structure ShortBand (s : Source) (length : ℕ) (T : Chart 2) : Prop where
  denominator : InBand s length T.denominator
  numerator : ∀ i, InBand s length (T.numerator i)

end StructuralList
