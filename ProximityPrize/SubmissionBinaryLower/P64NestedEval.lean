import ProximityPrize.SubmissionBinaryLower.P64Algebra

namespace ProximityPrize.SubmissionBinaryLower

/-- Substitute `Z = z` and then `Y = P(X)` in a polynomial represented as
`F[Z][X][Y]`. -/
noncomputable def triEval {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F) :
    Polynomial F :=
  Polynomial.eval P
    (Polynomial.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) Q)

end ProximityPrize.SubmissionBinaryLower
