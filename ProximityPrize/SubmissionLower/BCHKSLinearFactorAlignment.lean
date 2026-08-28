import ProximityPrize.SubmissionLower.BCHKSHenselSetup

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators

variable {F : Type} [Field F]

/-- In the selected linear branch the primitive factor occurring at the
centering point is linear as well.  This is the basic reduction needed by a
separate linear-factor alignment argument. -/
theorem henselFactor_natDegree_eq_one_of_R_natDegree_eq_one
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree)
    (hR : Bivariate.natDegreeY R = 1) :
    Bivariate.natDegreeY H = 1 := by
  have hle : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
    HenselNumerators.natDegree_H_le_natDegree_R_of_hypotheses hHyp
  change H.natDegree = 1
  change R.natDegree = 1 at hR
  change H.natDegree ≤ R.natDegree at hle
  omega

/-- Equivalent `≤ 1` formulation, convenient immediately after staged
selection (where positivity and an upper degree cap are usually separate). -/
theorem henselFactor_natDegree_eq_one_of_R_natDegree_le_one
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree)
    (hRpos : 0 < Bivariate.natDegreeY R)
    (hRle : Bivariate.natDegreeY R ≤ 1) :
    Bivariate.natDegreeY H = 1 := by
  apply henselFactor_natDegree_eq_one_of_R_natDegree_eq_one hHyp hH
  omega

end ProximityPrize.SubmissionLower
