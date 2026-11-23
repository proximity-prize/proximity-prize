import ProximityPrize.SubmissionLower.KoalaTaperExtraCore
import ProximityPrize.SubmissionLower.KoalaTaperExtraReceiptA
import ProximityPrize.SubmissionLower.KoalaTaperExtraReceiptB
import ProximityPrize.SubmissionLower.KoalaTaperExtraReceiptC
set_option autoImplicit false
namespace KoalaTaperExtra
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget Low48PrimaryPivot
open PolynomialDifferential ReedSolomon.HiddenDerivative

theorem node_rank (x y : Geom) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localCap := by
  apply rank_of_receipts x y
  · rw [rawA,rawB,rawC]
  · have a := debit_le_binCompute extraA (by decide)
    have b := debit_le_binCompute extraB (by decide)
    have c := debit_le_binCompute extraC (by decide)
    rw [binA] at a
    rw [binB] at b
    rw [binC] at c
    omega

#print axioms node_rank
end KoalaTaperExtra
