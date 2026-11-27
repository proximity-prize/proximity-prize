import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.R6960Low6960GeometryCut
import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleCaps
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleBound
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive
import ProximityPrize.SubmissionLower.R6960Low6960Retained
import ProximityPrize.SubmissionLower.Final50Price

set_option Elab.async false

-- merged module R6960Low6960WeightedTally
section Merged_R6960Low6960WeightedTally

-- merged module R6960Low6960SharedThirdCut
section Merged_R6960Low6960SharedThirdCut

set_option Elab.async false
set_option autoImplicit false

namespace Low6960SharedThirdCut
noncomputable section

open Finset Polynomial MvPolynomial
open P3 (I K)


open scoped BigOperators ENat Polynomial
open K1_13 (Row Geom Shape shape InBox chart atJet extend embed)
open K1_13_6 (GeoJets GeoField HighChart markIdeal evalGeneric toGeneric intersectionIdeal
  cycleLength divisorIdeal separant CurveSections Pieces)
open K1_13_6_1 (mem_markIdeal mark_curve)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective)
open K1_13_6_3 (dimension cycleWeight)
open K1_13_7_1 (derivative_in_box shape_chamber)
open P0_9_6_1_2 (exists_value_cut)



open P0_9_6_3 (canonical_unique cycleWeight_ge)
open K1_14_6 (curve_degree_nat)

























































































































































































































end
end Low6960SharedThirdCut

end Merged_R6960Low6960SharedThirdCut

-- merged module R6960Low6960SharedCount
section Merged_R6960Low6960SharedCount

set_option Elab.async false
set_option maxHeartbeats 1700000
set_option maxRecDepth 20000
namespace Low6960SharedCount
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape chart extend ceilDiv)
open K1_13_6 (GeoJets HighChart HighMark toGeneric intersectionIdeal cycleLength separant)
open K1_13_6_1_2 (VanishesTo pair_height)
open K1_13_6_2 (actualPoint)









open Finset
open scoped Polynomial BigOperators
attribute [local instance] Classical.propDecidable



























































































































































































































































































end
end Low6960SharedCount

end Merged_R6960Low6960SharedCount

-- merged module R6960Low6960WeightedTally
section Merged_R6960Low6960WeightedTally

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace Low6960WeightedTally
noncomputable section

open P3 (K)
open K1_13 (Row shape ceilDiv)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_1_2 (VanishesTo pair_height)









open scoped Polynomial BigOperators ENat

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}
  {S : Set (Ideal GeoJets)}














































































































































end
end Low6960WeightedTally

end Merged_R6960Low6960WeightedTally

end Merged_R6960Low6960WeightedTally

-- merged module R6960Low6960WeightedCut
section Merged_R6960Low6960WeightedCut

-- merged module KoalaSeparantCharge
section Merged_KoalaSeparantCharge
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 750000
namespace KoalaFarBridge
noncomputable section
open K1_13 (Row Geom shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric genericCoeffs separant cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo)
open MvPolynomial
open scoped Polynomial BigOperators





































theorem separant_box (f : Row 4) : InBox (shape (separant f))
    ⟨(shape f).b-1,(shape f).j-3,(shape f).t-1⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · change ((pderiv 3) f).totalDegree ≤ f.totalDegree - (1 : Fin 4 → ℕ) 3
    simpa only [weightedTotalDegree_one] using
      weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) (3 : Fin 4) f
  · change indexDegree ((pderiv 3) f) ≤ indexDegree f - (3 : Fin 4).val
    simpa only [← K1_13_1.indexDegree_eq] using
      weightedTotalDegree_pderiv_le_sub Fin.val (3 : Fin 4) f
  · exact degreeOf_pderiv_le_sub_one 3 f
theorem separant_proper {f : Row 4} (hf : f ≠ 0) (ht : 0 < f.degreeOf 3)
    (hchar : f.degreeOf 3 < K1.p) : ¬ f ∣ separant f := by
  have : CharP Geom K1.p := charP_of_injective_ringHom K1_13.embed.injective K1.p
  have : CharP (Polynomial Geom) K1.p := charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hcast : (f.degreeOf 3 : (Polynomial Geom)) ≠ 0 := fun hz => (not_le_of_gt hchar)
    (Nat.le_of_dvd ht ((CharP.cast_eq_zero_iff (Polynomial Geom) K1.p _).mp hz))
  have hn : separant f ≠ 0 := pderiv_ne_zero_of_natCast_ne_zero 3 f hcast
  rintro ⟨g,hg⟩
  have hgz : g ≠ 0 := fun hz => hn (by simp [hg,hz])
  have hd := degreeOf_pderiv_le_sub_one (3 : Fin 4) f
  change (separant f).degreeOf 3 ≤ _ at hd
  rw [hg,degreeOf_mul_eq hf hgz] at hd
  omega























































































end
end KoalaFarBridge

end Merged_KoalaSeparantCharge

-- merged module R6960Low6960WeightedCut
section Merged_R6960Low6960WeightedCut

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace Low6960WeightedCut
noncomputable section

open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric separant)
open K1_13_6_1_2 (VanishesTo)




open scoped ENat











































































































































end
end Low6960WeightedCut

end Merged_R6960Low6960WeightedCut

end Merged_R6960Low6960WeightedCut
