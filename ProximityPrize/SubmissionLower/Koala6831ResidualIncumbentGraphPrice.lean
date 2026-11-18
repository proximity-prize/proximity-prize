import ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentLedger
import ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentGraph
import ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentPrices

set_option Elab.async false
set_option maxHeartbeats 2500000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.Koala6831Residual

open scoped BigOperators
open RCN095 LocatorHybridCells MovingFiberThreeSources6811

private theorem originalGraphMovingTail_eq (f : Envelope)
    (hr : 3 ≤ f.slope) (hy : f.slope+2 ≤ f.middle) :
    rawMovingTail 0 f =
      MovingFiberRetainedStage6811.rawFirstFlag f.total f.middle f.slope := by
  rcases f with ⟨r,y,t⟩
  change 3 ≤ r at hr
  change r+2 ≤ y at hy
  simp only [MovingFiberRetainedStage6811.rawFirstFlag, cellA, cellB, cellS,
    RCN198.center, RCN198.direction, unitYZFlag, RCN327.w]
  change (⟨131073*(t-y),131073*(y-r),131073*r-1⟩ : FlagDegree) =
    ⟨0+2*(t-y)+131071*(t-y),
      1+(2*(y-r-1)+1)+131071*(y-r-1+1),
      0+(2*(r-2)+3)+131071*(r-2+2)⟩
  congr 1 <;> omega

private theorem originalFirstDirection_eq (f : Envelope) (j : Fin 3) :
    weightedCusp 0 f j = HFreeDir6813.hfreeFirstDir f.total f.middle f.slope j := by
  simp only [weightedCusp, cusp, HFreeDir6813.hfreeFirstDir, HFreeDir6813.hfreeFlagDir,
    HFreeDir6813.cuspFlag, Nat.zero_min, Nat.add_zero, Nat.sub_zero]
  rfl

private theorem sum_finRange_three (g : Fin 3 → ℕ) :
    ((List.finRange 3).map g).sum = ∑ j : Fin 3, g j := by
  rw [Fin.sum_univ_three, show List.finRange 3 = [0,1,2] by decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private theorem moving_coefficient_at_two (a b : ℕ) :
    ((524288*a+3*65539*b)*(residualPriceScale/3))/2 =
      524288*a*(residualPriceScale/(3*2))+65539*b*(residualPriceScale/2) := by
  change ((524288*a+3*65539*b)*90656106460920)/2 =
      524288*a*45328053230460+65539*b*135984159691380
  simp only [Nat.add_mul]
  omega

theorem originalGraphNumerator_eq_numeratorDir {K : Type} [Field K]
    {F : MvPolynomial (Fin 4) K} (f : Envelope)
    (hr : 3 ≤ f.slope) (hy : f.slope+2 ≤ f.middle)
    (cfg : Fin 3 → JetProfile) (source : Fin 3 → Source F)
    (hflag : ∀ j, (source j).flag = (cfg j).moving)
    (horder : ∀ j, (cfg j).derivativeOrder = 1 ∧ (source j).d = 2)
    (left : FlagDegree) :
    jetGraphNumerator TailCorrections.original f cfg left =
      HFreeDir6813.numeratorDir source residualPriceScale f.total f.middle f.slope left := by
  have hn := normalTail_zero_eq_cellNormal f
  have hdir (j : Fin 3) : unit j = MovingFiberThreeSources6811.direction j := rfl
  have haxis (p : FlagDegree) (j : Fin 3) : byAxis p j = weight p j := rfl
  unfold jetGraphNumerator graphFixed HFreeDir6813.numeratorDir
  simp only [sum_finRange_three, TailCorrections.original, hn, hdir, haxis, originalFirstDirection_eq]
  rw [Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    change _ * _ * (residualPriceScale/3) = _
    ac_rfl
  · apply Finset.sum_congr rfl
    intro j _
    unfold movingCharge
    simp only [hn, originalGraphMovingTail_eq f hr hy, haxis, hdir,
      ← hflag j, (horder j).1, (horder j).2]
    congr 1
    apply moving_coefficient_at_two

end ProximityPrize.SubmissionLower.Koala6831Residual
