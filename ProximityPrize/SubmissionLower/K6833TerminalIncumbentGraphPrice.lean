/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
/- Retuned from Lucieno, Proximity Prize PR 618 (Apache-2.0). All moving derivative orders are allowed by the coefficient identity. -/
import ProximityPrize.SubmissionLower.K6833TerminalLedger
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentGraph
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentPrices

set_option Elab.async false
set_option maxHeartbeats 2500000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.K6833Residual

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

private theorem moving_coefficient (a b d scale : ℕ) (hd : 0 < d) (hs : 3*d ∣ scale) :
    ((524288*a+3*65539*b)*(scale/3))/d =
      524288*a*(scale/(3*d))+65539*b*(scale/d) := by
  obtain ⟨v,rfl⟩ := hs
  have d3 : 0 < 3*d := by omega
  have h3 : 3*d*v/3=d*v := by rw [Nat.mul_assoc]; exact Nat.mul_div_cancel_left _ (by decide)
  have h3d : 3*d*v/(3*d)=v := Nat.mul_div_cancel_left _ d3
  have hD : 3*d*v/d=3*v := by
    rw [show 3*d*v=d*(3*v) by ring]
    exact Nat.mul_div_cancel_left _ hd
  rw [h3,h3d,hD,show (524288*a+3*65539*b)*(d*v)=d*((524288*a+3*65539*b)*v) by ring,
    Nat.mul_div_cancel_left _ hd]
  ring

theorem originalGraphNumerator_eq_numeratorDir {K : Type} [Field K]
    {F : MvPolynomial (Fin 4) K} (f : Envelope)
    (hr : 3 ≤ f.slope) (hy : f.slope+2 ≤ f.middle)
    (cfg : Fin 3 → JetProfile) (source : Fin 3 → Source F)
    (hflag : ∀ j, (source j).flag = (cfg j).moving)
    (horder : ∀ j, (cfg j).derivativeOrder + 1 = (source j).d)
    (hdiv : ∀ j, 3 * (source j).d ∣ residualPriceScale)
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
      ← hflag j, horder j]
    congr 1
    exact moving_coefficient _ _ _ _ (by simp [Source.d]) (hdiv j)

end ProximityPrize.SubmissionLower.K6833Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
