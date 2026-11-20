import ProximityPrize.SubmissionLower.Koala6831MovingAdaptive


namespace ProximityPrize.SubmissionLower.Koala6831MovingAdaptive

open RCN081 RCN095 RCN130 RCN156 RCN234 RCN266
open LocatorBatchProductRoute LocatorFactorAggregate LocatorLowQuotient
open Koala6831MovingStages Koala6831Moving

noncomputable section

variable {K : Type} [Field K]
variable {I : Type*} [Fintype I]
local instance movingScheduleDecidableEq : DecidableEq K := Classical.decEq K

abbrev aggregateFlag (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H)) : FlagDegree :=
  originalCumulativeFlag (regularProduct H A)

theorem aggregateFlag_mono (H : MvPolynomial (Fin 4) K)
    {U A : Finset (RegularIndex H)} (hUA : U ⊆ A) :
    Below (aggregateFlag H U) (aggregateFlag H A) := by
  have hd : regularProduct H U ∣ regularProduct H A :=
    Finset.prod_dvd_prod_of_subset U A (fun F => F.1) hUA
  have hn := regularProduct_ne_zero H A
  have ⟨hrU, hyU, htU⟩ := originalCumulativeFlag_cumulative (regularProduct H U)
  have ⟨hrA, hyA, htA⟩ := originalCumulativeFlag_cumulative (regularProduct H A)
  refine ⟨?_, ?_, ?_⟩
  · rw [aggregateFlag, aggregateFlag, hrU, hrA]
    exact weightedTotalDegree_le_of_dvd residualSWeights _ _ hd hn
  · change middle (originalCumulativeFlag (regularProduct H U)) ≤
      middle (originalCumulativeFlag (regularProduct H A))
    unfold middle
    rw [hyU, hyA]
    exact weightedTotalDegree_le_of_dvd residualYSWeights _ _ hd hn
  · change total (originalCumulativeFlag (regularProduct H U)) ≤
      total (originalCumulativeFlag (regularProduct H A))
    unfold total
    rw [htU, htA]
    exact weightedTotalDegree_le_of_dvd residualTotalWeights _ _ hd hn

theorem aggregateFlag_pos (H : MvPolynomial (Fin 4) K)
    {A : Finset (RegularIndex H)} (hA : A.Nonempty) : 0 < (aggregateFlag H A).all := by
  obtain ⟨F, hF⟩ := hA
  have hFpos := regularCumulativeFlag_positive H F
  have hd : F.1 ∣ regularProduct H A :=
    ⟨regularCofactor H A F, (regularFactor_mul_cofactor H A F hF).symm⟩
  rw [show (regularCumulativeFlag H F).all = wt residualSWeights F.1 from
    (originalCumulativeFlag_cumulative F.1).1] at hFpos
  rw [aggregateFlag, (originalCumulativeFlag_cumulative (regularProduct H A)).1]
  exact hFpos.trans_le (weightedTotalDegree_le_of_dvd residualSWeights _ _ hd
    (regularProduct_ne_zero H A))








end

end ProximityPrize.SubmissionLower.Koala6831MovingAdaptive
