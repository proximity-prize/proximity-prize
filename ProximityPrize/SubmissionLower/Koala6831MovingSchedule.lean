import ProximityPrize.SubmissionLower.Koala6831MovingAdaptive

namespace ProximityPrize.SubmissionLower.Koala6831MovingAdaptive

open RCN081 RCN095 RCN130 RCN156 RCN234 RCN266
open LocatorBatchProductRoute LocatorFactorAggregate LocatorLowQuotient
open Koala6831MovingSources Koala6831MovingStages Koala6831Moving

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

def postRoomCap : FlagDegree := ⟨15213, 108, 30⟩

private theorem fuel_pos_of_post_room_cap (s : Stage) (f : FlagDegree)
    (hr : 0 < f.all) (hcap : Below f postRoomCap) : 0 < s.numbers.fuel f := by
  have hy : 0 < middle f := by unfold middle; omega
  have ht : 0 < total f := by unfold total; omega
  have hsT : total postRoomCap ≤ s.numbers.totalCap := by cases s <;> decide +kernel
  have hsY : middle postRoomCap ≤ s.numbers.middleCap := by cases s <;> decide +kernel
  have hsR : postRoomCap.all ≤ s.numbers.slopeCap := by cases s <;> decide +kernel
  unfold LocatorPhase6800Oracle.SourceNumbers.fuel
  apply Nat.lt_of_succ_le
  apply le_min
  · exact (Nat.le_div_iff_mul_le ht).2 (by
      simpa only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add] using hcap.2.2.trans hsT)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hy).2 (by
        simpa only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add] using hcap.2.1.trans hsY)
    · exact (Nat.le_div_iff_mul_le hr).2 (by
        simpa only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add] using hcap.1.trans hsR)

private theorem below_trans {a b c : FlagDegree} (hab : Below a b) (hbc : Below b c) : Below a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩

structure ExhaustedPass (s : Stage) (nodes u₀ u₁ : I → K)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H)) where
  residue : Finset (RegularIndex H)
  subset_incoming : residue ⊆ A
  stopped : residue = ∅ ∨ ¬ adaptiveGate s.numbers (aggregateFlag H residue)
  partners : ∀ F ∈ A \ residue, ∃ Q : MvPolynomial (Fin 4) K,
    IsRelPrime F.1 Q ∧ Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
      (s.numbers.totalCap + s.numbers.slopeCap) s.numbers.middleCap s.numbers.slopeCap ∧
    ∀ i, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity Q

theorem exists_exhausted_adaptive_pass [CharP K 2130706433]
    (s : Stage) (B : FlowData K) (nodes u₀ u₁ normalized : I → K)
    (hcard : Fintype.card I ≤ 262144)
    (h₀ : ∀ i, B.d0.eval (nodes i) * u₀ i + B.c0.eval (nodes i) =
      B.a0.eval (nodes i) * normalized i)
    (h₁ : ∀ i, B.d0.eval (nodes i) * u₁ i + B.c1.eval (nodes i) =
      B.a1.eval (nodes i) * normalized i)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ 9554)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ weight + 9554)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hfield : A.card < ENat.card K) (hcap : Below (aggregateFlag H A) postRoomCap)
    (htrans : ∀ F ∈ A, ¬ F.1 ∣ B.flow F.1) :
    Nonempty (ExhaustedPass s nodes u₀ u₁ H A) := by
  let active (U : Finset (RegularIndex H)) := adaptiveGate s.numbers (aggregateFlag H U)
  let pays (F : RegularIndex H) := ∃ Q : MvPolynomial (Fin 4) K,
    IsRelPrime F.1 Q ∧ Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
      (s.numbers.totalCap + s.numbers.slopeCap) s.numbers.middleCap s.numbers.slopeCap ∧
    ∀ i, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity Q
  have hchar : s.numbers.slopeCap < 2130706433 := by cases s <;> decide +kernel
  obtain ⟨U, hsub, hstop, hpays⟩ := exhaust_finset_stage A active pays (fun R hRA hR hactive => by
    have hsmall : R.card < ENat.card K := by
      have h := Finset.card_le_card hRA
      exact (by exact_mod_cast h : (R.card : ENat) ≤ A.card).trans_lt hfield
    have hr := aggregateFlag_pos H hR
    exact exists_adaptive_exit_partners s B nodes u₀ u₁ normalized hcard hchar h₀ h₁ hden hminor
      H R hR hsmall hr (fuel_pos_of_post_room_cap s _ hr
        (below_trans (aggregateFlag_mono H hRA) hcap)) hactive (fun F hF => htrans F (hRA hF)))
  exact ⟨⟨U, hsub, hstop, hpays⟩⟩

end

end ProximityPrize.SubmissionLower.Koala6831MovingAdaptive
