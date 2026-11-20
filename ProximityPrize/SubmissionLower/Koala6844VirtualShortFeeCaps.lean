import ProximityPrize.SubmissionLower.Koala6844VirtualShortResultant
import ProximityPrize.SubmissionLower.Koala6844VirtualShortGermPrices
import ProximityPrize.SubmissionLower.Koala6844ReceiptsExactBand


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Koala6844Receipts LocatorFactorAggregate
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 15000

private def secondFeeStop (r : ℕ) : ℕ :=
  ([127,126,125,124,123,122,121,120,118,117,116,114,113,111,109,107,105,103,101,98,
    94,90,85,79,73,65,57,48,38,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50]
      : List ℕ).getD (r-1) 0

private theorem checkedSecondFeeStop (r : ℕ) (hr₀ : 1 ≤ r) (hr₁ : r ≤ 50) :
    r ≤ secondFeeStop r ∧
    bandCovers firstAdaptiveFlag ⟨r,secondFeeStop r,secondFeeStop r⟩ firstAdaptiveGap = true ∧
    (r < secondFeeStop r →
      germPrice ⟨r,secondFeeStop r - 1,afterRooms.t⟩ (adaptivePartnerFlag secondAdaptiveFlag) ≤
        7000000000000000) := by
  refine ⟨?_,?_,?_⟩
  · interval_cases r <;> decide +kernel
  · rw [bandCovers, decide_eq_true_eq]
    interval_cases r <;> decide +kernel
  · interval_cases r <;> decide +kernel

theorem germPrice_mono_left (f f' g : Flag) (hg : g.ordered)
    (h : f.cumulativeLE f') : germPrice f g ≤ germPrice f' g := by
  unfold germPrice
  rw [germDegreeY_eq _ _ hg.1,germDegreeY_eq _ _ hg.1]
  exact Nat.add_le_add
    (germDegreeT_mono_left f f' g (hg.1.trans hg.2) h.1 h.2.2)
    (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.1)
      (Nat.mul_le_mul_right _ h.1)))

theorem first_adaptive_germ_fee (f : Flag) (hfit : f.cumulativeLE afterRooms) :
    (adaptivePartnerFlag firstAdaptiveFlag).ordered ∧
    germDegreeT f (adaptivePartnerFlag firstAdaptiveFlag) < prime ∧
    germPrice f (adaptivePartnerFlag firstAdaptiveFlag) ≤ 524260340103650 := by
  let g := adaptivePartnerFlag firstAdaptiveFlag
  have hg : g.ordered := ⟨by decide +kernel,by decide +kernel⟩
  exact ⟨hg,(germDegreeT_mono_left f afterRooms g (hg.1.trans hg.2) hfit.1 hfit.2.2).trans_lt
      (by decide +kernel : germDegreeT afterRooms g < prime),
    (germPrice_mono_left f afterRooms g hg hfit).trans
      (by decide +kernel : germPrice afterRooms g ≤ 524260340103650)⟩

theorem second_adaptive_germ_fee (f : Flag) (hr : 1 ≤ f.r) (hf : f.ordered)
    (hfit : f.cumulativeLE afterRooms)
    (hfail : ¬ geometricGate flowWidth (bandSourceNumbers firstAdaptiveFlag firstAdaptiveGap)
      f.toFlagDegree) :
    (adaptivePartnerFlag secondAdaptiveFlag).ordered ∧
    germDegreeT f (adaptivePartnerFlag secondAdaptiveFlag) < prime ∧
    germPrice f (adaptivePartnerFlag secondAdaptiveFlag) ≤ 7000000000000000 := by
  let g := adaptivePartnerFlag secondAdaptiveFlag
  have hg : g.ordered := ⟨by decide +kernel,by decide +kernel⟩
  have hd := (germDegreeT_mono_left f afterRooms g (hg.1.trans hg.2) hfit.1 hfit.2.2).trans_lt
    (by decide +kernel : germDegreeT afterRooms g < prime)
  have hr₁ : f.r ≤ 50 := hfit.1
  obtain ⟨hst,hgate,hprice⟩ := checkedSecondFeeStop f.r hr hr₁
  let q : Flag := ⟨f.r,secondFeeStop f.r,secondFeeStop f.r⟩
  have hq : q.ordered := ⟨hst,le_rfl⟩
  have hy : f.y < secondFeeStop f.r := by
    by_contra! h
    have hbelow : Below q.toFlagDegree f.toFlagDegree := by
      unfold Below
      rw [Flag.toFlagDegree_middle q hq,Flag.toFlagDegree_middle f hf,
        Flag.toFlagDegree_total q hq,Flag.toFlagDegree_total f hf]
      exact ⟨le_rfl,h,h.trans hf.2⟩
    exact hfail (geometricGate_mono flowWidth _ hbelow hr
      ((bandCovers_iff_geometric _ q _ hq).mp hgate))
  refine ⟨hg,hd,?_⟩
  exact (germPrice_mono_left f ⟨f.r,secondFeeStop f.r-1,afterRooms.t⟩ g hg
    ⟨le_rfl,Nat.le_sub_one_of_lt hy,hfit.2.2⟩).trans (hprice (hf.1.trans_lt hy))

end ProximityPrize.SubmissionLower.Koala6844VirtualShort

