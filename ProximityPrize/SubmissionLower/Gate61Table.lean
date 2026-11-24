import ProximityPrize.SubmissionLower.Gate61Fin
import ProximityPrize.SubmissionLower.Gate61Gates
import ProximityPrize.SubmissionLower.Gate61Gt0
import ProximityPrize.SubmissionLower.Gate61Gt1
import ProximityPrize.SubmissionLower.Gate61Gt2
import ProximityPrize.SubmissionLower.Gate61Gt3
import ProximityPrize.SubmissionLower.Gate61Gt4
import ProximityPrize.SubmissionLower.Gate61Gt5
import ProximityPrize.SubmissionLower.Gate61Gt6
import ProximityPrize.SubmissionLower.Gate61Gt7

-- merged module Gate61Gt8
section Merged_Gate61Gt8
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_5_10 : gtOne 5 10 = true := by decide +kernel
theorem g_5_11 : gtOne 5 11 = true := by decide +kernel
theorem g_5_12 : gtOne 5 12 = true := by decide +kernel
theorem g_5_13 : gtOne 5 13 = true := by decide +kernel
end Gate61Fin

end Merged_Gate61Gt8

-- merged module Gate61Table
section Merged_Gate61Table
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
set_option Elab.async false
namespace Gate61Fin
open Gate61Cell
open K1_13 (Shape shape)
open Low6960Allocation
theorem allGt0 (id t : ℕ) (hid : id < 6) (ht : t < 15) : gtOne id t = true := by
  interval_cases id
  · interval_cases t
    · rfl
    · rfl
    · exact g_0_2
    · exact g_0_3
    · exact g_0_4
    · exact g_0_5
    · exact g_0_6
    · exact g_0_7
    · exact g_0_8
    · exact g_0_9
    · exact g_0_10
    · exact g_0_11
    · exact g_0_12
    · exact g_0_13
    · exact g_0_14
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact g_1_3
    · exact g_1_4
    · exact g_1_5
    · exact g_1_6
    · exact g_1_7
    · exact g_1_8
    · exact g_1_9
    · exact g_1_10
    · exact g_1_11
    · exact g_1_12
    · exact g_1_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_2_4
    · exact g_2_5
    · exact g_2_6
    · exact g_2_7
    · exact g_2_8
    · exact g_2_9
    · exact g_2_10
    · exact g_2_11
    · exact g_2_12
    · exact g_2_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_3_6
    · exact g_3_7
    · exact g_3_8
    · exact g_3_9
    · exact g_3_10
    · exact g_3_11
    · exact g_3_12
    · exact g_3_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_4_6
    · exact g_4_7
    · exact g_4_8
    · exact g_4_9
    · exact g_4_10
    · exact g_4_11
    · exact g_4_12
    · exact g_4_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_5_9
    · exact g_5_10
    · exact g_5_11
    · exact g_5_12
    · exact g_5_13
    · rfl

theorem allGt : ∀ id, id < 6 → ∀ t, t < 15 → gtOne id t = true := fun id hid t ht => allGt0 id t hid ht

theorem gateTable : GateTable bandOrders Gfun := by
  intro k x _ _ hg
  obtain ⟨hid, hm⟩ := hg
  have ht : x.t < 15 := by
    by_contra hc
    rw [gl_nil k.val x.t (by omega)] at hm
    simp at hm
  have h := List.all_eq_true.mp (allGt k.val hid x.t ht) (x.b, x.j) hm
  have hk : (⟨k.val % 19, Nat.mod_lt _ (by decide)⟩ : Band) = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  rw [hk] at h
  exact ⟨_, h.1, le_rfl, h.2⟩

theorem gateBank : Low6960RetainedCut.GateBank Gfun := by
  intro w Γ s n D hm f hf hdiff z hz i hi l active hl0 hl hact hchar Δ hΔ hon hoff id hbox hgated
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := D.proper_cut (hf i) hchar hl0 hl
  have := gated_price (Low6960Prices.Messages.mono hm hΔ) (hf i) hon hl0
    ⟨Q, h1, h2, h3, h4, fun γ hγ => h5 γ (hΔ hγ)⟩ hchar (gated_ok hgated)
  unfold Low6960Gate.gatePrice
  omega

theorem gates : Low6960Allocation.Gates := ⟨Gfun, gateBank, gateTable⟩

end Gate61Fin

end Merged_Gate61Table
