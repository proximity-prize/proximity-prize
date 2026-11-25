import ProximityPrize.SubmissionLower.Gate61Fin
import ProximityPrize.SubmissionLower.Gate61Gates
import ProximityPrize.SubmissionLower.Gate63Gt0
import ProximityPrize.SubmissionLower.Gate63Gt1
import ProximityPrize.SubmissionLower.Gate63Gt2
import ProximityPrize.SubmissionLower.Gate63Gt3
import ProximityPrize.SubmissionLower.Gate63Gt4
import ProximityPrize.SubmissionLower.Gate63Gt5
import ProximityPrize.SubmissionLower.Gate63Gt6
import ProximityPrize.SubmissionLower.Gate63Gt7
import ProximityPrize.SubmissionLower.Gate63Gt8
import ProximityPrize.SubmissionLower.Gate63Gt9
import ProximityPrize.SubmissionLower.Gate63Gt10
import ProximityPrize.SubmissionLower.Gate63Gt11

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
set_option Elab.async false

namespace Gate61Fin
open Gate61Cell
open K1_13 (Shape shape)
open Low6960Allocation

theorem allGt0 (id t : ℕ) (hid : id < 17) (ht : t < 15) : gtOne id t = true := by
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
    · exact g_1_2
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
    · exact g_2_2
    · exact g_2_3
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
    · exact g_3_2
    · exact g_3_3
    · exact g_3_4
    · exact g_3_5
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
    · exact g_4_2
    · exact g_4_3
    · exact g_4_4
    · exact g_4_5
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
    · exact g_5_3
    · exact g_5_4
    · exact g_5_5
    · exact g_5_6
    · exact g_5_7
    · exact g_5_8
    · exact g_5_9
    · exact g_5_10
    · exact g_5_11
    · exact g_5_12
    · exact g_5_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact g_6_3
    · exact g_6_4
    · exact g_6_5
    · exact g_6_6
    · exact g_6_7
    · exact g_6_8
    · exact g_6_9
    · exact g_6_10
    · exact g_6_11
    · exact g_6_12
    · exact g_6_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_7_4
    · exact g_7_5
    · exact g_7_6
    · exact g_7_7
    · exact g_7_8
    · exact g_7_9
    · exact g_7_10
    · exact g_7_11
    · exact g_7_12
    · exact g_7_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_8_5
    · exact g_8_6
    · exact g_8_7
    · exact g_8_8
    · exact g_8_9
    · exact g_8_10
    · exact g_8_11
    · exact g_8_12
    · exact g_8_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_9_7
    · exact g_9_8
    · exact g_9_9
    · exact g_9_10
    · exact g_9_11
    · exact g_9_12
    · exact g_9_13
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
    · rfl
    · exact g_10_10
    · exact g_10_11
    · exact g_10_12
    · exact g_10_13
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
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_12_5
    · exact g_12_6
    · exact g_12_7
    · exact g_12_8
    · exact g_12_9
    · exact g_12_10
    · exact g_12_11
    · exact g_12_12
    · exact g_12_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_13_6
    · exact g_13_7
    · exact g_13_8
    · exact g_13_9
    · exact g_13_10
    · exact g_13_11
    · exact g_13_12
    · exact g_13_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g_14_7
    · exact g_14_8
    · exact g_14_9
    · exact g_14_10
    · exact g_14_11
    · exact g_14_12
    · exact g_14_13
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
    · rfl
    · exact g_15_10
    · exact g_15_11
    · exact g_15_12
    · exact g_15_13
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
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

theorem allGt : ∀ id, id < 17 → ∀ t, t < 15 → gtOne id t = true := fun id hid t ht => allGt0 id t hid ht

theorem gateTable : GateTable bandOrders Gfun := by
  intro k x _ _ hg
  obtain ⟨hid, hm⟩ := hg
  have ht : x.t < 15 := by
    by_contra hc
    rw [gl_nil k.val x.t (by omega)] at hm
    simp at hm
  have h := List.all_eq_true.mp (allGt k.val hid x.t ht) (x.b, x.j) hm
  have hk : (⟨k.val % 44, Nat.mod_lt _ (by decide)⟩ : Band) = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  rw [hk] at h
  exact ⟨_, h.1, le_rfl, h.2⟩

theorem index_le (P : K1_13.Row 4) : K1_13.indexDegree P ≤ 2 * P.totalDegree + P.degreeOf 3 := by
  unfold K1_13.indexDegree
  apply Finset.sup_le
  intro m hm
  have h1 : (m.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hm
  have h2 : m 3 ≤ P.degreeOf 3 := MvPolynomial.monomial_le_degreeOf 3 hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
  rw [Finsupp.sum_fintype _ _ (fun _ => Nat.mul_zero _)]
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue] at h1 ⊢
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  omega

theorem gateBank : Low6960RetainedCut.GateBank Gfun := by
  intro w Γ s n D hm f hf hdiff z hz i hi l active hl0 hl hact hchar Δ hΔ hon hoff id hbox hgated
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := D.proper_cut (hf i) hchar hl0 hl
  have hv : valid (shape (f i)) = true := by
    have := index_le (f i)
    simp only [valid, shape, Nat.ble_eq]
    exact this
  have := gated_price (Low6960Prices.Messages.mono hm hΔ) (hf i) hon hl0
    ⟨Q, h1, h2, h3, h4, fun γ hγ => h5 γ (hΔ hγ)⟩ hchar (gated_ok hgated hv)
  unfold Low6960Gate.gatePrice
  omega

theorem gates : Low6960Allocation.Gates := ⟨Gfun, gateBank, gateTable⟩

end Gate61Fin
