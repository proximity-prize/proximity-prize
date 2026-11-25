import ProximityPrize.SubmissionLower.G6966Check0
import ProximityPrize.SubmissionLower.G6966Check1
import ProximityPrize.SubmissionLower.G6966Check2
import ProximityPrize.SubmissionLower.G6966Check3
import ProximityPrize.SubmissionLower.G6966Check4
import ProximityPrize.SubmissionLower.G6966Check5
import ProximityPrize.SubmissionLower.G6966Check6
import ProximityPrize.SubmissionLower.G6966Check7
import ProximityPrize.SubmissionLower.G6966Check8
import ProximityPrize.SubmissionLower.G6966Check9
import ProximityPrize.SubmissionLower.G6966Check10
import ProximityPrize.SubmissionLower.G6966Check11
import ProximityPrize.SubmissionLower.G6966Check12
set_option Elab.async false
set_option maxRecDepth 16000
namespace Gate6966Fin
open K1_13 (Shape shape)
open Low6966Allocation
theorem allOne (id : ℕ) (hi : id < 13) (t : ℕ) (ht : t < 16) : one id t = true := by
  interval_cases id
  · interval_cases t
    · rfl
    · rfl
    · exact fb_0_2.1
    · exact fb_0_3.1
    · exact fb_0_4.1
    · exact fb_0_5.1
    · exact fb_0_6.1
    · exact fb_0_7.1
    · exact fb_0_8.1
    · exact fb_0_9.1
    · exact fb_0_10.1
    · exact fb_0_11.1
    · exact fb_0_12.1
    · exact fb_0_13.1
    · exact fb_0_14.1
    · exact fb_0_15.1
  · interval_cases t
    · rfl
    · rfl
    · exact fb_1_2.1
    · exact fb_1_3.1
    · exact fb_1_4.1
    · exact fb_1_5.1
    · exact fb_1_6.1
    · exact fb_1_7.1
    · exact fb_1_8.1
    · exact fb_1_9.1
    · exact fb_1_10.1
    · exact fb_1_11.1
    · exact fb_1_12.1
    · exact fb_1_13.1
    · exact fb_1_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact fb_2_2.1
    · exact fb_2_3.1
    · exact fb_2_4.1
    · exact fb_2_5.1
    · exact fb_2_6.1
    · exact fb_2_7.1
    · exact fb_2_8.1
    · exact fb_2_9.1
    · exact fb_2_10.1
    · exact fb_2_11.1
    · exact fb_2_12.1
    · exact fb_2_13.1
    · exact fb_2_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact fb_3_2.1
    · exact fb_3_3.1
    · exact fb_3_4.1
    · exact fb_3_5.1
    · exact fb_3_6.1
    · exact fb_3_7.1
    · exact fb_3_8.1
    · exact fb_3_9.1
    · exact fb_3_10.1
    · exact fb_3_11.1
    · exact fb_3_12.1
    · exact fb_3_13.1
    · exact fb_3_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact fb_4_3.1
    · exact fb_4_4.1
    · exact fb_4_5.1
    · exact fb_4_6.1
    · exact fb_4_7.1
    · exact fb_4_8.1
    · exact fb_4_9.1
    · exact fb_4_10.1
    · exact fb_4_11.1
    · exact fb_4_12.1
    · exact fb_4_13.1
    · exact fb_4_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact fb_5_3.1
    · exact fb_5_4.1
    · exact fb_5_5.1
    · exact fb_5_6.1
    · exact fb_5_7.1
    · exact fb_5_8.1
    · exact fb_5_9.1
    · exact fb_5_10.1
    · exact fb_5_11.1
    · exact fb_5_12.1
    · exact fb_5_13.1
    · exact fb_5_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_6_4.1
    · exact fb_6_5.1
    · exact fb_6_6.1
    · exact fb_6_7.1
    · exact fb_6_8.1
    · exact fb_6_9.1
    · exact fb_6_10.1
    · exact fb_6_11.1
    · exact fb_6_12.1
    · exact fb_6_13.1
    · exact fb_6_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_7_5.1
    · exact fb_7_6.1
    · exact fb_7_7.1
    · exact fb_7_8.1
    · exact fb_7_9.1
    · exact fb_7_10.1
    · exact fb_7_11.1
    · exact fb_7_12.1
    · exact fb_7_13.1
    · exact fb_7_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_8_7.1
    · exact fb_8_8.1
    · exact fb_8_9.1
    · exact fb_8_10.1
    · exact fb_8_11.1
    · exact fb_8_12.1
    · exact fb_8_13.1
    · exact fb_8_14.1
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
    · exact fb_9_10.1
    · exact fb_9_11.1
    · exact fb_9_12.1
    · exact fb_9_13.1
    · exact fb_9_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_10_7.1
    · exact fb_10_8.1
    · exact fb_10_9.1
    · exact fb_10_10.1
    · exact fb_10_11.1
    · exact fb_10_12.1
    · exact fb_10_13.1
    · exact fb_10_14.1
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
    · exact fb_11_9.1
    · exact fb_11_10.1
    · exact fb_11_11.1
    · exact fb_11_12.1
    · exact fb_11_13.1
    · exact fb_11_14.1
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
    · exact fb_12_12.1
    · exact fb_12_13.1
    · rfl
    · rfl
theorem allGt (id : ℕ) (hi : id < 13) (t : ℕ) (ht : t < 16) : gtOne id t = true := by
  interval_cases id
  · interval_cases t
    · rfl
    · rfl
    · exact fb_0_2.2
    · exact fb_0_3.2
    · exact fb_0_4.2
    · exact fb_0_5.2
    · exact fb_0_6.2
    · exact fb_0_7.2
    · exact fb_0_8.2
    · exact fb_0_9.2
    · exact fb_0_10.2
    · exact fb_0_11.2
    · exact fb_0_12.2
    · exact fb_0_13.2
    · exact fb_0_14.2
    · exact fb_0_15.2
  · interval_cases t
    · rfl
    · rfl
    · exact fb_1_2.2
    · exact fb_1_3.2
    · exact fb_1_4.2
    · exact fb_1_5.2
    · exact fb_1_6.2
    · exact fb_1_7.2
    · exact fb_1_8.2
    · exact fb_1_9.2
    · exact fb_1_10.2
    · exact fb_1_11.2
    · exact fb_1_12.2
    · exact fb_1_13.2
    · exact fb_1_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact fb_2_2.2
    · exact fb_2_3.2
    · exact fb_2_4.2
    · exact fb_2_5.2
    · exact fb_2_6.2
    · exact fb_2_7.2
    · exact fb_2_8.2
    · exact fb_2_9.2
    · exact fb_2_10.2
    · exact fb_2_11.2
    · exact fb_2_12.2
    · exact fb_2_13.2
    · exact fb_2_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact fb_3_2.2
    · exact fb_3_3.2
    · exact fb_3_4.2
    · exact fb_3_5.2
    · exact fb_3_6.2
    · exact fb_3_7.2
    · exact fb_3_8.2
    · exact fb_3_9.2
    · exact fb_3_10.2
    · exact fb_3_11.2
    · exact fb_3_12.2
    · exact fb_3_13.2
    · exact fb_3_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact fb_4_3.2
    · exact fb_4_4.2
    · exact fb_4_5.2
    · exact fb_4_6.2
    · exact fb_4_7.2
    · exact fb_4_8.2
    · exact fb_4_9.2
    · exact fb_4_10.2
    · exact fb_4_11.2
    · exact fb_4_12.2
    · exact fb_4_13.2
    · exact fb_4_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact fb_5_3.2
    · exact fb_5_4.2
    · exact fb_5_5.2
    · exact fb_5_6.2
    · exact fb_5_7.2
    · exact fb_5_8.2
    · exact fb_5_9.2
    · exact fb_5_10.2
    · exact fb_5_11.2
    · exact fb_5_12.2
    · exact fb_5_13.2
    · exact fb_5_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_6_4.2
    · exact fb_6_5.2
    · exact fb_6_6.2
    · exact fb_6_7.2
    · exact fb_6_8.2
    · exact fb_6_9.2
    · exact fb_6_10.2
    · exact fb_6_11.2
    · exact fb_6_12.2
    · exact fb_6_13.2
    · exact fb_6_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_7_5.2
    · exact fb_7_6.2
    · exact fb_7_7.2
    · exact fb_7_8.2
    · exact fb_7_9.2
    · exact fb_7_10.2
    · exact fb_7_11.2
    · exact fb_7_12.2
    · exact fb_7_13.2
    · exact fb_7_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_8_7.2
    · exact fb_8_8.2
    · exact fb_8_9.2
    · exact fb_8_10.2
    · exact fb_8_11.2
    · exact fb_8_12.2
    · exact fb_8_13.2
    · exact fb_8_14.2
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
    · exact fb_9_10.2
    · exact fb_9_11.2
    · exact fb_9_12.2
    · exact fb_9_13.2
    · exact fb_9_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_10_7.2
    · exact fb_10_8.2
    · exact fb_10_9.2
    · exact fb_10_10.2
    · exact fb_10_11.2
    · exact fb_10_12.2
    · exact fb_10_13.2
    · exact fb_10_14.2
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
    · exact fb_11_9.2
    · exact fb_11_10.2
    · exact fb_11_11.2
    · exact fb_11_12.2
    · exact fb_11_13.2
    · exact fb_11_14.2
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
    · exact fb_12_12.2
    · exact fb_12_13.2
    · rfl
    · rfl
theorem gated_ok {id : ℕ} {x : Shape} (h : Low6966Gate.Gated id x) (hv : valid x = true) : shapeOK x = true := by
  obtain ⟨hid, hm⟩ := h
  have ht : x.t < 16 := by
    by_contra hc
    rw [gl_nil id x.t (by omega)] at hm
    simp at hm
  have := allOne id hid x.t ht
  have := List.all_eq_true.mp this (x.b, x.j) hm
  simpa [hv] using this

theorem gateTable : GateTable bandOrders Gfun := by
  intro k x _ _ hg
  obtain ⟨hid, hm⟩ := hg
  have ht : x.t < 16 := by
    by_contra hc
    rw [gl_nil k.val x.t (by omega)] at hm
    simp at hm
  have h := List.all_eq_true.mp (allGt k.val hid x.t ht) (x.b, x.j) hm
  have hk : (⟨k.val % 34, Nat.mod_lt _ (by decide)⟩ : Band) = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
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

theorem gateBank : Low6966RetainedCut.GateBank Gfun := by
  intro w Γ s n D hm f hf hdiff z hz i hi l active hl0 hl hact hchar Δ hΔ hon hoff id hbox hgated
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := D.proper_cut (hf i) hchar hl0 hl
  have hv : valid (shape (f i)) = true := by
    have := index_le (f i)
    simp only [valid, shape, Nat.ble_eq]
    exact this
  have := gated_price (Low6966Prices.Messages.mono hm hΔ) (hf i) hon hl0
    ⟨Q, h1, h2, h3, h4, fun γ hγ => h5 γ (hΔ hγ)⟩ hchar (gated_ok hgated hv)
  unfold Low6966Gate.gatePrice
  omega

theorem gates : Low6966Allocation.Gates := ⟨Gfun, gateBank, gateTable⟩

end Gate6966Fin
