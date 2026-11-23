import ProximityPrize.SubmissionLower.KoalaTaperTransferReceipt
import ProximityPrize.SubmissionLower.KoalaTaperExtraWindows

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

namespace KoalaTaperExtra
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget Low48PrimaryPivot
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open private paid paid_invoice published_tail noPowers
  from ProximityPrize.SubmissionLower.KoalaTaperTransfer
open private charged inWindow from ProximityPrize.SubmissionLower.Wide50EulerPrimaryRank
open private fees from ProximityPrize.SubmissionLower.PrimaryTaperBudget
open private combine from ProximityPrize.SubmissionLower.Fast022

private def mask (p : BlockIndex → Powers) (i : BlockIndex) : Powers :=
  if w1.Contains i then p i else noPowers i

private theorem mask_saving (p : BlockIndex → Powers) :
    savingsSum w1 (mask p) = savingsSum w1 p := by
  unfold savingsSum
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : w1.Contains i <;> simp only [h,mask,if_true,if_false]

private def addWindow (w : Window) (old : BlockIndex → ℕ) (i : BlockIndex) : ℕ :=
  if w.Contains i then ∑ q : Column, charge i q else old i

private theorem add_bill (w : Window) (old : BlockIndex → ℕ)
    (hbase : ∀ i, w.Contains i → old i = baseline i) :
    (∑ i : BlockIndex,addWindow w old i) + rawWindow w =
      (∑ i : BlockIndex, old i) + debit w := by
  unfold rawWindow debit
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : w.Contains i
  · simp only [addWindow,h,if_true,hbase i h,Nat.add_comm]
  · simp only [addWindow,h,if_false,Nat.add_zero]

private theorem base_off (p : BlockIndex → Powers) (i : BlockIndex)
    (hi : i.1.val < 3514) (h1 : ¬ w1.Contains i)
    (h2 : ¬ w2.Contains i) (h3 : ¬ w3.Contains i) :
    paid (mask p) i = baseline i := by
  have hi' : ¬ inWindow i := by unfold inWindow; omega
  have hz : (noPowers i).expand = fun _ => 0 := by
    funext k
    fin_cases k <;> rfl
  unfold paid charged fees combine
  simp only [hi,h1,h2,h3,hi',mask,ite_false,ite_true,or_self]
  by_cases h : i.1.val < 2008 <;> by_cases h' : i.1.val < 3012 <;>
    simp only [h,h',ite_true,ite_false,hz,baseline]

attribute [local irreducible] Finset.univ
abbrev localCap : ℕ := 343740063412549

theorem rank_of_receipts (x y : Geom)
    (hraw : 4376779620457 ≤ rawWindow extraA+rawWindow extraB+rawWindow extraC)
    (hdebit : debit extraA+debit extraB+debit extraC ≤ 4372837898284) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localCap := by
  classical
  obtain ⟨p,hp⟩ := K1_13_2_3_4.proof
  let rank (i : BlockIndex) :=
    Module.finrank Geom (LinearMap.range (TaperNormalize.originBlock (cap i.1.val) i))
  have h₂ := K1_13_2_2_2.proof
  have h₃ := K1_13_2_2_3.proof
  have h₄ := K1_13_2_2_4.proof
  have h₅ := K1_13_2_2_5.proof
  have hBlock := K1_13_2_2.of_children K1_13_2_2_1.proof h₂ h₃ h₄ h₅
  have hbound (i : BlockIndex) : rank i ≤ fees (mask p) noPowers noPowers i := by
    have ho := Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)
    unfold fees
    split
    · exact ho.trans (hBlock i _)
    · exact le_min (ho.trans (hBlock i _))
        (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
  have charge_bound (i : BlockIndex) (hi : 1650 ≤ i.1.val) :
      rank i ≤ ∑ q : Column, charge i q :=
    (Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)).trans
      (block_le_charge i hi)
  have old_bound (i : BlockIndex) : rank i ≤ paid (mask p) i := by
    unfold paid
    split
    · rename_i h
      apply charge_bound
      rcases h with h | h
      · simp only [w2,Window.Contains] at h
        omega
      · simp only [w3,Window.Contains] at h
        omega
    · unfold charged
      split
      · exact le_min (hbound i) (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
      · exact hbound i
  have add_bound (w : Window) (hw : 1650 ≤ w.gradeLo) (old : BlockIndex → ℕ)
      (ho : ∀ i, rank i ≤ old i) (i : BlockIndex) :
      rank i ≤ addWindow w old i := by
    unfold addWindow
    split
    · rename_i h
      exact charge_bound i (hw.trans h.1)
    · exact ho i
  let old := paid (mask p)
  let payA := addWindow extraA old
  let payB := addWindow extraB payA
  let payC := addWindow extraC payB
  have hA := add_bill extraA old (fun i hi => by
    apply base_off
    all_goals
      simp only [extraA, w1,w2,w3, Window.Contains] at *
      omega)
  have hB := add_bill extraB payA (fun i hi => by
    unfold payA addWindow
    rw [if_neg (by simp only [extraA,extraB,Window.Contains] at *; omega)]
    apply base_off
    all_goals
      simp only [extraB,w1,w2,w3,Window.Contains] at *
      omega)
  have hC := add_bill extraC payB (fun i hi => by
    unfold payB payA addWindow
    rw [if_neg (by simp only [extraB,extraC,Window.Contains] at *; omega),
        if_neg (by simp only [extraA,extraC,Window.Contains] at *; omega)]
    apply base_off
    all_goals
      simp only [extraC,w1,w2,w3,Window.Contains] at *
      omega)
  have hr := TaperNormalize.rank_le_of_blocks cap_antitone x y payC
    (add_bound extraC (by decide) payB
      (add_bound extraB (by decide) payA (add_bound extraA (by decide) old old_bound)))
  have htail := published_tail (mask p) (by simpa only [mask_saving] using hp)
  have hbalance := paid_invoice (mask p)
  have hD2 := debit_le_binCompute w2 (by decide)
  have hD3 := debit_le_binCompute w3 (by decide)
  rw [binCompute2] at hD2
  rw [binCompute3] at hD3
  rw [rawWindow_w2,rawWindow_w3] at hbalance
  change (∑ i : BlockIndex, old i) + _ + _ = _ at hbalance
  change (∑ i : BlockIndex, payA i) + _ = _ at hA
  change (∑ i : BlockIndex, payB i) + _ = _ at hB
  change (∑ i : BlockIndex, payC i) + _ = _ at hC
  unfold localCap
  omega

#print axioms rank_of_receipts
end KoalaTaperExtra
