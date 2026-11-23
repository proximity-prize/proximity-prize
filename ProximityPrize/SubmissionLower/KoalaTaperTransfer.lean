import ProximityPrize.SubmissionLower.Wide50EulerPrimaryRank
import ProximityPrize.SubmissionLower.Low48PrimaryPivotFinish

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace KoalaTaperTransfer
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget Low48PrimaryPivot
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open private charged inWindow charged_add_gain gain window_gain
  from ProximityPrize.SubmissionLower.Wide50EulerPrimaryRank
open private fees saved_by_fees fees_le_baseline
  from ProximityPrize.SubmissionLower.PrimaryTaperBudget
open private combine baseline_budget_on sum_add_pointwise_eq
  from ProximityPrize.SubmissionLower.Fast022
open private sum_checked from ProximityPrize.SubmissionLower.PrimaryTaperRankData

abbrev localRank:ℕ:=343744005134722

private abbrev noPowers:BlockIndex→Powers:=fun _ => ⟨0,0,0⟩

private def paid (p₁ : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if w2.Contains i ∨ w3.Contains i then ∑ q:Column,charge i q
  else charged p₁ noPowers noPowers i

private theorem middle_baseline (p₁ : BlockIndex → Powers) (i : BlockIndex)
    (hlo:2008≤ i.1.val) (hhi:i.1.val < 3514) :
    charged p₁ noPowers noPowers i=baseline i:=by
  have hw : ¬ inWindow i := by
    unfold inWindow
    omega
  have h₁ : ¬ i.1.val < 2008:=by omega
  have hz : (noPowers i).expand = fun _ => 0 := by
    funext k
    fin_cases k <;> rfl
  unfold charged fees combine
  simp only [hw,hhi,h₁,ite_false,ite_true]
  split <;> rw [hz] <;> rfl

private theorem sum_window_exchange {ι : Type} (S : Finset ι)
    (first second:ι→Prop) [DecidablePred first] [DecidablePred second]
    (old new baseline:ι→ℕ) (disjoint : ∀ i,first i → ¬ second i)
    (same : ∀ i, (first i ∨ second i) → old i = baseline i) :
    (∑ i ∈ S, if first i ∨ second i then new i else old i) +
      (∑ i ∈ S,if first i then baseline i else 0) +
      (∑ i ∈ S,if second i then baseline i else 0) =
    (∑ i ∈ S, old i) + (∑ i ∈ S, if first i then new i else 0) +
      (∑ i ∈ S,if second i then new i else 0):=by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h₁:first i
  · have h₂ := disjoint i h₁
    rw [same i (Or.inl h₁)]
    simp only [h₁,h₂,true_or,ite_true,ite_false,Nat.add_zero]
    exact Nat.add_comm _ _
  · by_cases h₂ : second i
    · rw [same i (Or.inr h₂)]
      simp only [h₁,h₂,or_true,ite_true,ite_false,Nat.add_zero]
      exact Nat.add_comm _ _
    · simp [h₁,h₂]

attribute [local irreducible] Finset.univ

private theorem raw_def (w : Window) :
    rawWindow w = ∑ i:BlockIndex,if w.Contains i then baseline i else 0:=rfl

private theorem debit_def (w : Window) :
    debit w = ∑ i:BlockIndex,if w.Contains i then ∑ q:Column,charge i q else 0:=rfl

private theorem paid_invoice (p₁ : BlockIndex → Powers) :
    (∑ i : BlockIndex, paid p₁ i) + rawWindow w2 + rawWindow w3 =
      (∑ i:BlockIndex,charged p₁ noPowers noPowers i)+debit w2+debit w3:=by
  rw [raw_def,raw_def,debit_def,debit_def]
  apply sum_window_exchange Finset.univ w2.Contains w3.Contains
    (charged p₁ noPowers noPowers) (fun i => ∑ q:Column,charge i q) baseline
  · intro i h₂
    simp only [w2,w3,Window.Contains] at *
    omega
  · intro i h
    rcases h with h | h
    · simp only [w2, Window.Contains] at h
      exact middle_baseline p₁ i h.1 (by omega)
    · simp only [w3, Window.Contains] at h
      exact middle_baseline p₁ i (by omega) h.2.1

private theorem published_tail (p₁ : BlockIndex → Powers)
    (hp₁:9573892230≤savingsSum w1 p₁) :
    (∑ i:BlockIndex,charged p₁ noPowers noPowers i)≤344162560924059:=by
  classical
  have hbase := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low
    K1_13_2_3_1.proof K1_13_2_3_2.proof K1_13_2_3_3.proof
  have hgain:=window_gain
  have hsumGain : (∑ i, charged p₁ noPowers noPowers i) + (∑ i, gain i) =
      ∑ i,fees p₁ noPowers noPowers i:=by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => charged_add_gain p₁ noPowers noPowers i
  have htail : 396610034658 ≤ ∑ i : BlockIndex, tailSaving i := by
    have h:=fastSavings_le (J:=600) (by decide)
    rw [← sumChunk_eq_fastSavings,sum_checked] at h
    exact h
  have hsave:=saved_by_fees p₁ noPowers noPowers
  have hsum := sum_add_pointwise_eq Finset.univ (fees p₁ noPowers noPowers)
    (fun i => baseline i - fees p₁ noPowers noPowers i) baseline
    (fun i _ => Nat.add_sub_of_le (fees_le_baseline p₁ noPowers noPowers i))
  omega

theorem node_rank_of_receipts (x y : Geom)
    (hraw:28571050105634≤rawWindow w2+rawWindow w3)
    (hfee:debit w2+debit w3≤28152494316297) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap)))≤localRank:=by
  classical
  obtain ⟨p₁,hp₁⟩:=K1_13_2_3_4.proof
  have h₂:=K1_13_2_2_2.proof
  have h₃:=K1_13_2_2_3.proof
  have h₄:=K1_13_2_2_4.proof
  have h₅:=K1_13_2_2_5.proof
  have hBlock:=K1_13_2_2.of_children K1_13_2_2_1.proof h₂ h₃ h₄ h₅
  have hbound (i : BlockIndex) :
      Module.finrank Geom (LinearMap.range (TaperNormalize.originBlock (cap i.1.val) i)) ≤
        fees p₁ noPowers noPowers i:=by
    have ho:=Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)
    unfold fees
    split
    · exact ho.trans (hBlock i _)
    · exact le_min (ho.trans (hBlock i _))
        (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
  have hr := TaperNormalize.rank_le_of_blocks cap_antitone x y (paid p₁) (fun i => by
    unfold paid
    split
    · rename_i h
      have hs : 1650 ≤ i.1.val := by
        rcases h with h | h
        · simp only [w2, Window.Contains] at h
          omega
        · simp only [w3, Window.Contains] at h
          omega
      exact (Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)).trans
        (block_le_charge i hs)
    · unfold charged
      split
      · exact le_min (hbound i) (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
      · exact hbound i)
  have hbalance:=paid_invoice p₁
  have hother:=published_tail p₁ hp₁
  unfold localRank
  omega

#print axioms node_rank_of_receipts
end KoalaTaperTransfer
