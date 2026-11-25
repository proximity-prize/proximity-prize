import ProximityPrize.SubmissionLower.PrimaryTaperBudget
import Mathlib.Algebra.BigOperators.Intervals
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryRank

-- merged module Low48PrimaryPivotBaseline
section Merged_Low48PrimaryPivotBaseline

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace Low48PrimaryPivot
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators

def w0 : Window := ⟨1650, 2008, 993, 1424, 3000, 3163⟩

def rawWindow (w : Window) : ℕ :=
  ∑ i : BlockIndex, if w.Contains i then baseline i else 0

def baselineFast (g o : ℕ) : ℕ :=
  let delta := (o : ℤ) - 1650
  let F : Flag := ⟨min (g : ℤ) 1650, -delta, 1650, 550, 3000-(g : ℤ)-delta⟩
  if F.order ≤ 0 then 0 else
    let active := oldCount { F with upper := min F.upper (2999-delta) }
    (min active (oldCount F - max 0 (kernelLower F))).toNat

private theorem baseline_eq (i : BlockIndex) :
    baseline i = baselineFast i.1.val i.2.val := by
  have residual_zero (F : Flag) : residualFlag F (fun _ => 0) = F := by
    cases F
    simp [residualFlag]
  simp only [baseline, blockBound, baselineFast, initialFlag, offset, residual_zero, max_self]

def rawAt (w : Window) (o : ℕ) : ℕ :=
  let lo := max w.gradeLo (w.diagonalLo-o)
  let hi := min w.gradeHi (w.diagonalHi+1-o)
  ((List.range' lo (hi-lo)).map fun g => baselineFast g o).sum

def rawCompute (w : Window) : ℕ :=
  ((List.range' w.offsetLo (w.offsetHi+1-w.offsetLo)).map (rawAt w)).sum

private theorem sum_fin_mod (n : ℕ) [NeZero n] (f : Fin n → ℕ) :
    (∑ i, f i) = ∑ i ∈ range n, f (Fin.ofNat n i) := by
  calc
    (∑ i, f i) = ∑ i : Fin n, f (Fin.ofNat n i.val) := by
      apply sum_congr rfl
      intro i _
      have h : Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [h]
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => f (Fin.ofNat n i)) n

theorem raw_eq_compute (w : Window) (hg : w.gradeHi ≤ 4013)
    (ho : w.offsetHi < 4650) : rawWindow w = rawCompute w := by
  classical
  unfold rawWindow rawCompute
  rw [Fintype.sum_prod_type]
  rw [sum_comm]
  have row (o : Fin 4650) :
      (∑ g : Fin 4013, if w.Contains (g,o) then baseline (g,o) else 0) =
        if w.offsetLo ≤ (o : ℕ) ∧ (o : ℕ) ≤ w.offsetHi then rawAt w o else 0 := by
    rw [sum_fin_mod 4013 (fun g => if w.Contains (g,o) then baseline (g,o) else 0)]
    by_cases hh : w.offsetLo ≤ (o : ℕ) ∧ (o : ℕ) ≤ w.offsetHi
    · rw [if_pos hh]
      let lo := max w.gradeLo (w.diagonalLo-o.val)
      let hi := min w.gradeHi (w.diagonalHi+1-o.val)
      have hif (g : ℕ) (hmem : g ∈ range 4013) :
          (if w.Contains (Fin.ofNat 4013 g,o) then baseline (Fin.ofNat 4013 g,o) else 0) =
            if g ∈ Ico lo hi then baselineFast g o.val else 0 := by
        have hlt : g < 4013 := mem_range.mp hmem
        have hv : (Fin.ofNat 4013 g).val = g := Nat.mod_eq_of_lt hlt
        have heq : w.Contains (Fin.ofNat 4013 g,o) ↔ g ∈ Ico lo hi := by
          simp only [Window.Contains, hv, mem_Ico, lo, hi, max_le_iff, lt_min_iff]
          omega
        simp only [heq, baseline_eq, hv]
      rw [sum_congr rfl hif, ← sum_filter]
      have hfilter : (range 4013).filter (fun g => g ∈ Ico lo hi) = Ico lo hi := by
        ext g
        simp only [mem_filter, mem_range, mem_Ico, lo, hi, max_le_iff, lt_min_iff]
        omega
      rw [hfilter]
      rw [Nat.Ico_eq_range']
      rfl
    · rw [if_neg hh]
      apply sum_eq_zero
      intro g _
      exact if_neg (fun h => hh ⟨h.2.2.1,h.2.2.2.1⟩)
  simp_rw [row]
  rw [Fin.sum_univ_eq_sum_range
    (fun o => if w.offsetLo ≤ o ∧ o ≤ w.offsetHi then rawAt w o else 0) 4650]
  rw [← sum_filter]
  have hfilter : (range 4650).filter (fun o => w.offsetLo ≤ o ∧ o ≤ w.offsetHi) =
      Ico w.offsetLo (w.offsetHi+1) := by
    ext o
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hfilter, Nat.Ico_eq_range']
  rfl

#print axioms raw_eq_compute
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBaseline

-- merged module Low48PrimaryPivotFinish
section Merged_Low48PrimaryPivotFinish

set_option Elab.async false
set_option maxHeartbeats 2500000

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_2 K1_13_2_3
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators



open K1_13_2_3 (baseline_budget_on bound_le_baseline)



attribute [local irreducible] Finset.univ







end Low48PrimaryPivot

end Merged_Low48PrimaryPivotFinish

-- merged module KoalaTaperTransfer
section Merged_KoalaTaperTransfer

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

namespace KoalaTaperTransfer
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget Low48PrimaryPivot
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open Wide50EulerPrimary (charged inWindow charged_add_gain gain window_gain)
open TaperBudget (fees saved_by_fees fees_le_baseline)
open K1_13_2_3 (combine baseline_budget_on sum_add_pointwise_eq)
open TaperBudget (sum_checked)

abbrev localRank : ℕ := 343722599203719

private abbrev noPowers : BlockIndex → Powers := fun _ => ⟨0, 0, 0⟩

private def paid (p₁ : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if w0.Contains i ∨ w2.Contains i ∨ w3.Contains i then ∑ q : Column, charge i q
  else charged p₁ noPowers noPowers i

private theorem middle_baseline (p₁ : BlockIndex → Powers)
    (hp₁ : ∀ i, p₁ i = ⟨0, 0, 0⟩) (i : BlockIndex)
    (hlo : 1650 ≤ i.1.val) (hhi : i.1.val < 3514) :
    charged p₁ noPowers noPowers i = baseline i := by
  have hw : ¬ inWindow i := by
    unfold inWindow
    omega
  have hz : (noPowers i).expand = fun _ => 0 := by
    funext k
    fin_cases k <;> rfl
  have hz1 : (p₁ i).expand = fun _ => 0 := by
    rw [hp₁ i]
    exact hz
  unfold charged fees combine
  simp only [hw, hhi, ite_false, ite_true]
  split
  · rw [hz1]; rfl
  · split <;> rw [hz] <;> rfl

private theorem sum_window_exchange3 {ι : Type} (S : Finset ι)
    (p0 p2 p3 : ι → Prop) [DecidablePred p0] [DecidablePred p2] [DecidablePred p3]
    (old new baseline : ι → ℕ)
    (d02 : ∀ i, p0 i → ¬ p2 i) (d03 : ∀ i, p0 i → ¬ p3 i) (d23 : ∀ i, p2 i → ¬ p3 i)
    (same : ∀ i, p0 i ∨ p2 i ∨ p3 i → old i = baseline i) :
    (∑ i ∈ S, if p0 i ∨ p2 i ∨ p3 i then new i else old i) +
      (∑ i ∈ S, if p0 i then baseline i else 0) +
      (∑ i ∈ S, if p2 i then baseline i else 0) +
      (∑ i ∈ S, if p3 i then baseline i else 0) =
    (∑ i ∈ S, old i) + (∑ i ∈ S, if p0 i then new i else 0) +
      (∑ i ∈ S, if p2 i then new i else 0) +
      (∑ i ∈ S, if p3 i then new i else 0) := by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h0 : p0 i
  · have h2 := d02 i h0; have h3 := d03 i h0
    rw [same i (Or.inl h0)]
    simp only [h0, h2, h3, true_or, ite_true, ite_false, Nat.add_zero]
    exact Nat.add_comm _ _
  · by_cases h2 : p2 i
    · have h3 := d23 i h2
      rw [same i (Or.inr (Or.inl h2))]
      simp only [h0, h2, h3, true_or, or_true, ite_true, ite_false, Nat.add_zero]
      exact Nat.add_comm _ _
    · by_cases h3 : p3 i
      · rw [same i (Or.inr (Or.inr h3))]
        simp only [h0, h2, h3, or_true, ite_true, ite_false, Nat.add_zero]
        exact Nat.add_comm _ _
      · simp [h0, h2, h3]

attribute [local irreducible] Finset.univ

private theorem raw_def (w : Window) :
    rawWindow w = ∑ i : BlockIndex, if w.Contains i then baseline i else 0 := rfl

private theorem debit_def (w : Window) :
    debit w = ∑ i : BlockIndex, if w.Contains i then ∑ q : Column, charge i q else 0 := rfl

private theorem paid_invoice (p₁ : BlockIndex → Powers) (hp₁ : ∀ i, p₁ i = ⟨0, 0, 0⟩) :
    (∑ i : BlockIndex, paid p₁ i) + rawWindow w0 + rawWindow w2 + rawWindow w3 =
      (∑ i : BlockIndex, charged p₁ noPowers noPowers i) + debit w0 + debit w2 + debit w3 := by
  rw [raw_def, raw_def, raw_def, debit_def, debit_def, debit_def]
  apply sum_window_exchange3 Finset.univ w0.Contains w2.Contains w3.Contains
    (charged p₁ noPowers noPowers) (fun i => ∑ q : Column, charge i q) baseline
  · intro i h0; simp only [w0, w2, Window.Contains] at *; omega
  · intro i h0; simp only [w0, w3, Window.Contains] at *; omega
  · intro i h2; simp only [w2, w3, Window.Contains] at *; omega
  · intro i h
    rcases h with h | h | h
    · simp only [w0, Window.Contains] at h; exact middle_baseline p₁ hp₁ i h.1 (by omega)
    · simp only [w2, Window.Contains] at h; exact middle_baseline p₁ hp₁ i (by omega) (by omega)
    · simp only [w3, Window.Contains] at h; exact middle_baseline p₁ hp₁ i (by omega) h.2.1

private theorem published_tail (p₁ : BlockIndex → Powers) :
    (∑ i : BlockIndex, charged p₁ noPowers noPowers i) ≤ 344172134816289 := by
  classical
  have hbase := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low
    K1_13_2_3_1.proof K1_13_2_3_2.proof K1_13_2_3_3.proof
  have hgain := window_gain
  have hsumGain : (∑ i, charged p₁ noPowers noPowers i) + (∑ i, gain i) =
      ∑ i, fees p₁ noPowers noPowers i := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => charged_add_gain p₁ noPowers noPowers i
  have htail : 396610034658 ≤ ∑ i : BlockIndex, tailSaving i := by
    have h := fastSavings_le (J := 600) (by decide)
    rw [← sumChunk_eq_fastSavings, sum_checked] at h
    exact h
  have hsave := saved_by_fees p₁ noPowers noPowers
  have hsum := sum_add_pointwise_eq Finset.univ (fees p₁ noPowers noPowers)
    (fun i => baseline i - fees p₁ noPowers noPowers i) baseline
    (fun i _ => Nat.add_sub_of_le (fees_le_baseline p₁ noPowers noPowers i))
  omega

private theorem node_rank_aux (x y : Geom) (p₁ : BlockIndex → Powers) (hp₁ : ∀ i, p₁ i = ⟨0, 0, 0⟩)
    (hraw : 34510370296121 ≤ rawWindow w0 + rawWindow w2 + rawWindow w3)
    (hfee : debit w0 + debit w2 + debit w3 ≤ 34060834683551) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localRank := by
  classical
  have h₂ := K1_13_2_2_2.proof
  have h₃ := K1_13_2_2_3.proof
  have h₄ := K1_13_2_2_4.proof
  have h₅ := K1_13_2_2_5.proof
  have hBlock := K1_13_2_2.of_children K1_13_2_2_1.proof h₂ h₃ h₄ h₅
  have hbound (i : BlockIndex) :
      Module.finrank Geom (LinearMap.range (TaperNormalize.originBlock (cap i.1.val) i)) ≤
        fees p₁ noPowers noPowers i := by
    have ho := Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)
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
        rcases h with h | h | h
        · simp only [w0, Window.Contains] at h; omega
        · simp only [w2, Window.Contains] at h; omega
        · simp only [w3, Window.Contains] at h; omega
      exact (Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)).trans
        (block_le_charge i hs)
    · unfold charged
      split
      · exact le_min (hbound i) (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
      · exact hbound i)
  have hbalance := paid_invoice p₁ hp₁
  have hother := published_tail p₁
  unfold localRank
  omega

theorem node_rank_of_receipts (x y : Geom)
    (hraw : 34510370296121 ≤ rawWindow w0 + rawWindow w2 + rawWindow w3)
    (hfee : debit w0 + debit w2 + debit w3 ≤ 34060834683551) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localRank :=
  node_rank_aux x y noPowers (fun _ => rfl) hraw hfee

#print axioms node_rank_of_receipts
end KoalaTaperTransfer

end Merged_KoalaTaperTransfer
