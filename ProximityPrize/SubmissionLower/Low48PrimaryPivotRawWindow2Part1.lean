import ProximityPrize.SubmissionLower.PrimaryTaperBudget
import Mathlib.Algebra.BigOperators.Intervals
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryRank

set_option Elab.async false

-- merged module KoalaTaperTransfer
section Merged_KoalaTaperTransfer

-- merged module Low48PrimaryPivotBaseline
section Merged_Low48PrimaryPivotBaseline

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace Low48PrimaryPivot
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators

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

abbrev localRank : ℕ := 343744005134722

private abbrev noPowers : BlockIndex → Powers := fun _ => ⟨0, 0, 0⟩

private def paid (p₁ : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if w2.Contains i ∨ w3.Contains i then ∑ q : Column, charge i q
  else charged p₁ noPowers noPowers i

private theorem middle_baseline (p₁ : BlockIndex → Powers) (i : BlockIndex)
    (hlo : 2008 ≤ i.1.val) (hhi : i.1.val < 3514) :
    charged p₁ noPowers noPowers i = baseline i := by
  have hw : ¬ inWindow i := by
    unfold inWindow
    omega
  have h₁ : ¬ i.1.val < 2008 := by omega
  have hz : (noPowers i).expand = fun _ => 0 := by
    funext k
    fin_cases k <;> rfl
  unfold charged fees combine
  simp only [hw, hhi, h₁, ite_false, ite_true]
  split <;> rw [hz] <;> rfl

private theorem sum_window_exchange {ι : Type} (S : Finset ι)
    (first second : ι → Prop) [DecidablePred first] [DecidablePred second]
    (old new baseline : ι → ℕ) (disjoint : ∀ i, first i → ¬ second i)
    (same : ∀ i, first i ∨ second i → old i = baseline i) :
    (∑ i ∈ S, if first i ∨ second i then new i else old i) +
      (∑ i ∈ S, if first i then baseline i else 0) +
      (∑ i ∈ S, if second i then baseline i else 0) =
    (∑ i ∈ S, old i) + (∑ i ∈ S, if first i then new i else 0) +
      (∑ i ∈ S, if second i then new i else 0) := by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h₁ : first i
  · have h₂ := disjoint i h₁
    rw [same i (Or.inl h₁)]
    simp only [h₁, h₂, true_or, ite_true, ite_false, Nat.add_zero]
    exact Nat.add_comm _ _
  · by_cases h₂ : second i
    · rw [same i (Or.inr h₂)]
      simp only [h₁, h₂, or_true, ite_true, ite_false, Nat.add_zero]
      exact Nat.add_comm _ _
    · simp [h₁, h₂]

attribute [local irreducible] Finset.univ

private theorem raw_def (w : Window) :
    rawWindow w = ∑ i : BlockIndex, if w.Contains i then baseline i else 0 := rfl

private theorem debit_def (w : Window) :
    debit w = ∑ i : BlockIndex, if w.Contains i then ∑ q : Column, charge i q else 0 := rfl

private theorem paid_invoice (p₁ : BlockIndex → Powers) :
    (∑ i : BlockIndex, paid p₁ i) + rawWindow w2 + rawWindow w3 =
      (∑ i : BlockIndex, charged p₁ noPowers noPowers i) + debit w2 + debit w3 := by
  rw [raw_def, raw_def, debit_def, debit_def]
  apply sum_window_exchange Finset.univ w2.Contains w3.Contains
    (charged p₁ noPowers noPowers) (fun i => ∑ q : Column, charge i q) baseline
  · intro i h₂
    simp only [w2, w3, Window.Contains] at *
    omega
  · intro i h
    rcases h with h | h
    · simp only [w2, Window.Contains] at h
      exact middle_baseline p₁ i h.1 (by omega)
    · simp only [w3, Window.Contains] at h
      exact middle_baseline p₁ i (by omega) h.2.1

private theorem published_tail (p₁ : BlockIndex → Powers)
    (hp₁ : 9573892230 ≤ savingsSum w1 p₁) :
    (∑ i : BlockIndex, charged p₁ noPowers noPowers i) ≤ 344162560924059 := by
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

theorem node_rank_of_receipts (x y : Geom)
    (hraw : 28571050105634 ≤ rawWindow w2 + rawWindow w3)
    (hfee : debit w2 + debit w3 ≤ 28152494316297) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localRank := by
  classical
  obtain ⟨p₁, hp₁⟩ := K1_13_2_3_4.proof
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
  have hbalance := paid_invoice p₁
  have hother := published_tail p₁ hp₁
  unfold localRank
  omega

#print axioms node_rank_of_receipts
end KoalaTaperTransfer

end Merged_KoalaTaperTransfer

end Merged_KoalaTaperTransfer

-- merged module Low48PrimaryRawDenomSum
section Merged_Low48PrimaryRawDenomSum

-- merged module Low48PrimaryPivotRawChunks
section Merged_Low48PrimaryPivotRawChunks

set_option autoImplicit false

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

def rawChunk (w : Window) (start count : ℕ) : ℕ :=
  ((List.range' start count).map (rawAt w)).sum

theorem joinRaw {w : Window} {start a b x y : ℕ}
    (left : rawChunk w start a = x) (right : rawChunk w (start + a) b = y) :
    rawChunk w start (a + b) = x + y := by
  have happend : rawChunk w start (a + b) = rawChunk w start a + rawChunk w (start + a) b := by
    unfold rawChunk
    rw [← List.range'_append_1, List.map_append, List.sum_append]
  exact happend.trans (congrArg₂ (· + ·) left right)

theorem rawCompute_eq (w : Window) :
    rawCompute w = rawChunk w w.offsetLo (w.offsetHi + 1 - w.offsetLo) := rfl

end Low48PrimaryPivot.RawReceipt

end Merged_Low48PrimaryPivotRawChunks

-- merged module Low48PrimaryPivotRawFast
section Merged_Low48PrimaryPivotRawFast

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2 K1_13_2_3
open Low48PrimaryPivot (baselineFast)

private theorem denom_neg {u : ℤ} (h : u < 0) : denominator u = 0 := by
  simp [denominator, h]

private theorem cum_neg (d : ℤ) {u : ℤ} (h : u < 0) : cumulative d u = 0 := by
  simp [cumulative, h]

private theorem cum_four (d u : ℤ) (hd : 0 ≤ d) (hcap : u ≤ 3*d) (hlo : u ≤ 2*d+2) :
    cumulative d u = denominator u - denominator (u-d-1) - denominator (u-d-2) -
      denominator (u-d-3) := by
  by_cases hu : u < 0
  · simp [cum_neg d hu, denom_neg hu, denom_neg (by omega : u-d-1 < 0),
      denom_neg (by omega : u-d-2 < 0), denom_neg (by omega : u-d-3 < 0)]
  · simp [cumulative, not_lt.mpr hd, hu, min_eq_left hcap,
      denom_neg (by omega : u-2*d-3 < 0), denom_neg (by omega : u-2*d-4 < 0),
      denom_neg (by omega : u-2*d-5 < 0), denom_neg (by omega : u-3*d-6 < 0)]

private theorem cum_one (d u : ℤ) (hd : 0 ≤ d) (hu : u ≤ d) :
    cumulative d u = denominator u := by
  rw [cum_four d u hd (by omega) (by omega)]
  simp [denom_neg (by omega : u-d-1 < 0), denom_neg (by omega : u-d-2 < 0),
    denom_neg (by omega : u-d-3 < 0)]

def columnsAt (o : ℕ) : ℤ :=
  denominator 1650 - denominator (1649 - (o : ℤ))

private theorem columns_eq (o : ℕ) (order : ℤ) :
    oldCount ⟨1650, 1650-(o : ℤ), 1650, 550, order⟩ = columnsAt o := by
  have hmin : min (1650 : ℤ) (1650-(o : ℤ)-1) = 1649-(o : ℤ) := by
    rw [min_eq_right (by omega)]
    omega
  change cappedCount 1650 1650 550 - cappedCount 1650 (min 1650 (1650-(o : ℤ)-1)) 550 =
    columnsAt o
  rw [hmin]
  simp only [cappedCount, show ¬(550 : ℤ) < 0 by decide, ↓reduceIte]
  rw [cum_one 1650 1650 (by decide) le_rfl,
    cum_one 1650 (1649-(o : ℤ)) (by decide) (by omega),
    cum_neg _ (by decide : (1650 : ℤ)-3*(550+1) < 0),
    cum_neg _ (by omega : (1649-(o : ℤ))-3*(550+1) < 0)]
  simp [columnsAt]

def targetAt (g o : ℕ) : ℤ :=
  let removed := (4649 - (g : ℤ)) / 4 + 1
  let degree := 1650 - removed
  let order := 4649 - (g : ℤ) - (o : ℤ)
  let lower := 1649 - (o : ℤ)
  denominator order - denominator (order - 3*removed) -
    denominator (lower-degree-1) - denominator (lower-degree-2) -
    denominator (lower-degree-3)

theorem target_eq (g o : ℕ) (hg : 1650 ≤ g) (hlo : 3000 ≤ g+o)
    (hhi : g+o < 4650) :
    targetCount ⟨1650, 1650-(o : ℤ), 1650, 550, 4650-(g : ℤ)-(o : ℤ)⟩ = targetAt g o := by
  let removed : ℤ := (4649-(g : ℤ))/4+1
  let degree : ℤ := 1650-removed
  let order : ℤ := 4649-(g : ℤ)-(o : ℤ)
  let lower : ℤ := 1649-(o : ℤ)
  have hbalance :
      (4650-(g : ℤ)-(o : ℤ))-1-(1650-(o : ℤ))+1650 = 4649-(g : ℤ) := by omega
  have hpos : ¬4649-(g : ℤ) < 0 := by omega
  have hdiv : (4649-(g : ℤ))/4 ≤ 1650 := by omega
  have hord : (4650-(g : ℤ)-(o : ℤ))-1 = order := by dsimp [order]; omega
  have hlow : (1650-(o : ℤ))-1 = lower := by dsimp [lower]; omega
  have hd : 0 ≤ degree := by dsimp [degree, removed]; omega
  have hthree : lower ≤ 3*degree := by dsimp [lower, degree, removed]; omega
  have htwo : lower ≤ 2*degree+2 := by dsimp [lower, degree, removed]; omega
  have hcut : order-3*removed ≤ degree := by dsimp [order, degree, removed]; omega
  have hmax : order ≤ 1650 := by dsimp [order]; omega
  change (let balance := (4650-(g : ℤ)-(o : ℤ))-1-(1650-(o : ℤ))+1650
    if balance < 0 then 0 else
      let r := min 1650 (balance / 4) + 1
      cumulative 1650 ((4650-(g : ℤ)-(o : ℤ))-1) -
        cumulative (1650-r) ((4650-(g : ℤ)-(o : ℤ))-1-3*r) -
        cumulative 1650 ((1650-(o : ℤ))-1) + cumulative (1650-r) ((1650-(o : ℤ))-1)) =
      targetAt g o
  rw [hbalance]
  simp only [hpos, ↓reduceIte, min_eq_right hdiv, hord, hlow]
  change cumulative 1650 order - cumulative degree (order-3*removed) -
    cumulative 1650 lower + cumulative degree lower = targetAt g o
  rw [cum_one 1650 order (by decide) hmax, cum_one degree (order-3*removed) hd hcut,
      cum_one 1650 lower (by decide) (by dsimp [lower]; omega),
      cum_four degree lower hd hthree htwo]
  change _ = denominator order - denominator (order-3*removed) -
    denominator (lower-degree-1) - denominator (lower-degree-2) -
    denominator (lower-degree-3)
  ring

private theorem grade_eq (g o : ℕ) (hg : 1650 ≤ g) (hlo : 3000 ≤ g+o)
    (hhi : g+o < 4650) (ho : o ≤ 2999) :
    baselineFast g o = (min (columnsAt o) (targetAt g o)).toNat := by
  let F : Flag := ⟨1650, 1650-(o : ℤ), 1650, 550, 4650-(g : ℤ)-(o : ℤ)⟩
  have hdegree : min (g : ℤ) 1650 = 1650 := min_eq_right (by omega)
  have hindex : -((o : ℤ)-1650) = 1650-(o : ℤ) := by omega
  have hord : 3000-(g : ℤ)-((o : ℤ)-1650) = 4650-(g : ℤ)-(o : ℤ) := by omega
  have hpos : ¬4650-(g : ℤ)-(o : ℤ) ≤ 0 := by omega
  have hupper : min (1650 : ℤ) (2999-((o : ℤ)-1650)) = 1650 := min_eq_left (by omega)
  have hkernel : kernelLower F = oldCount F - targetCount F := by
    simp [F, kernelLower]
  have hcount : oldCount F = columnsAt o := columns_eq o _
  have htarget : targetCount F = targetAt g o := target_eq g o hg hlo hhi
  unfold baselineFast
  simp only [hdegree, hindex, hord, hpos, ↓reduceIte, hupper]
  change (min (oldCount F) (oldCount F - max 0 (kernelLower F))).toNat =
    (min (columnsAt o) (targetAt g o)).toNat
  rw [hkernel, hcount, htarget]
  congr 1
  omega

def fastAt (w : Window) (o : ℕ) : ℕ :=
  let lo := max w.gradeLo (w.diagonalLo-o)
  let hi := min w.gradeHi (w.diagonalHi+1-o)
  let columns := columnsAt o
  ((List.range' lo (hi-lo)).map fun g => (min columns (targetAt g o)).toNat).sum

theorem rawAt_fast (w : Window) (hg : 1650 ≤ w.gradeLo) (hl : 3000 ≤ w.diagonalLo)
    (hh : w.diagonalHi < 4650) (o : ℕ) (ho : o ≤ 2999) : rawAt w o = fastAt w o := by
  unfold rawAt fastAt
  apply congrArg List.sum
  apply List.map_congr_left
  intro g h
  have hr := List.mem_range'_1.mp h
  refine grade_eq g o (by have h := le_max_left w.gradeLo (w.diagonalLo-o); omega) ?_ ?_ ho
  · have h := le_max_right w.gradeLo (w.diagonalLo-o)
    omega
  · have h := min_le_right w.gradeHi (w.diagonalHi+1-o)
    omega



end Low48PrimaryPivot.RawReceipt

end Merged_Low48PrimaryPivotRawFast

-- merged module Low48PrimaryRawDenomSum
section Merged_Low48PrimaryRawDenomSum

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Low48PrimaryPivot.RawClosed
open K1_13_2 Finset
open scoped BigOperators

private theorem twice_dvd (z : ℤ) : (2 : ℤ) ∣ z*(z-1) := by
  obtain h | h : z=2*(z/2) ∨ z=2*(z/2)+1 := by omega
  · exact ⟨(z/2)*(z-1), by linear_combination (z-1)*h⟩
  · exact ⟨z*(z/2), by linear_combination z*h⟩

private def cubic (q r : ℤ) := 12*q^3+(21+6*r)*q^2+(r^2+7*r+11)*q+(r^2+r+2)

private theorem double_den {u : ℤ} (hu : 0≤u) : 2*denominator u = cubic (u/6) (u%6) := by
  simp only [denominator, show ¬ u<0 by omega, ↓reduceIte]
  set q:=u/6
  set r:=u%6
  have hp : (2:ℤ) ∣ r*(r+1) := by
    convert twice_dvd (r+1) using 1 <;> ring
  unfold cubic
  linear_combination Int.ediv_mul_cancel hp + q * Int.ediv_mul_cancel (twice_dvd r) +
    (57+6*r)* Int.ediv_mul_cancel (twice_dvd q)

/-- Twenty-four times the sum of n values of the denominator polynomial for one residue. -/
private def primitive (q r d n : ℤ) : ℤ :=
  let p1 := -d*(36*q^2+2*(21+6*r)*q+(r^2+7*r+11))
  let p2 := d^2*(36*q+21+6*r)
  let p3 := -12*d^3
  12*n*cubic q r+6*n*(n-1)*p1+2*n*(n-1)*(2*n-1)*p2+3*n^2*(n-1)^2*p3

private theorem primitive_sum (q r d : ℤ) (n : ℕ) :
    primitive q r d n = 12 * ∑ i ∈ range n, cubic (q-d*(i:ℤ)) r := by
  induction n with
  | zero => simp [primitive]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← ih, Nat.cast_succ]
    unfold primitive cubic
    ring

def denomRun (x : ℤ) (d n : ℕ) : ℤ :=
  let len := min n (x/(6*(d:ℤ))+1).toNat
  primitive (x/6) (x%6) d len / 24

private theorem run_spec (x : ℤ) (d n : ℕ) (hd : d=1 ∨ d=4) :
    denomRun x d n = ∑ i ∈ range n, denominator (x-6*(d:ℤ)*(i:ℤ)) := by
  let len := min n (x/(6*(d:ℤ))+1).toNat
  have hn : len≤n := min_le_left _ _
  have pos (i : ℕ) (hi : i<len) : 0≤x-6*(d:ℤ)*(i:ℤ) := by
    dsimp [len] at hi; rcases hd with rfl|rfl <;> norm_num at * <;> omega
  have neg (i : ℕ) (hi : i<n-len) : x-6*(d:ℤ)*(↑(len+i):ℤ)<0 := by
    dsimp [len] at *; rcases hd with rfl|rfl <;> norm_num at * <;> omega
  have core : primitive (x/6) (x%6) d len = 24 * ∑ i ∈ range len, denominator (x-6*(d:ℤ)*(i:ℤ)) := by
    rw [primitive_sum]
    have eq : ∑ i ∈ range len, cubic (x/6-(d:ℤ)*(i:ℤ)) (x%6) =
        ∑ i ∈ range len, 2*denominator (x-6*(d:ℤ)*(i:ℤ)) := by
      apply sum_congr rfl; intro i hi
      rw [double_den (pos i (mem_range.mp hi))]
      have ha : x-6*(d:ℤ)*(i:ℤ) = x+6*(-((d:ℤ)*(i:ℤ))) := by ring
      rw [ha, Int.add_mul_ediv_left _ _ (by decide), Int.add_mul_emod_self_left]; rfl
    rw [eq, ← mul_sum]; ring
  have tail : ∑ i ∈ range (n-len), denominator (x-6*(d:ℤ)*(↑(len+i):ℤ)) = 0 := by
    apply sum_eq_zero; intro i hi; rw [denominator, if_pos (neg i (mem_range.mp hi))]
  change primitive (x/6) (x%6) d len / 24 = _
  rw [core, Int.mul_ediv_cancel_left _ (by decide)]
  conv_rhs => rw [show n=len+(n-len) by omega, sum_range_add]
  rw [tail, add_zero]

theorem run1 (x : ℤ) (n : ℕ) : denomRun x 1 n = ∑ i ∈ range n, denominator (x-6*(i:ℤ)) := by
  simpa using run_spec x 1 n (Or.inl rfl)

theorem run4 (x : ℤ) (n : ℕ) : denomRun x 4 n = ∑ i ∈ range n, denominator (x-24*(i:ℤ)) := by
  simpa using run_spec x 4 n (Or.inr rfl)

end Low48PrimaryPivot.RawClosed

end Merged_Low48PrimaryRawDenomSum

end Merged_Low48PrimaryRawDenomSum

-- merged module Low48PrimaryPivotRawWindow2Part0
section Merged_Low48PrimaryPivotRawWindow2Part0

-- merged module Low48PrimaryRawSplit
section Merged_Low48PrimaryRawSplit

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
namespace Low48PrimaryPivot.RawClosed
open Finset K1_13_2 K1_13_2_2 K1_13_2_3
open scoped BigOperators
open Low48PrimaryPivot.RawReceipt (columnsAt targetAt target_eq)

def firstCross (p : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0,lo,_ => lo
  | fuel+1,lo,hi => if hi≤lo then lo else
    let mid := (lo+hi)/2
    if p mid then firstCross p fuel lo mid else firstCross p fuel (mid+1) hi

theorem cross_spec (p : ℕ → Bool) (fuel lo hi : ℕ) (h : lo≤hi) (hn : hi-lo<2^fuel) :
    let k:= firstCross p fuel lo hi
    lo≤k ∧ k≤hi ∧ (k=lo ∨ p (k-1)=false) ∧ (k=hi ∨ p k=true) := by
  induction fuel generalizing lo hi with
  | zero => simp only [pow_zero] at hn; simp [firstCross, show hi=lo by omega]
  | succ f ih =>
    rw [pow_succ] at hn
    simp only [firstCross]
    split
    · rename_i he; simp [show hi=lo by omega]
    · rename_i he
      let mid:=(lo+hi)/2
      have hm : lo≤mid ∧ mid<hi := by dsimp [mid]; omega
      change (let k:=if p mid=true then firstCross p f lo mid else firstCross p f (mid+1) hi; _) 
      split
      · rename_i hp
        obtain ⟨a,b,c,e⟩:=ih lo mid hm.1 (by dsimp [mid]; omega)
        exact ⟨a, b.trans hm.2.le, c, Or.inr (e.elim (fun eq => eq ▸ hp) id)⟩
      · rename_i hp
        obtain ⟨a,b,c,e⟩:=ih (mid+1) hi (by omega) (by dsimp [mid]; omega)
        refine ⟨(show lo≤mid+1 by omega).trans a,b,Or.inr ?_,e⟩
        rcases c with c|c
        · rw [c]; simpa using hp
        · exact c

theorem target_nonneg {g o : ℕ} (hg : 1650≤g) (hlo : 3000≤g+o) (hhi : g+o<4650) :
    0≤targetAt g o := by
  rw [← target_eq g o hg hlo hhi, ← K1_13_2_2_4.proof K1_13_2_2_2.proof]
  positivity

private theorem target_mono_order {d l u c a b : ℤ} (hab : a≤b) :
    targetCount ⟨d,l,u,c,a⟩ ≤ targetCount ⟨d,l,u,c,b⟩ := by
  rw [← K1_13_2_2_4.proof K1_13_2_2_2.proof, ← K1_13_2_2_4.proof K1_13_2_2_2.proof]
  apply Int.ofNat_le.mpr; apply card_le_card
  intro e he; rw [mem_targetColumns] at he ⊢
  change _ ∧ _ ∧ (e.weight contactWeight : ℤ)<a at he
  change _ ∧ _ ∧ (e.weight contactWeight : ℤ)<b
  exact ⟨he.1, he.2.1, he.2.2.trans_le hab⟩

theorem target_anti {g h o : ℕ} (gh : g≤h) (hg : 1650≤g) (hlo : 3000≤g+o) (hhi : h+o<4650) :
    targetAt h o≤targetAt g o := by
  rw [← target_eq g o hg hlo (by omega), ← target_eq h o (by omega) (by omega) hhi]
  apply target_mono_order
  exact sub_le_sub_right (sub_le_sub_left (Int.ofNat_le.mpr gh) 4650) _

def laneLen (n r : ℕ) := (n+23-r)/24

theorem sum_lanes (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range n, f i = ∑ r ∈ range 24, ∑ j ∈ range (laneLen n r), f (r+24*j) := by
  classical
  rw [sum_sigma']
  refine sum_bij' (fun i _ => ⟨i%24,i/24⟩) (fun v _ => v.1+24*v.2) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_range] at hi; simp only [mem_sigma,mem_range,laneLen]; omega
  · rintro ⟨r,i⟩ hi; simp only [mem_sigma,mem_range,laneLen] at hi; simp only [mem_range]; omega
  · intro i hi; dsimp; omega
  · rintro ⟨r,i⟩ hi; simp only [mem_sigma,mem_range] at hi
    dsimp; congr <;> omega
  · intro i hi; dsimp; congr 1; omega

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (lo n : ℕ) :
    ((List.range' lo n).map f).sum = ∑ i ∈ range n, f (lo+i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range'_concat, Finset.sum_range_succ, ih]

end Low48PrimaryPivot.RawClosed

end Merged_Low48PrimaryRawSplit

-- merged module Low48PrimaryRawFastSum
section Merged_Low48PrimaryRawFastSum

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
namespace Low48PrimaryPivot.RawClosed
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators
open Low48PrimaryPivot.RawReceipt
open Low48PrimaryPivot.RawReceipt (targetAt columnsAt fastAt rawAt_fast)

private def positiveRun (x : ℤ) (d n : ℕ) := if x<0 then 0 else denomRun x d n
private theorem positiveRun_eq (x : ℤ) (d n : ℕ) (hd : d=1 ∨ d=4) :
    positiveRun x d n=denomRun x d n := by
  by_cases hx : x<0
  · simp only [positiveRun,hx,↓reduceIte]; rcases hd with rfl|rfl
    · rw [run1]; symm; apply sum_eq_zero; intro i _; rw [denominator, if_pos (by omega)]
    · rw [run4]; symm; apply sum_eq_zero; intro i _; rw [denominator, if_pos (by omega)]
  · simp [positiveRun,hx]

private def stripe (g o n : ℕ) : ℤ :=
  let r := (4649-(g:ℤ))/4+1
  let a := 4649-(g:ℤ)-(o:ℤ)
  let z := r-(o:ℤ)-2
  positiveRun a 4 n - positiveRun (a-3*r) 1 n - positiveRun z 1 n -
    positiveRun (z-1) 1 n - positiveRun (z-2) 1 n

private theorem stripe_eq (g o n : ℕ) : stripe g o n = ∑ i ∈ range n, targetAt (g+24*i) o := by
  simp only [stripe,positiveRun_eq _ _ _ (Or.inl rfl),positiveRun_eq _ _ _ (Or.inr rfl),run4,run1,
    ← sum_sub_distrib]
  apply sum_congr rfl; intro i _
  simp only [targetAt,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hdiv : (4649-((g:ℤ)+24*(i:ℤ)))/4=(4649-(g:ℤ))/4-6*(i:ℤ) := by omega
  rw [hdiv]
  repeat' first | omega | congr 1

private def tailCost (g o n : ℕ) : ℤ := if n=0 then 0 else
  ((List.range' 0 24).map fun r => stripe (g+r) o (laneLen n r)).sum

private theorem tail_eq (g o n : ℕ) : tailCost g o n = ∑ i ∈ range n, targetAt (g+i) o := by
  by_cases zero : n=0
  · simp [tailCost,zero]
  · simp only [tailCost,zero,↓reduceIte,list_sum_range,zero_add,stripe_eq]
    rw [sum_lanes (fun i => targetAt (g+i) o) n]
    simp only [Nat.add_assoc]

private def closedAt (w : Window) (o : ℕ) : ℕ :=
  let lo:=max w.gradeLo (w.diagonalLo-o)
  let n:=min w.gradeHi (w.diagonalHi+1-o)-lo
  let col:=columnsAt o
  let k:=firstCross (fun i => decide (targetAt (lo+i) o < col)) 13 0 n
  k*col.toNat + (tailCost (lo+k) o (n-k)).toNat

private theorem fast_closed (w : Window) (o : ℕ) (hg : 1650≤w.gradeLo) (hl : 3000≤w.diagonalLo)
    (hh : w.diagonalHi<4650) : fastAt w o = closedAt w o := by
  let lo:=max w.gradeLo (w.diagonalLo-o)
  let n:=min w.gradeHi (w.diagonalHi+1-o)-lo
  let c:=columnsAt o
  let p:=fun i : ℕ => decide (targetAt (lo+i) o < c)
  let k:= firstCross p 13 0 n
  have valid (i : ℕ) (hi : i<n) : 1650≤lo+i ∧ 3000≤lo+i+o ∧ lo+i+o<4650 := by
    have h1:= le_max_left w.gradeLo (w.diagonalLo-o)
    have h2:= le_max_right w.gradeLo (w.diagonalLo-o)
    have h3:= min_le_right w.gradeHi (w.diagonalHi+1-o)
    dsimp [n,lo] at *; omega
  have hn : n < 2^13 := by
    have h:=min_le_right w.gradeHi (w.diagonalHi+1-o)
    dsimp [n]; norm_num; omega
  have hs:=cross_spec p 13 0 n (Nat.zero_le _) (by simpa using hn)
  change 0≤k ∧ k≤n ∧ (k=0 ∨ p (k-1)=false) ∧ (k=n ∨ p k=true) at hs
  obtain ⟨_,hk,hL,hR⟩:= hs
  have left (i : ℕ) (hi : i<k) : c≤targetAt (lo+i) o := by
    have hnz : k≠0 := by omega
    have hp:=hL.resolve_left hnz
    have ht : c≤targetAt (lo+(k-1)) o := by simpa [p] using hp
    have va:=valid i (by omega);have vb:=valid (k-1) (by omega)
    exact ht.trans (target_anti (by omega : lo+i≤lo+(k-1)) va.1 va.2.1 vb.2.2)
  have right (i : ℕ) (hi : i<n-k) : targetAt (lo+(k+i)) o ≤ c := by
    have hkn : k≠n := by omega
    have hp:=hR.resolve_left hkn
    have ht : targetAt (lo+k) o < c := by simpa [p] using hp
    have va:=valid k (by omega);have vb:=valid (k+i) (by omega)
    exact (target_anti (by omega : lo+k≤lo+(k+i)) va.1 va.2.1 vb.2.2).trans ht.le
  change ((List.range' lo n).map fun g => (min c (targetAt g o)).toNat).sum =
    k*c.toNat+(tailCost (lo+k) o (n-k)).toNat
  rw [list_sum_range]
  have split := sum_range_add (fun i => (min c (targetAt (lo+i) o)).toNat) k (n-k)
  rw [show k+(n-k)=n by omega] at split
  rw [split,tail_eq]
  congr 1
  · calc
      _ = ∑ _ ∈ range k, c.toNat := sum_congr rfl (fun i hi => by rw [min_eq_left (left i (mem_range.mp hi))])
      _ = _ := by simp
  · have pos (i : ℕ) (hi : i<n-k) : 0≤targetAt (lo+k+i) o := by
      have v:=valid (k+i) (by omega)
      rw [Nat.add_assoc]; exact target_nonneg v.1 v.2.1 v.2.2
    apply Int.ofNat_inj.mp
    rw [Nat.cast_sum,Int.toNat_of_nonneg (sum_nonneg (fun i hi => pos i (mem_range.mp hi)))]
    apply sum_congr rfl; intro i hi
    rw [min_eq_right (right i (mem_range.mp hi)), ← Nat.add_assoc, Int.toNat_of_nonneg (pos i (mem_range.mp hi))]

def closedChunk (w : Window) (start count : ℕ) : ℕ :=
  ((List.range' start count).map (closedAt w)).sum

theorem rawChunk_closed (w : Window) (start count : ℕ)
    (hg : 1650≤w.gradeLo) (hl : 3000≤w.diagonalLo) (hh : w.diagonalHi<4650)
    (ho : start+count≤3000) : rawChunk w start count=closedChunk w start count := by
  unfold rawChunk closedChunk
  apply congrArg List.sum; apply List.map_congr_left; intro o h
  have hr:=List.mem_range'_1.mp h
  exact (rawAt_fast w hg hl hh o (by omega)).trans (fast_closed w o hg hl hh)

#print axioms rawChunk_closed
end Low48PrimaryPivot.RawClosed

end Merged_Low48PrimaryRawFastSum

-- merged module Low48PrimaryPivotRawWindow2Part0
section Merged_Low48PrimaryPivotRawWindow2Part0

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At322 : rawChunk w2 322 16 = 334716499936 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 322 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At338 : rawChunk w2 338 16 = 362914994745 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 338 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At354 : rawChunk w2 354 16 = 389882069846 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 354 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged_Low48PrimaryPivotRawWindow2Part0

end Merged_Low48PrimaryPivotRawWindow2Part0

-- merged module Low48PrimaryPivotRawWindow2Part1
section Merged_Low48PrimaryPivotRawWindow2Part1

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At370 : rawChunk w2 370 16 = 415482599923 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 370 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At386 : rawChunk w2 386 16 = 439777509404 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 386 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At402 : rawChunk w2 402 16 = 460501578311 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 402 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged_Low48PrimaryPivotRawWindow2Part1
