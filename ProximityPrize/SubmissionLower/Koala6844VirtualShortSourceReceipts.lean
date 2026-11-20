import ProximityPrize.SubmissionLower.Koala6844VirtualShortSource
import ProximityPrize.SubmissionLower.Koala6844VirtualShortRankReceipts
import ProximityPrize.SubmissionLower.Koala6844ReceiptsBridge


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetSpecialize SecondJetCoefficients SecondJetCoefficientSpecialization
open Koala6844Normalization Koala6844Receipts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I] [Fintype I]

theorem normalizedRankBudget_eq (src : SourceShape) (hsB : 2*src.s ≤ src.B)
    (hsU : src.s ≤ src.U) (hUL : src.U ≤ src.L) (hqU : src.q ≤ src.U)
    (hcaps : ∀ h ≤ src.s, src.U ≤ (sourceCutoff src h+src.B-1)/degree) :
    normalizedRankBudget (sourceCutoff src) degree src.m src.L src.B src.s src.U src.q =
      localRankBound src := by
  unfold normalizedRankBudget localRankBound
  rw [ordinaryRankBound_eq _ _ hsB hsU hUL hcaps, Koala6844Receipts.sumRange_eq_fin_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact seedlessRankBudget_eq_auxiliaryRankSlice src (j.val+1) hsB
    ((Nat.succ_le_of_lt j.isLt).trans hqU)

theorem exists_physical_source_of_receipt
    {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x domain σ degree agreements errors excess)
    (hSize : Fintype.card I ≤ Koala6844Receipts.nodes)
    (hPole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (hFact : ∀ d < prime, (d.factorial : K) ≠ 0)
    (src : SourceShape) (hForm : sourceWellFormed src = true) (hMargin : sourceMargin src) :
    ∃ F : Poly (K := K), F ≠ 0 ∧
      (∀ e ∈ F.support, 2*e 1+e 3 ≤ src.B ∧ e 1 ≤ src.s ∧ e 1+e 2+e 3 ≤ src.U ∧
        e 1+e 2+e 3+e 4 ≤ src.L+src.q) ∧
      (∀ g ∈ data.seeds, ∀ d ≤ src.k,
        specialize (data.selected g) g ((MvPolynomial.pderiv 1)^[d] F) = 0) ∧
      ((asS F).natDegree < src.n0 → ∀ g ∈ data.seeds,
        coefficientSpecialize (data.selected g) g (asS F).leadingCoeff = 0) := by
  have hm : 2*src.s ≤ src.B ∧ src.B ≤ src.m ∧ src.m+src.s ≤ src.U ∧ src.U ≤ src.L ∧
      src.k ≤ src.s ∧ src.s < src.m ∧ src.k+1 ≤ src.n0 ∧ 2*(src.n0-src.k-1) ≤ src.B ∧
      src.s < prime ∧ src.q ≤ src.U := of_decide_eq_true ((Bool.and_eq_true_iff.mp hForm).1)
  obtain ⟨hsB,_,hmsU,hUL,hks,hsm,_,_,hsp,hqU⟩ := hm
  have hcaps (h : ℕ) (hh : h ≤ src.s) : src.U ≤ (sourceCutoff src h+src.B-1)/degree := by
    have hall := (Bool.and_eq_true_iff.mp hForm).2
    exact of_decide_eq_true (List.all_eq_true.mp hall h (List.mem_range.mpr (Nat.lt_succ_of_le hh)))
  have hQ (g : K) (hg : g ∈ data.seeds) : (data.normalized g).natDegree ≤ degree+poleWidth := by
    have hb := data.normalized_degree g hg
    omega
  have hgap : domain.card * normalizedRankBudget (sourceCutoff src) degree src.m src.L src.B src.s src.U src.q <
      Fintype.card (NormalizedIndex (sourceCutoff src) degree (degree+poleWidth) src.L src.B src.s src.U src.q) := by
    rw [normalizedRankBudget_eq src hsB (by omega) hUL hqU hcaps,←globalColumnCount_eq src hsB hUL]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (domain.card_le_univ.trans hSize)) hMargin
  have hweight (h v : ℕ) (hv : v < sourceCutoff src h) :
      v+SecondJetRelaxedDifferentiation.reserve src.k src.n0 h*(agreements-(degree-2)) < src.m*agreements := by
    change v < src.m*agreements-SecondJetRelaxedDifferentiation.reserve src.k src.n0 h*(agreements-(degree-2)) at hv
    omega
  exact exists_physical_source data hLead (sourceCutoff src) (degree+poleWidth)
    src.m src.L src.B src.s src.U src.q src.k src.n0 hQ (by decide) (by decide)
    hsB hUL hqU hks hsm (fun d hd => hFact d (hd.trans_lt hsp)) hcaps hweight hgap

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
