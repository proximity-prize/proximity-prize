/- Apache-2.0. Original-family reduction based on the Bome2017/Lucieno five groups and BitWonka PR 623. -/
import ProximityPrize.SubmissionLower.Night6836Groups
import ProximityPrize.SubmissionLower.Night6836Frontier
import ProximityPrize.SubmissionLower.Night6836PrimaryShell
namespace ProximityPrize.SubmissionLower.Night6836Terminal
open ProximityPrize.Benchmark Genuine6969
open RCN095 RCN156 RCN238 RCN266 RCN319 Koala6831Moving
open LocatorFactorAggregate Left6836Ready Night6836FlowSources
open Night6836FlowAdaptive Night6836FlowPaid Night6836Group Night6836AdaptiveCert
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem credit_eq (j:Fin 5) (f:FlagDegree) :
    credit (capStage j) f=priceAt j f.all (middle f) (total f) := by
  have hraw : f = raw f.all (middle f) (total f) := by
    cases f with | mk z y r =>
      change (⟨z,y,r⟩ : FlagDegree)=⟨z+y+r-(y+r),y+r-r,r⟩
      congr <;> omega
  by_cases pos : 0<f.all
  · have same {a b : FlagDegree} (e : a=b) (ha : 0<a.all) (hb : 0<b.all) :
        stagePrice a ha (capStage j) (capStage j).numbers.slopeCap =
        stagePrice b hb (capStage j) (capStage j).numbers.slopeCap := by cases e; rfl
    simpa only [credit,priceAt,dif_pos pos,stagePrice] using same hraw pos pos
  · simp only [credit,priceAt,dif_neg pos]


def finalBudget : ℕ := 267159171641512934
def charged (r y t : ℕ) : ℕ := ∑ i : Fin 5, (fee i-priceAt i r y t)
theorem charged_antitone (r y l t : ℕ) (rp : 0<r) (ry : r≤y) (yl : y≤l) (lt : l≤t) :
    charged r y t ≤ charged r y l := by
  unfold charged
  apply Finset.sum_le_sum
  intro i _
  apply Nat.sub_le_sub_left
  unfold priceAt
  simp only [dif_pos rp]
  apply price_mono rp rp
  obtain ⟨rm,ym,tm⟩ := raw_cumul ry yl
  obtain ⟨rn,yn,tn⟩ := raw_cumul ry (yl.trans lt)
  exact ⟨rm.trans_le rn.symm.le,ym.trans_le yn.symm.le,tm.trans_le (lt.trans_eq tn.symm)⟩

theorem empty_budget : (∑ i : Fin 5, fee i) ≤ finalBudget := by decide +kernel

def RowBudget : Prop :=
  ∀(original : Finset F) (R : Ready Dmn original) (H : P4 F), H≠0 →
    H∈LocatorLowQuotient.nestedCoefficientBox F Stage.primary.cutoff 131071 83491 444 99 →
    ∀(Γ : Finset F), Γ⊆R.seeds → ∀(A : Finset (RegularIndex H)), A.Nonempty →
    let f := aggregateFlag H A
    f.all≤18 → middle f≤maxY f.all → total f≤endCap f.all (middle f) →
    (A.biUnion (regularFiber H Γ R.selected)).card≤finalBudget-charged f.all (middle f) (total f)

def UniformRowBudget : Prop :=
  ∀(original : Finset F) (R : Ready Dmn original) (H : P4 F), H≠0 →
    H∈LocatorLowQuotient.nestedCoefficientBox F Stage.primary.cutoff 131071 83491 444 99 →
    ∀(Γ : Finset F), Γ⊆R.seeds → ∀(A : Finset (RegularIndex H)), A.Nonempty →
    let f := aggregateFlag H A
    f.all≤18 → middle f≤maxY f.all → total f≤endCap f.all (middle f) →
    (A.biUnion (regularFiber H Γ R.selected)).card≤finalBudget-charged f.all (middle f) (middle f)

theorem rows_of_uniform (h : UniformRowBudget) : RowBudget := by
  intro original R H nz box Γ hg A ne _ hr hy ht
  let f := aggregateFlag H A
  have pos := aggregateFlag_pos H ne
  have ry : f.all≤middle f := Nat.le_add_left _ _
  have yt : middle f≤total f := by unfold middle total; omega
  have base := h original R H nz box Γ hg A ne hr hy ht
  exact base.trans (Nat.sub_le_sub_left (charged_antitone f.all (middle f) (middle f) (total f) pos ry le_rfl yt) _)
theorem regular_of_rows (rows : RowBudget) : Night6836PrimaryBridge.RegularBudget := by
  classical
  intro original R H nz box _ Γ hg A trans field cap _
  let old : DecidableEq F := inferInstance
  change (@Finset.biUnion _ F old A (regularFiber H Γ R.selected)).card≤267159171641512934
  have instEq : old = Classical.decEq F := Subsingleton.elim _ _
  rw [instEq]
  letI : DecidableEq F := Classical.decEq _
  let hchar := Koala6831BenchmarkField.characteristic
  obtain ⟨v⟩ := visit R H Γ hg A field cap trans 5 (by decide)
  let f := aggregateFlag H v.current
  have b := v.paid v.current Finset.Subset.rfl
  rw [accrued_five] at b
  have target : finalBudget≤267159171641512934 := by decide +kernel
  rcases v.current.eq_empty_or_nonempty with empty|ne
  · have zero : (v.current.biUnion (regularFiber H Γ R.selected)).card=0 := by simp [empty]
    have feeSum : (∑ i : Fin 5, (fee i-credit (capStage i) f))≤∑ i : Fin 5, fee i := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 5) _ => Nat.sub_le (fee i) (credit (capStage i) f))
    change (A.biUnion (regularFiber H Γ R.selected)).card≤(v.current.biUnion (regularFiber H Γ R.selected)).card+∑ i : Fin 5, (fee i-credit (capStage i) f) at b
    rw [zero,zero_add] at b
    exact b.trans (feeSum.trans (empty_budget.trans target))

  · have hp := aggregateFlag_pos H ne
    have pr := v.prior ne
    obtain ⟨_,hr,ry,hy⟩ := inside hp pr
    have t := end_bound f hp pr
    have bills : (∑ i : Fin 5, (fee i-credit (capStage i) f))=charged f.all (middle f) (total f) := by
      simp only [charged,credit_eq]
    have lim := rows original R H nz box Γ hg v.current ne hr hy t
    change (A.biUnion (regularFiber H Γ R.selected)).card≤(v.current.biUnion (regularFiber H Γ R.selected)).card+∑ i : Fin 5, (fee i-credit (capStage i) f) at b
    have s : charged f.all (middle f) (total f)≤finalBudget := (Finset.sum_le_sum (s:=Finset.univ)
      (fun (i : Fin 5) _ => Nat.sub_le (fee i) (priceAt i f.all (middle f) (total f)))).trans empty_budget
    rw [bills] at b
    change (@Finset.biUnion _ F old v.current (regularFiber H Γ R.selected)).card≤finalBudget-charged f.all (middle f) (total f) at lim
    rw [instEq] at lim
    omega
theorem short_of_rows (rows : RowBudget) : Intermediate.OpenAt 181039 274980640798883310 2133 9615 :=
  Night6836PrimaryBridge.short_of_regularBudget (regular_of_rows rows)
#print axioms short_of_rows
end
end ProximityPrize.SubmissionLower.Night6836Terminal
