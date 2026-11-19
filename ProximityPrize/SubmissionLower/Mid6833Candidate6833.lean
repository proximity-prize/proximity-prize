/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. KoalaBear soundness at 68.33 on the full benchmark domain.
Builds on Bome2017's verified 68.32 theorem, Lucieno's comparison and moving-factor methods,
and BitWonka's interpolation and jet constructions. -/
import ProximityPrize.SubmissionLower.Mid6833FiveGroups
import ProximityPrize.SubmissionLower.Mid6833K6833AdaptiveTerminal
import ProximityPrize.SubmissionLower.K6833TerminalCount
import ProximityPrize.SubmissionLower.Mid6833K6833RegularProtocol
import ProximityPrize.SubmissionLower.P33Ledger
namespace ProximityPrize.SubmissionLower.Intermediate6833
open ProximityPrize.Benchmark Genuine6969
open RCN095 RCN156 RCN238 RCN266 RCN319 Koala6831Moving
open LocatorFactorAggregate K6833PrimaryReady K6833FlowSources
open K6833FlowAdaptive K6833FlowPaid K6833Group K6833AdaptiveCert
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem regular : K6833PrimaryBridge.RegularBudget := by
  classical
  intro original R H nz box _ Γ hg A trans field cap _
  let old : DecidableEq F := inferInstance
  change (@Finset.biUnion _ F old A (regularFiber H Γ R.selected)).card≤264040334683142352
  have instEq : old = Classical.decEq F := Subsingleton.elim _ _
  rw [instEq]
  letI : DecidableEq F := Classical.decEq _
  let hchar := Koala6831BenchmarkField.characteristic
  obtain ⟨v⟩ := visit R H Γ hg A field cap trans 5 (by decide)
  let f := aggregateFlag H v.current
  have b := v.paid v.current Finset.Subset.rfl
  rw [accrued_five] at b
  have target : finalBudget≤264040334683142352 := by decide +kernel
  rcases v.current.eq_empty_or_nonempty with empty|ne
  · have zero : (v.current.biUnion (regularFiber H Γ R.selected)).card=0 := by simp [empty]
    have feeSum : (∑ i : Fin 5, (fee i-credit (capStage i) f))≤∑ i : Fin 5, fee i := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 5) _ => Nat.sub_le (fee i) (credit (capStage i) f))
    change (A.biUnion (regularFiber H Γ R.selected)).card≤(v.current.biUnion (regularFiber H Γ R.selected)).card+∑ i : Fin 5, (fee i-credit (capStage i) f) at b
    rw [zero,zero_add] at b
    exact b.trans (feeSum.trans (empty_budget.trans target))
  · obtain ⟨row,entry,rs,ys,ts,budget⟩ := terminal_link f (aggregateFlag_pos H ne) (v.prior ne)
    let info : K6833Residual.TerminalData Dmn := {
      primary := H, primary_ne := nz, primary_box := box, seeds := Γ, u₀ := R.u₀, u₁ := R.u₁,
      selected := R.selected, nodes_card := R.nodes_card, degree := fun g h => R.degree g (hg h),
      agreement := fun g h => R.agreement g (hg h),
      pencil := RCN243.noLargeSelectedPencil_mono R.selected R.seeds Γ 131071 81085 hg R.pencil }
    have bound := P33.row_count info v.current row (P33.rowAt_ok entry) rs ys ts
    change (v.current.biUnion (regularFiber H Γ R.selected)).card≤row.terminalLimit at bound
    change (A.biUnion (regularFiber H Γ R.selected)).card≤(v.current.biUnion (regularFiber H Γ R.selected)).card+∑ i : Fin 5, (fee i-credit (capStage i) f) at b
    omega

theorem candidate : ProtocolClaim 6834 332127561 1073741824 :=
  K6833PrimaryBridge.protocol_of_regularBudget regular
#print axioms candidate
end
end ProximityPrize.SubmissionLower.Intermediate6833
