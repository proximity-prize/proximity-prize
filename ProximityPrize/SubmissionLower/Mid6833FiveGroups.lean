/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Chain the five exhausted groups on the same received word and
the same surviving factors. The reserve is evaluated on the final aggregate. -/
import ProximityPrize.SubmissionLower.Mid6833GroupRun
import ProximityPrize.SubmissionLower.Mid6833K6833AdaptiveFees
namespace ProximityPrize.SubmissionLower.K6833Group
open scoped Classical BigOperators
open RCN095 RCN156 RCN238 RCN266 RCN319 Koala6831Moving K6833FlowAdaptive K6833FlowPaid
open K6833FlowSources K6833FlowStages K6833AdaptiveCert K6833PrimaryReady LocatorFactorAggregate
open LocatorPhase6800Oracle (sumFlag_all)
noncomputable section
set_option maxRecDepth 60000
set_option maxHeartbeats 2400000
variable {K I : Type} [Field K] [Fintype I]
local instance mid6833Local_FiveGroups_14  : DecidableEq K := Classical.decEq _

theorem valid_menu (i : Fin 5) (s : Stage) (hs : s∈menu i) : s≠.primary := by
  fin_cases i <;> cases s <;> simp_all [menu]
theorem dominates_menu (i : Fin 5) (s : Stage) (hs : s∈menu i) : Dominates s (capStage i) := by
  fin_cases i <;> cases s <;> simp [menu] at hs <;> unfold Dominates <;> decide +kernel

def accrued : ℕ → FlagDegree → ℕ
  | 0, _ => 0
  | n+1, f => accrued n f + if h:n<5 then fee ⟨n,h⟩ - credit (capStage ⟨n,h⟩) f else 0

theorem accrued_five (f : FlagDegree) : accrued 5 f=∑ j : Fin 5, (fee j-credit (capStage j) f) := by
  let term (i : ℕ) := if h:i<5 then fee ⟨i,h⟩-credit (capStage ⟨i,h⟩) f else 0
  calc
    _ = ∑ i ∈ Finset.range 5, term i := by simp [accrued,term,Finset.sum_range_succ]
    _ = ∑ i : Fin 5, term i.val := (Fin.sum_univ_eq_sum_range term 5).symm
    _ = _ := Finset.sum_congr rfl fun i _=>by simp [term,i.isLt]

theorem card_peel {H : P4 K} {T A : Finset (RegularIndex H)} (su : T⊆A) (groups : RegularIndex H→Finset K) :
    (A.biUnion groups).card ≤ ((A\T).biUnion groups).card+(T.biUnion groups).card := by
  classical
  calc
    _ = (((A\T).biUnion groups) ∪ (T.biUnion groups)).card := by rw [←Finset.union_biUnion,Finset.sdiff_union_of_subset su]
    _ ≤ _ := Finset.card_union_le _ _

theorem ne_of_pos {H : P4 K} {T : Finset (RegularIndex H)} (p : 0<(aggregateFlag H T).all) : T.Nonempty := by
  by_contra! h
  have e : T=∅ := Finset.not_nonempty_iff_eq_empty.mp (by simpa using h)
  change 0<(contactFlag (LocatorBatchProductRoute.regularProduct H T)).all at p
  rw [contactFlag_regularProduct,sumFlag_all,e,Finset.sum_empty] at p
  omega

structure Visit (H : P4 K) (A : Finset (RegularIndex H)) (fib : RegularIndex H→Finset K) (j:ℕ) where
  current : Finset (RegularIndex H)
  subset : current⊆A
  prior : current.Nonempty → Prior j (aggregateFlag H current)
  paid : ∀ final⊆current, (A.biUnion fib).card ≤ (current.biUnion fib).card+accrued j (aggregateFlag H final)

theorem visit [CharP K 2130706433] {x : I ↪ K} {original : Finset K}
    (R : Ready x original) (H : P4 K) (Γ : Finset K) (hg : Γ⊆R.seeds)
    (A : Finset (RegularIndex H)) (field : (A.card:ENat)<ENat.card K)
    (cap : Below (aggregateFlag H A) primaryIncoming) (trans : ∀F∈A,¬F.1∣R.flow.flow F.1)
    (j : ℕ) (hj : j≤5) : Nonempty (Visit H A (regularFiber H Γ R.selected) j) := by
  induction j with
  | zero => exact ⟨⟨A,Finset.Subset.rfl,fun _ i hi=>(Nat.not_lt_zero _ hi).elim,fun _ _=>by simp [accrued]⟩⟩
  | succ j prev =>
    have valid : j<5 := by omega
    let k : Fin 5 := ⟨j,valid⟩
    obtain ⟨V⟩ := prev (by omega)
    have capv := transBelow (aggregateFlag_mono H V.subset) cap
    obtain ⟨T,sub,stop,pay⟩ := group_run (menu k) (capStage k) (valid_menu k) (dominates_menu k)
      R H Γ hg V.current
      ((show (V.current.card:ENat)≤A.card by exact_mod_cast Finset.card_le_card V.subset).trans_lt field)
      capv (fun F h=>trans F (V.subset h)) (fee k)
      (fun pos => fee_bound k (aggregateFlag H V.current) pos capv (V.prior (ne_of_pos pos)))
    refine ⟨⟨T,sub.trans V.subset,?_,?_⟩⟩
    · intro ne i hi s hs gate
      by_cases same : i.val=j
      · have ii : i=k := Fin.ext same
        subst i
        exact ((stop.resolve_left ne.ne_empty) s hs) gate
      · have old := V.prior (ne.mono sub) i (by omega) s hs
        exact old (adaptiveGate_mono s.numbers (aggregateFlag_mono H sub) (aggregateFlag_pos H ne) gate)
    · intro final last
      have b := V.paid final (last.trans sub)
      have c := card_peel sub (regularFiber H Γ R.selected)
      have d := pay final last
      simp only [accrued,dif_pos valid]
      dsimp [k] at d
      omega
#print axioms visit
end
end ProximityPrize.SubmissionLower.K6833Group
