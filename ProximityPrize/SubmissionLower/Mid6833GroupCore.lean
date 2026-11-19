/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Builds on the public comparison argument of Lucieno and Bome2017.
A group can use a distinct admissible source for each successive set of factors. -/
import ProximityPrize.SubmissionLower.Mid6833K6833FlowPaid
import ProximityPrize.SubmissionLower.Mid6833FullCredit
namespace ProximityPrize.SubmissionLower.K6833Group
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN156 RCN167 RCN234 RCN238 RCN243 RCN263 RCN266 RCN275 RCN313 RCN319
open K6833FlowSources K6833FlowStages K6833FlowAdaptive K6833FlowPaid
open Koala6831Moving Koala6831MovingLedger Koala6831MovingPairIncidence
open LocatorBatchProductRoute (regularProduct regularProduct_ne_zero)
open LocatorFactorAggregate LocatorLowQuotient
open LocatorPhase6800Oracle (sumFlag sumFlag_all sumFlag_middle sumFlag_total)
noncomputable section
variable {K I : Type} [Field K] [Fintype I]
local instance mid6833Local_GroupCore_15  : DecidableEq K := Classical.decEq _

def sourceCap (s : Stage) : FlagDegree :=
  ⟨s.numbers.totalCap-s.numbers.middleCap,s.numbers.middleCap-s.numbers.slopeCap,s.numbers.slopeCap⟩

theorem transBelow {a b c : FlagDegree} (h : Below a b) (g : Below b c) : Below a c :=
  ⟨h.1.trans g.1,h.2.1.trans g.2.1,h.2.2.trans g.2.2⟩

theorem primary_fits (s : Stage) (hs : s≠.primary) : Below primaryIncoming (sourceCap s) := by
  cases s <;> first | exact (hs rfl).elim | (unfold Below; decide +kernel)

theorem exhaust_group [CharP K 2130706433] (menu : List Stage)
    (valid : ∀s∈menu,s≠.primary) (B : FlowData K) (nodes u₀ u₁ normalized : I → K)
    (card : Fintype.card I ≤ 262144)
    (h₀ : ∀i,B.d0.eval (nodes i)*u₀ i+B.c0.eval (nodes i)=B.a0.eval (nodes i)*normalized i)
    (h₁ : ∀i,B.d0.eval (nodes i)*u₁ i+B.c1.eval (nodes i)=B.a1.eval (nodes i)*normalized i)
    (den : B.d0.natDegree+max B.a0.natDegree B.a1.natDegree≤9583)
    (minor : (B.a1*B.c0-B.a0*B.c1).natDegree≤weight+9583)
    (H : P4 K) (A : Finset (RegularIndex H)) (field : (A.card:ENat)<ENat.card K)
    (cap : Below (aggregateFlag H A) primaryIncoming) (trans : ∀F∈A, ¬F.1∣B.flow F.1) :
    ∃U⊆A, (U=∅ ∨ ∀s∈menu, ¬adaptiveGate s.numbers (aggregateFlag H U)) ∧
      ∀F∈A\U, ∃s∈menu, ∃Q:P4 K, IsRelPrime F.1 Q ∧
        Q∈nestedCoefficientBox K (s.multiplicity*agreement) weight (s.numbers.totalCap+s.numbers.slopeCap)
          s.numbers.middleCap s.numbers.slopeCap ∧
        ∀i,ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity Q := by
  classical
  let active (R: Finset (RegularIndex H)) := ∃s∈menu,adaptiveGate s.numbers (aggregateFlag H R)
  let pays (F:RegularIndex H) := ∃s∈menu, ∃Q:P4 K, IsRelPrime F.1 Q ∧
      Q∈nestedCoefficientBox K (s.multiplicity*agreement) weight (s.numbers.totalCap+s.numbers.slopeCap)
        s.numbers.middleCap s.numbers.slopeCap ∧
      ∀i,ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity Q
  obtain ⟨U,sub,stop,done⟩ := exhaust_finset_stage A active pays (by
    intro R sub ne ah
    obtain ⟨s,hs,gate⟩ := ah
    have size : (R.card:ENat)<ENat.card K :=
      (show (R.card:ENat)≤A.card by exact_mod_cast Finset.card_le_card sub).trans_lt field
    obtain ⟨P⟩ := exists_exhausted_adaptive_pass s B nodes u₀ u₁ normalized card h₀ h₁ den minor H R size
      (transBelow (transBelow (aggregateFlag_mono H sub) cap) (primary_fits s (valid s hs))) (fun F h => trans F (sub h))
    have neq : P.residue≠R := by
      intro e
      rcases P.stopped with em|inactive
      · exact ne.ne_empty (e ▸ em)
      · exact inactive (by rw [e];exact gate)
    exact ⟨P.residue,Finset.ssubset_iff_subset_ne.mpr ⟨P.subset_incoming,neq⟩,fun f hf=>⟨s,hs,P.partners f hf⟩⟩)
  exact ⟨U,sub,stop.imp_right (fun h s hs g=>h ⟨s,hs,g⟩),done⟩
#print axioms exhaust_group
end
end ProximityPrize.SubmissionLower.K6833Group
