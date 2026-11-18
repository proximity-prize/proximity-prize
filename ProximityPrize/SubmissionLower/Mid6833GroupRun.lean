/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. A group of adaptive sources may choose different partners for different retained factors.
Derived from the fixed-source paid route of Lucieno and Bome2017. -/
import ProximityPrize.SubmissionLower.Mid6833GroupCredit
import ProximityPrize.SubmissionLower.Mid6833K6833PrimaryReady
namespace ProximityPrize.SubmissionLower.K6833Group
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN156 RCN167 RCN234 RCN238 RCN243 RCN263 RCN266 RCN275 RCN313 RCN319
open K6833FlowSources K6833FlowStages K6833FlowAdaptive K6833FlowPaid
open Koala6831Moving Koala6831MovingLedger Koala6831MovingPairIncidence
open LocatorFactorAggregate LocatorLowQuotient K6833PrimaryReady
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
variable {K I : Type} [Field K] [Fintype I]
local instance mid6833Local_GroupRun_15  : DecidableEq K := Classical.decEq _

def Dominates (u v : Stage) : Prop :=
  u.multiplicity≤v.multiplicity ∧ u.numbers.totalCap+u.numbers.slopeCap≤v.numbers.totalCap+v.numbers.slopeCap ∧
  u.numbers.middleCap≤v.numbers.middleCap ∧ u.numbers.slopeCap≤v.numbers.slopeCap

theorem group_run [CharP K 2130706433] (menu : List Stage) (top : Stage)
    (valid : ∀s∈menu,s≠.primary) (dominant : ∀s∈menu,Dominates s top)
    {x : I ↪ K} {original : Finset K} (R : Ready x original) (H : P4 K) (Γ : Finset K)
    (hg : Γ⊆R.seeds) (A : Finset (RegularIndex H)) (field : (A.card:ENat)<ENat.card K)
    (cap : Below (aggregateFlag H A) primaryIncoming) (trans : ∀F∈A,¬F.1∣R.flow.flow F.1)
    (fee : ℕ) (charge : ∀ pos : 0<(aggregateFlag H A).all,
      stagePrice (aggregateFlag H A) pos top top.numbers.slopeCap ≤ fee) :
    ∃U⊆A, (U=∅ ∨ ∀s∈menu, ¬adaptiveGate s.numbers (aggregateFlag H U)) ∧
      ∀final⊆U, ((A\U).biUnion (regularFiber H Γ R.selected)).card ≤ fee-credit top (aggregateFlag H final) := by
  classical
  let xg : R.good ↪ K := ⟨fun i=>x i.val,fun _ _ e=>Subtype.ext (x.injective e)⟩
  let uv (i : R.good) := R.u₀ i.val
  let vv (i : R.good) := R.u₁ i.val
  let word (i : R.good) := R.word i.val
  let supp (g:K) := Finset.univ.filter (fun i:R.good => (R.selected g).eval (xg i)=uv i+g*vv i)
  have nodes : (Finset.univ : Finset I).card=262144 := Finset.card_univ.trans R.nodes_card
  have card : Fintype.card R.good≤262144 := by
    rw [Fintype.card_coe,←nodes];exact Finset.card_le_card (Finset.subset_univ _)
  have h₀ (i : R.good) := (R.fixedWord i.val i.property).1
  have h₁ (i : R.good) := (R.fixedWord i.val i.property).2
  have fit (g:K) (mem:g∈Γ) : agreement≤(supp g).card := by
    have sub : Finset.univ.filter (fun i=>(R.selected g).eval (x i)=R.u₀ i+g*R.u₁ i) ⊆ (supp g).image Subtype.val := by
      intro i hi
      have eq := (Finset.mem_filter.mp hi).2
      exact Finset.mem_image.mpr ⟨⟨i,R.agree_good g (hg mem) i eq⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩,rfl⟩
    exact (R.agreement g (hg mem)).trans ((Finset.card_le_card sub).trans Finset.card_image_le)
  obtain ⟨U,sub,stop,paid⟩ := exhaust_group menu valid R.flow xg uv vv word card h₀ h₁
    R.denominator_degree R.minor_degree H A field cap trans
  refine ⟨U,sub,stop,?_⟩
  intro final last
  by_cases ne : A.Nonempty
  swap
  · have empty := Finset.not_nonempty_iff_eq_empty.mp ne
    simp [empty]
  let a := aggregateFlag H A
  have pos := aggregateFlag_pos H ne
  have prices (F : RegularIndex H) (hF : F∈A\U) : (regularFiber H Γ R.selected F).card≤
      flagMixed (contactFlag F.1) (stagePartnerFlag top top.numbers.slopeCap) (stageScaledCut a pos)/agreementScale := by
    obtain ⟨s,hs,Q,rel,box,contacts⟩ := paid F hF
    obtain ⟨hm,ht,hy,hr⟩ := dominant s hs
    have big : Q∈nestedCoefficientBox K (top.multiplicity*agreement) weight
        (top.numbers.totalCap+top.numbers.slopeCap) top.numbers.middleCap top.numbers.slopeCap := by
      intro e he
      have h := box he
      exact ⟨h.1.trans ht,h.2.1.trans hy,h.2.2.1.trans hr,h.2.2.2.trans_le (Nat.mul_le_mul_right _ hm)⟩
    apply regularFiber_le_paid_factor H A F (Finset.mem_sdiff.mp hF).1 a pos ⟨le_rfl,le_rfl,le_rfl⟩ cap top top.numbers.slopeCap
      Γ R.selected Finset.univ x R.u₀ R.u₁ x.injective.injOn nodes (fun g mem=>R.degree g (hg mem))
      (fun g mem=>R.agreement g (hg mem))
      (noLargeSelectedPencil_mono R.selected R.seeds Γ weight 81076 hg R.pencil) Q rel big
    intro g mem
    exact specialization_zero_of_box_and_agreement xg uv vv s Q (R.selected g) g (supp g) box
      (fun i _=>contacts i) (R.degree g (hg mem)) (fit g mem) (fun i hi=>(Finset.mem_filter.mp hi).2)
  have n := (bill top H A U final sub last (regularFiber H Γ R.selected) pos prices).trans (charge pos)
  omega
#print axioms group_run
end
end ProximityPrize.SubmissionLower.K6833Group
