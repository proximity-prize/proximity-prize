import ProximityPrize.SubmissionLower.Left6836Ready
import ProximityPrize.SubmissionLower.Mid6833FullCredit
import ProximityPrize.SubmissionLower.Night6836FeeCert
import ProximityPrize.SubmissionLower.Night6836FlowKernel
section BP0
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Builds on the public comparison argument of Lucieno and Bome2017.
A group can use a distinct admissible source for each successive set of factors. -/
namespace ProximityPrize.SubmissionLower.Night6836Group
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN156 RCN167 RCN234 RCN238 RCN243 RCN263 RCN266 RCN275 RCN313 RCN319
open Night6836FlowSources Night6836FlowStages Night6836FlowAdaptive Night6836FlowPaid
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
    (den : B.d0.natDegree+max B.a0.natDegree B.a1.natDegree≤9614)
    (minor : (B.a1*B.c0-B.a0*B.c1).natDegree≤weight+9614)
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
end ProximityPrize.SubmissionLower.Night6836Group

end BP0

section BP1
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. The cumulative-direction identities build on the accepted 68.32 argument.
This version credits final factors retained through a whole group of adaptive passes. -/
namespace ProximityPrize.SubmissionLower.Night6836Group
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN156 RCN238 RCN243 RCN263 RCN266 RCN275 RCN313 RCN319
open Night6836FlowSources Night6836FlowStages Night6836FlowAdaptive Night6836FlowPaid
open Koala6831Moving Koala6831MovingLedger Koala6831MovingPairIncidence
open LocatorBatchProductRoute (regularProduct regularProduct_ne_zero)
open LocatorFactorAggregate LocatorLowQuotient
open LocatorPhase6800Oracle (sumFlag sumFlag_all sumFlag_middle sumFlag_total)
noncomputable section
set_option maxRecDepth 30000
variable {K : Type} [Field K]
local instance mid6833Local_GroupCredit_15  : DecidableEq K := Classical.decEq _
private theorem direction_cumulative (P : ResidualSupportParameters) :
    (reducedAgreementDirection P).all = 2 * P.s - 2 ∧
      middle (reducedAgreementDirection P) = 2 * P.ys - 2 ∧
      total (reducedAgreementDirection P) = 2 * P.total - 2 := by
  have hs := P.one_le_s
  have hy := P.s_le_ys
  have ht := P.ys_le_total
  simp only [reducedAgreementDirection, middle, total, true_and]
  omega

private theorem direction_mono {f g : FlagDegree} (hf : 0 < f.all) (hg : 0 < g.all)
    (hfg : Below f g) :
    Below (reducedAgreementDirection (stageSupport f hf))
      (reducedAgreementDirection (stageSupport g hg)) := by
  obtain ⟨hr, hy, ht⟩ := hfg
  obtain ⟨hrf, hyf, htf⟩ := direction_cumulative (stageSupport f hf)
  obtain ⟨hrg, hyg, htg⟩ := direction_cumulative (stageSupport g hg)
  unfold Below
  rw [hrf, hrg, hyf, hyg, htf, htg]
  have hy' := max_le_max_left 2 hy
  have ht' := max_le_max_left 2 ht
  change _ ∧ (2 * max 2 (middle f) - 2 ≤ 2 * max 2 (middle g) - 2) ∧
    (2 * max 2 (total f) - 2 ≤ 2 * max 2 (total g) - 2)
  exact ⟨by simpa only [stageSupport] using Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 2,
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hy') 2,
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 ht') 2⟩

private theorem below_scaled_add {f g : FlagDegree} (hfg : Below f g)
    (k : ℕ) (p q : FlagDegree) : Below (k • f + p + q) (k • g + p + q) := by
  obtain ⟨hr, hy, ht⟩ := hfg
  simp only [Below, middle, total, add_all, add_yz, add_zOnly, nsmul_all, nsmul_yz, nsmul_zOnly]
  have hS := Nat.mul_le_mul_left k hr
  have hY := Nat.mul_le_mul_left k hy
  have hT := Nat.mul_le_mul_left k ht
  simp only [middle, total, Nat.mul_add] at hY hT
  omega

theorem stagePrice_mono {f g : FlagDegree} (hf : 0 < f.all) (hg : 0 < g.all)
    (hfg : Below f g) (s : Stage) (gain : ℕ) :
    stagePrice f hf s gain ≤ stagePrice g hg s gain := by
  unfold stagePrice
  apply Nat.div_le_div_right
  apply (mixed_mono_first hfg _ _).trans
  apply mixed_mono_third
  unfold stageScaledCut scaledPairFlag
  exact below_scaled_add (direction_mono hf hg hfg) _ _ _

private theorem flag_eq_of_cumulative {a b : FlagDegree}
    (hR : a.all = b.all) (hY : middle a = middle b) (hT : total a = total b) : a = b := by
  cases a with
  | mk za ya ra =>
    cases b with
    | mk zb yb rb =>
      simp only [middle, total] at hR hY hT
      have hy : ya = yb := by omega
      have hz : za = zb := by omega
      cases hR; cases hy; cases hz
      rfl

private theorem sumFlag_split {ι : Type} [DecidableEq ι] {A R : Finset ι} (hR : R ⊆ A)
    (flag : ι → FlagDegree) : sumFlag (A \ R) flag + sumFlag R flag = sumFlag A flag := by
  apply flag_eq_of_cumulative
  · simpa only [add_all, sumFlag_all] using Finset.sum_sdiff (f := fun i => (flag i).all) hR
  · have hmiddle (P Q : FlagDegree) : middle (P + Q) = middle P + middle Q := by
      simp only [middle, add_yz, add_all]
      omega
    simpa only [hmiddle, sumFlag_middle] using Finset.sum_sdiff (f := fun i => middle (flag i)) hR
  · have htotal (P Q : FlagDegree) : total (P + Q) = total P + total Q := by
      simp only [total, add_zOnly, add_yz, add_all]
      omega
    simpa only [htotal, sumFlag_total] using Finset.sum_sdiff (f := fun i => total (flag i)) hR


def credit (s : Stage) (f : FlagDegree) : ℕ :=
  if h : 0 < f.all then
    flagMixed f (stagePartnerFlag s s.numbers.slopeCap)
      (stageScaledCut f h) / agreementScale
  else 0

theorem bill [DecidableEq K] (s : Stage) (H : P4 K) (A U final : Finset (RegularIndex H))
    (sub : U⊆A) (last : final⊆U) (seeds : RegularIndex H→Finset K)
    (pos : 0<(aggregateFlag H A).all)
    (cnt : ∀ F∈A\U,(seeds F).card≤flagMixed (contactFlag F.1) (stagePartnerFlag s s.numbers.slopeCap)
      (stageScaledCut (aggregateFlag H A) pos) / agreementScale) :
    ((A\U).biUnion seeds).card + credit s (aggregateFlag H final) ≤
      stagePrice (aggregateFlag H A) pos s s.numbers.slopeCap := by
  classical
  let f := aggregateFlag H final
  let g := aggregateFlag H A
  let z := f
  have zf : Below z f := by simp [z,Below]
  have zU := transBelow zf (aggregateFlag_mono H last)
  have zg := transBelow zU (aggregateFlag_mono H sub)
  have split : sumFlag (A\U) (fun i=>contactFlag i.1) + aggregateFlag H U = g := by
    change sumFlag (A\U) (fun i=>contactFlag i.1) + contactFlag (regularProduct H U) = contactFlag (regularProduct H A)
    rw [contactFlag_regularProduct,contactFlag_regularProduct,sumFlag_split sub]
  have invoice := IntermediateCredit.full_credit (A\U) (fun i=>contactFlag i.1) seeds z (aggregateFlag H U) g
    (stagePartnerFlag s s.numbers.slopeCap) (stageScaledCut g pos) agreementScale_pos zU
    (by rw [split];exact ⟨le_rfl,le_rfl,le_rfl⟩) cnt
  have save : credit s (aggregateFlag H final)≤flagMixed z (stagePartnerFlag s s.numbers.slopeCap) (stageScaledCut g pos)/agreementScale := by
    unfold credit
    split
    next h =>
      apply Nat.div_le_div_right
      apply mixed_mono_third
      unfold stageScaledCut scaledPairFlag
      exact below_scaled_add (direction_mono (f:=z) (g:=g) h pos zg) _ _ _
    next => exact Nat.zero_le _
  exact (Nat.add_le_add_left save _).trans invoice
#print axioms bill
end
end ProximityPrize.SubmissionLower.Night6836Group

end BP1

section BP2
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. A group of adaptive sources may choose different partners for different retained factors.
Derived from the fixed-source paid route of Lucieno and Bome2017. -/
namespace ProximityPrize.SubmissionLower.Night6836Group
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN156 RCN167 RCN234 RCN238 RCN243 RCN263 RCN266 RCN275 RCN313 RCN319
open Night6836FlowSources Night6836FlowStages Night6836FlowAdaptive Night6836FlowPaid
open Koala6831Moving Koala6831MovingLedger Koala6831MovingPairIncidence
open LocatorFactorAggregate LocatorLowQuotient Left6836Ready
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
      (noLargeSelectedPencil_mono R.selected R.seeds Γ weight 81105 hg R.pencil) Q rel big
    intro g mem
    exact specialization_zero_of_box_and_agreement xg uv vv s Q (R.selected g) g (supp g) box
      (fun i _=>contacts i) (R.degree g (hg mem)) (fit g mem) (fun i hi=>(Finset.mem_filter.mp hi).2)
  have n := (bill top H A U final sub last (regularFiber H Γ R.selected) pos prices).trans (charge pos)
  omega
#print axioms group_run
end
end ProximityPrize.SubmissionLower.Night6836Group

end BP2

section BP3
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Chain the five exhausted groups on the same received word and
the same surviving factors. The reserve is evaluated on the final aggregate. -/
namespace ProximityPrize.SubmissionLower.Night6836Group
open scoped Classical BigOperators
open RCN095 RCN156 RCN238 RCN266 RCN319 Koala6831Moving Night6836FlowAdaptive Night6836FlowPaid
open Night6836FlowSources Night6836FlowStages Night6836AdaptiveCert Left6836Ready LocatorFactorAggregate
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
end ProximityPrize.SubmissionLower.Night6836Group

end BP3
