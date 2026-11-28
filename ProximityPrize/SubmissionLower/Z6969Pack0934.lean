import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0933
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0667
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0650
import ProximityPrize.SubmissionLower.Z6969Pack0652
import ProximityPrize.SubmissionLower.Z6969Pack0645
import ProximityPrize.SubmissionLower.Z6969Pack0655
import ProximityPrize.SubmissionLower.Z6969Pack0647
import ProximityPrize.SubmissionLower.Z6969Pack0636
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.Z6969Pack0646
import ProximityPrize.SubmissionLower.Z6969Pack0648
import ProximityPrize.SubmissionLower.Z6969Pack0649
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false

-- Source: Research6969.ConfirmedDistinct
section Z6969Source2567
set_option autoImplicit true
namespace Research6969.ConfirmedDistinct
noncomputable section
open K1 (K I p)
open K1_14 (Equation FX atX jetAt)
open K1_14_2_2_2_1 (seedDegree)
open Lower6960.Far6969RescueGeometry (word)
open Research6966
open HighPackets (State)
open NormalGeometry (Geometry helper nativeHelper)
open PairCell (Row)
open PairPrices (Decision)
open TransitionPacket.NormalCatalogue (mainBook rescueBook savedMainGrade seed)
open PairedMarks (mainLabels rescueLabels)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 2500000
set_option maxRecDepth 13000
set_option Elab.async false
attribute [local irreducible] GraphLedger.excess FastHeight.side FastHeight.ordinate
  TransitionPacket.NormalCatalogue.mainBook TransitionPacket.NormalCatalogue.rescueBook
  TransitionPacket.NormalCatalogue.savedMainGrade PairPrices.primaryRate RescuePrice.ticket

theorem proves {i} (s:State i) (b:Row) (h:PairCell.Facts s b) (z:Geometry s) (p₀:Decision)
    (different:GraphIntersection.determinant (nativeHelper s) s.native≠0) (pay:PairPrices.distinctOK b i p₀)
    (room:3≤savedMainGrade i) (small:b.off+b.cross<64)
    (safeM:(2*b.off-1)*(mainBook i).seedMass<p) (safeR:(2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p)
    (nodeGuard:OnTariff.NodeGuard p₀.main (NormalGeometry.weight s) p₀.cutoff):
    s.labels.card≤CertifiedCell.target := by
  classical
  let C:=z.pairData
  obtain ⟨rg,lg⟩:=PairCell.distinct_bounds s b h z different
  obtain ⟨g,v,x,o⟩:=PairCell.primary_bounds s b h z
  rcases pay with impossible|⟨legal,okay,cash⟩
  · exact (Nat.not_lt_of_ge (lg.trans (g.trans (min_le_right ..))) impossible).elim
  let rate:=PairPrices.primaryRate b i p₀
  have owner:=OwnedTariffs.owners s.F s.native C.main
  have actualLegal:OnTariff.Legal p₀.main s.graph.graphDegree b.seedHi b.axisHi (b.gm i) (mainBook i).seedMass 2411 p₀.cutoff:=by
    rw [h.degree];exact legal
  have nativeFee:(C.main.onLabels).card≤rate.pay C.main.onEq:=by
    have counted:=OnTariff.on_marks s.F (C.main.onSub.trans (PairedMarks.main_sub s.pair)) s.crt s.native s.gp s.physical owner
      C.main.onProduct.primitive C.main.onProduct.separable (GraphPartition.labels_root C.main).1 (b.gm i)
      (mainBook i).seedMass p₀.cutoff b.seedHi b.axisHi p₀.main actualLegal g (v.trans (min_le_right ..))
      h.seedHigh h.axisHigh s.lower s.higher nodeGuard s.nodes
      (fun y hy=>s.residues y (PairedMarks.main_sub s.pair (C.main.onSub hy)))
    rw [h.degree] at counted
    simpa only [rate,PairPrices.primaryRate] using counted
  have endBound (extra:ℕ) (pays:C.main.onLabels.card+extra≤rate.pay C.main.onEq)
      (res:(rescueLabels s.pair).card≤extra+(rescueBook i).ordinateCredit*C.rescueFull.natDegree+
        (rescueBook i).seedCredit*K1_14_4.seedDegree C.rescueFull+PairPrices.rescueCharge b i p₀) :
      s.labels.card≤CertifiedCell.target:=by
    have raw:(C.main.onLabels.card:ℤ)+extra≤rate.cash+rate.y*(C.main.onEq.natDegree:ℤ)+
        rate.seed*(K1_14_4.seedDegree C.main.onEq:ℤ)+rate.axis*(KoalaRect.axisDegree C.main.onEq 1:ℤ):=by
      unfold PriceMethod.Rate.pay at pays
      exact_mod_cast pays
    have bound:=DistinctCore.shared_invoice s.pair s.native C extra
      (off:=b.off) (low:=b.loPrimary) (hi:=b.gm i) (seedMax:=b.vm i) (axisMax:=(b.cap i).axis)
      (s.higher.trans (by decide))
      (s.mainGrade ▸ room) ((Nat.le_add_right ..).trans_lt small) safeM o lg g v x
      ((savedMainGrade i)^2+rate.cash:ℕ) rate.y rate.seed rate.axis (by positivity) (by
        push_cast;have positive:(0:ℤ)≤((savedMainGrade i:ℤ)^2):=sq_nonneg _;linarith only [raw,positive])
      (PairPrices.rescueCharge b i p₀) res
    rw [s.mainGrade] at bound
    unfold PairPrices.primaryCharge at cash
    exact Int.ofNat_le.mp (bound.trans cash)
  cases mode:p₀.rescue with
  | whole =>
    refine endBound 0 (by simpa only [Nat.add_zero] using nativeFee) ?_
    rw [Nat.zero_add]
    exact DistinctPaymentRescue.whole s b z p₀ mode rg small safeR
  | intersection =>
    rw [mode] at okay
    by_cases node : PairPrices.modeNode p₀.main=true
    · exact endBound C.rescue.onLabels.card (DistinctPaymentNode.pays s b h z p₀ node legal nodeGuard)
        (DistinctPaymentRescue.node_rescue s b h z p₀ mode node small safeR)
    · refine endBound 0 (by simpa only [Nat.add_zero] using nativeFee) ?_
      rw [Nat.zero_add]
      exact DistinctPaymentRescue.graph_rescue s b h z p₀ mode node different
        (okay.resolve_left node) small safeR

end
end Research6969.ConfirmedDistinct
end Z6969Source2567

-- Source: Research6969.ConfirmedSame
section Z6969Source2568
set_option autoImplicit true
namespace Research6969.ConfirmedSame
noncomputable section
open K1 (I p)
open K1_14 (Equation atX jetAt)
open K1_14_2_2_2_1 (seedDegree)
open Lower6960.Far6969RescueGeometry (word)
open Research6966
open HighPackets (State)
open NormalGeometry (Geometry helper nativeHelper)
open PairCell (Row)
open PairPrices (Decision)
open TransitionPacket.NormalCatalogue (seed mainBook rescueBook savedMainGrade savedRescueGrade)
open PairedMarks (rescueLabels)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 2200000
set_option maxRecDepth 15000

theorem proves {i} (s:State i) (b:Row) (h:PairCell.Facts s b) (z:Geometry s) (p₀:Decision)
    (same:GraphIntersection.determinant (nativeHelper s) s.native=0) (pay:PairPrices.sameOK b i p₀)
    (low:b.off<64) (safe:(2*b.off-1)*(mainBook i).seedMass<p)
    (nodeLow:∀fee,p₀.same=.node fee→NormalGeometry.weight s<p₀.cutoff):s.labels.card≤CertifiedCell.target:=by
  classical
  let A:=nativeHelper s
  let C:=z.pairData
  have gp:=PhysicalHelperTariff.primitive s.prime s.slope
  have d0:=NormalGeometry.helper_degree s
  have original:A.poly=s.H:=rfl
  obtain ⟨mdiv,rdiv,sum⟩:=SameCore.degrees s.pair A s.native C gp s.gp original same s.product z.onWitness.1 z.offProduct
  obtain ⟨gc,sc,_⟩:=PairCell.caps s b h z
  have rawOff:=z.offCap
  rw [h.control,h.degree] at rawOff
  have md:C.mainFull.natDegree≤b.off:=(natDegree_le_of_dvd mdiv z.offProduct.primitive.ne_zero).trans rawOff
  have rs:=JointProjection.measures C.rescuePr s.pair.bSrc s.pair.rescueActive s.pair.rescueOrigin
  have grade:C.rescueFull.natDegree≤b.gr i:=le_min
    ((natDegree_le_of_dvd rdiv z.onWitness.1.primitive.ne_zero).trans gc)
    ((rs.1.trans s.pair.rescueDegreeCap).trans_eq s.rescueGrade)
  have rv:K1_14_4.seedDegree C.rescueFull≤b.vr i:=le_min
    (((JointProjection.remainder (Or.inl z.onWitness.1) rdiv).2).trans sc) (rs.2.trans s.pair.boundsR)
  have lower:b.lowerGrade-b.off≤C.rescueFull.natDegree:=by have e:=h.gradeLow;omega
  have inc:=SameCore.invoice s.pair s.native C (s.higher.trans (by decide)) low safe md lower grade rv
  have ph:131071+s.model.overhead≤(133482:ℤ):=OnTariff.degree_bound s.higher
  cases tag:p₀.same with
  | impossible=>
    rw [PairPrices.sameOK,tag] at pay
    have ⟨de,wd⟩:=HelperGraph.same_degrees A s.native gp s.gp same
    have deg:b.graph=2:=h.degree.symm.trans (de.symm.trans d0)
    have seedEq:seedDegree s.native.poly=seed i:=wd.symm.trans s.helperSeed
    rcases pay with wrong|tooSmall|tooLarge|tooMany
    · exact (wrong deg).elim
    · exact (Nat.not_lt_of_ge (h.seedLow.trans_eq seedEq) tooSmall).elim
    · cases hs:b.seedHi with
      | none=>simp [hs] at tooLarge
      | some v=>
        have u:=h.seedHigh v hs
        simp only [hs] at tooLarge
        omega
    · have g:=grade.trans (min_le_right ..)
      omega
  | marked=>
    rw [PairPrices.sameOK,tag] at pay
    obtain ⟨small,char,paid⟩:=pay
    have count:=ThreeLedger.marked s.F (PairedMarks.rescue_sub s.pair) (s.higher.trans (by decide))
      C.rescuePr.primitive C.rescuePr.separable (grade.trans_lt small)
      ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 grade) _) rv).trans_lt char) (PairedMarks.native_rescue s.pair C.rescuePr)
    have rate:ThreeLedger.rate C.rescueFull.natDegree≤Near6969FactorPrice.rate (max 3 (b.gr i))+2*(b.gr i)-1:=
      (PriceMethod.rate_mono grade).trans (by unfold ThreeLedger.rate;split <;>omega)
    have bigger:=(Nat.add_le_add (Nat.mul_le_mul_right (K1_14_4.seedDegree C.rescueFull) (Nat.mul_le_mul_right K1.p rate))
        (PriceMethod.tail_mono grade))
    have nf:=(count.1.trans bigger).trans_eq (Nat.add_comm ..)
    have cd:=inc (ThreeLedger.tail (b.gr i)) 0 (JointLedger.coefficient (b.gr i)) (by
      simp only [Int.zero_mul,Int.add_zero];exact_mod_cast nf)
    exact_mod_cast cd.trans paid
  | surface=>
    rw [PairPrices.sameOK,tag] at pay
    have fit:179730≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
    have sp:0<seed i:=by unfold seed;omega
    have sc:=NativeSurfaceCount.regular_equation s.F (PairedMarks.rescue_sub s.pair) C.rescuePr.primitive.ne_zero A gp d0.ge sp
      (NormalGeometry.helper_cap s) ((K1_14_4.seedDegree_le_iff ..).mp le_rfl) ph (by decide:0<133482)
      (by decide) fit (by decide) (fun y hy=>(PairedMarks.rescue_law s.pair A gp original hy).1)
      (fun y hy=>by simpa [NonlinearMarkRows.evaluate,NativeSurfaceCount.label,K1_14.graphEval,Polynomial.eval_map] using PairedMarks.native_rescue s.pair C.rescuePr y hy)
      (fun y hy=>(PairedMarks.rescue_law s.pair A gp original hy).2)
    have amount:=NativeSurfaceCount.round_price (bad:=0) (g:=C.rescueFull.natDegree) (v:=K1_14_4.seedDegree C.rescueFull)
      (u:=seed i) (r:=(helper s).graphDegree-1) (d:=133482) (a:=179730) (n:=Fintype.card I) (by simpa using sc)
    change (rescueLabels s.pair).card≤0+C.rescueFull.natDegree*(JointRouted.seedWeight 133482 (seed i))^2+
      2*K1_14_4.seedDegree C.rescueFull*JointRouted.seedWeight 133482 (seed i)*JointRouted.ordWeight 133482 ((helper s).graphDegree-1) at amount
    rw [d0,FastHeight.side_eq,FastHeight.ordinate_eq 133482 _ (by decide)] at amount
    have cd:=inc 0 ((PairPrices.sx i)^2:ℕ) (2*PairPrices.sx i*PairPrices.sy:ℕ) (by
      simp only [Int.zero_add]
      exact_mod_cast amount.trans_eq (by dsimp [PairPrices.sx,PairPrices.sy,PairPrices.d];ring))
    exact_mod_cast cd.trans pay
  | node fee=>
    rw [PairPrices.sameOK,tag] at pay
    obtain ⟨quad,yes,char,ok,paid⟩:=pay
    have cert:=NodeBudget.family s.F (PairedMarks.rescue_sub s.pair) rfl ((by decide:0<2314).trans_le s.lower) s.higher
      (by decide) s.physical (OrdinaryCell.native_prime s.native s.gp) (NativeGraphMarks.slope_degree s.native s.gp)
      ((HelperWeightCap.native_degree s.native s.gp).trans (h.degree.trans quad)) char
      ((K1_14_2_2_2_1.seedDegree_le ..).mp (h.seedHigh _ (OnTariff.selected yes))) s.nodes (fun z hz=>s.residues z (PairedMarks.rescue_sub s.pair hz))
      (by intro z hz
          let ev:K1_14.Jet→+*K1_14.FX:=eval₂RingHom (eval₂RingHom (K1_14.graphEval (s.model.label z)) (atX (s.F.scalar z))) (atX (s.F.scalar z).derivative)
          exact (HelperGraph.same_mark A s.native gp s.gp same ev).mp ((PairedMarks.rescue s.pair hz).1))
      (nodeLow fee tag) ok
    have cd:=inc fee 0 0 (by simp only [Int.zero_mul,Int.add_zero];exact_mod_cast cert)
    exact_mod_cast cd.trans paid

end
end Research6969.ConfirmedSame
end Z6969Source2568

-- Source: Research6969.ThreeRule
section Z6969Source2569
set_option autoImplicit true
namespace Research6969.ThreeRule
open PairCell (Row)
open TransitionPacket.NormalCatalogue (mainBook rescueBook)
open HighPackets (State)
open NormalGeometry (Geometry nativeHelper)
open Research6966
open Finset
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000

def fee (b:Row) (n:Fin 18) (i k j:ℕ):ℤ:=
  let m:=mainBook n
  let r:=rescueBook n
  (m.fee:ℤ)+r.fee+ThreeLedger.debit (ThreeLedger.rate k*K1.p) (ThreeLedger.rate i)
    m.seedMass (b.vm n) (b.cap n).axis i k m.ordinateCredit m.seedCredit (ThreeLedger.tail i) (ThreeLedger.tail k)+
    RescuePrice.ticket r j (PairPrices.sx n) PairPrices.sy

def check (b:Row) (n:Fin 18):Bool:=
  decide (b.upperGrade<64 ∧ (2*b.upperGrade-1)*(mainBook n).seedMass<K1.p ∧
      (2*b.upperGrade-1)*(rescueBook n).seedMass<K1.p) &&
  GradeTable.first (fun delta=>let grade:=b.lowerGrade+delta
    GradeTable.first (fun j=>GradeTable.first (fun k=>
      let i:=grade-(j+k)
      decide (j+k>grade ∨ i>b.gm n ∨ i<grade-b.off-b.cross ∨ fee b n i k j≤CertifiedCell.target))
      (b.off+1)) (min (b.off+b.cross) grade+1)) (b.upperGrade+1-b.lowerGrade)

theorem proves {n} (s:State n) (b:Row) (h:PairCell.Facts s b) (ok:check b n=true)
    (z:Geometry s) (distinct:GraphIntersection.determinant (nativeHelper s) s.native≠0):
    s.labels.card≤CertifiedCell.target:=by
  have ⟨guards,check⟩:=Bool.and_eq_true_iff.mp ok
  obtain ⟨small,mg,rg⟩:=of_decide_eq_true guards
  let C:=z.pairData
  let i:=C.main.onEq.natDegree
  let k:=C.three.off.natDegree
  let j:=C.three.rescue.natDegree
  let grade:=s.f.natDegree
  have eBounds:b.lowerGrade≤grade ∧ grade≤b.upperGrade:=⟨h.gradeLow,h.gradeHigh⟩
  have tsum:i+k+j=grade:=C.three.total_grade
  obtain ⟨gu,gv,ax,k₀⟩:=PairCell.primary_bounds s b h z
  have kl:k≤b.off:=(Polynomial.natDegree_le_of_dvd C.three.off_dvd C.main.offProduct.primitive.ne_zero).trans k₀
  obtain ⟨jl,global⟩:=PairCell.distinct_total s b h z distinct
  have ju:j≤b.off+b.cross:=(Polynomial.natDegree_le_of_dvd C.three.rescue_dvd C.rescuePr.primitive.ne_zero).trans jl
  have un:0<TransitionPacket.NormalCatalogue.seed n:=by unfold TransitionPacket.NormalCatalogue.seed;omega
  have d0:=NormalGeometry.helper_degree s
  have upper':i≤b.gm n:=gu
  have eg : grade-b.off-b.cross ≤ i := by
    change grade ≤ i+b.off+b.cross at global
    omega
  have pt:=GradeTable.entry check (i:=grade-b.lowerGrade) (by omega)
  rw [Nat.add_sub_of_le eBounds.1] at pt
  have pj:=GradeTable.entry pt (i:=j) (show j<min (b.off+b.cross) grade+1 by omega)
  have pk:=of_decide_eq_true (GradeTable.entry pj (i:=k) (show k<b.off+1 by omega))
  have cost:fee b n i k j≤CertifiedCell.target:=by
    have sub:grade-(j+k)=i:=by omega
    rw [sub] at pk
    rcases pk with x|x|x|x
    · omega
    · omega
    · omega
    · exact x
  have ph:131071+s.model.overhead≤(133482:ℤ):=by have d:=s.higher;omega
  have amount:=ThreeInvoice.charge s.pair (nativeHelper s) s.native C (PhysicalHelperTariff.primitive s.prime s.slope)
    rfl d0.ge un (NormalGeometry.helper_cap s) s.product (h.gradeHigh.trans_lt small)
    ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h.gradeHigh) _)).trans_lt mg)
    ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h.gradeHigh) _)).trans_lt rg)
    (s.higher.trans (by decide)) ph (by decide) (by decide) (by decide) gv ax
  rw [d0,FastHeight.side_eq,FastHeight.ordinate_eq 133482 _ (by decide)] at amount
  exact_mod_cast amount.trans cost

end Research6969.ThreeRule
end Z6969Source2569

-- Source: Research6969.PairProof
section Z6969Source2570
set_option autoImplicit true
namespace Research6969.PairProof
noncomputable section
open HighPackets (State)
open NormalGeometry (Geometry nativeHelper)
open PairCell (Row)
open PairPrices (Decision)
open scoped Classical
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

def node (p:Decision):Bool:=
  PairPrices.modeNode p.main || match p.same with | .node _=>true | _=>false

theorem price {i} (s:State i) (b:Row) (p:Decision) (facts:PairCell.Facts s b)
    (cert:PairPrices.valid b i p) (weight:node p=true→NormalGeometry.weight s<p.cutoff):
    s.labels.card≤CertifiedCell.target:=by
  obtain ⟨_,room,small,mc,rc,dist,same⟩:=cert
  obtain ⟨z⟩:=NormalGeometry.geometry s
  by_cases eq:GraphIntersection.determinant (nativeHelper s) s.native=0
  · apply ConfirmedSame.proves s b facts z p eq same ((Nat.le_add_right ..).trans_lt small) mc
    intro fee atNode
    apply weight
    simp only [node,atNode,Bool.or_true]
  · apply ConfirmedDistinct.proves s b facts z p eq dist room small mc rc
    cases h:p.main <;>simp only [OnTariff.NodeGuard,true_iff] <;>try trivial
    apply weight
    simp [node,h,PairPrices.modeNode]

theorem three {i} (s:State i) (b:Row) (facts:PairCell.Facts s b) (checked:ThreeRule.check b i=true)
    (different:b.graph≠2):s.labels.card≤CertifiedCell.target:=by
  obtain ⟨z⟩:=NormalGeometry.geometry s
  apply ThreeRule.proves s b facts checked z
  intro same
  have eq:=(HelperGraph.same_degrees (nativeHelper s) s.native (Research6966.PhysicalHelperTariff.primitive s.prime s.slope) s.gp same).1
  exact different (facts.degree.symm.trans (eq.symm.trans (NormalGeometry.helper_degree s)))

theorem excluded {i} (s:State i) (b:Row) (facts:PairCell.Facts s b)
    (impossible:(b.cap i).grade<b.lowerGrade-b.off):s.labels.card≤CertifiedCell.target:=by
  obtain ⟨z⟩:=NormalGeometry.geometry s
  obtain ⟨g,_,_⟩:=PairCell.caps s b facts z
  have off:=z.offCap
  rw [facts.control,facts.degree] at off
  have total:=z.wholeGrade
  have large:=facts.gradeLow
  unfold PairCell.Row.off at impossible
  omega

end
end Research6969.PairProof
end Z6969Source2570

-- Source: Research6969.PairLeaves
section Z6969Source2571
set_option autoImplicit true
namespace Research6969.PairLeaves
open PairRoute
open PairCell (Row)
open PairPrices (Decision)
open scoped Classical

theorem paired {i} (b:Row) (p:Decision) (result:PairPrices.valid b i p) (wh:Option ℕ)
    (use:PairProof.node p=true→wh=some p.cutoff) : Done i (of_row b wh):=by
  intro s h
  exact PairProof.price s b p (facts h) result (fun yes=>h.wh _ (use yes))

theorem three {i} (b:Row) (checked:ThreeRule.check b i=true) (different:b.graph≠2) (wh:Option ℕ):
    Done i (of_row b wh):=by
  intro s h
  exact PairProof.three s b (facts h) checked different

theorem excluded {i} (b:Row) (checked:(b.cap i).grade<b.lowerGrade-b.off) (wh:Option ℕ):
    Done i (of_row b wh):=by
  intro s h
  exact PairProof.excluded s b (facts h) checked

end Research6969.PairLeaves
end Z6969Source2571

-- Source: Research6969.PhysicalChecks027
section Z6969Source2572
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1784 : Request := ⟨⟨⟨2600,3625,819,530820⟩,546063062138880,4901614794409⟩,85,2,1,257319,21⟩
theorem cover1784 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1784 7207) 2411 2314 [2319, 2336, 2384, 2411] := rectangleCover (by decide +kernel)
def src1785 : Request := ⟨⟨⟨2600,3625,793,530820⟩,532875289296896,4780245027563⟩,85,2,1,257319,22⟩
theorem cover1785 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1785 6653) 2411 2314 [2320, 2339, 2393, 2411] := rectangleCover (by decide +kernel)
def src1786 : Request := ⟨⟨⟨2600,3625,793,530820⟩,532875289296896,4780245027563⟩,85,2,1,257319,23⟩
theorem cover1786 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1786 6142) 2411 2314 [2324, 2355, 2411] := rectangleCover (by decide +kernel)
def src1787 : Request := ⟨⟨⟨2300,3207,702,530820⟩,369170633195520,2930605494152⟩,85,2,1,257319,24⟩
theorem cover1787 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1787 6653) 2411 2314 [2322, 2347, 2411] := rectangleCover (by decide +kernel)
def src1788 : Request := ⟨⟨⟨2800,3903,882,530820⟩,681932636815360,6587245977411⟩,115,2,1,257319,25⟩
theorem cover1788 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1788 9161) 2411 2314 [2316, 2325, 2350, 2411] := rectangleCover (by decide +kernel)
def src1789 : Request := ⟨⟨⟨2800,3903,854,530820⟩,665461916958720,6424126719762⟩,115,2,1,257319,26⟩
theorem cover1789 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1789 8457) 2411 2314 [2323, 2351, 2411] := rectangleCover (by decide +kernel)
def src1790 : Request := ⟨⟨⟨2800,3903,854,530820⟩,665461916958720,6424126719762⟩,115,2,1,257319,27⟩
theorem cover1790 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1790 7807) 2411 2314 [2334, 2394, 2411] := rectangleCover (by decide +kernel)
def src1791 : Request := ⟨⟨⟨2600,3624,819,530820⟩,546063062138880,4897259437389⟩,115,2,1,257319,28⟩
theorem cover1791 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1791 7207) 2411 2314 [2316, 2325, 2350, 2411] := rectangleCover (by decide +kernel)
def src1792 : Request := ⟨⟨⟨2600,3624,793,530820⟩,532875289296896,4776001446129⟩,115,2,1,257319,29⟩
theorem cover1792 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1792 7207) 2411 2314 [2319, 2336, 2384, 2411] := rectangleCover (by decide +kernel)
def src1793 : Request := ⟨⟨⟨2600,3624,775,530820⟩,523640687820800,4691256264577⟩,115,2,1,257319,30⟩
theorem cover1793 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1793 7807) 2411 2314 [2321, 2344, 2410, 2411] := rectangleCover (by decide +kernel)
def src1794 : Request := ⟨⟨⟨2600,3624,775,530820⟩,523640687820800,4691256264577⟩,115,2,1,257319,31⟩
theorem cover1794 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1794 7207) 2411 2314 [2322, 2348, 2411] := rectangleCover (by decide +kernel)
def src1795 : Request := ⟨⟨⟨2300,3206,724,530820⟩,377903408742400,2998712046218⟩,115,2,1,257319,32⟩
theorem cover1795 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1795 7807) 2411 2314 [2322, 2347, 2411] := rectangleCover (by decide +kernel)
def src1796 : Request := ⟨⟨⟨2300,3206,702,530820⟩,369170633195520,2927665016684⟩,115,2,1,257319,33⟩
theorem cover1796 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1796 7207) 2411 2314 [2316, 2324, 2347, 2411] := rectangleCover (by decide +kernel)
def src1797 : Request := ⟨⟨⟨2300,3206,702,530820⟩,369170633195520,2927665016684⟩,115,2,1,257319,34⟩
theorem cover1797 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1797 6653) 2411 2314 [2316, 2325, 2350, 2411] := rectangleCover (by decide +kernel)
def src1798 : Request := ⟨⟨⟨2800,3902,882,530820⟩,681932636815360,6581809445307⟩,150,2,1,257319,35⟩
theorem cover1798 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1798 9161) 2411 2314 [2325, 2359, 2411] := rectangleCover (by decide +kernel)
def src1799 : Request := ⟨⟨⟨2800,3902,854,530820⟩,665461916958720,6418829718882⟩,150,2,1,257319,36⟩
theorem cover1799 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1799 9161) 2411 2314 [2323, 2351, 2411] := rectangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source2572

-- Source: Research6969.PhysicalChecks028
section Z6969Source2573
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1800 : Request := ⟨⟨⟨2800,3902,854,530820⟩,665461916958720,6418829718882⟩,150,2,1,257319,37⟩
theorem cover1800 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1800 8457) 2411 2314 [2323, 2351, 2411] := rectangleCover (by decide +kernel)
def src1801 : Request := ⟨⟨⟨2800,3902,834,530820⟩,653560508579840,6301295063987⟩,150,2,1,257319,38⟩
theorem cover1801 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1801 9161) 2411 2314 [2317, 2328, 2359, 2411] := rectangleCover (by decide +kernel)
def src1802 : Request := ⟨⟨⟨2600,3623,819,530820⟩,546063062138880,4892906717079⟩,150,2,1,257319,39⟩
theorem cover1802 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1802 9161) 2411 2314 [2322, 2348, 2411] := rectangleCover (by decide +kernel)
def src1803 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257319,40⟩
theorem cover1803 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1803 9161) 2411 2314 [2318, 2333, 2375, 2411] := rectangleCover (by decide +kernel)
def src1804 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257319,41⟩
theorem cover1804 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1804 8457) 2411 2314 [2320, 2340, 2396, 2411] := rectangleCover (by decide +kernel)
def src1805 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257319,42⟩
theorem cover1805 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1805 8457) 2411 2314 [2332, 2386, 2411] := rectangleCover (by decide +kernel)
def src1806 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257319,43⟩
theorem cover1806 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1806 7807) 2411 2314 [2324, 2355, 2411] := rectangleCover (by decide +kernel)
def src1807 : Request := ⟨⟨⟨2600,3623,775,530820⟩,523640687820800,4687093383477⟩,150,2,1,257319,44⟩
theorem cover1807 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1807 8457) 2411 2314 [2320, 2340, 2397, 2411] := rectangleCover (by decide +kernel)
def src1808 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257319,45⟩
theorem cover1808 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1808 7207) 2411 2314 [2315, 2321, 2338, 2386, 2411] := rectangleCover (by decide +kernel)
def src1809 : Request := ⟨⟨⟨2600,3623,775,530820⟩,523640687820800,4687093383477⟩,150,2,1,257319,46⟩
theorem cover1809 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1809 7807) 2411 2314 [2318, 2333, 2376, 2411] := rectangleCover (by decide +kernel)
def src1810 : Request := ⟨⟨⟨2600,3623,775,530820⟩,523640687820800,4687093383477⟩,150,2,1,257319,47⟩
theorem cover1810 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1810 7807) 2411 2314 [2328, 2371, 2411] := rectangleCover (by decide +kernel)
def src1811 : Request := ⟨⟨⟨1450,2020,442,530820⟩,92522927882240,461852681878⟩,85,2,1,257319,48⟩
theorem cover1811 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1811 4461) 2411 2314 [2318, 2332, 2373, 2411] := rectangleCover (by decide +kernel)
def src1812 : Request := ⟨⟨⟨2300,3204,724,530820⟩,377903408742400,2992689220368⟩,150,2,1,257319,49⟩
theorem cover1812 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1812 8457) 2411 2314 [2316, 2324, 2347, 2411] := rectangleCover (by decide +kernel)
def src1813 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257319,50⟩
theorem cover1813 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1813 9161) 2411 2314 [2316, 2324, 2347, 2411] := rectangleCover (by decide +kernel)
def src1814 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257319,51⟩
theorem cover1814 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1814 8457) 2411 2314 [2317, 2329, 2363, 2411] := rectangleCover (by decide +kernel)
def src1815 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257319,52⟩
theorem cover1815 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1815 8457) 2411 2314 [2327, 2367, 2411] := rectangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source2573

-- Source: Research6969.TerminalFits13
section Z6969Source2574
set_option autoImplicit true
namespace Research6969.TerminalFits
open PhysicalCatalogue
set_option maxHeartbeats 800000
theorem fit1780: TerminalWitness.Fits src1780 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1781: TerminalWitness.Fits src1781 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1782: TerminalWitness.Fits src1782 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1783: TerminalWitness.Fits src1783 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1784: TerminalWitness.Fits src1784 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.TransitionBanks.rank263 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1785: TerminalWitness.Fits src1785 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks44To47.rank46 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1786: TerminalWitness.Fits src1786 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks44To47.rank46 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1787: TerminalWitness.Fits src1787 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1788: TerminalWitness.Fits src1788 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank65 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1789: TerminalWitness.Fits src1789 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank64 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1790: TerminalWitness.Fits src1790 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank64 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1791: TerminalWitness.Fits src1791 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks44To47.rank44 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1792: TerminalWitness.Fits src1792 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank43 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1793: TerminalWitness.Fits src1793 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank42 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1794: TerminalWitness.Fits src1794 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank42 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1795: TerminalWitness.Fits src1795 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks28To31.rank29 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1796: TerminalWitness.Fits src1796 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks28To31.rank28 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1797: TerminalWitness.Fits src1797 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks28To31.rank28 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1798: TerminalWitness.Fits src1798 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank63 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1799: TerminalWitness.Fits src1799 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank62 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1800: TerminalWitness.Fits src1800 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank62 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1801: TerminalWitness.Fits src1801 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank61 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1802: TerminalWitness.Fits src1802 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.TransitionBanks.rank259 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1803: TerminalWitness.Fits src1803 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1804: TerminalWitness.Fits src1804 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1805: TerminalWitness.Fits src1805 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1806: TerminalWitness.Fits src1806 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1807: TerminalWitness.Fits src1807 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks36To39.rank39 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1808: TerminalWitness.Fits src1808 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1809: TerminalWitness.Fits src1809 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks36To39.rank39 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1810: TerminalWitness.Fits src1810 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks36To39.rank39 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1811: TerminalWitness.Fits src1811 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks4To7.rank6 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

end Research6969.TerminalFits
end Z6969Source2574

-- Source: Research6969.PhysicalChecks029
section Z6969Source2575
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1816 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257319,53⟩
theorem cover1816 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1816 7807) 2411 2314 [2320, 2339, 2393, 2411] := rectangleCover (by decide +kernel)
def src1817 : Request := ⟨⟨⟨3000,4180,894,530820⟩,804053213511680,8301255031708⟩,195,2,1,257319,54⟩
theorem cover1817 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1817 10751) 2411 2314 [2320, 2340, 2397, 2411] := rectangleCover (by decide +kernel)
def src1818 : Request := ⟨⟨⟨3000,4180,894,530820⟩,804053213511680,8301255031708⟩,195,2,1,257319,55⟩
theorem cover1818 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1818 10751) 2411 2314 [2329, 2374, 2411] := rectangleCover (by decide +kernel)
def src1819 : Request := ⟨⟨⟨2800,3901,882,530820⟩,681932636815360,6576375970149⟩,195,2,1,257319,56⟩
theorem cover1819 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1819 10751) 2411 2314 [2323, 2351, 2411] := rectangleCover (by decide +kernel)
def src1820 : Request := ⟨⟨⟨2800,3901,854,530820⟩,665461916958720,6413535689982⟩,195,2,1,257319,57⟩
theorem cover1820 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1820 11646) 2411 2314 [2320, 2340, 2396, 2411] := rectangleCover (by decide +kernel)
def src1821 : Request := ⟨⟨⟨2800,3907,834,530820⟩,653560508579840,6327305614587⟩,22,3,1,385979,0⟩
theorem cover1821 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1821 62519) 2411 2314 [2318, 2332, 2372, 2411] := rectangleCover (by decide +kernel)
def src1822 : Request := ⟨⟨⟨2800,3907,834,530820⟩,653560508579840,6327305614587⟩,22,3,1,385979,1⟩
theorem cover1822 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1822 57710) 2411 2314 [2318, 2332, 2372, 2411] := rectangleCover (by decide +kernel)
def src1823 : Request := ⟨⟨⟨2600,3628,793,530820⟩,532875289296896,4792991160379⟩,22,3,1,385979,2⟩
theorem cover1823 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1823 53271) 2411 2314 [2315, 2321, 2338, 2385, 2411] := rectangleCover (by decide +kernel)
def src1824 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,385979,3⟩
theorem cover1824 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1824 45392) 2411 2314 [2316, 2324, 2346, 2408, 2411] := rectangleCover (by decide +kernel)
def src1825 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,385979,4⟩
theorem cover1825 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1825 41901) 2411 2314 [2318, 2332, 2372, 2411] := rectangleCover (by decide +kernel)
def src1826 : Request := ⟨⟨⟨2600,3628,793,530820⟩,532875289296896,4792991160379⟩,22,3,1,385979,5⟩
theorem cover1826 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1826 38678) 2411 2314 [2316, 2324, 2347, 2411] := rectangleCover (by decide +kernel)
def src1827 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,385979,6⟩
theorem cover1827 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1827 32957) 2411 2314 [2320, 2340, 2396, 2411] := rectangleCover (by decide +kernel)
def src1828 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,385979,7⟩
theorem cover1828 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1828 28082) 2411 2314 [2320, 2340, 2396, 2411] := rectangleCover (by decide +kernel)
def src1829 : Request := ⟨⟨⟨2600,3628,793,530820⟩,532875289296896,4792991160379⟩,22,3,1,385979,8⟩
theorem cover1829 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1829 23928) 2411 2314 [2316, 2325, 2350, 2411] := rectangleCover (by decide +kernel)
def src1830 : Request := ⟨⟨⟨2600,3628,793,530820⟩,532875289296896,4792991160379⟩,22,3,1,385979,9⟩
theorem cover1830 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1830 18821) 2411 2314 [2315, 2321, 2337, 2382, 2411] := rectangleCover (by decide +kernel)
def src1831 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,385979,10⟩
theorem cover1831 : PhysicalWindow.Cover (PhysicalWindow.Rectangle src1831 13667) 2411 2314 [2319, 2336, 2384, 2411] := rectangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source2575

-- Source: Research6969.TerminalFits14
section Z6969Source2576
set_option autoImplicit true
namespace Research6969.TerminalFits
open PhysicalCatalogue
set_option maxHeartbeats 800000
theorem fit1812: TerminalWitness.Fits src1812 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank27 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1813: TerminalWitness.Fits src1813 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank26 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1814: TerminalWitness.Fits src1814 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank26 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1815: TerminalWitness.Fits src1815 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank26 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1816: TerminalWitness.Fits src1816 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank26 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1817: TerminalWitness.Fits src1817 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks76To78.rank76 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1818: TerminalWitness.Fits src1818 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks76To78.rank76 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1819: TerminalWitness.Fits src1819 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank60 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1820: TerminalWitness.Fits src1820 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks56To59.rank59 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1821: TerminalWitness.Fits src1821 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks68To71.rank71 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1822: TerminalWitness.Fits src1822 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks68To71.rank71 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1823: TerminalWitness.Fits src1823 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1824: TerminalWitness.Fits src1824 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1825: TerminalWitness.Fits src1825 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1826: TerminalWitness.Fits src1826 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1827: TerminalWitness.Fits src1827 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1828: TerminalWitness.Fits src1828 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1829: TerminalWitness.Fits src1829 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1830: TerminalWitness.Fits src1830 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1831: TerminalWitness.Fits src1831 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1832: TerminalWitness.Fits src1832 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1833: TerminalWitness.Fits src1833 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks68To71.rank70 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1834: TerminalWitness.Fits src1834 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks36To39.rank37 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1835: TerminalWitness.Fits src1835 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.TransitionBanks.rank268 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1836: TerminalWitness.Fits src1836 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks32To35.rank34 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1837: TerminalWitness.Fits src1837 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1838: TerminalWitness.Fits src1838 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1839: TerminalWitness.Fits src1839 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1840: TerminalWitness.Fits src1840 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1841: TerminalWitness.Fits src1841 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.TransitionBanks.rank263 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1842: TerminalWitness.Fits src1842 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks44To47.rank46 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1843: TerminalWitness.Fits src1843 2314 2411 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

end Research6969.TerminalFits
end Z6969Source2576

-- Source: Research6969.AxisChoices01
section Z6969Source2577
set_option autoImplicit true
namespace Research6969.AxisChoices
open TerminalFits PhysicalCatalogue
def test1798:AxisTests.Test:=⟨src1798,9161,fit1798,by decide,_,cover1798⟩
def test1799:AxisTests.Test:=⟨src1799,9161,fit1799,by decide,_,cover1799⟩
def test1800:AxisTests.Test:=⟨src1800,8457,fit1800,by decide,_,cover1800⟩
def test1801:AxisTests.Test:=⟨src1801,9161,fit1801,by decide,_,cover1801⟩
def test1802:AxisTests.Test:=⟨src1802,9161,fit1802,by decide,_,cover1802⟩
def test1803:AxisTests.Test:=⟨src1803,9161,fit1803,by decide,_,cover1803⟩
def test1804:AxisTests.Test:=⟨src1804,8457,fit1804,by decide,_,cover1804⟩
def test1805:AxisTests.Test:=⟨src1805,8457,fit1805,by decide,_,cover1805⟩
def test1806:AxisTests.Test:=⟨src1806,7807,fit1806,by decide,_,cover1806⟩
def test1807:AxisTests.Test:=⟨src1807,8457,fit1807,by decide,_,cover1807⟩
def test1808:AxisTests.Test:=⟨src1808,7207,fit1808,by decide,_,cover1808⟩
def test1809:AxisTests.Test:=⟨src1809,7807,fit1809,by decide,_,cover1809⟩
def test1810:AxisTests.Test:=⟨src1810,7807,fit1810,by decide,_,cover1810⟩
def test1811:AxisTests.Test:=⟨src1811,4461,fit1811,by decide,_,cover1811⟩
def test1812:AxisTests.Test:=⟨src1812,8457,fit1812,by decide,_,cover1812⟩
def test1813:AxisTests.Test:=⟨src1813,9161,fit1813,by decide,_,cover1813⟩
def test1814:AxisTests.Test:=⟨src1814,8457,fit1814,by decide,_,cover1814⟩
def test1815:AxisTests.Test:=⟨src1815,8457,fit1815,by decide,_,cover1815⟩
def test1816:AxisTests.Test:=⟨src1816,7807,fit1816,by decide,_,cover1816⟩
def test1817:AxisTests.Test:=⟨src1817,10751,fit1817,by decide,_,cover1817⟩
def test1818:AxisTests.Test:=⟨src1818,10751,fit1818,by decide,_,cover1818⟩
def test1819:AxisTests.Test:=⟨src1819,10751,fit1819,by decide,_,cover1819⟩
def test1820:AxisTests.Test:=⟨src1820,11646,fit1820,by decide,_,cover1820⟩
def test1821:AxisTests.Test:=⟨src1821,62519,fit1821,by decide,_,cover1821⟩
end Research6969.AxisChoices
end Z6969Source2577

-- Source: Research6969.AxisChoices02
section Z6969Source2578
set_option autoImplicit true
namespace Research6969.AxisChoices
open TerminalFits PhysicalCatalogue
def test1822:AxisTests.Test:=⟨src1822,57710,fit1822,by decide,_,cover1822⟩
def test1823:AxisTests.Test:=⟨src1823,53271,fit1823,by decide,_,cover1823⟩
def test1824:AxisTests.Test:=⟨src1824,45392,fit1824,by decide,_,cover1824⟩
def test1825:AxisTests.Test:=⟨src1825,41901,fit1825,by decide,_,cover1825⟩
def test1826:AxisTests.Test:=⟨src1826,38678,fit1826,by decide,_,cover1826⟩
def test1827:AxisTests.Test:=⟨src1827,32957,fit1827,by decide,_,cover1827⟩
def test1828:AxisTests.Test:=⟨src1828,28082,fit1828,by decide,_,cover1828⟩
def test1829:AxisTests.Test:=⟨src1829,23928,fit1829,by decide,_,cover1829⟩
def test1830:AxisTests.Test:=⟨src1830,18821,fit1830,by decide,_,cover1830⟩
def test1831:AxisTests.Test:=⟨src1831,13667,fit1831,by decide,_,cover1831⟩
def test1832:AxisTests.Test:=⟨src1832,9161,fit1832,by decide,_,cover1832⟩
def test1833:AxisTests.Test:=⟨src1833,8457,fit1833,by decide,_,cover1833⟩
def test1834:AxisTests.Test:=⟨src1834,6653,fit1834,by decide,_,cover1834⟩
def test1835:AxisTests.Test:=⟨src1835,7207,fit1835,by decide,_,cover1835⟩
def test1836:AxisTests.Test:=⟨src1836,6142,fit1836,by decide,_,cover1836⟩
def test1837:AxisTests.Test:=⟨src1837,7207,fit1837,by decide,_,cover1837⟩
def test1838:AxisTests.Test:=⟨src1838,6653,fit1838,by decide,_,cover1838⟩
def test1839:AxisTests.Test:=⟨src1839,6142,fit1839,by decide,_,cover1839⟩
def test1840:AxisTests.Test:=⟨src1840,7807,fit1840,by decide,_,cover1840⟩
def test1841:AxisTests.Test:=⟨src1841,7207,fit1841,by decide,_,cover1841⟩
def test1842:AxisTests.Test:=⟨src1842,7207,fit1842,by decide,_,cover1842⟩
def test1843:AxisTests.Test:=⟨src1843,7207,fit1843,by decide,_,cover1843⟩
def test1844:AxisTests.Test:=⟨src1844,6653,fit1844,by decide,_,cover1844⟩
def test1845:AxisTests.Test:=⟨src1845,9161,fit1845,by decide,_,cover1845⟩
end Research6969.AxisChoices
end Z6969Source2578
