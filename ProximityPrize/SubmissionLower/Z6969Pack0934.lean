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
  have actualLegal:OnTariff.Legal p₀.main s.graph.graphDegree b.seedHi b.axisHi (b.gm i) (mainBook i).seedMass 2389 p₀.cutoff:=by
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
  have ph:131071+s.model.overhead≤(133460:ℤ):=OnTariff.degree_bound s.higher
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
    have fit:179740≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
    have sp:0<seed i:=by unfold seed;omega
    have sc:=NativeSurfaceCount.regular_equation s.F (PairedMarks.rescue_sub s.pair) C.rescuePr.primitive.ne_zero A gp d0.ge sp
      (NormalGeometry.helper_cap s) ((K1_14_4.seedDegree_le_iff ..).mp le_rfl) ph (by decide:0<133460)
      (by decide) fit (by decide) (fun y hy=>(PairedMarks.rescue_law s.pair A gp original hy).1)
      (fun y hy=>by simpa [NonlinearMarkRows.evaluate,NativeSurfaceCount.label,K1_14.graphEval,Polynomial.eval_map] using PairedMarks.native_rescue s.pair C.rescuePr y hy)
      (fun y hy=>(PairedMarks.rescue_law s.pair A gp original hy).2)
    have amount:=NativeSurfaceCount.round_price (bad:=0) (g:=C.rescueFull.natDegree) (v:=K1_14_4.seedDegree C.rescueFull)
      (u:=seed i) (r:=(helper s).graphDegree-1) (d:=133460) (a:=179740) (n:=Fintype.card I) (by simpa using sc)
    change (rescueLabels s.pair).card≤0+C.rescueFull.natDegree*(JointRouted.seedWeight 133460 (seed i))^2+
      2*K1_14_4.seedDegree C.rescueFull*JointRouted.seedWeight 133460 (seed i)*JointRouted.ordWeight 133460 ((helper s).graphDegree-1) at amount
    rw [d0,FastHeight.side_eq,FastHeight.ordinate_eq 133460 _ (by decide)] at amount
    have cd:=inc 0 ((PairPrices.sx i)^2:ℕ) (2*PairPrices.sx i*PairPrices.sy:ℕ) (by
      simp only [Int.zero_add]
      exact_mod_cast amount.trans_eq (by dsimp [PairPrices.sx,PairPrices.sy,PairPrices.d];ring))
    exact_mod_cast cd.trans pay
  | node fee=>
    rw [PairPrices.sameOK,tag] at pay
    obtain ⟨quad,yes,char,ok,paid⟩:=pay
    have cert:=NodeBudget.family s.F (PairedMarks.rescue_sub s.pair) rfl ((by decide:0<2293).trans_le s.lower) s.higher
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
  have ph:131071+s.model.overhead≤(133460:ℤ):=by have d:=s.higher;omega
  have amount:=ThreeInvoice.charge s.pair (nativeHelper s) s.native C (PhysicalHelperTariff.primitive s.prime s.slope)
    rfl d0.ge un (NormalGeometry.helper_cap s) s.product (h.gradeHigh.trans_lt small)
    ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h.gradeHigh) _)).trans_lt mg)
    ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h.gradeHigh) _)).trans_lt rg)
    (s.higher.trans (by decide)) ph (by decide) (by decide) (by decide) gv ax
  rw [d0,FastHeight.side_eq,FastHeight.ordinate_eq 133460 _ (by decide)] at amount
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1784 : Request := ⟨⟨⟨2600,3625,819,530820⟩,546063062138880,4901614794409⟩,85,2,1,257363,21⟩
private theorem pass1784_2293 : (Rectangle src1784 7207) 2293 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1784_2297 : (Rectangle src1784 7207) 2297 2307 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1784_2308 : (Rectangle src1784 7207) 2308 2338 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1784_2339 : (Rectangle src1784 7207) 2339 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1784 : Cover (Rectangle src1784 7207) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1784_2293, by decide, by decide, pass1784_2297, by decide, by decide, pass1784_2308, by decide, by decide, pass1784_2339, rfl⟩
def src1785 : Request := ⟨⟨⟨2600,3625,793,530820⟩,532875289296896,4780245027563⟩,85,2,1,257363,22⟩
private theorem pass1785_2293 : (Rectangle src1785 6653) 2293 2297 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1785_2298 : (Rectangle src1785 6653) 2298 2311 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1785_2312 : (Rectangle src1785 6653) 2312 2351 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1785_2352 : (Rectangle src1785 6653) 2352 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1785 : Cover (Rectangle src1785 6653) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass1785_2293, by decide, by decide, pass1785_2298, by decide, by decide, pass1785_2312, by decide, by decide, pass1785_2352, rfl⟩
def src1786 : Request := ⟨⟨⟨2600,3625,793,530820⟩,532875289296896,4780245027563⟩,85,2,1,257363,23⟩
private theorem pass1786_2293 : (Rectangle src1786 6142) 2293 2301 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1786_2302 : (Rectangle src1786 6142) 2302 2327 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1786_2328 : (Rectangle src1786 6142) 2328 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1786 : Cover (Rectangle src1786 6142) 2389 2293 [2301,2327,2389] := by
  exact ⟨by decide, by decide, pass1786_2293, by decide, by decide, pass1786_2302, by decide, by decide, pass1786_2328, rfl⟩
def src1787 : Request := ⟨⟨⟨2300,3207,702,530820⟩,369170633195520,2930605494152⟩,85,2,1,257363,24⟩
private theorem pass1787_2293 : (Rectangle src1787 6653) 2293 2299 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1787_2300 : (Rectangle src1787 6653) 2300 2319 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1787_2320 : (Rectangle src1787 6653) 2320 2376 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1787_2377 : (Rectangle src1787 6653) 2377 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1787 : Cover (Rectangle src1787 6653) 2389 2293 [2299,2319,2376,2389] := by
  exact ⟨by decide, by decide, pass1787_2293, by decide, by decide, pass1787_2300, by decide, by decide, pass1787_2320, by decide, by decide, pass1787_2377, rfl⟩
def src1788 : Request := ⟨⟨⟨2800,3903,882,530820⟩,681932636815360,6587245977411⟩,115,2,1,257363,25⟩
private theorem pass1788_2293 : (Rectangle src1788 9161) 2293 2294 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1788_2295 : (Rectangle src1788 9161) 2295 2299 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1788_2300 : (Rectangle src1788 9161) 2300 2313 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1788_2314 : (Rectangle src1788 9161) 2314 2352 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1788_2353 : (Rectangle src1788 9161) 2353 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1788 : Cover (Rectangle src1788 9161) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass1788_2293, by decide, by decide, pass1788_2295, by decide, by decide, pass1788_2300, by decide, by decide, pass1788_2314, by decide, by decide, pass1788_2353, rfl⟩
def src1789 : Request := ⟨⟨⟨2800,3903,854,530820⟩,665461916958720,6424126719762⟩,115,2,1,257363,26⟩
private theorem pass1789_2293 : (Rectangle src1789 8457) 2293 2300 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1789_2301 : (Rectangle src1789 8457) 2301 2322 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1789_2323 : (Rectangle src1789 8457) 2323 2385 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1789_2386 : (Rectangle src1789 8457) 2386 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1789 : Cover (Rectangle src1789 8457) 2389 2293 [2300,2322,2385,2389] := by
  exact ⟨by decide, by decide, pass1789_2293, by decide, by decide, pass1789_2301, by decide, by decide, pass1789_2323, by decide, by decide, pass1789_2386, rfl⟩
def src1790 : Request := ⟨⟨⟨2800,3903,854,530820⟩,665461916958720,6424126719762⟩,115,2,1,257363,27⟩
private theorem pass1790_2293 : (Rectangle src1790 7807) 2293 2311 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1790_2312 : (Rectangle src1790 7807) 2312 2365 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1790_2366 : (Rectangle src1790 7807) 2366 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1790 : Cover (Rectangle src1790 7807) 2389 2293 [2311,2365,2389] := by
  exact ⟨by decide, by decide, pass1790_2293, by decide, by decide, pass1790_2312, by decide, by decide, pass1790_2366, rfl⟩
def src1791 : Request := ⟨⟨⟨2600,3624,819,530820⟩,546063062138880,4897259437389⟩,115,2,1,257363,28⟩
private theorem pass1791_2293 : (Rectangle src1791 7207) 2293 2294 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1791_2295 : (Rectangle src1791 7207) 2295 2299 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1791_2300 : (Rectangle src1791 7207) 2300 2313 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1791_2314 : (Rectangle src1791 7207) 2314 2353 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1791_2354 : (Rectangle src1791 7207) 2354 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1791 : Cover (Rectangle src1791 7207) 2389 2293 [2294,2299,2313,2353,2389] := by
  exact ⟨by decide, by decide, pass1791_2293, by decide, by decide, pass1791_2295, by decide, by decide, pass1791_2300, by decide, by decide, pass1791_2314, by decide, by decide, pass1791_2354, rfl⟩
def src1792 : Request := ⟨⟨⟨2600,3624,793,530820⟩,532875289296896,4776001446129⟩,115,2,1,257363,29⟩
private theorem pass1792_2293 : (Rectangle src1792 7207) 2293 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1792_2297 : (Rectangle src1792 7207) 2297 2308 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1792_2309 : (Rectangle src1792 7207) 2309 2341 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1792_2342 : (Rectangle src1792 7207) 2342 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1792 : Cover (Rectangle src1792 7207) 2389 2293 [2296,2308,2341,2389] := by
  exact ⟨by decide, by decide, pass1792_2293, by decide, by decide, pass1792_2297, by decide, by decide, pass1792_2309, by decide, by decide, pass1792_2342, rfl⟩
def src1793 : Request := ⟨⟨⟨2600,3624,775,530820⟩,523640687820800,4691256264577⟩,115,2,1,257363,30⟩
private theorem pass1793_2293 : (Rectangle src1793 7807) 2293 2298 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1793_2299 : (Rectangle src1793 7807) 2299 2315 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1793_2316 : (Rectangle src1793 7807) 2316 2364 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1793_2365 : (Rectangle src1793 7807) 2365 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1793 : Cover (Rectangle src1793 7807) 2389 2293 [2298,2315,2364,2389] := by
  exact ⟨by decide, by decide, pass1793_2293, by decide, by decide, pass1793_2299, by decide, by decide, pass1793_2316, by decide, by decide, pass1793_2365, rfl⟩
def src1794 : Request := ⟨⟨⟨2600,3624,775,530820⟩,523640687820800,4691256264577⟩,115,2,1,257363,31⟩
private theorem pass1794_2293 : (Rectangle src1794 7207) 2293 2299 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1794_2300 : (Rectangle src1794 7207) 2300 2319 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1794_2320 : (Rectangle src1794 7207) 2320 2376 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1794_2377 : (Rectangle src1794 7207) 2377 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1794 : Cover (Rectangle src1794 7207) 2389 2293 [2299,2319,2376,2389] := by
  exact ⟨by decide, by decide, pass1794_2293, by decide, by decide, pass1794_2300, by decide, by decide, pass1794_2320, by decide, by decide, pass1794_2377, rfl⟩
def src1795 : Request := ⟨⟨⟨2300,3206,724,530820⟩,377903408742400,2998712046218⟩,115,2,1,257363,32⟩
private theorem pass1795_2293 : (Rectangle src1795 7807) 2293 2299 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1795_2300 : (Rectangle src1795 7807) 2300 2319 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1795_2320 : (Rectangle src1795 7807) 2320 2376 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1795_2377 : (Rectangle src1795 7807) 2377 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1795 : Cover (Rectangle src1795 7807) 2389 2293 [2299,2319,2376,2389] := by
  exact ⟨by decide, by decide, pass1795_2293, by decide, by decide, pass1795_2300, by decide, by decide, pass1795_2320, by decide, by decide, pass1795_2377, rfl⟩
def src1796 : Request := ⟨⟨⟨2300,3206,702,530820⟩,369170633195520,2927665016684⟩,115,2,1,257363,33⟩
private theorem pass1796_2293 : (Rectangle src1796 7207) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1796_2294 : (Rectangle src1796 7207) 2294 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1796_2297 : (Rectangle src1796 7207) 2297 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1796_2305 : (Rectangle src1796 7207) 2305 2327 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1796_2328 : (Rectangle src1796 7207) 2328 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1796 : Cover (Rectangle src1796 7207) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1796_2293, by decide, by decide, pass1796_2294, by decide, by decide, pass1796_2297, by decide, by decide, pass1796_2305, by decide, by decide, pass1796_2328, rfl⟩
def src1797 : Request := ⟨⟨⟨2300,3206,702,530820⟩,369170633195520,2927665016684⟩,115,2,1,257363,34⟩
private theorem pass1797_2293 : (Rectangle src1797 6653) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1797_2294 : (Rectangle src1797 6653) 2294 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1797_2297 : (Rectangle src1797 6653) 2297 2305 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1797_2306 : (Rectangle src1797 6653) 2306 2330 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1797_2331 : (Rectangle src1797 6653) 2331 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1797 : Cover (Rectangle src1797 6653) 2389 2293 [2293,2296,2305,2330,2389] := by
  exact ⟨by decide, by decide, pass1797_2293, by decide, by decide, pass1797_2294, by decide, by decide, pass1797_2297, by decide, by decide, pass1797_2306, by decide, by decide, pass1797_2331, rfl⟩
def src1798 : Request := ⟨⟨⟨2800,3902,882,530820⟩,681932636815360,6581809445307⟩,150,2,1,257363,35⟩
private theorem pass1798_2293 : (Rectangle src1798 9161) 2293 2303 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1798_2304 : (Rectangle src1798 9161) 2304 2334 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1798_2335 : (Rectangle src1798 9161) 2335 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1798 : Cover (Rectangle src1798 9161) 2389 2293 [2303,2334,2389] := by
  exact ⟨by decide, by decide, pass1798_2293, by decide, by decide, pass1798_2304, by decide, by decide, pass1798_2335, rfl⟩
def src1799 : Request := ⟨⟨⟨2800,3902,854,530820⟩,665461916958720,6418829718882⟩,150,2,1,257363,36⟩
private theorem pass1799_2293 : (Rectangle src1799 9161) 2293 2301 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1799_2302 : (Rectangle src1799 9161) 2302 2326 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1799_2327 : (Rectangle src1799 9161) 2327 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1799 : Cover (Rectangle src1799 9161) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1799_2293, by decide, by decide, pass1799_2302, by decide, by decide, pass1799_2327, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2572

-- Source: Research6969.PhysicalChecks028
section Z6969Source2573
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1800 : Request := ⟨⟨⟨2800,3902,854,530820⟩,665461916958720,6418829718882⟩,150,2,1,257363,37⟩
private theorem pass1800_2293 : (Rectangle src1800 8457) 2293 2300 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1800_2301 : (Rectangle src1800 8457) 2301 2323 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1800_2324 : (Rectangle src1800 8457) 2324 2388 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1800_2389 : (Rectangle src1800 8457) 2389 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1800 : Cover (Rectangle src1800 8457) 2389 2293 [2300,2323,2388,2389] := by
  exact ⟨by decide, by decide, pass1800_2293, by decide, by decide, pass1800_2301, by decide, by decide, pass1800_2324, by decide, by decide, pass1800_2389, rfl⟩
def src1801 : Request := ⟨⟨⟨2800,3902,834,530820⟩,653560508579840,6301295063987⟩,150,2,1,257363,38⟩
private theorem pass1801_2293 : (Rectangle src1801 9161) 2293 2294 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1801_2295 : (Rectangle src1801 9161) 2295 2299 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1801_2300 : (Rectangle src1801 9161) 2300 2314 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1801_2315 : (Rectangle src1801 9161) 2315 2357 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1801_2358 : (Rectangle src1801 9161) 2358 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1801 : Cover (Rectangle src1801 9161) 2389 2293 [2294,2299,2314,2357,2389] := by
  exact ⟨by decide, by decide, pass1801_2293, by decide, by decide, pass1801_2295, by decide, by decide, pass1801_2300, by decide, by decide, pass1801_2315, by decide, by decide, pass1801_2358, rfl⟩
def src1802 : Request := ⟨⟨⟨2600,3623,819,530820⟩,546063062138880,4892906717079⟩,150,2,1,257363,39⟩
private theorem pass1802_2293 : (Rectangle src1802 9161) 2293 2300 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1802_2301 : (Rectangle src1802 9161) 2301 2322 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1802_2323 : (Rectangle src1802 9161) 2323 2384 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1802_2385 : (Rectangle src1802 9161) 2385 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1802 : Cover (Rectangle src1802 9161) 2389 2293 [2300,2322,2384,2389] := by
  exact ⟨by decide, by decide, pass1802_2293, by decide, by decide, pass1802_2301, by decide, by decide, pass1802_2323, by decide, by decide, pass1802_2385, rfl⟩
def src1803 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257363,40⟩
private theorem pass1803_2293 : (Rectangle src1803 9161) 2293 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1803_2297 : (Rectangle src1803 9161) 2297 2307 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1803_2308 : (Rectangle src1803 9161) 2308 2338 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1803_2339 : (Rectangle src1803 9161) 2339 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1803 : Cover (Rectangle src1803 9161) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1803_2293, by decide, by decide, pass1803_2297, by decide, by decide, pass1803_2308, by decide, by decide, pass1803_2339, rfl⟩
def src1804 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257363,41⟩
private theorem pass1804_2293 : (Rectangle src1804 8457) 2293 2297 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1804_2298 : (Rectangle src1804 8457) 2298 2311 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1804_2312 : (Rectangle src1804 8457) 2312 2351 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1804_2352 : (Rectangle src1804 8457) 2352 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1804 : Cover (Rectangle src1804 8457) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass1804_2293, by decide, by decide, pass1804_2298, by decide, by decide, pass1804_2312, by decide, by decide, pass1804_2352, rfl⟩
def src1805 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257363,42⟩
private theorem pass1805_2293 : (Rectangle src1805 8457) 2293 2310 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1805_2311 : (Rectangle src1805 8457) 2311 2361 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1805_2362 : (Rectangle src1805 8457) 2362 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1805 : Cover (Rectangle src1805 8457) 2389 2293 [2310,2361,2389] := by
  exact ⟨by decide, by decide, pass1805_2293, by decide, by decide, pass1805_2311, by decide, by decide, pass1805_2362, rfl⟩
def src1806 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257363,43⟩
private theorem pass1806_2293 : (Rectangle src1806 7807) 2293 2301 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1806_2302 : (Rectangle src1806 7807) 2302 2326 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1806_2327 : (Rectangle src1806 7807) 2327 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1806 : Cover (Rectangle src1806 7807) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1806_2293, by decide, by decide, pass1806_2302, by decide, by decide, pass1806_2327, rfl⟩
def src1807 : Request := ⟨⟨⟨2600,3623,775,530820⟩,523640687820800,4687093383477⟩,150,2,1,257363,44⟩
private theorem pass1807_2293 : (Rectangle src1807 8457) 2293 2297 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1807_2298 : (Rectangle src1807 8457) 2298 2311 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1807_2312 : (Rectangle src1807 8457) 2312 2351 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1807_2352 : (Rectangle src1807 8457) 2352 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1807 : Cover (Rectangle src1807 8457) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass1807_2293, by decide, by decide, pass1807_2298, by decide, by decide, pass1807_2312, by decide, by decide, pass1807_2352, rfl⟩
def src1808 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257363,45⟩
private theorem pass1808_2293 : (Rectangle src1808 7207) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1808_2294 : (Rectangle src1808 7207) 2294 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1808_2297 : (Rectangle src1808 7207) 2297 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1808_2305 : (Rectangle src1808 7207) 2305 2327 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1808_2328 : (Rectangle src1808 7207) 2328 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1808 : Cover (Rectangle src1808 7207) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1808_2293, by decide, by decide, pass1808_2294, by decide, by decide, pass1808_2297, by decide, by decide, pass1808_2305, by decide, by decide, pass1808_2328, rfl⟩
def src1809 : Request := ⟨⟨⟨2600,3623,775,530820⟩,523640687820800,4687093383477⟩,150,2,1,257363,46⟩
private theorem pass1809_2293 : (Rectangle src1809 7807) 2293 2295 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1809_2296 : (Rectangle src1809 7807) 2296 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1809_2305 : (Rectangle src1809 7807) 2305 2330 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1809_2331 : (Rectangle src1809 7807) 2331 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1809 : Cover (Rectangle src1809 7807) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass1809_2293, by decide, by decide, pass1809_2296, by decide, by decide, pass1809_2305, by decide, by decide, pass1809_2331, rfl⟩
def src1810 : Request := ⟨⟨⟨2600,3623,775,530820⟩,523640687820800,4687093383477⟩,150,2,1,257363,47⟩
private theorem pass1810_2293 : (Rectangle src1810 7807) 2293 2305 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1810_2306 : (Rectangle src1810 7807) 2306 2343 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1810_2344 : (Rectangle src1810 7807) 2344 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1810 : Cover (Rectangle src1810 7807) 2389 2293 [2305,2343,2389] := by
  exact ⟨by decide, by decide, pass1810_2293, by decide, by decide, pass1810_2306, by decide, by decide, pass1810_2344, rfl⟩
def src1811 : Request := ⟨⟨⟨1450,2020,442,530820⟩,92522927882240,461852681878⟩,85,2,1,257363,48⟩
private theorem pass1811_2293 : (Rectangle src1811 4461) 2293 2295 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1811_2296 : (Rectangle src1811 4461) 2296 2303 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1811_2304 : (Rectangle src1811 4461) 2304 2326 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1811_2327 : (Rectangle src1811 4461) 2327 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1811 : Cover (Rectangle src1811 4461) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass1811_2293, by decide, by decide, pass1811_2296, by decide, by decide, pass1811_2304, by decide, by decide, pass1811_2327, rfl⟩
def src1812 : Request := ⟨⟨⟨2300,3204,724,530820⟩,377903408742400,2992689220368⟩,150,2,1,257363,49⟩
private theorem pass1812_2293 : (Rectangle src1812 8457) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1812_2294 : (Rectangle src1812 8457) 2294 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1812_2297 : (Rectangle src1812 8457) 2297 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1812_2305 : (Rectangle src1812 8457) 2305 2327 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1812_2328 : (Rectangle src1812 8457) 2328 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1812 : Cover (Rectangle src1812 8457) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1812_2293, by decide, by decide, pass1812_2294, by decide, by decide, pass1812_2297, by decide, by decide, pass1812_2305, by decide, by decide, pass1812_2328, rfl⟩
def src1813 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257363,50⟩
private theorem pass1813_2293 : (Rectangle src1813 9161) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1813_2294 : (Rectangle src1813 9161) 2294 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1813_2297 : (Rectangle src1813 9161) 2297 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1813_2305 : (Rectangle src1813 9161) 2305 2327 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1813_2328 : (Rectangle src1813 9161) 2328 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1813 : Cover (Rectangle src1813 9161) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1813_2293, by decide, by decide, pass1813_2294, by decide, by decide, pass1813_2297, by decide, by decide, pass1813_2305, by decide, by decide, pass1813_2328, rfl⟩
def src1814 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257363,51⟩
private theorem pass1814_2293 : (Rectangle src1814 8457) 2293 2295 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1814_2296 : (Rectangle src1814 8457) 2296 2303 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1814_2304 : (Rectangle src1814 8457) 2304 2326 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1814_2327 : (Rectangle src1814 8457) 2327 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1814 : Cover (Rectangle src1814 8457) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass1814_2293, by decide, by decide, pass1814_2296, by decide, by decide, pass1814_2304, by decide, by decide, pass1814_2327, rfl⟩
def src1815 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257363,52⟩
private theorem pass1815_2293 : (Rectangle src1815 8457) 2293 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1815_2305 : (Rectangle src1815 8457) 2305 2338 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1815_2339 : (Rectangle src1815 8457) 2339 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1815 : Cover (Rectangle src1815 8457) 2389 2293 [2304,2338,2389] := by
  exact ⟨by decide, by decide, pass1815_2293, by decide, by decide, pass1815_2305, by decide, by decide, pass1815_2339, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2573

-- Source: Research6969.TerminalFits13
section Z6969Source2574
set_option autoImplicit true
namespace Research6969.TerminalFits
open PhysicalCatalogue
set_option maxHeartbeats 800000
theorem fit1780: TerminalWitness.Fits src1780 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1781: TerminalWitness.Fits src1781 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1782: TerminalWitness.Fits src1782 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1783: TerminalWitness.Fits src1783 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1784: TerminalWitness.Fits src1784 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.TransitionBanks.rank263 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1785: TerminalWitness.Fits src1785 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks44To47.rank46 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1786: TerminalWitness.Fits src1786 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks44To47.rank46 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1787: TerminalWitness.Fits src1787 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1788: TerminalWitness.Fits src1788 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank65 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1789: TerminalWitness.Fits src1789 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank64 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1790: TerminalWitness.Fits src1790 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank64 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1791: TerminalWitness.Fits src1791 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks44To47.rank44 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1792: TerminalWitness.Fits src1792 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank43 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1793: TerminalWitness.Fits src1793 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank42 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1794: TerminalWitness.Fits src1794 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank42 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1795: TerminalWitness.Fits src1795 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks28To31.rank29 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1796: TerminalWitness.Fits src1796 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks28To31.rank28 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1797: TerminalWitness.Fits src1797 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks28To31.rank28 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1798: TerminalWitness.Fits src1798 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank63 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1799: TerminalWitness.Fits src1799 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank62 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1800: TerminalWitness.Fits src1800 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank62 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1801: TerminalWitness.Fits src1801 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank61 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1802: TerminalWitness.Fits src1802 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.TransitionBanks.rank259 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1803: TerminalWitness.Fits src1803 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1804: TerminalWitness.Fits src1804 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1805: TerminalWitness.Fits src1805 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1806: TerminalWitness.Fits src1806 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1807: TerminalWitness.Fits src1807 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks36To39.rank39 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1808: TerminalWitness.Fits src1808 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1809: TerminalWitness.Fits src1809 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks36To39.rank39 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1810: TerminalWitness.Fits src1810 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks36To39.rank39 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1811: TerminalWitness.Fits src1811 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks4To7.rank6 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

end Research6969.TerminalFits
end Z6969Source2574

-- Source: Research6969.PhysicalChecks029
section Z6969Source2575
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1816 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257363,53⟩
private theorem pass1816_2293 : (Rectangle src1816 7807) 2293 2297 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1816_2298 : (Rectangle src1816 7807) 2298 2311 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1816_2312 : (Rectangle src1816 7807) 2312 2351 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1816_2352 : (Rectangle src1816 7807) 2352 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1816 : Cover (Rectangle src1816 7807) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass1816_2293, by decide, by decide, pass1816_2298, by decide, by decide, pass1816_2312, by decide, by decide, pass1816_2352, rfl⟩
def src1817 : Request := ⟨⟨⟨3000,4180,894,530820⟩,804053213511680,8301255031708⟩,195,2,1,257363,54⟩
private theorem pass1817_2293 : (Rectangle src1817 10751) 2293 2297 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1817_2298 : (Rectangle src1817 10751) 2298 2312 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1817_2313 : (Rectangle src1817 10751) 2313 2354 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1817_2355 : (Rectangle src1817 10751) 2355 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1817 : Cover (Rectangle src1817 10751) 2389 2293 [2297,2312,2354,2389] := by
  exact ⟨by decide, by decide, pass1817_2293, by decide, by decide, pass1817_2298, by decide, by decide, pass1817_2313, by decide, by decide, pass1817_2355, rfl⟩
def src1818 : Request := ⟨⟨⟨3000,4180,894,530820⟩,804053213511680,8301255031708⟩,195,2,1,257363,55⟩
private theorem pass1818_2293 : (Rectangle src1818 10751) 2293 2306 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1818_2307 : (Rectangle src1818 10751) 2307 2346 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1818_2347 : (Rectangle src1818 10751) 2347 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1818 : Cover (Rectangle src1818 10751) 2389 2293 [2306,2346,2389] := by
  exact ⟨by decide, by decide, pass1818_2293, by decide, by decide, pass1818_2307, by decide, by decide, pass1818_2347, rfl⟩
def src1819 : Request := ⟨⟨⟨2800,3901,882,530820⟩,681932636815360,6576375970149⟩,195,2,1,257363,56⟩
private theorem pass1819_2293 : (Rectangle src1819 10751) 2293 2300 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1819_2301 : (Rectangle src1819 10751) 2301 2322 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1819_2323 : (Rectangle src1819 10751) 2323 2384 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1819_2385 : (Rectangle src1819 10751) 2385 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1819 : Cover (Rectangle src1819 10751) 2389 2293 [2300,2322,2384,2389] := by
  exact ⟨by decide, by decide, pass1819_2293, by decide, by decide, pass1819_2301, by decide, by decide, pass1819_2323, by decide, by decide, pass1819_2385, rfl⟩
def src1820 : Request := ⟨⟨⟨2800,3901,854,530820⟩,665461916958720,6413535689982⟩,195,2,1,257363,57⟩
private theorem pass1820_2293 : (Rectangle src1820 11646) 2293 2298 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1820_2299 : (Rectangle src1820 11646) 2299 2315 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1820_2316 : (Rectangle src1820 11646) 2316 2363 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1820_2364 : (Rectangle src1820 11646) 2364 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1820 : Cover (Rectangle src1820 11646) 2389 2293 [2298,2315,2363,2389] := by
  exact ⟨by decide, by decide, pass1820_2293, by decide, by decide, pass1820_2299, by decide, by decide, pass1820_2316, by decide, by decide, pass1820_2364, rfl⟩
def src1821 : Request := ⟨⟨⟨2800,3907,834,530820⟩,653560508579840,6327305614587⟩,22,3,1,386045,0⟩
private theorem pass1821_2293 : (Rectangle src1821 62519) 2293 2295 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1821_2296 : (Rectangle src1821 62519) 2296 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1821_2305 : (Rectangle src1821 62519) 2305 2329 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1821_2330 : (Rectangle src1821 62519) 2330 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1821 : Cover (Rectangle src1821 62519) 2389 2293 [2295,2304,2329,2389] := by
  exact ⟨by decide, by decide, pass1821_2293, by decide, by decide, pass1821_2296, by decide, by decide, pass1821_2305, by decide, by decide, pass1821_2330, rfl⟩
def src1822 : Request := ⟨⟨⟨2800,3907,834,530820⟩,653560508579840,6327305614587⟩,22,3,1,386045,1⟩
private theorem pass1822_2293 : (Rectangle src1822 57710) 2293 2295 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1822_2296 : (Rectangle src1822 57710) 2296 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1822_2305 : (Rectangle src1822 57710) 2305 2329 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1822_2330 : (Rectangle src1822 57710) 2330 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1822 : Cover (Rectangle src1822 57710) 2389 2293 [2295,2304,2329,2389] := by
  exact ⟨by decide, by decide, pass1822_2293, by decide, by decide, pass1822_2296, by decide, by decide, pass1822_2305, by decide, by decide, pass1822_2330, rfl⟩
def src1823 : Request := ⟨⟨⟨2600,3628,793,530820⟩,532875289296896,4792991160379⟩,22,3,1,386045,2⟩
private theorem pass1823_2293 : (Rectangle src1823 53271) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1823_2294 : (Rectangle src1823 53271) 2294 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1823_2297 : (Rectangle src1823 53271) 2297 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1823_2305 : (Rectangle src1823 53271) 2305 2326 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1823_2327 : (Rectangle src1823 53271) 2327 2388 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1823_2389 : (Rectangle src1823 53271) 2389 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1823 : Cover (Rectangle src1823 53271) 2389 2293 [2293,2296,2304,2326,2388,2389] := by
  exact ⟨by decide, by decide, pass1823_2293, by decide, by decide, pass1823_2294, by decide, by decide, pass1823_2297, by decide, by decide, pass1823_2305, by decide, by decide, pass1823_2327, by decide, by decide, pass1823_2389, rfl⟩
def src1824 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,386045,3⟩
private theorem pass1824_2293 : (Rectangle src1824 45392) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1824_2294 : (Rectangle src1824 45392) 2294 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1824_2297 : (Rectangle src1824 45392) 2297 2304 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1824_2305 : (Rectangle src1824 45392) 2305 2327 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1824_2328 : (Rectangle src1824 45392) 2328 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1824 : Cover (Rectangle src1824 45392) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1824_2293, by decide, by decide, pass1824_2294, by decide, by decide, pass1824_2297, by decide, by decide, pass1824_2305, by decide, by decide, pass1824_2328, rfl⟩
def src1825 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,386045,4⟩
private theorem pass1825_2293 : (Rectangle src1825 41901) 2293 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1825_2297 : (Rectangle src1825 41901) 2297 2307 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1825_2308 : (Rectangle src1825 41901) 2308 2338 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1825_2339 : (Rectangle src1825 41901) 2339 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1825 : Cover (Rectangle src1825 41901) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1825_2293, by decide, by decide, pass1825_2297, by decide, by decide, pass1825_2308, by decide, by decide, pass1825_2339, rfl⟩
def src1826 : Request := ⟨⟨⟨2600,3628,793,530820⟩,532875289296896,4792991160379⟩,22,3,1,386045,5⟩
private theorem pass1826_2293 : (Rectangle src1826 38678) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1826_2294 : (Rectangle src1826 38678) 2294 2296 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1826_2297 : (Rectangle src1826 38678) 2297 2305 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1826_2306 : (Rectangle src1826 38678) 2306 2330 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1826_2331 : (Rectangle src1826 38678) 2331 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1826 : Cover (Rectangle src1826 38678) 2389 2293 [2293,2296,2305,2330,2389] := by
  exact ⟨by decide, by decide, pass1826_2293, by decide, by decide, pass1826_2294, by decide, by decide, pass1826_2297, by decide, by decide, pass1826_2306, by decide, by decide, pass1826_2331, rfl⟩
def src1827 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,386045,6⟩
private theorem pass1827_2293 : (Rectangle src1827 32957) 2293 2298 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1827_2299 : (Rectangle src1827 32957) 2299 2314 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1827_2315 : (Rectangle src1827 32957) 2315 2359 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1827_2360 : (Rectangle src1827 32957) 2360 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1827 : Cover (Rectangle src1827 32957) 2389 2293 [2298,2314,2359,2389] := by
  exact ⟨by decide, by decide, pass1827_2293, by decide, by decide, pass1827_2299, by decide, by decide, pass1827_2315, by decide, by decide, pass1827_2360, rfl⟩
def src1828 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,386045,7⟩
private theorem pass1828_2293 : (Rectangle src1828 28082) 2293 2297 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1828_2298 : (Rectangle src1828 28082) 2298 2311 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1828_2312 : (Rectangle src1828 28082) 2312 2351 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1828_2352 : (Rectangle src1828 28082) 2352 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1828 : Cover (Rectangle src1828 28082) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass1828_2293, by decide, by decide, pass1828_2298, by decide, by decide, pass1828_2312, by decide, by decide, pass1828_2352, rfl⟩
def src1829 : Request := ⟨⟨⟨2600,3628,793,530820⟩,532875289296896,4792991160379⟩,22,3,1,386045,8⟩
private theorem pass1829_2293 : (Rectangle src1829 23928) 2293 2294 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1829_2295 : (Rectangle src1829 23928) 2295 2299 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1829_2300 : (Rectangle src1829 23928) 2300 2313 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1829_2314 : (Rectangle src1829 23928) 2314 2352 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1829_2353 : (Rectangle src1829 23928) 2353 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1829 : Cover (Rectangle src1829 23928) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass1829_2293, by decide, by decide, pass1829_2295, by decide, by decide, pass1829_2300, by decide, by decide, pass1829_2314, by decide, by decide, pass1829_2353, rfl⟩
def src1830 : Request := ⟨⟨⟨2600,3628,793,530820⟩,532875289296896,4792991160379⟩,22,3,1,386045,9⟩
private theorem pass1830_2293 : (Rectangle src1830 18821) 2293 2293 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1830_2294 : (Rectangle src1830 18821) 2294 2295 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1830_2296 : (Rectangle src1830 18821) 2296 2301 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1830_2302 : (Rectangle src1830 18821) 2302 2318 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1830_2319 : (Rectangle src1830 18821) 2319 2365 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1830_2366 : (Rectangle src1830 18821) 2366 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1830 : Cover (Rectangle src1830 18821) 2389 2293 [2293,2295,2301,2318,2365,2389] := by
  exact ⟨by decide, by decide, pass1830_2293, by decide, by decide, pass1830_2294, by decide, by decide, pass1830_2296, by decide, by decide, pass1830_2302, by decide, by decide, pass1830_2319, by decide, by decide, pass1830_2366, rfl⟩
def src1831 : Request := ⟨⟨⟨2800,3907,854,530820⟩,665461916958720,6445344460182⟩,22,3,1,386045,10⟩
private theorem pass1831_2293 : (Rectangle src1831 13667) 2293 2297 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1831_2298 : (Rectangle src1831 13667) 2298 2311 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1831_2312 : (Rectangle src1831 13667) 2312 2350 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
private theorem pass1831_2351 : (Rectangle src1831 13667) 2351 2389 := Research6969.PhysicalWindow.rectangle_of_fast _ _ _ _ (by decide +kernel)
theorem cover1831 : Cover (Rectangle src1831 13667) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass1831_2293, by decide, by decide, pass1831_2298, by decide, by decide, pass1831_2312, by decide, by decide, pass1831_2351, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2575

-- Source: Research6969.TerminalFits14
section Z6969Source2576
set_option autoImplicit true
namespace Research6969.TerminalFits
open PhysicalCatalogue
set_option maxHeartbeats 800000
theorem fit1812: TerminalWitness.Fits src1812 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank27 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1813: TerminalWitness.Fits src1813 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank26 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1814: TerminalWitness.Fits src1814 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank26 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1815: TerminalWitness.Fits src1815 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank26 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1816: TerminalWitness.Fits src1816 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks24To27.rank26 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1817: TerminalWitness.Fits src1817 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks76To78.rank76 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1818: TerminalWitness.Fits src1818 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks76To78.rank76 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1819: TerminalWitness.Fits src1819 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks60To63.rank60 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1820: TerminalWitness.Fits src1820 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks56To59.rank59 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1821: TerminalWitness.Fits src1821 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks68To71.rank71 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1822: TerminalWitness.Fits src1822 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks68To71.rank71 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1823: TerminalWitness.Fits src1823 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1824: TerminalWitness.Fits src1824 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1825: TerminalWitness.Fits src1825 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1826: TerminalWitness.Fits src1826 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1827: TerminalWitness.Fits src1827 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1828: TerminalWitness.Fits src1828 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1829: TerminalWitness.Fits src1829 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1830: TerminalWitness.Fits src1830 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1831: TerminalWitness.Fits src1831 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1832: TerminalWitness.Fits src1832 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks52To55.rank53 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1833: TerminalWitness.Fits src1833 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks68To71.rank70 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1834: TerminalWitness.Fits src1834 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks36To39.rank37 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1835: TerminalWitness.Fits src1835 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.TransitionBanks.rank268 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1836: TerminalWitness.Fits src1836 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks32To35.rank34 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1837: TerminalWitness.Fits src1837 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1838: TerminalWitness.Fits src1838 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1839: TerminalWitness.Fits src1839 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1840: TerminalWitness.Fits src1840 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1841: TerminalWitness.Fits src1841 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.TransitionBanks.rank263 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1842: TerminalWitness.Fits src1842 2293 2389 SpreadCatalogue.shape := by
  exact ⟨Research6969.PackedRanks.TerminalRanks44To47.rank46 530820, by unfold Research6966.TerminalBanks.inside; decide +kernel,
    by decide, rfl, by decide, by decide, by decide,
    by unfold Lower6960.HelperSource.WidthGuard; decide +kernel⟩

theorem fit1843: TerminalWitness.Fits src1843 2293 2389 SpreadCatalogue.shape := by
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
