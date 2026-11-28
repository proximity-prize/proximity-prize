import ProximityPrize.SubmissionLower.R6970Height2313CompressedCore
import ProximityPrize.SubmissionLower.Z6969Pack0934

set_option Elab.async false

-- Source: Research6969.PairCell
section Z6969Source2550
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.PairCell
open _root_.Research6969
noncomputable section
open Finset Polynomial
open K1 (K I p)
open K1_14 (Jet Equation FX L)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface SeedField ProjectedProduct)
open Lower6960.Far6969RescueGeometry (word)
open Research6966
open _root_.Research6970.Height2313.Research6969.BookView (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry helper nativeHelper)
open PriceMethod (Mode Rate)
open scoped Classical
set_option maxRecDepth 14000
set_option maxHeartbeats 1900000

structure Row where
  lowerGrade:ℕ
  upperGrade:ℕ
  content:ℕ
  graph:ℕ
  seedLo:ℕ
  seedHi:Option ℕ
  axisLo:ℕ
  axisHi:Option ℕ
  wt:ℕ
  tests:List _root_.Research6970.Height2313.Research6969.MeasuredBound.Test
  rect:List _root_.Research6970.Height2313.Research6969.AxisTests.Test

def Row.off (b:Row):=b.content-b.graph
def Row.cross (b:Row):=2+b.graph-1
def Row.loPrimary (b:Row):=b.lowerGrade-b.off-b.cross
def Row.cap (b:Row) (i:Fin 18):_root_.Research6970.Height2313.Research6969.NormalGeometry.Bounds:=
  _root_.Research6970.Height2313.Research6969.NormalGeometry.limits ⟨b.upperGrade,(mainBook i).seedMass+(rescueBook i).seedMass⟩ b.tests (if b.axisHi.isSome then b.rect else [])
    b.graph b.seedLo b.wt b.seedHi b.axisLo (b.axisHi.getD 0)
def Row.gm (b:Row) (i:Fin 18):=min (b.cap i).grade (savedMainGrade i)
def Row.vm (b:Row) (i:Fin 18):=min (b.cap i).seed (mainBook i).seedMass
def Row.gr (b:Row) (i:Fin 18):=min (b.cap i).grade (savedRescueGrade i)
def Row.vr (b:Row) (i:Fin 18):=min (b.cap i).seed (rescueBook i).seedMass

structure Facts {i} (s:State i) (b:Row):Prop where
  gradeLow:b.lowerGrade≤s.f.natDegree
  gradeHigh:s.f.natDegree≤b.upperGrade
  control:_root_.Research6970.Height2313.Research6969.NormalGeometry.content s=b.content
  degree:s.graph.graphDegree=b.graph
  seedLow:b.seedLo≤seedDegree s.native.poly
  seedHigh:∀v,b.seedHi=some v→seedDegree s.native.poly≤v
  axisLow:b.axisLo≤PadeNativeQuotient.axis s.native.poly 1
  axisHigh:∀v,b.axisHi=some v→PadeNativeQuotient.axis s.native.poly 1≤v
  physical:b.wt≤_root_.Research6970.Height2313.Research6969.NormalGeometry.weight s

theorem caps {i} (s:State i) (b:Row) (h:Facts s b) (z:Geometry s):
    z.onPoly.natDegree≤(b.cap i).grade ∧ K1_14_4.seedDegree z.onPoly≤(b.cap i).seed ∧
      KoalaRect.axisDegree z.onPoly 1≤(b.cap i).axis:=by
  cases height:b.axisHi with
  | none=>
    have bounds:=_root_.Research6970.Height2313.Research6969.NormalGeometry.measured s z b.tests [] b.upperGrade b.graph b.seedLo b.wt b.axisLo
      (PadeNativeQuotient.axis s.native.poly 1) b.seedHi h.gradeHigh h.degree h.seedLow h.seedHigh h.axisLow le_rfl h.physical
    simpa only [Row.cap,height,Option.isSome_none,Bool.false_eq_true,ite_false,Option.getD_none,
      _root_.Research6970.Height2313.Research6969.NormalGeometry.limits,_root_.Research6970.Height2313.Research6969.AxisTests.run,List.isEmpty,ite_true] using bounds
  | some v=>
    have bounds:=_root_.Research6970.Height2313.Research6969.NormalGeometry.measured s z b.tests b.rect b.upperGrade b.graph b.seedLo b.wt b.axisLo v
      b.seedHi h.gradeHigh h.degree h.seedLow h.seedHigh h.axisLow (h.axisHigh v height) h.physical
    simpa only [Row.cap,height,Option.isSome_some,ite_true,Option.getD_some] using bounds

theorem primary_bounds {i} (s:State i) (b:Row) (h:Facts s b) (z:Geometry s):
    z.pairData.main.onEq.natDegree≤b.gm i ∧ K1_14_4.seedDegree z.pairData.main.onEq≤b.vm i ∧
      KoalaRect.axisDegree z.pairData.main.onEq 1≤(b.cap i).axis ∧ z.pairData.main.offEq.natDegree≤b.off := by
  obtain ⟨grade,seedCap,axis⟩:=caps s b h z
  have d:=natDegree_le_of_dvd z.pairData.mainOn_dvd z.onWitness.1.primitive.ne_zero
  have v:=JointOwnership.rescue_caps z.onWitness.1 z.pairData.mainOn_dvd
  have m:=GraphPartition.measured z.pairData.main s.pair.aSrc s.pair.mainActive s.pair.mainOrigin
  have off:=natDegree_le_of_dvd z.pairData.mainOff_dvd z.offProduct.primitive.ne_zero
  refine ⟨le_min (d.trans grade) (((Nat.le_add_right ..).trans (m.1.trans s.pair.mainDegreeCap)).trans_eq s.mainGrade),
    le_min (v.2.1.trans seedCap) ((Nat.le_add_right ..).trans (m.2.trans s.pair.boundsM)),(v.2.2 1).trans axis,?_⟩
  have bound:=z.offCap
  rw [h.control,h.degree] at bound
  exact off.trans bound

theorem distinct_total {i} (s:State i) (b:Row) (h:Facts s b) (z:Geometry s)
    (different:GraphIntersection.determinant (nativeHelper s) s.native≠0):
    z.pairData.rescueFull.natDegree≤b.off+b.cross ∧ s.f.natDegree≤z.pairData.main.onEq.natDegree+b.off+b.cross := by
  have d0:=_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_degree s
  have pos:0<s.graph.graphDegree:=by unfold Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  have d1:=(SharedGraphCount.degrees (nativeHelper s) s.native (PhysicalHelperTariff.primitive s.prime s.slope) s.gp
    (by omega) pos (_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_cap s) ((K1_14_2_2_2_1.seedDegree_le s.native.poly _).mp le_rfl)).1
  rw [d0,h.degree] at d1
  have off:=z.offCap
  rw [h.control,h.degree] at off
  obtain ⟨r,total⟩:=PairedComparison.distinct s.pair (nativeHelper s) s.native z.pairData s.product z.offProduct
    (PhysicalHelperTariff.primitive s.prime s.slope) s.gp rfl different d1 off
  exact ⟨r,total⟩

theorem distinct_bounds {i} (s:State i) (b:Row) (h:Facts s b) (z:Geometry s)
    (different:GraphIntersection.determinant (nativeHelper s) s.native≠0):
    z.pairData.rescueFull.natDegree≤b.off+b.cross ∧ b.loPrimary≤z.pairData.main.onEq.natDegree := by
  obtain ⟨rcap,all⟩:=distinct_total s b h z different
  have left:=h.gradeLow
  exact ⟨rcap,by unfold Row.loPrimary;omega⟩

end
end Research6970.Height2313.Research6969.PairCell
end Z6969Source2550

-- Source: Research6969.OnTariffHeader
section Z6969Source2551
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

def Legal (how:Mode) (a:ℕ) (height narrow:Option ℕ) (grade mainSeed last cutoff:ℕ):Prop:=
  match how with
  | .marked=>grade<64 ∧ (2*grade-1)*mainSeed<p
  | .markedAxis=>grade<64 ∧ (2*grade-1)*mainSeed<p
  | .affine=>a=1 ∧ height.isSome=true ∧ max 1 (height.getD 0)<p
  | .surface=>2≤a ∧ height.isSome=true ∧ (2*a-1)*(height.getD 0)<p
  | .ambient=>2≤a ∧ height.isSome=true ∧ (2*a-1)*(height.getD 0)<p
  | .separate=>2≤a ∧ height.isSome=true ∧ narrow.isSome=true ∧ (2*a-1)*(height.getD 0)<p
  | .node fee=>a=2 ∧ height.isSome=true ∧ 3*height.getD 0<p ∧ NodeBudget.Valid last (height.getD 0) cutoff fee

instance (how a h s g v last w):Decidable (Legal how a h s g v last w):=by
  cases how <;>unfold Legal <;>infer_instance

def NodeGuard (how:Mode) (act cutoff:ℕ):Prop:=match how with | .node _=>act<cutoff | _=>True

theorem selected {u:Option ℕ} (yes:u.isSome=true):u=some (u.getD 0):=by
  cases u <;> simp_all

theorem degree_bound {h:ℤ} (bound:h.toNat≤2313):131071+h≤(133384:ℤ):=by omega

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2551

-- Source: Research6969.PairPrices
section Z6969Source2552
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.PairPrices
open _root_.Research6969
open K1 (p)
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.BookView (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open PriceMethod (Mode Rate)
open Finset
set_option maxHeartbeats 1300000
set_option maxRecDepth 12500

inductive Rescue where | whole | intersection
deriving DecidableEq
inductive Same where | impossible | marked | surface | node (allowance:ℕ)
deriving DecidableEq

structure Decision where
  main:Mode
  rescue:Rescue
  same:Same
  cutoff:ℕ

abbrev d:ℕ:=133384
def sx (i:Fin 18):=FastHeight.side d (seed i)
def sy:=FastHeight.ordinate d 1
def modeNode:Mode→Bool | .node _=>true | _=>false
def primaryRate (b:Row) (i:Fin 18) (p:Decision):Rate:=
  PriceMethod.rates p.main d b.graph (b.seedHi.getD 0) (b.axisHi.getD 0) (b.gm i) (mainBook i).seedMass

def primaryCharge (b:Row) (i:Fin 18) (p:Decision):ℤ:=
  let t:=primaryRate b i p
  GraphLedger.excess (mainBook i) (savedMainGrade i) b.off b.loPrimary (b.gm i) (b.vm i) (b.cap i).axis
    ((savedMainGrade i)^2+t.cash:ℕ) t.y t.seed t.axis

def crossCharge (b:Row) (i:Fin 18):ℕ:=b.cross*(sx i)^2+2*(seed i+b.seedHi.getD 0)*sx i*sy

def rescueCharge (b:Row) (i:Fin 18) (p:Decision):ℕ:=
  match p.rescue with
  | .whole=>RescuePrice.ticket (rescueBook i) (b.off+b.cross) (sx i) sy
  | .intersection=>RescuePrice.ticket (rescueBook i) b.off (sx i) sy+
      if modeNode p.main then 0 else crossCharge b i

def distinctOK (b:Row) (i:Fin 18) (p:Decision):Prop:=
  savedMainGrade i<b.loPrimary ∨
  (_root_.Research6970.Height2313.Research6969.OnTariff.Legal p.main b.graph b.seedHi b.axisHi (b.gm i) (mainBook i).seedMass 2313 p.cutoff ∧
    (match p.rescue with | .whole=>True | .intersection=>modeNode p.main=true ∨ b.seedHi.isSome=true) ∧
    ((mainBook i).fee:ℤ)+(rescueBook i).fee+primaryCharge b i p+rescueCharge b i p≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target)

def impossible (b:Row) (i:Fin 18):Prop:=
  b.graph≠2 ∨ seed i<b.seedLo ∨ (match b.seedHi with | none=>False | some v=>v<seed i) ∨
    savedRescueGrade i<b.lowerGrade-b.off

def sameOK (b:Row) (i:Fin 18) (p:Decision):Prop:=
  let pay:=SameCore.due (mainBook i) (rescueBook i) b.off b.lowerGrade (b.gr i) (b.vr i)
  match p.same with
  | .impossible=>impossible b i
  | .marked=>(b.gr i)<64 ∧ (2*b.gr i-1)*b.vr i<K1.p ∧
      pay (ThreeLedger.tail (b.gr i)) 0 (JointLedger.coefficient (b.gr i))≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target
  | .surface=>pay 0 ((sx i)^2:ℕ) (2*sx i*sy:ℕ)≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target
  | .node fee=>b.graph=2 ∧ b.seedHi.isSome=true ∧ 3*b.seedHi.getD 0<K1.p ∧ NodeBudget.Valid 2313 (b.seedHi.getD 0) p.cutoff fee ∧
      pay fee 0 0≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target

def valid (b:Row) (i:Fin 18) (p:Decision):Prop:=
  b.content<b.lowerGrade ∧ 3≤savedMainGrade i ∧ b.off+b.cross<64 ∧ (2*b.off-1)*(mainBook i).seedMass<K1.p ∧
  (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<K1.p ∧ distinctOK b i p ∧ sameOK b i p

instance (b:Row) (i:Fin 18):Decidable (impossible b i):=by unfold impossible;cases b.seedHi <;>infer_instance
instance (b:Row) (i:Fin 18) (p:Decision):Decidable (distinctOK b i p):=by unfold distinctOK;cases p.rescue <;>infer_instance
instance (b:Row) (i:Fin 18) (p:Decision):Decidable (sameOK b i p):=by unfold sameOK;cases p.same <;>infer_instance
instance (b:Row) (i:Fin 18) (p:Decision):Decidable (valid b i p):=by unfold valid;infer_instance
end Research6970.Height2313.Research6969.PairPrices
end Z6969Source2552

-- Source: Research6969.PairRoute
section Z6969Source2553
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.PairRoute
open _root_.Research6969
noncomputable section
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open OrdinaryRoute (Region)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open scoped Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 9000

structure Window where
  region:Region
  axisLo:ℕ
  axisHi:Option ℕ
  weightLo:ℕ
  weightHi:Option ℕ
deriving DecidableEq

def of_row (b:Row) (wh:Option ℕ):Window:=
  ⟨⟨b.lowerGrade,b.upperGrade,b.content,b.graph,b.seedLo,b.seedHi⟩,b.axisLo,b.axisHi,b.wt,wh⟩

structure Applies {i} (s:State i) (w:Window):Prop where
  root:_root_.Research6970.Height2313.Research6969.NormalRoute.Applies s w.region
  al:w.axisLo≤Research6966.PadeNativeQuotient.axis s.native.poly 1
  ah:∀n,w.axisHi=some n→Research6966.PadeNativeQuotient.axis s.native.poly 1≤n
  wl:w.weightLo≤_root_.Research6970.Height2313.Research6969.NormalGeometry.weight s
  wh:∀n,w.weightHi=some n→_root_.Research6970.Height2313.Research6969.NormalGeometry.weight s<n

abbrev Done (i:Fin 18) (w:Window):Prop:=∀s:State i,Applies s w→s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target

theorem facts {i} {s:State i} {b:Row} {w:Option ℕ} (h:Applies s (of_row b w)):_root_.Research6970.Height2313.Research6969.PairCell.Facts s b :=
  ⟨h.root.1,h.root.2.1,h.root.2.2.1,h.root.2.2.2.1,h.root.2.2.2.2.1,h.root.2.2.2.2.2,h.al,h.ah,h.wl⟩

theorem weight {i r l u low high} (cut:ℕ)
    (left:Done i ⟨r,l,u,low,some cut⟩) (right:Done i ⟨r,l,u,cut,high⟩):
    Done i ⟨r,l,u,low,high⟩:=by
  intro s h
  by_cases below:_root_.Research6970.Height2313.Research6969.NormalGeometry.weight s<cut
  · exact left s ⟨h.root,h.al,h.ah,h.wl,fun v eq=>by
      have same:cut=v:=Option.some.inj eq;simpa [←same] using below⟩
  · exact right s ⟨h.root,h.al,h.ah,Nat.le_of_not_lt below,h.wh⟩

theorem axis {i r lo hi w high} (cut:ℕ)
    (left:Done i ⟨r,lo,some cut,w,high⟩) (right:Done i ⟨r,cut+1,hi,w,high⟩):
    Done i ⟨r,lo,hi,w,high⟩:=by
  intro s h
  by_cases below:Research6966.PadeNativeQuotient.axis s.native.poly 1≤cut
  · exact left s ⟨h.root,h.al,fun v eq=>by
      have same:cut=v:=Option.some.inj eq;simpa [←same] using below,h.wl,h.wh⟩
  · exact right s ⟨h.root,by change cut+1≤_;omega,h.ah,h.wl,h.wh⟩

theorem axes_of_total {i e top c a lo hi wt high}
    (all:Done i ⟨⟨e,top,c,a,lo,some hi⟩,0,some hi,wt,high⟩):
    Done i ⟨⟨e,top,c,a,lo,some hi⟩,0,none,wt,high⟩:=by
  intro s h
  have seed:=h.root.2.2.2.2.2 hi rfl
  have axis:Research6966.PadeNativeQuotient.axis s.native.poly 1≤hi:=
    (Research6966.NearTerminal.axis_seed s.native.poly 1).trans seed
  exact all s ⟨h.root,h.al,fun v eq=>by have same:hi=v:=Option.some.inj eq;simpa [←same] using axis,h.wl,h.wh⟩

theorem grade {i e top c a sl su l u w wh} (mid:ℕ)
    (left:Done i ⟨⟨e,mid,c,a,sl,su⟩,l,u,w,wh⟩)
    (right:Done i ⟨⟨mid+1,top,c,a,sl,su⟩,l,u,w,wh⟩) :
    Done i ⟨⟨e,top,c,a,sl,su⟩,l,u,w,wh⟩:=by
  intro s h
  obtain ⟨gl,gh,ct,d,low,up⟩:=h.root
  by_cases lower:s.f.natDegree≤mid
  · exact left s ⟨⟨gl,lower,ct,d,low,up⟩,h.al,h.ah,h.wl,h.wh⟩
  · exact right s ⟨⟨by change mid+1≤_;omega,gh,ct,d,low,up⟩,h.al,h.ah,h.wl,h.wh⟩

theorem splitSeed {i e top c a lo hi l u w wh} (cut:ℕ)
    (left:Done i ⟨⟨e,top,c,a,lo,some cut⟩,l,u,w,wh⟩)
    (right:Done i ⟨⟨e,top,c,a,cut+1,some hi⟩,l,u,w,wh⟩) :
    Done i ⟨⟨e,top,c,a,lo,some hi⟩,l,u,w,wh⟩:=by
  intro s h
  obtain ⟨gl,gh,ct,d,low,up⟩:=h.root
  by_cases lower:K1_14_2_2_2_1.seedDegree s.native.poly≤cut
  · exact left s ⟨⟨gl,gh,ct,d,low,fun v eq=>by
      have same:cut=v:=Option.some.inj eq
      simpa [←same] using lower⟩,h.al,h.ah,h.wl,h.wh⟩
  · exact right s ⟨⟨gl,gh,ct,d,by change cut+1≤_;omega,up⟩,h.al,h.ah,h.wl,h.wh⟩

theorem start {i} (r:Region) (all:Done i ⟨r,0,none,r.graph*(131071-2411)-1,none⟩):_root_.Research6970.Height2313.Research6969.NormalRoute.Done i r:=by
  intro s h
  have degree:=h.2.2.2.1
  have mono : r.graph*(131071-2411)-1 ≤ r.graph*(131071-2313)-1 := by omega
  exact all s ⟨h,Nat.zero_le _,by simp,mono.trans (degree ▸ _root_.Research6970.Height2313.Research6969.NormalGeometry.base s),by simp⟩

end
end Research6970.Height2313.Research6969.PairRoute
end Z6969Source2553

-- Source: Research6969.OnTariffMarked
section Z6969Source2554
set_option autoImplicit true
set_option Elab.async false
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem marked_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .marked G.graphDegree width axis grade v 2313 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodeGuard:NodeGuard .marked (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .marked 133384 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  exact (PriceMethod.marked F sub (hi.trans (by decide)) prim sep legal.1 limit seed legal.2 roots
    133384 G.graphDegree (width.getD 0) (axis.getD 0)).1

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2554

-- Source: Research6969.OnTariffMarkedAxis
section Z6969Source2555
set_option autoImplicit true
set_option Elab.async false
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem markedAxis_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .markedAxis G.graphDegree width axis grade v 2313 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodeGuard:NodeGuard .markedAxis (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .markedAxis 133384 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  exact (PriceMethod.marked F sub (hi.trans (by decide)) prim sep legal.1 limit seed legal.2 roots
    133384 G.graphDegree (width.getD 0) (axis.getD 0)).2

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2555

-- Source: Research6969.OnTariffAffine
section Z6969Source2556
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 100000
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

attribute [local irreducible] WholeAffine.fee FastHeight.side FastHeight.ordinate
private theorem affine_pay (d a w x g u:ℕ) (f:Equation):
    (PriceMethod.rates .affine d a w x g u).pay f=WholeAffine.fee d (max 1 w):=by
  simp only [PriceMethod.rates,PriceMethod.Rate.pay,Nat.zero_mul,Nat.add_zero]

set_option maxHeartbeats 100000
theorem affine_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .affine G.graphDegree width axis grade v 2313 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodeGuard:NodeGuard .affine (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .affine 133384 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  rw [affine_pay]
  obtain ⟨linear,present,small⟩:=legal
  have member:T⊆UnionTariffs.group F N parents:=by
    intro z hz
    obtain ⟨q,hq,contains,vanishes⟩:=owners z hz
    exact Finset.mem_filter.mpr ⟨sub hz,q,Finset.mem_filter.mpr ⟨hq,contains⟩,vanishes⟩
  have widthCap:K1_14_2_2_2_1.seedDegree N.poly≤max 1 (width.getD 0):=
    (trueWidth _ (selected present)).trans (le_max_right ..)
  exact (Finset.card_le_card member).trans (UnionTariffs.affine (d:=133384) (w:=max 1 (width.getD 0))
    F N parents gp linear (Nat.zero_lt_one.trans_le (le_max_left ..)) small widthCap (degree_bound hi)
    (by decide:0<133384) (by decide:133384<179730) (by decide:133384<K1.p))

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2556

-- Source: Research6969.OnTariffSurface
section Z6969Source2557
set_option autoImplicit true
set_option Elab.async false
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem surface_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .surface G.graphDegree width axis grade v 2313 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodeGuard:NodeGuard .surface (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .surface 133384 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  classical
  let d:=133384
  have ph:131071+M.overhead≤(d:ℤ):=degree_bound hi
  have dp:0<d:=by decide
  have gap:d<179730:=by decide
  have tame:d<p:=by decide
  have age:0<M.overhead.toNat:=(by decide:0<2308).trans_le lo
  have bounds (yes:width.isSome=true):∀j k,((N.poly.coeff j).coeff k).totalDegree≤width.getD 0:=
    (K1_14_2_2_2_1.seedDegree_le N.poly (width.getD 0)).mp (trueWidth _ (selected yes))
  have laws z (hz:z∈T):WordRates.law F N z:=by
    obtain ⟨q,_,owned,atQ⟩:=owners z hz;exact NativeGraphMarks.mark_law N gp owned atQ
  have on z (hz:z∈T):WordRates.ev F z f=0:=by
    have root:=roots z hz
    rw [Polynomial.eval_map] at root
    exact root
  obtain ⟨big,yes,char⟩:=legal
  have pay:=WordRates.on_surface F N gp big (bounds yes) char sub ph dp gap tame prim.ne_zero laws on
  rw [FastHeight.side_eq,FastHeight.ordinate_eq d _ gap] at pay
  exact pay.trans_eq (by simp [PriceMethod.rates,PriceMethod.Rate.pay,d];ring)

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2557

-- Source: Research6969.OnTariffAmbient
section Z6969Source2558
set_option autoImplicit true
set_option Elab.async false
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem ambient_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .ambient G.graphDegree width axis grade v 2313 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodeGuard:NodeGuard .ambient (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .ambient 133384 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  classical
  let d:=133384
  have ph:131071+M.overhead≤(d:ℤ):=degree_bound hi
  have dp:0<d:=by decide
  have gap:d<179730:=by decide
  have tame:d<p:=by decide
  have age:0<M.overhead.toNat:=(by decide:0<2308).trans_le lo
  have bounds (yes:width.isSome=true):∀j k,((N.poly.coeff j).coeff k).totalDegree≤width.getD 0:=
    (K1_14_2_2_2_1.seedDegree_le N.poly (width.getD 0)).mp (trueWidth _ (selected yes))
  have laws z (hz:z∈T):WordRates.law F N z:=by
    obtain ⟨q,_,owned,atQ⟩:=owners z hz;exact NativeGraphMarks.mark_law N gp owned atQ
  obtain ⟨big,yes,char⟩:=legal
  have pay:=WordRates.ambient F N gp big (bounds yes) char sub ph dp gap tame laws
  rw [FastHeight.side_eq,FastHeight.ordinate_eq d _ gap] at pay
  simpa [PriceMethod.rates,PriceMethod.Rate.pay,d] using pay

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2558

-- Source: Research6969.OnTariffSeparate
section Z6969Source2559
set_option autoImplicit true
set_option Elab.async false
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem separate_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .separate G.graphDegree width axis grade v 2313 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodeGuard:NodeGuard .separate (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .separate 133384 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  classical
  let d:=133384
  have ph:131071+M.overhead≤(d:ℤ):=degree_bound hi
  have dp:0<d:=by decide
  have gap:d<179730:=by decide
  have tame:d<p:=by decide
  have age:0<M.overhead.toNat:=(by decide:0<2308).trans_le lo
  have bounds (yes:width.isSome=true):∀j k,((N.poly.coeff j).coeff k).totalDegree≤width.getD 0:=
    (K1_14_2_2_2_1.seedDegree_le N.poly (width.getD 0)).mp (trueWidth _ (selected yes))
  have laws z (hz:z∈T):WordRates.law F N z:=by
    obtain ⟨q,_,owned,atQ⟩:=owners z hz;exact NativeGraphMarks.mark_law N gp owned atQ
  have on z (hz:z∈T):WordRates.ev F z f=0:=by
    have root:=roots z hz
    rw [Polynomial.eval_map] at root
    exact root
  obtain ⟨big,yes,thin,char⟩:=legal
  have point:=trueAxis (axis.getD 0) (selected thin)
  have one:∀j k,((N.poly.coeff j).coeff k).degreeOf 1≤axis.getD 0:=(PadeNativeQuotient.axis_le ..).mp point
  exact (PriceMethod.nonlinear F sub N gp big char (bounds yes) one ph dp gap tame prim.ne_zero laws on grade v).2.1

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2559

-- Source: Research6969.OnTariffNode
section Z6969Source2560
set_option autoImplicit true
set_option Elab.async false
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem node_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ) (fee:ℕ) (legal:Legal (.node fee) G.graphDegree width axis grade v 2313 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodeGuard:NodeGuard (.node fee) (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates (.node fee) 133384 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  classical
  let d:=133384
  have ph:131071+M.overhead≤(d:ℤ):=degree_bound hi
  have dp:0<d:=by decide
  have gap:d<179730:=by decide
  have tame:d<p:=by decide
  have age:0<M.overhead.toNat:=(by decide:0<2308).trans_le lo
  have bounds (yes:width.isSome=true):∀j k,((N.poly.coeff j).coeff k).totalDegree≤width.getD 0:=
    (K1_14_2_2_2_1.seedDegree_le N.poly (width.getD 0)).mp (trueWidth _ (selected yes))
  obtain ⟨q,yes,char,ok⟩:=legal
  have pay:=NodeBudget.family F sub rfl age hi (by decide) phys (OrdinaryCell.native_prime N gp) (NativeGraphMarks.slope_degree N gp)
    ((HelperWeightCap.native_degree N gp).trans q) char (bounds yes) nodes res
    (fun z hz=>by obtain ⟨q,_,hit,mark⟩:=owners z hz;exact mark _ hit) nodeGuard ok
  simpa only [PriceMethod.rates,PriceMethod.Rate.pay,Nat.zero_mul,Nat.add_zero] using pay

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2560

-- Source: Research6969.OnTariff
section Z6969Source2561
set_option autoImplicit true
set_option Elab.async false
namespace Research6970.Height2313.Research6969.OnTariff
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem on_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ) (how:Mode) (legal:Legal how G.graphDegree width axis grade v 2313 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    (nodeGuard:NodeGuard how (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates how 133384 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  cases how with
  | marked=>exact marked_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | markedAxis=>exact markedAxis_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | affine=>exact affine_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | surface=>exact surface_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | ambient=>exact ambient_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | separate=>exact separate_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | node fee=>exact node_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis fee legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res

end
end Research6970.Height2313.Research6969.OnTariff
end Z6969Source2561

-- Source: Research6969.DistinctPaymentCharges
section Z6969Source2562
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.DistinctPaymentCharges
open _root_.Research6969
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open _root_.Research6970.Height2313.Research6969.BookView (rescueBook)
set_option Elab.async false
set_option maxRecDepth 2000
attribute [local irreducible] RescuePrice.ticket _root_.Research6970.Height2313.Research6969.PairPrices.sx _root_.Research6970.Height2313.Research6969.PairPrices.sy
  _root_.Research6970.Height2313.Research6969.PairPrices.crossCharge TransitionPacket.NormalCatalogue.rescueBook

theorem nodeCharge {b : Row} {i : Fin 18} {p₀ : Decision}
    (mode : p₀.rescue = .intersection) (node : _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p₀.main = true) :
    _root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀ =
      RescuePrice.ticket (rescueBook i) b.off (_root_.Research6970.Height2313.Research6969.PairPrices.sx i) _root_.Research6970.Height2313.Research6969.PairPrices.sy := by
  unfold _root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge
  rw [mode]
  change _ + (if _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p₀.main=true then 0 else _root_.Research6970.Height2313.Research6969.PairPrices.crossCharge b i) = _
  rw [if_pos node, Nat.add_zero]


theorem graphCharge {b : Row} {i : Fin 18} {p₀ : Decision}
    (mode : p₀.rescue = .intersection) (node : ¬ _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p₀.main = true) :
    _root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀ =
      RescuePrice.ticket (rescueBook i) b.off (_root_.Research6970.Height2313.Research6969.PairPrices.sx i) _root_.Research6970.Height2313.Research6969.PairPrices.sy+_root_.Research6970.Height2313.Research6969.PairPrices.crossCharge b i := by
  unfold _root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge
  rw [mode]
  change _ + (if _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p₀.main=true then 0 else _root_.Research6970.Height2313.Research6969.PairPrices.crossCharge b i) = _
  rw [if_neg node]

end Research6970.Height2313.Research6969.DistinctPaymentCharges
end Z6969Source2562

-- Source: Research6969.DistinctPaymentRescueCore
section Z6969Source2563
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.DistinctPaymentRescue
open _root_.Research6969
noncomputable section

open K1 (p)
open Research6966
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry nativeHelper)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open _root_.Research6970.Height2313.Research6969.BookView (rescueBook seed)
open PairedMarks (rescueLabels)
open Polynomial
open scoped Classical

set_option Elab.async false
set_option maxRecDepth 13000
set_option maxHeartbeats 2500000
attribute [local irreducible] FastHeight.side FastHeight.ordinate RescuePrice.ticket
  TransitionPacket.NormalCatalogue.rescueBook

private theorem wholeCharge {b : Row} {i : Fin 18} {p₀ : Decision}
    (mode : p₀.rescue = .whole) :
    _root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀ =
      RescuePrice.ticket (rescueBook i) (b.off+b.cross) (_root_.Research6970.Height2313.Research6969.PairPrices.sx i) _root_.Research6970.Height2313.Research6969.PairPrices.sy := by
  rw [_root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge, mode]

theorem whole {i} (s : State i) (b : Row) (z : Geometry s) (p₀ : Decision)
    (mode : p₀.rescue = .whole) (cap : z.pairData.rescueFull.natDegree≤b.off+b.cross)
    (small : b.off+b.cross<64)
    (safe : (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p) :
    (rescueLabels s.pair).card≤(rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree+
      (rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull+_root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀ := by
  have degree := _root_.Research6970.Height2313.Research6969.NormalGeometry.helper_degree s
  have pos : 0<seed i := Nat.zero_lt_succ _
  have result := RescueComparison.full s.pair (nativeHelper s) s.native z.pairData
    (PhysicalHelperTariff.primitive s.prime s.slope) rfl degree.ge pos (_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_cap s)
    (_root_.Research6970.Height2313.Research6969.OnTariff.degree_bound s.higher) (by decide) (by decide) (by decide)
    (s.higher.trans (by decide)) cap small safe
  rw [degree,FastHeight.side_eq,FastHeight.ordinate_eq 133384 _ (by decide)] at result
  rw [wholeCharge mode]
  exact result

theorem outside {i} (s : State i) (b : Row) (h : _root_.Research6970.Height2313.Research6969.PairCell.Facts s b) (z : Geometry s)
    (small : b.off+b.cross<64)
    (safe : (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p) :
    z.pairData.rescue.offLabels.card≤(rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree+
      (rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull+
        RescuePrice.ticket (rescueBook i) b.off (_root_.Research6970.Height2313.Research6969.PairPrices.sx i) _root_.Research6970.Height2313.Research6969.PairPrices.sy := by
  have offRes : z.pairData.rescue.offEq.natDegree≤b.off :=
    (natDegree_le_of_dvd z.pairData.rescueOff_dvd z.offProduct.primitive.ne_zero).trans (by
      have no:=z.offCap;rw [h.control,h.degree] at no;exact no)
  have le : b.off≤b.off+b.cross := Nat.le_add_right _ _
  have sR : (2*b.off-1)*(rescueBook i).seedMass<p :=
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 le) _)).trans_lt safe
  have degree := _root_.Research6970.Height2313.Research6969.NormalGeometry.helper_degree s
  have pos : 0<seed i := Nat.zero_lt_succ _
  have result := RescueComparison.outside s.pair (nativeHelper s) s.native z.pairData
    (PhysicalHelperTariff.primitive s.prime s.slope) rfl degree.ge pos (_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_cap s)
    (_root_.Research6970.Height2313.Research6969.OnTariff.degree_bound s.higher) (by decide) (by decide) (by decide)
    (s.higher.trans (by decide)) offRes (le.trans_lt small) sR
  rw [degree,FastHeight.side_eq,FastHeight.ordinate_eq 133384 _ (by decide)] at result
  exact result


end
end Research6970.Height2313.Research6969.DistinctPaymentRescue
end Z6969Source2563

-- Source: Research6969.DistinctPaymentRescue
section Z6969Source2564
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.DistinctPaymentRescue
open _root_.Research6969
noncomputable section

open K1 (p)
open Research6966
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry nativeHelper)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open _root_.Research6970.Height2313.Research6969.BookView (rescueBook seed)
open PairedMarks (rescueLabels)
open Polynomial
open scoped Classical

set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
attribute [local irreducible] FastHeight.side FastHeight.ordinate RescuePrice.ticket
  TransitionPacket.NormalCatalogue.rescueBook

private theorem node_rescue_count (n a b x y ticket cost : ℕ) (split : a+b=n)
    (off : b≤x+y+ticket) (eq : cost=ticket) : n≤a+x+y+cost := by omega

theorem node_rescue {i} (s : State i) (b : Row) (h : _root_.Research6970.Height2313.Research6969.PairCell.Facts s b) (z : Geometry s)
    (p₀ : Decision) (mode : p₀.rescue = .intersection) (node : _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p₀.main = true)
    (small : b.off+b.cross<64) (safe : (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p) :
    (rescueLabels s.pair).card≤z.pairData.rescue.onLabels.card+
      (rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree+
      (rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull+_root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀ := by
  have cost := _root_.Research6970.Height2313.Research6969.DistinctPaymentCharges.nodeCharge (b:=b) (i:=i) mode node
  exact node_rescue_count
    (rescueLabels s.pair).card z.pairData.rescue.onLabels.card z.pairData.rescue.offLabels.card
    ((rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree)
    ((rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull)
    (RescuePrice.ticket (rescueBook i) b.off (_root_.Research6970.Height2313.Research6969.PairPrices.sx i) _root_.Research6970.Height2313.Research6969.PairPrices.sy)
    (_root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀) z.pairData.rescue.size (outside s b h z small safe) cost


end
end Research6970.Height2313.Research6969.DistinctPaymentRescue
end Z6969Source2564

-- Source: Research6969.DistinctPaymentIntersection
section Z6969Source2565
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.DistinctPaymentRescue
open _root_.Research6969
noncomputable section

open K1 (p)
open Research6966
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry nativeHelper)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open _root_.Research6970.Height2313.Research6969.BookView (rescueBook seed)
open PairedMarks (rescueLabels)
open Polynomial
open scoped Classical

set_option Elab.async false
set_option maxRecDepth 13000
set_option maxHeartbeats 2500000
attribute [local irreducible] FastHeight.side FastHeight.ordinate RescuePrice.ticket
  TransitionPacket.NormalCatalogue.rescueBook

private theorem graph_rescue_count (n a b x y ticket cross cost : ℕ) (split : a+b=n)
    (off : b≤x+y+ticket) (on : a≤cross) (eq : cost=ticket+cross) : n≤x+y+cost := by omega

theorem graph_rescue {i} (s : State i) (b : Row) (h : _root_.Research6970.Height2313.Research6969.PairCell.Facts s b) (z : Geometry s)
    (p₀ : Decision) (mode : p₀.rescue = .intersection) (node : ¬ _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p₀.main = true)
    (different : GraphIntersection.determinant (nativeHelper s) s.native≠0) (given : b.seedHi.isSome=true)
    (small : b.off+b.cross<64) (safe : (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p) :
    (rescueLabels s.pair).card≤(rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree+
      (rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull+_root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀ := by
  have bound:=(K1_14_2_2_2_1.seedDegree_le ..).mp (h.seedHigh _ (_root_.Research6970.Height2313.Research6969.OnTariff.selected given))
  have positive:0<s.graph.graphDegree:=by
    unfold Pade.Row.graphDegree
    exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  have degree := _root_.Research6970.Height2313.Research6969.NormalGeometry.helper_degree s
  have pos : 0<seed i := Nat.zero_lt_succ _
  have inter:=RescueComparison.intersection s.pair (nativeHelper s) s.native z.pairData
    (PhysicalHelperTariff.primitive s.prime s.slope) s.gp rfl degree.ge positive pos
    (_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_cap s) bound different (_root_.Research6970.Height2313.Research6969.OnTariff.degree_bound s.higher)
    (by decide) (by decide) (by decide)
  rw [degree,h.degree,FastHeight.side_eq,FastHeight.ordinate_eq 133384 _ (by decide)] at inter
  have cross : z.pairData.rescue.onLabels.card≤_root_.Research6970.Height2313.Research6969.PairPrices.crossCharge b i := by
    rw [_root_.Research6970.Height2313.Research6969.PairPrices.crossCharge,_root_.Research6970.Height2313.Research6969.PairCell.Row.cross,_root_.Research6970.Height2313.Research6969.PairPrices.sx,_root_.Research6970.Height2313.Research6969.PairPrices.sy]
    exact inter
  have cost := _root_.Research6970.Height2313.Research6969.DistinctPaymentCharges.graphCharge (b:=b) (i:=i) mode node
  exact graph_rescue_count
    (rescueLabels s.pair).card z.pairData.rescue.onLabels.card z.pairData.rescue.offLabels.card
    ((rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree)
    ((rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull)
    (RescuePrice.ticket (rescueBook i) b.off (_root_.Research6970.Height2313.Research6969.PairPrices.sx i) _root_.Research6970.Height2313.Research6969.PairPrices.sy)
    (_root_.Research6970.Height2313.Research6969.PairPrices.crossCharge b i) (_root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀)
    z.pairData.rescue.size (outside s b h z small safe) cross cost


end
end Research6970.Height2313.Research6969.DistinctPaymentRescue
end Z6969Source2565

-- Source: Research6969.DistinctPaymentNode
section Z6969Source2566
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.DistinctPaymentNode
open _root_.Research6969
noncomputable section
open K1_14 (jetAt)
open Research6966
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open _root_.Research6970.Height2313.Research6969.BookView (mainBook)
open Finset
open scoped Classical

set_option Elab.async false
set_option maxHeartbeats 2500000
set_option maxRecDepth 13000
attribute [local irreducible] TransitionPacket.NormalCatalogue.mainBook

private theorem node_mode (m : PriceMethod.Mode) (h : _root_.Research6970.Height2313.Research6969.PairPrices.modeNode m = true) :
    ∃ fee, m = .node fee := by
  cases m <;> cases h; exact ⟨_,rfl⟩


theorem pays {i} (s : State i) (b : Row) (h : _root_.Research6970.Height2313.Research6969.PairCell.Facts s b) (z : Geometry s) (p₀ : Decision)
    (node : _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p₀.main = true)
    (legal : _root_.Research6970.Height2313.Research6969.OnTariff.Legal p₀.main b.graph b.seedHi b.axisHi (b.gm i) (mainBook i).seedMass 2313 p₀.cutoff)
    (nodeGuard : _root_.Research6970.Height2313.Research6969.OnTariff.NodeGuard p₀.main (_root_.Research6970.Height2313.Research6969.NormalGeometry.weight s) p₀.cutoff) :
    z.pairData.main.onLabels.card+z.pairData.rescue.onLabels.card≤
      (_root_.Research6970.Height2313.Research6969.PairPrices.primaryRate b i p₀).pay z.pairData.main.onEq := by
  let C := z.pairData
  obtain ⟨fee,which⟩ := node_mode p₀.main node
  rw [which] at legal nodeGuard
  obtain ⟨q,yes,char,ok⟩:=legal
  let U:=C.main.onLabels∪C.rescue.onLabels
  have sub:U⊆s.labels:=by
    intro y hy
    exact (mem_union.mp hy).elim (fun l=>PairedMarks.main_sub s.pair (C.main.onSub l))
      (fun r=>PairedMarks.rescue_sub s.pair (C.rescue.onSub r))
  have hit y (hy:y∈U):jetAt s.native.poly (s.model.label y) (s.F.scalar y)=0:=by
    rcases mem_union.mp hy with m|r
    · obtain ⟨q,hq,atQ⟩:=C.main.onMarks y m;exact atQ s.native.poly (mem_filter.mp hq).2
    · obtain ⟨q,hq,atQ⟩:=C.rescue.onMarks y r;exact atQ s.native.poly (mem_filter.mp hq).2
  have count:=NodeBudget.family s.F sub rfl ((by decide:0<2308).trans_le s.lower) s.higher (by decide)
    s.physical (OrdinaryCell.native_prime s.native s.gp) (NativeGraphMarks.slope_degree s.native s.gp)
    ((HelperWeightCap.native_degree s.native s.gp).trans (h.degree.trans q)) char
    ((K1_14_2_2_2_1.seedDegree_le ..).mp (h.seedHigh _ (_root_.Research6970.Height2313.Research6969.OnTariff.selected yes)))
    s.nodes (fun y hy=>s.residues y (sub hy)) hit nodeGuard ok
  have dis:Disjoint C.main.onLabels C.rescue.onLabels:=Finset.disjoint_left.mpr (fun y hm hr=>
    (PairedMarks.main s.pair (C.main.onSub hm)).1 (PairedMarks.rescue s.pair (C.rescue.onSub hr)).1)
  change (C.main.onLabels∪C.rescue.onLabels).card≤fee at count
  rw [card_union_of_disjoint dis] at count
  simpa only [_root_.Research6970.Height2313.Research6969.PairPrices.primaryRate,which,PriceMethod.rates,PriceMethod.Rate.pay,Nat.zero_mul,Nat.add_zero] using count

end
end Research6970.Height2313.Research6969.DistinctPaymentNode
end Z6969Source2566

-- Source: Research6969.ConfirmedDistinct
section Z6969Source2567
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.ConfirmedDistinct
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Equation FX atX jetAt)
open K1_14_2_2_2_1 (seedDegree)
open Lower6960.Far6969RescueGeometry (word)
open Research6966
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry helper nativeHelper)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open _root_.Research6970.Height2313.Research6969.BookView (mainBook rescueBook savedMainGrade seed)
open PairedMarks (mainLabels rescueLabels)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 2500000
set_option maxRecDepth 13000
set_option Elab.async false
attribute [local irreducible] GraphLedger.excess FastHeight.side FastHeight.ordinate
  TransitionPacket.NormalCatalogue.mainBook TransitionPacket.NormalCatalogue.rescueBook
  TransitionPacket.NormalCatalogue.savedMainGrade _root_.Research6970.Height2313.Research6969.PairPrices.primaryRate RescuePrice.ticket

theorem proves {i} (s:State i) (b:Row) (h:_root_.Research6970.Height2313.Research6969.PairCell.Facts s b) (z:Geometry s) (p₀:Decision)
    (different:GraphIntersection.determinant (nativeHelper s) s.native≠0) (pay:_root_.Research6970.Height2313.Research6969.PairPrices.distinctOK b i p₀)
    (room:3≤savedMainGrade i) (small:b.off+b.cross<64)
    (safeM:(2*b.off-1)*(mainBook i).seedMass<p) (safeR:(2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p)
    (nodeGuard:_root_.Research6970.Height2313.Research6969.OnTariff.NodeGuard p₀.main (_root_.Research6970.Height2313.Research6969.NormalGeometry.weight s) p₀.cutoff):
    s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target := by
  classical
  let C:=z.pairData
  obtain ⟨rg,lg⟩:=_root_.Research6970.Height2313.Research6969.PairCell.distinct_bounds s b h z different
  obtain ⟨g,v,x,o⟩:=_root_.Research6970.Height2313.Research6969.PairCell.primary_bounds s b h z
  rcases pay with impossible|⟨legal,okay,cash⟩
  · exact (Nat.not_lt_of_ge (lg.trans (g.trans (min_le_right ..))) impossible).elim
  let rate:=_root_.Research6970.Height2313.Research6969.PairPrices.primaryRate b i p₀
  have owner:=OwnedTariffs.owners s.F s.native C.main
  have actualLegal:_root_.Research6970.Height2313.Research6969.OnTariff.Legal p₀.main s.graph.graphDegree b.seedHi b.axisHi (b.gm i) (mainBook i).seedMass 2313 p₀.cutoff:=by
    rw [h.degree];exact legal
  have nativeFee:(C.main.onLabels).card≤rate.pay C.main.onEq:=by
    have counted:=_root_.Research6970.Height2313.Research6969.OnTariff.on_marks s.F (C.main.onSub.trans (PairedMarks.main_sub s.pair)) s.crt s.native s.gp s.physical owner
      C.main.onProduct.primitive C.main.onProduct.separable (GraphPartition.labels_root C.main).1 (b.gm i)
      (mainBook i).seedMass p₀.cutoff b.seedHi b.axisHi p₀.main actualLegal g (v.trans (min_le_right ..))
      h.seedHigh h.axisHigh s.lower s.higher nodeGuard s.nodes
      (fun y hy=>s.residues y (PairedMarks.main_sub s.pair (C.main.onSub hy)))
    rw [h.degree] at counted
    simpa only [rate,_root_.Research6970.Height2313.Research6969.PairPrices.primaryRate] using counted
  have endBound (extra:ℕ) (pays:C.main.onLabels.card+extra≤rate.pay C.main.onEq)
      (res:(rescueLabels s.pair).card≤extra+(rescueBook i).ordinateCredit*C.rescueFull.natDegree+
        (rescueBook i).seedCredit*K1_14_4.seedDegree C.rescueFull+_root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀) :
      s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target:=by
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
      (_root_.Research6970.Height2313.Research6969.PairPrices.rescueCharge b i p₀) res
    rw [s.mainGrade] at bound
    unfold _root_.Research6970.Height2313.Research6969.PairPrices.primaryCharge at cash
    exact Int.ofNat_le.mp (bound.trans cash)
  cases mode:p₀.rescue with
  | whole =>
    refine endBound 0 (by simpa only [Nat.add_zero] using nativeFee) ?_
    rw [Nat.zero_add]
    exact _root_.Research6970.Height2313.Research6969.DistinctPaymentRescue.whole s b z p₀ mode rg small safeR
  | intersection =>
    rw [mode] at okay
    by_cases node : _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p₀.main=true
    · exact endBound C.rescue.onLabels.card (_root_.Research6970.Height2313.Research6969.DistinctPaymentNode.pays s b h z p₀ node legal nodeGuard)
        (_root_.Research6970.Height2313.Research6969.DistinctPaymentRescue.node_rescue s b h z p₀ mode node small safeR)
    · refine endBound 0 (by simpa only [Nat.add_zero] using nativeFee) ?_
      rw [Nat.zero_add]
      exact _root_.Research6970.Height2313.Research6969.DistinctPaymentRescue.graph_rescue s b h z p₀ mode node different
        (okay.resolve_left node) small safeR

end
end Research6970.Height2313.Research6969.ConfirmedDistinct
end Z6969Source2567

-- Source: Research6969.ConfirmedSame
section Z6969Source2568
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.ConfirmedSame
open _root_.Research6969
noncomputable section
open K1 (I p)
open K1_14 (Equation atX jetAt)
open K1_14_2_2_2_1 (seedDegree)
open Lower6960.Far6969RescueGeometry (word)
open Research6966
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry helper nativeHelper)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open _root_.Research6970.Height2313.Research6969.BookView (seed mainBook rescueBook savedMainGrade savedRescueGrade)
open PairedMarks (rescueLabels)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 2200000
set_option maxRecDepth 15000

theorem proves {i} (s:State i) (b:Row) (h:_root_.Research6970.Height2313.Research6969.PairCell.Facts s b) (z:Geometry s) (p₀:Decision)
    (same:GraphIntersection.determinant (nativeHelper s) s.native=0) (pay:_root_.Research6970.Height2313.Research6969.PairPrices.sameOK b i p₀)
    (low:b.off<64) (safe:(2*b.off-1)*(mainBook i).seedMass<p)
    (nodeLow:∀fee,p₀.same=.node fee→_root_.Research6970.Height2313.Research6969.NormalGeometry.weight s<p₀.cutoff):s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target:=by
  classical
  let A:=nativeHelper s
  let C:=z.pairData
  have gp:=PhysicalHelperTariff.primitive s.prime s.slope
  have d0:=_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_degree s
  have original:A.poly=s.H:=rfl
  obtain ⟨mdiv,rdiv,sum⟩:=SameCore.degrees s.pair A s.native C gp s.gp original same s.product z.onWitness.1 z.offProduct
  obtain ⟨gc,sc,_⟩:=_root_.Research6970.Height2313.Research6969.PairCell.caps s b h z
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
  have ph:131071+s.model.overhead≤(133384:ℤ):=_root_.Research6970.Height2313.Research6969.OnTariff.degree_bound s.higher
  cases tag:p₀.same with
  | impossible=>
    rw [_root_.Research6970.Height2313.Research6969.PairPrices.sameOK,tag] at pay
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
    rw [_root_.Research6970.Height2313.Research6969.PairPrices.sameOK,tag] at pay
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
    rw [_root_.Research6970.Height2313.Research6969.PairPrices.sameOK,tag] at pay
    have fit:179730≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
    have sp:0<seed i:=by unfold seed;omega
    have sc:=NativeSurfaceCount.regular_equation s.F (PairedMarks.rescue_sub s.pair) C.rescuePr.primitive.ne_zero A gp d0.ge sp
      (_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_cap s) ((K1_14_4.seedDegree_le_iff ..).mp le_rfl) ph (by decide:0<133384)
      (by decide) fit (by decide) (fun y hy=>(PairedMarks.rescue_law s.pair A gp original hy).1)
      (fun y hy=>by simpa [NonlinearMarkRows.evaluate,NativeSurfaceCount.label,K1_14.graphEval,Polynomial.eval_map] using PairedMarks.native_rescue s.pair C.rescuePr y hy)
      (fun y hy=>(PairedMarks.rescue_law s.pair A gp original hy).2)
    have amount:=NativeSurfaceCount.round_price (bad:=0) (g:=C.rescueFull.natDegree) (v:=K1_14_4.seedDegree C.rescueFull)
      (u:=seed i) (r:=(helper s).graphDegree-1) (d:=133384) (a:=179730) (n:=Fintype.card I) (by simpa using sc)
    change (rescueLabels s.pair).card≤0+C.rescueFull.natDegree*(JointRouted.seedWeight 133384 (seed i))^2+
      2*K1_14_4.seedDegree C.rescueFull*JointRouted.seedWeight 133384 (seed i)*JointRouted.ordWeight 133384 ((helper s).graphDegree-1) at amount
    rw [d0,FastHeight.side_eq,FastHeight.ordinate_eq 133384 _ (by decide)] at amount
    have cd:=inc 0 ((_root_.Research6970.Height2313.Research6969.PairPrices.sx i)^2:ℕ) (2*_root_.Research6970.Height2313.Research6969.PairPrices.sx i*_root_.Research6970.Height2313.Research6969.PairPrices.sy:ℕ) (by
      simp only [Int.zero_add]
      exact_mod_cast amount.trans_eq (by dsimp [_root_.Research6970.Height2313.Research6969.PairPrices.sx,_root_.Research6970.Height2313.Research6969.PairPrices.sy,_root_.Research6970.Height2313.Research6969.PairPrices.d];ring))
    exact_mod_cast cd.trans pay
  | node fee=>
    rw [_root_.Research6970.Height2313.Research6969.PairPrices.sameOK,tag] at pay
    obtain ⟨quad,yes,char,ok,paid⟩:=pay
    have cert:=NodeBudget.family s.F (PairedMarks.rescue_sub s.pair) rfl ((by decide:0<2308).trans_le s.lower) s.higher
      (by decide) s.physical (OrdinaryCell.native_prime s.native s.gp) (NativeGraphMarks.slope_degree s.native s.gp)
      ((HelperWeightCap.native_degree s.native s.gp).trans (h.degree.trans quad)) char
      ((K1_14_2_2_2_1.seedDegree_le ..).mp (h.seedHigh _ (_root_.Research6970.Height2313.Research6969.OnTariff.selected yes))) s.nodes (fun z hz=>s.residues z (PairedMarks.rescue_sub s.pair hz))
      (by intro z hz
          let ev:K1_14.Jet→+*K1_14.FX:=eval₂RingHom (eval₂RingHom (K1_14.graphEval (s.model.label z)) (atX (s.F.scalar z))) (atX (s.F.scalar z).derivative)
          exact (HelperGraph.same_mark A s.native gp s.gp same ev).mp ((PairedMarks.rescue s.pair hz).1))
      (nodeLow fee tag) ok
    have cd:=inc fee 0 0 (by simp only [Int.zero_mul,Int.add_zero];exact_mod_cast cert)
    exact_mod_cast cd.trans paid

end
end Research6970.Height2313.Research6969.ConfirmedSame
end Z6969Source2568

-- Source: Research6969.ThreeRule
section Z6969Source2569
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.ThreeRule
open _root_.Research6969
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.BookView (mainBook rescueBook)
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry nativeHelper)
open Research6966
open Finset
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000

def fee (b:Row) (n:Fin 18) (i k j:ℕ):ℤ:=
  let m:=mainBook n
  let r:=rescueBook n
  (m.fee:ℤ)+r.fee+ThreeLedger.debit (ThreeLedger.rate k*K1.p) (ThreeLedger.rate i)
    m.seedMass (b.vm n) (b.cap n).axis i k m.ordinateCredit m.seedCredit (ThreeLedger.tail i) (ThreeLedger.tail k)+
    RescuePrice.ticket r j (_root_.Research6970.Height2313.Research6969.PairPrices.sx n) _root_.Research6970.Height2313.Research6969.PairPrices.sy

def check (b:Row) (n:Fin 18):Bool:=
  decide (b.upperGrade<64 ∧ (2*b.upperGrade-1)*(mainBook n).seedMass<K1.p ∧
      (2*b.upperGrade-1)*(rescueBook n).seedMass<K1.p) &&
  GradeTable.first (fun delta=>let grade:=b.lowerGrade+delta
    GradeTable.first (fun j=>GradeTable.first (fun k=>
      let i:=grade-(j+k)
      decide (j+k>grade ∨ i>b.gm n ∨ i<grade-b.off-b.cross ∨ fee b n i k j≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target))
      (b.off+1)) (min (b.off+b.cross) grade+1)) (b.upperGrade+1-b.lowerGrade)

theorem proves {n} (s:State n) (b:Row) (h:_root_.Research6970.Height2313.Research6969.PairCell.Facts s b) (ok:check b n=true)
    (z:Geometry s) (distinct:GraphIntersection.determinant (nativeHelper s) s.native≠0):
    s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target:=by
  have ⟨guards,check⟩:=Bool.and_eq_true_iff.mp ok
  obtain ⟨small,mg,rg⟩:=of_decide_eq_true guards
  let C:=z.pairData
  let i:=C.main.onEq.natDegree
  let k:=C.three.off.natDegree
  let j:=C.three.rescue.natDegree
  let grade:=s.f.natDegree
  have eBounds:b.lowerGrade≤grade ∧ grade≤b.upperGrade:=⟨h.gradeLow,h.gradeHigh⟩
  have tsum:i+k+j=grade:=C.three.total_grade
  obtain ⟨gu,gv,ax,k₀⟩:=_root_.Research6970.Height2313.Research6969.PairCell.primary_bounds s b h z
  have kl:k≤b.off:=(Polynomial.natDegree_le_of_dvd C.three.off_dvd C.main.offProduct.primitive.ne_zero).trans k₀
  obtain ⟨jl,global⟩:=_root_.Research6970.Height2313.Research6969.PairCell.distinct_total s b h z distinct
  have ju:j≤b.off+b.cross:=(Polynomial.natDegree_le_of_dvd C.three.rescue_dvd C.rescuePr.primitive.ne_zero).trans jl
  have un:0<TransitionPacket.NormalCatalogue.seed n:=by unfold TransitionPacket.NormalCatalogue.seed;omega
  have d0:=_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_degree s
  have upper':i≤b.gm n:=gu
  have eg : grade-b.off-b.cross ≤ i := by
    change grade ≤ i+b.off+b.cross at global
    omega
  have pt:=GradeTable.entry check (i:=grade-b.lowerGrade) (by omega)
  rw [Nat.add_sub_of_le eBounds.1] at pt
  have pj:=GradeTable.entry pt (i:=j) (show j<min (b.off+b.cross) grade+1 by omega)
  have pk:=of_decide_eq_true (GradeTable.entry pj (i:=k) (show k<b.off+1 by omega))
  have cost:fee b n i k j≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target:=by
    have sub:grade-(j+k)=i:=by omega
    rw [sub] at pk
    rcases pk with x|x|x|x
    · omega
    · omega
    · omega
    · exact x
  have ph:131071+s.model.overhead≤(133384:ℤ):=by have d:=s.higher;omega
  have amount:=ThreeInvoice.charge s.pair (nativeHelper s) s.native C (PhysicalHelperTariff.primitive s.prime s.slope)
    rfl d0.ge un (_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_cap s) s.product (h.gradeHigh.trans_lt small)
    ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h.gradeHigh) _)).trans_lt mg)
    ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 h.gradeHigh) _)).trans_lt rg)
    (s.higher.trans (by decide)) ph (by decide) (by decide) (by decide) gv ax
  rw [d0,FastHeight.side_eq,FastHeight.ordinate_eq 133384 _ (by decide)] at amount
  exact_mod_cast amount.trans cost

end Research6970.Height2313.Research6969.ThreeRule
end Z6969Source2569

-- Source: Research6969.PairProof
section Z6969Source2570
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.PairProof
open _root_.Research6969
noncomputable section
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.NormalGeometry (Geometry nativeHelper)
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open scoped Classical
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

def node (p:Decision):Bool:=
  _root_.Research6970.Height2313.Research6969.PairPrices.modeNode p.main || match p.same with | .node _=>true | _=>false

theorem price {i} (s:State i) (b:Row) (p:Decision) (facts:_root_.Research6970.Height2313.Research6969.PairCell.Facts s b)
    (cert:_root_.Research6970.Height2313.Research6969.PairPrices.valid b i p) (weight:node p=true→_root_.Research6970.Height2313.Research6969.NormalGeometry.weight s<p.cutoff):
    s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target:=by
  obtain ⟨_,room,small,mc,rc,dist,same⟩:=cert
  obtain ⟨z⟩:=_root_.Research6970.Height2313.Research6969.NormalGeometry.geometry s
  by_cases eq:GraphIntersection.determinant (nativeHelper s) s.native=0
  · apply _root_.Research6970.Height2313.Research6969.ConfirmedSame.proves s b facts z p eq same ((Nat.le_add_right ..).trans_lt small) mc
    intro fee atNode
    apply weight
    simp only [node,atNode,Bool.or_true]
  · apply _root_.Research6970.Height2313.Research6969.ConfirmedDistinct.proves s b facts z p eq dist room small mc rc
    cases h:p.main <;>simp only [_root_.Research6970.Height2313.Research6969.OnTariff.NodeGuard,true_iff] <;>try trivial
    apply weight
    simp [node,h,_root_.Research6970.Height2313.Research6969.PairPrices.modeNode]

theorem three {i} (s:State i) (b:Row) (facts:_root_.Research6970.Height2313.Research6969.PairCell.Facts s b) (checked:_root_.Research6970.Height2313.Research6969.ThreeRule.check b i=true)
    (different:b.graph≠2):s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target:=by
  obtain ⟨z⟩:=_root_.Research6970.Height2313.Research6969.NormalGeometry.geometry s
  apply _root_.Research6970.Height2313.Research6969.ThreeRule.proves s b facts checked z
  intro same
  have eq:=(HelperGraph.same_degrees (nativeHelper s) s.native (Research6966.PhysicalHelperTariff.primitive s.prime s.slope) s.gp same).1
  exact different (facts.degree.symm.trans (eq.symm.trans (_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_degree s)))

theorem excluded {i} (s:State i) (b:Row) (facts:_root_.Research6970.Height2313.Research6969.PairCell.Facts s b)
    (impossible:(b.cap i).grade<b.lowerGrade-b.off):s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target:=by
  obtain ⟨z⟩:=_root_.Research6970.Height2313.Research6969.NormalGeometry.geometry s
  obtain ⟨g,_,_⟩:=_root_.Research6970.Height2313.Research6969.PairCell.caps s b facts z
  have off:=z.offCap
  rw [facts.control,facts.degree] at off
  have total:=z.wholeGrade
  have large:=facts.gradeLow
  unfold _root_.Research6970.Height2313.Research6969.PairCell.Row.off at impossible
  omega

end
end Research6970.Height2313.Research6969.PairProof
end Z6969Source2570

-- Source: Research6969.PairLeaves
section Z6969Source2571
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.PairLeaves
open _root_.Research6969
open _root_.Research6970.Height2313.Research6969.PairRoute
open _root_.Research6970.Height2313.Research6969.PairCell (Row)
open _root_.Research6970.Height2313.Research6969.PairPrices (Decision)
open scoped Classical

theorem paired {i} (b:Row) (p:Decision) (result:_root_.Research6970.Height2313.Research6969.PairPrices.valid b i p) (wh:Option ℕ)
    (use:_root_.Research6970.Height2313.Research6969.PairProof.node p=true→wh=some p.cutoff) : Done i (of_row b wh):=by
  intro s h
  exact _root_.Research6970.Height2313.Research6969.PairProof.price s b p (facts h) result (fun yes=>h.wh _ (use yes))

theorem three {i} (b:Row) (checked:_root_.Research6970.Height2313.Research6969.ThreeRule.check b i=true) (different:b.graph≠2) (wh:Option ℕ):
    Done i (of_row b wh):=by
  intro s h
  exact _root_.Research6970.Height2313.Research6969.PairProof.three s b (facts h) checked different

theorem excluded {i} (b:Row) (checked:(b.cap i).grade<b.lowerGrade-b.off) (wh:Option ℕ):
    Done i (of_row b wh):=by
  intro s h
  exact _root_.Research6970.Height2313.Research6969.PairProof.excluded s b (facts h) checked

end Research6970.Height2313.Research6969.PairLeaves
end Z6969Source2571
