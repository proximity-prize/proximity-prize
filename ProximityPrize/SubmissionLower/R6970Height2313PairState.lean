import ProximityPrize.SubmissionLower.R6970Height2308SelectedGeometry
import ProximityPrize.SubmissionLower.R6970Height2313PairBounds
import ProximityPrize.SubmissionLower.R6970Height2313Books

set_option Elab.async false

-- Source: Research6969.PrefixNormalCatalogue
section Z6969Source0829
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.BookView
open _root_.Research6969
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14 (Equation)
open K1_14_3 (ProjectedProduct SeedField)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Lower6960 Research6966
open Far6969RescueGeometry (Model Family word)
open scoped Classical
set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

abbrev seed (i : Fin 18) : ℕ := i.val+1
def savedMainGrade (i : Fin 18) : ℕ := ![335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335, 335] i
def savedRescueGrade (i : Fin 18) : ℕ := ![386, 387, 387, 321, 319, 319, 371, 387, 319, 315, 319, 319, 256, 293, 293, 293, 293, 246] i
def mainBook (i : Fin 18) : JointLedger.Book := ![_root_.Research6970.Height2313.Research6969.SmallCertificates.primary1, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary2, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary3, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary4, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary5, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary6, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary7, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary8, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary9, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary10, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary11, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary12, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary13, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary14, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary15, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary16, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary17, _root_.Research6970.Height2313.Research6969.SmallCertificates.primary18] i
def rescueBook (i : Fin 18) : JointLedger.Book := ![_root_.Research6970.Height2313.Research6969.SmallCertificates.rescue1, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue2, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue3, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue4, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue5, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue6, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue7, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue8, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue9, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue10, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue11, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue12, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue13, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue14, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue15, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue16, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue17, _root_.Research6970.Height2313.Research6969.SmallCertificates.rescue18] i


end
end Research6970.Height2313.Research6969.BookView
end Z6969Source0829

-- Source: Research6969.HighPackets
section Z6969Source1018
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPackets
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation L)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct nodeL)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface SeedField Parent ProjectedProduct)
open Lower6960
open Far6969RescueGeometry (Model Family word)
open Research6966
open PadeNativeQuotient (Native)
open TransitionPacket (Pair)
open _root_.Research6970.Height2313.Research6969.BookView (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

structure State (i:Fin 18) where
  u:P1.Words
  del:Finset I
  model:Model u del
  labels:Finset K
  F:Family model labels
  D:PoleData model.overhead.toNat
  crt:CRTLift D
  lower:2308≤model.overhead.toNat
  higher:model.overhead.toNat≤2313
  nodes:∀j:I,(poleProduct D).eval (algebraMap K L (K1.node j))≠0
  residues:∀z∈labels,MarkResidues D (model.label z) (F.scalar z)
  H:Jet
  prime:Prime H
  slope:H.natDegree=1
  nonlinear:2≤jetDegree H
  helperCaps:K1_14_2_2.RowCaps H (Prefix6969Rescue.graphShape 2 (seed i))
  helperSeed:seedDegree H=seed i
  pair:Pair F crt H (mainBook i) (rescueBook i)
  mainGrade:pair.mainGrade=savedMainGrade i
  rescueGrade:pair.rescueGrade=savedRescueGrade i
  f:Equation
  product:ProjectedProduct (pair.main∪pair.rescue) f
  high:22≤f.natDegree
  graph:Pade.Row SeedField
  native:Native graph
  gp:graph.primitive
  graphBound:graph.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band f.natDegree)
  controls:Pade.Controls (graph.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (pair.main∪pair.rescue))
    (TransitionClassification.content (TransitionClassification.band f.natDegree))
  physical:HelperPhysicalModel.Model crt native.poly

  overrideContent :
    Option {c : ℕ // c ≤ TransitionClassification.content (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (graph.map (algebraMap SeedField Pade.Native.Sep))
        (Pade.Native.sheets (pair.main∪pair.rescue)) c} := none

abbrev State.StockContent {i} (s : State i) : ℕ :=
  TransitionClassification.content (TransitionClassification.band s.f.natDegree)

abbrev State.ControlAt {i} (s : State i) (c : ℕ) : Prop :=
  Pade.Controls (s.graph.map (algebraMap SeedField Pade.Native.Sep))
    (Pade.Native.sheets (s.pair.main∪s.pair.rescue)) c

def State.clearContent {i} (s : State i) : State i := {s with overrideContent := none}

def State.withContent {i} (s : State i) (c : ℕ) (room : c ≤ s.StockContent)
    (control : s.ControlAt c) : State i :=
  {s with overrideContent := some ⟨c, room, control⟩}


def Goal:Prop:=∀(i:Fin 18)(s:State i),s.labels.card≤_root_.Research6969.CertifiedCell.target

theorem State.degree_bound {i} (s:State i):s.f.natDegree≤savedMainGrade i+savedRescueGrade i:=by
  obtain ⟨fm,pm⟩:=JointProjection.exists_product s.pair.main (fun q h=>(s.pair.mainGeo q h).1)
  obtain ⟨fr,pr⟩:=JointProjection.exists_product s.pair.rescue (fun q h=>(s.pair.rescueGeo q h).1)
  have div:s.f∣fm*fr:=NativeOrdinateMass.divides_of_member s.product (by
    intro q hq;rw [map_mul];rcases mem_union.mp hq with a|b
    · exact q.asIdeal.mul_mem_right _ (pm.vanishes a)
    · exact q.asIdeal.mul_mem_left _ (pr.vanishes b))
  have degree:=natDegree_le_of_dvd div (mul_ne_zero pm.primitive.ne_zero pr.primitive.ne_zero)
  rw [natDegree_mul pm.primitive.ne_zero pr.primitive.ne_zero] at degree
  have m:=(JointProjection.measures pm s.pair.aSrc s.pair.mainActive s.pair.mainOrigin).1.trans s.pair.mainDegreeCap
  have r:=(JointProjection.measures pr s.pair.bSrc s.pair.rescueActive s.pair.rescueOrigin).1.trans s.pair.rescueDegreeCap
  exact degree.trans (Nat.add_le_add (m.trans_eq s.mainGrade) (r.trans_eq s.rescueGrade))


end
end Research6970.Height2313.Research6969.HighPackets
end Z6969Source1018

-- Source: Research6969.NormalGeometry
section Z6969Source1030
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.NormalGeometry
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface SeedField ProjectedProduct Parent)
open Lower6960
open Far6969RescueGeometry (word)
open Research6966
open NearBook (owning outside)
open PadeNativeQuotient (Native)
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.BookView (mainBook rescueBook seed)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 1700000
set_option maxRecDepth 12000

variable {i:Fin 18} (s:State i)
abbrev helper (s:State i):=PhysicalHelperTariff.graphOf s.H
abbrev nativeHelper (s:State i):Native (helper s):=PhysicalHelperTariff.realization s.prime s.slope
def content (s : State i) : ℕ :=
  match s.overrideContent with
  | none => s.StockContent
  | some bound => bound.val

theorem content_le_stock (s : State i) : content s ≤ s.StockContent := by
  unfold content
  cases s.overrideContent with
  | none => exact le_rfl
  | some bound => exact bound.property.1

theorem control (s : State i) : s.ControlAt (content s) := by
  unfold content
  cases s.overrideContent with
  | none => exact s.controls
  | some bound => exact bound.property.2

abbrev allParents (s:State i):=s.pair.main∪s.pair.rescue
abbrev weight (s:State i):=RawPhysicalDegree.weight (131071-s.model.overhead.toNat)
  (131071-s.model.overhead.toNat-1) s.physical.raw

theorem helper_degree:(helper s).graphDegree=2:=by
  have a:=HelperWeightCap.native_degree (nativeHelper s) (PhysicalHelperTariff.primitive s.prime s.slope)
  have lim:jetDegree s.H≤2:=(K1_14_2_2_2_1.jetDegree_le ..).mpr fun j k nz=>(s.helperCaps j k nz).1
  exact a.symm.trans (Nat.le_antisymm lim s.nonlinear)

theorem helper_cap (j k:ℕ):(((nativeHelper s).poly.coeff j).coeff k).totalDegree≤seed i:=by
  change ((s.H.coeff j).coeff k).totalDegree≤seed i
  by_cases zero:(s.H.coeff j).coeff k=0
  · simp [zero]
  · exact (s.helperCaps j k zero).2.2

theorem base: s.graph.graphDegree*(131071-2313)-1≤weight s:=by
  have rp:=HelperWeightCap.weight_lower s.physical s.native.primitive.ne_zero (131071-s.model.overhead.toNat)
    (by have:=s.higher;omega)
  rw [HelperWeightCap.native_degree s.native s.gp,NativeGraphMarks.slope_degree s.native s.gp] at rp
  have mul:=Nat.mul_le_mul_right s.graph.graphDegree (Nat.sub_le_sub_left s.higher 131071)
  unfold weight;rw [Nat.mul_comm s.graph.graphDegree];omega

structure Geometry where
  onPoly:Equation
  offPoly:Equation
  onWitness:NativeWitnessBank.witnessed s.native (owning s.native.poly (allParents s)) onPoly
  offProduct:JointProjection.Product (outside s.native.poly (allParents s)) offPoly
  offCap:offPoly.natDegree≤content s-s.graph.graphDegree
  wholeGrade:s.f.natDegree≤onPoly.natDegree+offPoly.natDegree
  pairData:PairedComparison.Base s.pair s.native s.f onPoly offPoly

theorem geometry:Nonempty (Geometry s):=by
  have upper (b:Fin 8):TransitionClassification.content b≤12:=by fin_cases b <;>decide
  have large:content s<s.f.natDegree:=(content_le_stock s).trans_lt ((upper _).trans_lt ((by decide:12<22).trans_le s.high))
  have geom q (hq:q∈allParents s):Parent q:=(mem_union.mp hq).elim (fun m=>(s.pair.mainGeo q m).1) (fun m=>(s.pair.rescueGeo q m).1)
  obtain ⟨onEq,off,checked,z,deg,all⟩:=NearTerminal.partition geom s.product _ large s.native s.gp (control s)
  obtain ⟨data⟩:=PairedComparison.base s.pair s.native s.product checked.1 z
  exact ⟨⟨_,_,checked,z,deg,all,data⟩⟩

structure Bounds where
  grade:ℕ
  seed:ℕ
  axis:ℕ

private def dualTests : List _root_.Research6970.Height2313.Research6969.Geometry2308.DualAxis.Test :=
  [_root_.Research6970.Height2313.Research6969.Geometry2308.test332, _root_.Research6970.Height2313.Research6969.Geometry2308.test344, _root_.Research6970.Height2313.Research6969.Geometry2308.test495]

private def tightenAxis (degree lo W axisLo axisHi prior : ℕ) : ℕ :=
  dualTests.foldl (fun amount test => _root_.Research6970.Height2313.Research6969.Geometry2308.DualAxis.tighten test degree lo W axisLo axisHi amount) prior

def limits (initial:_root_.Research6970.Height2313.Research6969.CaseBounds.Cap) (tests:List _root_.Research6970.Height2313.Research6969.MeasuredBound.Test) (rect:List _root_.Research6970.Height2313.Research6969.AxisTests.Test)
    (degree lo W:ℕ) (high:Option ℕ) (axisLo axisHi:ℕ):Bounds:=
  let c:=_root_.Research6970.Height2313.Research6969.CaseBounds.run degree lo W high tests initial
  let side:=_root_.Research6970.Height2313.Research6969.AxisTests.run degree lo axisLo axisHi W rect ⟨c.grade,c.seed⟩
  ⟨side.grade,c.seed,if rect.isEmpty = true then side.seed else
    tightenAxis degree lo W axisLo axisHi side.seed⟩

theorem measured (z:Geometry s) (tests:List _root_.Research6970.Height2313.Research6969.MeasuredBound.Test) (rect:List _root_.Research6970.Height2313.Research6969.AxisTests.Test)
    (upperGrade degree lo W axisLo axisHi:ℕ) (high:Option ℕ) (cap:s.f.natDegree≤upperGrade)
    (deg:s.graph.graphDegree=degree) (tl:lo≤seedDegree s.native.poly)
    (tu:∀v,high=some v→seedDegree s.native.poly≤v) (al:axisLo≤PadeNativeQuotient.axis s.native.poly 1)
    (au:PadeNativeQuotient.axis s.native.poly 1≤axisHi) (physical:W≤weight s):
    let bound:=limits ⟨upperGrade,(mainBook i).seedMass+(rescueBook i).seedMass⟩ tests rect degree lo W high axisLo axisHi
    z.onPoly.natDegree≤bound.grade ∧ K1_14_4.seedDegree z.onPoly≤bound.seed ∧ KoalaRect.axisDegree z.onPoly 1≤bound.axis:=by
  let set:=owning s.native.poly (allParents s)
  have ge q (hq:q∈set):Parent q:=(mem_union.mp (mem_filter.mp hq).1).elim (fun m=>(s.pair.mainGeo q m).1) (fun m=>(s.pair.rescueGeo q m).1)
  have pass q (hq:q∈set):TerminalBanks.Pass s.crt (word s.model) 179730 SpreadCatalogue.shape q:=
    (mem_union.mp (mem_filter.mp hq).1).elim (fun m=>(s.pair.mainGeo q m).2.1) (fun m=>(s.pair.rescueGeo q m).2.1)
  have gCap:=(NearTerminal.subset_degree (show set⊆allParents s from filter_subset ..) z.onWitness.1 s.product).trans cap
  obtain ⟨view⟩:=UnionPartition.data s.pair s.native z.onWitness.1 z.offProduct z.offCap
  have l:=K1_14_2_2.mass_mono (show NearBook.ownerSources s.native.poly s.pair.aSrc⊆s.pair.aSrc from filter_subset ..) 1
  have r:=K1_14_2_2.mass_mono (show NearBook.ownerSources s.native.poly s.pair.bSrc⊆s.pair.bSrc from filter_subset ..) 1
  have seedCap:=view.onSeed.trans (Nat.add_le_add (l.trans s.pair.boundsM) (r.trans s.pair.boundsR))
  let c:=_root_.Research6970.Height2313.Research6969.CaseBounds.run degree lo W high tests ⟨upperGrade,(mainBook i).seedMass+(rescueBook i).seedMass⟩
  have tc:=_root_.Research6970.Height2313.Research6969.CaseBounds.sound tests s.crt (word s.model) s.lower s.higher ge pass s.native s.gp deg z.onWitness tl tu
    s.physical physical ⟨upperGrade,(mainBook i).seedMass+(rescueBook i).seedMass⟩ gCap seedCap
  have aCap:= (NearBook.axis_total ((K1_14_4.seedDegree_le_iff ..).mp le_rfl) 1).trans tc.2
  have ac:=_root_.Research6970.Height2313.Research6969.AxisTests.sound rect s.crt (word s.model) s.lower s.higher ge pass s.native s.gp z.onWitness deg tl al au
    s.physical physical (⟨c.grade,c.seed⟩:_root_.Research6970.Height2313.Research6969.CaseBounds.Cap) tc.1 aCap
  refine ⟨ac.1,tc.2,?_⟩
  dsimp only [limits]
  split
  · exact ac.2
  · have step (t : _root_.Research6970.Height2313.Research6969.Geometry2308.DualAxis.Test) (n : ℕ)
        (old : KoalaRect.axisDegree z.onPoly 1 ≤ n) :
        KoalaRect.axisDegree z.onPoly 1 ≤ _root_.Research6970.Height2313.Research6969.Geometry2308.DualAxis.tighten t degree lo W axisLo axisHi n :=
      _root_.Research6970.Height2313.Research6969.Geometry2308.DualAxis.Test.tighten_bound t s.crt (word s.model) s.lower s.higher ge pass s.native
        s.gp z.onWitness deg tl al au s.physical physical old
    unfold tightenAxis dualTests
    exact step _root_.Research6970.Height2313.Research6969.Geometry2308.test495 _
      (step _root_.Research6970.Height2313.Research6969.Geometry2308.test344 _ (step _root_.Research6970.Height2313.Research6969.Geometry2308.test332 _ ac.2))

end
end Research6970.Height2313.Research6969.NormalGeometry
end Z6969Source1030
