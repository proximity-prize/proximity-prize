import ProximityPrize.SubmissionLower.R6970Height2313PairState
import ProximityPrize.SubmissionLower.Z6969Pack0640

set_option Elab.async false

-- Source: Research6969.CertifiedCell
section Z6969Source0864
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.CertifiedCell
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Equation Jet)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2 (mass)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface SeedField ProjectedProduct Parent)
open Lower6960.Far6969RescueGeometry (Model Family word)
open Research6966
open Finset Polynomial
open PadeNativeQuotient (Native)
open TransitionPacket (Pair)
open JointLedger (Book)
open JointRouted (seedWeight ordWeight)
open scoped Classical
set_option maxHeartbeats 2400000
set_option maxRecDepth 15000

inductive Method where | excluded | marked | affine | surface
deriving DecidableEq
structure Row where
  minGrade:ℕ
  maxGrade:ℕ
  content:ℕ
  graph:ℕ
  lowSeed:ℕ
  highSeed:Option ℕ
  tests:List _root_.Research6970.Height2313.Research6969.MeasuredBound.Test
  method:Method

abbrev target:ℕ:=274779381266040419
abbrev d:ℕ:=133384
def Row.weight (b:Row):ℕ:=b.graph*(131071-2313)-1
def Row.off (b:Row):ℕ:=b.content-b.graph
def Row.lower (b:Row):ℕ:=b.minGrade-b.off
def Row.cap (b:Row) (m r:Book):_root_.Research6970.Height2313.Research6969.CaseBounds.Cap:=
  _root_.Research6970.Height2313.Research6969.CaseBounds.run b.graph b.lowSeed b.weight b.highSeed b.tests ⟨b.maxGrade,m.seedMass+r.seedMass⟩
def Row.affineFee (b:Row):ℕ:=WholeAffine.fee d (max 1 (b.highSeed.getD 0))
def Row.side (b:Row):ℕ:=seedWeight d (b.highSeed.getD 0)
def Row.y (b:Row):ℕ:=ordWeight d (b.graph-1)

def Row.check (b:Row) (m r:Book):Prop:=
  let bound:=b.cap m r
  b.content<b.minGrade ∧ b.off<64 ∧ (2*b.off-1)*m.seedMass<p ∧ (2*b.off-1)*r.seedMass<p ∧
  match b.method with
  | .excluded=>bound.grade<b.lower
  | .marked=>bound.grade<64 ∧ (2*bound.grade-1)*bound.seed<p ∧
    WholeGraph.bill m r b.off b.lower bound.grade bound.seed (bound.grade*(max 3 bound.grade-1):ℕ) 0 (JointLedger.coefficient bound.grade)≤target
  | .affine=>b.graph=1 ∧ b.highSeed.isSome=true ∧ max 1 (b.highSeed.getD 0)<p ∧
    WholeGraph.bill m r b.off b.lower bound.grade bound.seed b.affineFee 0 0≤target
  | .surface=>2≤b.graph ∧ b.highSeed.isSome=true ∧ (2*b.graph-1)*(b.highSeed.getD 0)<p ∧
    WholeGraph.bill m r b.off b.lower bound.grade bound.seed
      ((2*b.graph-1)*((p+1)*(b.highSeed.getD 0)):ℕ) (b.side^2:ℕ) (2*b.side*b.y:ℕ)≤target

instance (b:Row) (m r:Book):Decidable (b.check m r):=by
  unfold Row.check
  cases b.method <;> infer_instance

theorem Row.proves (b:Row) {m r:Book} (ok:b.check m r)
    {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} {H:Jet} (P:Pair F Crt H m r) (lo:2308≤M.overhead.toNat) (hi:M.overhead.toNat≤2313)
    {f:Equation} (pr:ProjectedProduct (P.main∪P.rescue) f) (minGrade:b.minGrade≤f.natDegree) (maxGrade:f.natDegree≤b.maxGrade)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (degree:G.graphDegree=b.graph)
    (control:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue)) b.content)
    (low:b.lowSeed≤seedDegree N.poly) (upper:∀v,b.highSeed=some v→seedDegree N.poly≤v):
    Γ.card≤target := by
  classical
  let S:=P.main∪P.rescue
  have geo q (hq:q∈S):Parent q:=(mem_union.mp hq).elim (fun h=>(P.mainGeo q h).1) (fun h=>(P.rescueGeo q h).1)
  have pass q (hq:q∈S):TerminalBanks.Pass Crt (word M) 179730 SpreadCatalogue.shape q:=
    (mem_union.mp hq).elim (fun h=>(P.mainGeo q h).2.1) (fun h=>(P.rescueGeo q h).2.1)
  obtain ⟨gc,offSmall,guardM,guardR,pay⟩:=ok
  obtain ⟨onEq,offEq,seen,off,offCap,total⟩:=NearTerminal.partition geo pr b.content (gc.trans_le minGrade) N gp control
  obtain ⟨data⟩:=UnionPartition.data P N seen.1 off offCap
  have passOn q (hq:q∈NearBook.owning N.poly S):=pass q (mem_filter.mp hq).1
  have geoOn q (hq:q∈NearBook.owning N.poly S):=geo q (mem_filter.mp hq).1
  have slope:=NativeGraphMarks.slope_degree N gp
  obtain ⟨phys⟩:=HelperPhysicalModel.exists_model Crt (NativeWitnessBank.irreducible N gp) (by omega)
  have wt:=HelperWeightCap.weight_lower phys N.primitive.ne_zero (131071-M.overhead.toNat) (by omega)
  rw [HelperWeightCap.native_degree N gp,slope,degree] at wt
  have weight:b.weight≤RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw:=by
    have sw:=Nat.mul_le_mul_right b.graph (Nat.sub_le_sub_left hi 131071)
    unfold Row.weight
    rw [Nat.mul_comm b.graph]
    omega
  have rawDegree:=NearTerminal.subset_degree (show NearBook.owning N.poly S⊆S from filter_subset _ _) seen.1 pr
  have x:=K1_14_2_2.mass_mono (show NearBook.ownerSources N.poly P.aSrc⊆P.aSrc from filter_subset ..) 1
  have y:=K1_14_2_2.mass_mono (show NearBook.ownerSources N.poly P.bSrc⊆P.bSrc from filter_subset ..) 1
  have seedCap:=data.onSeed.trans (Nat.add_le_add (x.trans P.boundsM) (y.trans P.boundsR))
  have ⟨gcap,vcap⟩:=_root_.Research6970.Height2313.Research6969.CaseBounds.sound b.tests Crt (word M) lo hi geoOn passOn N gp degree seen low upper phys weight
    (⟨b.maxGrade,m.seedMass+r.seedMass⟩:_root_.Research6970.Height2313.Research6969.CaseBounds.Cap) (rawDegree.trans maxGrade) seedCap
  change onEq.natDegree≤(b.cap m r).grade at gcap
  change K1_14_4.seedDegree onEq≤(b.cap m r).seed at vcap
  have lower:b.lower≤onEq.natDegree:=by
    have cf:=offCap;rw [degree] at cf;unfold Row.lower Row.off;omega
  have small: b.content-G.graphDegree<64:=degree ▸ offSmall
  have guards:(2*(b.content-G.graphDegree)-1)*m.seedMass<p ∧ (2*(b.content-G.graphDegree)-1)*r.seedMass<p:=degree ▸ ⟨guardM,guardR⟩
  have budget:=WholeGraph.count P N data (hi.trans (by decide)) small guards.1 guards.2 lower gcap vcap
  have dh:131071+M.overhead≤(d:ℤ):=by change 131071+M.overhead≤(133384:ℤ);omega
  have ds:0<d:=by decide
  have gap:d<179730:=by decide
  have tp:d<p:=by decide
  let t:=UnionTariffs.group F N S
  have close (k y z:ℤ) (cp:(t.card:ℤ)≤k+y*onEq.natDegree+z*K1_14_4.seedDegree onEq)
      (paid:WholeGraph.bill m r b.off b.lower (b.cap m r).grade (b.cap m r).seed k y z≤target) :
      Γ.card≤target:=by
    have due:=budget k y z cp
    rw [degree] at due
    exact_mod_cast due.trans paid
  cases method:b.method with
  | excluded=>
    rw [method] at pay
    exact (Nat.not_lt_of_ge (lower.trans gcap) pay).elim
  | marked=>
    rw [method] at pay
    obtain ⟨legal,char,paid⟩:=pay
    have char':(2*onEq.natDegree-1)*K1_14_4.seedDegree onEq<p:=
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 gcap) _) vcap).trans_lt char
    have all:=UnionTariffs.marked F N S seen.1 (hi.trans (by decide)) gcap legal char'
    apply close _ _ _ _ paid
    simp only [Int.zero_mul,Int.add_zero]
    exact_mod_cast all.trans_eq (Nat.add_comm ..)
  | affine=>
    rw [method] at pay
    obtain ⟨eq,yes,char,paid⟩:=pay
    have up:seedDegree N.poly≤b.highSeed.getD 0:=upper _ (by cases h:b.highSeed <;>simp_all)
    have all:=UnionTariffs.affine F N S gp (degree.trans eq) (by omega:0<max 1 (b.highSeed.getD 0)) char
      (up.trans (le_max_right ..)) dh ds gap tp
    apply close _ _ _ _ paid
    simpa [Row.affineFee] using (show (t.card:ℤ)≤(WholeAffine.fee d (max 1 (b.highSeed.getD 0)):ℤ) by exact_mod_cast all)
  | surface=>
    rw [method] at pay
    obtain ⟨big,yes,char,paid⟩:=pay
    let U:=b.highSeed.getD 0
    have up:seedDegree N.poly≤U:=upper _ (by cases h:b.highSeed <;>simp_all [U])
    have nonlinear:2≤G.graphDegree:=big.trans_eq degree.symm
    have all:t.card≤(2*b.graph-1)*((p+1)*U)+onEq.natDegree*b.side^2+2*K1_14_4.seedDegree onEq*b.side*b.y:=by
      by_cases z:U=0
      · have empty:seedDegree N.poly=0:=by omega
        have small:=UnionTariffs.seedless F N S gp nonlinear empty dh ds gap tp seen.1
        have emptyWidth:b.highSeed.getD 0=0:=z
        simpa only [degree,t,Row.side,Row.y,U,emptyWidth,Nat.mul_zero,Nat.zero_add] using small
      · have cost:=UnionTariffs.surface F N S gp nonlinear (Nat.pos_of_ne_zero z) (degree ▸ char) up dh ds gap tp seen.1
        simpa only [degree,Row.side,Row.y] using cost
    apply close _ _ _ _ paid
    exact_mod_cast all.trans_eq (by dsimp [Row.side,Row.y]; ring)

end
end Research6970.Height2313.Research6969.CertifiedCell
end Z6969Source0864

-- Source: Research6969.FastCell
section Z6969Source0865
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.FastCell
open _root_.Research6969
open JointRouted (seedWeight ordWeight)
open K1 (I)
set_option maxHeartbeats 800000

def ceilRatio (n d:ℕ):ℕ:=(-((-(n:ℤ))/(d:ℤ))).toNat
theorem ratio (n d:ℕ) : ceilRatio n d=⌈(n:ℚ)/d⌉₊:=by
  rw [←Int.ceil_toNat,Rat.ceil_natCast_div_natCast]
  rfl

def side (u:ℕ):ℕ:=ceilRatio (2*262144*133384*u) 179730+4
def ordinate (r:ℕ):ℕ:=ceilRatio (2*262144*133384*r*(179730-133384)+(262144-133384)*179730) (179730*(179730-133384))+4

theorem side_eq (u:ℕ):seedWeight _root_.Research6970.Height2313.Research6969.CertifiedCell.d u=side u:=by
  unfold seedWeight side MarkedAdaptive.price
  rw [show Fintype.card I=262144 from Fintype.card_fin (2^18),ratio]
  congr 2
  dsimp [_root_.Research6970.Height2313.Research6969.CertifiedCell.d]
  push_cast
  ring

theorem ordinate_eq (r:ℕ):ordWeight _root_.Research6970.Height2313.Research6969.CertifiedCell.d r=ordinate r:=by
  unfold ordWeight ordinate MarkedAdaptive.price
  rw [show Fintype.card I=262144 from Fintype.card_fin (2^18),ratio]
  congr 2
  dsimp [_root_.Research6970.Height2313.Research6969.CertifiedCell.d]
  norm_num
  ring


/-- A closed decision procedure for case receipts; expensive section
proofs in the interpolation sources are never inspected by these tests. -/
def accepts (b:_root_.Research6970.Height2313.Research6969.CertifiedCell.Row) (m r:JointLedger.Book):Bool:=
  let g:=(b.cap m r).grade
  let v:=(b.cap m r).seed
  let offs:=b.off
  decide (b.content<b.minGrade ∧ offs<64 ∧ (2*offs-1)*m.seedMass<K1.p ∧ (2*offs-1)*r.seedMass<K1.p) &&
    match b.method with
    | .excluded=>decide (g<b.lower)
    | .marked=>decide (g<64 ∧ (2*g-1)*v<K1.p ∧
        WholeGraph.bill m r offs b.lower g v (g*(max 3 g-1):ℕ) 0 (JointLedger.coefficient g)≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target)
    | .affine=>decide (b.graph=1 ∧ b.highSeed.isSome=true ∧ max 1 (b.highSeed.getD 0)<K1.p ∧
        WholeGraph.bill m r offs b.lower g v b.affineFee 0 0≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target)
    | .surface=>
      let u:=b.highSeed.getD 0
      let x:=side u
      let y:=ordinate (b.graph-1)
      decide (2≤b.graph ∧ b.highSeed.isSome=true ∧ (2*b.graph-1)*u<K1.p ∧
        WholeGraph.bill m r offs b.lower g v ((2*b.graph-1)*((K1.p+1)*u):ℕ) (x^2:ℕ) (2*x*y:ℕ)≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target)

theorem checked {b:_root_.Research6970.Height2313.Research6969.CertifiedCell.Row} {m r:JointLedger.Book} (h:accepts b m r=true):b.check m r:=by
  unfold accepts at h
  obtain ⟨guard,caseOK⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨large,small,mc,rc⟩:=of_decide_eq_true guard
  refine ⟨large,small,mc,rc,?_⟩
  cases method:b.method <;> rw [method] at caseOK <;>
    simpa only [_root_.Research6970.Height2313.Research6969.CertifiedCell.Row.side,_root_.Research6970.Height2313.Research6969.CertifiedCell.Row.y,side_eq,ordinate_eq] using of_decide_eq_true caseOK

end Research6970.Height2313.Research6969.FastCell
end Z6969Source0865

-- Source: Research6969.NormalRoute
section Z6969Source1031
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.NormalRoute
open _root_.Research6969
noncomputable section
open K1 (K I p)
open K1_14 (Equation)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (SeedField)
open Lower6960
open Far6969RescueGeometry (word)
open Research6966
open _root_.Research6970.Height2313.Research6969.HighPackets (State)
open _root_.Research6970.Height2313.Research6969.BookView (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 15000
abbrev Region:=OrdinaryRoute.Region
def Applies {i} (s:State i) (r:Region):Prop:=
  r.gradeLo≤s.f.natDegree ∧ s.f.natDegree≤r.gradeHi ∧ _root_.Research6970.Height2313.Research6969.NormalGeometry.content s=r.content ∧
  s.graph.graphDegree=r.graph ∧ r.lowSeed≤seedDegree s.native.poly ∧ ∀v,r.highSeed=some v→seedDegree s.native.poly≤v
abbrev Done (i:Fin 18) (r:Region):Prop:=∀s:State i,Applies s r→s.labels.card≤_root_.Research6970.Height2313.Research6969.CertifiedCell.target
def region (b:_root_.Research6970.Height2313.Research6969.CertifiedCell.Row):Region:=⟨b.minGrade,b.maxGrade,b.content,b.graph,b.lowSeed,b.highSeed⟩

theorem entire {i} (b:_root_.Research6970.Height2313.Research6969.CertifiedCell.Row) (checked:b.check (mainBook i) (rescueBook i)):Done i (region b):=by
  intro s eligible
  obtain ⟨lo,hi,c,a,sd,su⟩:=eligible
  change _root_.Research6970.Height2313.Research6969.NormalGeometry.content s=b.content at c
  exact b.proves checked s.pair s.lower s.higher s.product lo hi s.native s.gp a (by rw [←c];exact _root_.Research6970.Height2313.Research6969.NormalGeometry.control s) sd su

theorem small {i} (r:Region) (maxGrade:ℕ) (limit:r.gradeHi≤maxGrade) (feasible:maxGrade<64)
    (safeM:(2*maxGrade-1)*(mainBook i).seedMass<p) (safeR:(2*maxGrade-1)*(rescueBook i).seedMass<p)
    (table:∀a b:Fin (maxGrade+1),a.val+b.val≤maxGrade→JointLedger.Pass (mainBook i) (rescueBook i)
      (JointRouted.seedWeight 133384 (seed i)) (JointRouted.ordWeight 133384 1) _root_.Research6970.Height2313.Research6969.CertifiedCell.target a.val b.val):Done i r:=by
  intro s h
  let N:=_root_.Research6970.Height2313.Research6969.NormalGeometry.nativeHelper s
  have gp:=PhysicalHelperTariff.primitive s.prime s.slope
  have deg:=_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_degree s
  have phys:131071+s.model.overhead≤(133384:ℤ):=by have hi:=s.higher;omega
  have sp:0<seed i:=by dsimp [seed];omega
  apply JointClosure.bounded s.F (s.higher.trans (by decide)) s.pair.paid s.pair.main s.pair.rescue
    (fun q h=>(s.pair.mainGeo q h).1) (fun q h=>(s.pair.rescueGeo q h).1) s.pair.aSrc s.pair.bSrc s.pair.mainActive
    s.pair.rescueActive s.pair.mainOrigin s.pair.rescueOrigin (mainBook i) (rescueBook i) s.pair.wm s.pair.wr
    s.pair.mainOrd s.pair.mainSeed s.pair.rescueOrd s.pair.rescueSeed s.pair.bill s.pair.boundsM s.pair.boundsR N gp deg.ge
    sp (by decide:0<133384) phys (by decide:133384<179730) (by decide:133384<p) (_root_.Research6970.Height2313.Research6969.NormalGeometry.helper_cap s) _ (maxDegree:=maxGrade) feasible (h:=s.f) (Or.inl s.product)
    (h.2.1.trans limit) safeM safeR (by simpa only [deg,show 2-1=1 by decide] using table)
  intro z hz
  rcases s.pair.cover z hz with taken|⟨_,atQ⟩|⟨root,reg,atQ⟩
  · exact Or.inl taken
  · exact Or.inr (Or.inl atQ)
  · exact Or.inr (Or.inr ⟨Prefix6969Rescue.graph_law s.slope root,reg,atQ⟩)

theorem splitSeed {i e top c a lo hi} (cut:ℕ)
    (left:Done i ⟨e,top,c,a,lo,some cut⟩)
    (right:Done i ⟨e,top,c,a,cut+1,some hi⟩):
    Done i ⟨e,top,c,a,lo,some hi⟩:=by
  intro s hs
  obtain ⟨l,t,ct,ag,sl,sh⟩:=hs
  by_cases below:seedDegree s.native.poly≤cut
  · exact left s ⟨l,t,ct,ag,sl,fun v eq=>by
      have same:cut=v:=Option.some.inj eq
      simpa [←same] using below⟩
  · exact right s ⟨l,t,ct,ag,by change cut+1≤_;omega,sh⟩

def Tail (i:Fin 18) (e top c a lo:ℕ):Prop:=Done i ⟨e,top,c,a,lo,none⟩
theorem join {i e top c a lo hi} (left:Done i ⟨e,top,c,a,lo,some hi⟩)
    (tail:Tail i e top c a (hi+1)):Tail i e top c a lo:=by
  intro s h
  obtain ⟨l,t,ct,ag,seed,_⟩:=h
  by_cases before:seedDegree s.native.poly≤hi
  · exact left s ⟨l,t,ct,ag,seed,fun v eq=>by have same:hi=v:=Option.some.inj eq;simpa [←same] using before⟩
  · exact tail s ⟨l,t,ct,ag,by change hi+1≤seedDegree s.native.poly;omega,by simp⟩

end
end Research6970.Height2313.Research6969.NormalRoute
end Z6969Source1031
