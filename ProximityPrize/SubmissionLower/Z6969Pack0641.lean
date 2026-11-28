import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0636
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineTariff
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts
import ProximityPrize.SubmissionLower.Z6969Pack0635
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1

set_option Elab.async false

-- Source: Research6969.FastHeight
section Z6969Source0866
set_option autoImplicit true
namespace Research6969.FastHeight
open JointRouted (seedWeight ordWeight)

def side (d u:ℕ):ℕ:=FastCell.ceilRatio (2*262144*d*u) 179730+4
def ordinate (d r:ℕ):ℕ:=FastCell.ceilRatio (2*262144*d*r*(179730-d)+(262144-d)*179730) (179730*(179730-d))+4

theorem side_eq (d u:ℕ):seedWeight d u=side d u:=by
  unfold seedWeight side MarkedAdaptive.price
  rw [show Fintype.card K1.I=262144 from Fintype.card_fin (2^18),FastCell.ratio]
  congr 2
  push_cast
  ring

theorem ordinate_eq (d r:ℕ) (gap:d<179730):ordWeight d r=ordinate d r:=by
  unfold ordWeight ordinate MarkedAdaptive.price
  rw [show Fintype.card K1.I=262144 from Fintype.card_fin (2^18),FastCell.ratio]
  congr 2
  have pos:0<179730-d:=by omega
  have nz:((179730-d:ℕ):ℚ)≠0:=by exact_mod_cast pos.ne'
  push_cast
  field_simp [nz]
  <;> ring

end Research6969.FastHeight
end Z6969Source0866

-- Source: Research6969.OrdinaryCell
section Z6969Source0867
set_option autoImplicit true
namespace Research6969.OrdinaryCell
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation L FX atX jetAt)
open K1_14_1 (PoleData CRTLift poleProduct MarkResidues)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Parent Surface SeedField ProjectedProduct)
open Lower6960
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6966
open PadeNativeQuotient (Native)
open JointLedger (Book)
open Finset Polynomial
open scoped Classical Differential
set_option maxRecDepth 13000
set_option maxHeartbeats 2000000

inductive Method where | excluded | marked | affine | surface | ambient | node (fee cutoff:ℕ)
deriving DecidableEq
structure Row (first last:ℕ) where
  lowerGrade:ℕ
  upperGrade:ℕ
  content:ℕ
  graph:ℕ
  lowerSeed:ℕ
  upperSeed:Option ℕ
  weight:ℕ
  sources:List (OrdinaryBounds.Source first last)
  method:Method
abbrev target:ℕ:=274779381266040419

def Row.off {l h} (b:Row l h):=b.content-b.graph
def Row.cap {l h} (b:Row l h) (m:Book):=OrdinaryBounds.run b.graph b.lowerSeed b.weight b.upperSeed b.sources ⟨b.upperGrade,m.seedMass⟩
def Row.width {l h} (b:Row l h):=b.upperSeed.getD 0
def Row.x {l h} (b:Row l h):=FastHeight.side (131071+h) b.width
def Row.y {l h} (b:Row l h):=FastHeight.ordinate (131071+h) (b.graph-1)
def Row.bad {l h} (b:Row l h):=(2*b.graph-1)*((p+1)*b.width)

def Row.check {l h} (b:Row l h) (m:Book) (G:ℕ):Prop:=
  let c:=b.cap m
  let pay:=OrdinaryLedger.due m G b.off b.lowerGrade c.grade c.seed
  b.content<b.lowerGrade ∧ 3≤G ∧ b.off<64 ∧ (2*b.off-1)*m.seedMass<p ∧
  match b.method with
  | .excluded=>c.grade<b.lowerGrade-b.off
  | .marked=>c.grade<64 ∧ (2*c.grade-1)*c.seed<p ∧ pay true (c.grade^2:ℕ) 0 (JointLedger.coefficient c.grade)≤target
  | .affine=>b.graph=1 ∧ b.upperSeed.isSome=true ∧ max 1 b.width<p ∧
      pay true (WholeAffine.fee (131071+h) (max 1 b.width)) 0 0≤target
  | .surface=>2≤b.graph ∧ b.upperSeed.isSome=true ∧ (2*b.graph-1)*b.width<p ∧
      pay false b.bad (b.x^2:ℕ) (2*b.x*b.y:ℕ)≤target
  | .ambient=>2≤b.graph ∧ b.upperSeed.isSome=true ∧ (2*b.graph-1)*b.width<p ∧
      pay true (b.bad+3*b.y*b.x^2:ℕ) 0 0≤target
  | .node fee cutoff=>b.graph=2 ∧ b.upperSeed.isSome=true ∧ 3*b.width<p ∧ NodeBudget.Valid h b.width cutoff fee ∧
      pay true fee 0 0≤target

instance {l h} (b:Row l h) (m:Book) (G:ℕ):Decidable (b.check m G):=by
  unfold Row.check;cases b.method <;>infer_instance

def lowBranch (m:Method) (wt:ℕ):Prop:=match m with | .node _ cutoff=>wt<cutoff | _=>True

theorem native_prime {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive):Prime N.poly:=by
  classical
  let _:=UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Equation)
  let _:=UniqueFactorizationMonoid.toNormalizedGCDMonoid Equation
  letI : UniqueFactorizationMonoid Jet:=Polynomial.uniqueFactorizationMonoid (D:=Equation)
  exact (NativeWitnessBank.irreducible N gp).prime

theorem Row.proves {first last} (b:Row first last) {m:Book} {GCap:ℕ} (ok:b.check m GCap)
    {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (P:Prefix6969Early.Packet F Crt m.fee m.ordinateCredit m.seedCredit GCap m.seedMass)
    (start:2314≤first) (stop:last≤2557) (lo:first≤M.overhead.toNat) (hi:M.overhead.toNat≤last)
    (pr:ProjectedProduct P.parents P.projected) (e:b.lowerGrade≤P.projected.natDegree) (E:P.projected.natDegree≤b.upperGrade)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (a:G.graphDegree=b.graph)
    (ctrl:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets P.parents) b.content)
    (lower:b.lowerSeed≤seedDegree N.poly) (upper:∀v,b.upperSeed=some v→seedDegree N.poly≤v)
    (phys:HelperPhysicalModel.Model Crt N.poly)
    (weight:b.weight≤RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw)
    (branch:lowBranch b.method (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw))
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈Γ,MarkResidues D (M.label z) (F.scalar z)): Γ.card≤target:=by
  classical
  obtain ⟨thresh,gc,offSmall,offChar,pay⟩:=ok
  obtain ⟨onEq,J,seen,off,offBound,total⟩:=NearTerminal.partition P.geo pr b.content (thresh.trans_le e) N gp ctrl
  obtain ⟨S⟩:=OffFirst.parts F P.parents N.poly (Or.inl pr) (Or.inl seen.1) off (OrdinaryGeometry.remaining_marks P)
  let d:=131071+last
  let c:=b.cap m
  have safe:M.overhead.toNat≤2557:=hi.trans stop
  have age:0<M.overhead.toNat:=by omega
  have gcop:∀q∈NearBook.owning N.poly P.parents,Parent q:=fun q h=>P.geo q (mem_filter.mp h).1
  have passes:=fun q (h:q∈NearBook.owning N.poly P.parents)=>P.terminal q (mem_filter.mp h).1
  have ytop: onEq.natDegree≤P.projected.natDegree:=NearTerminal.subset_degree (filter_subset ..) seen.1 pr
  have topDiv:onEq∣P.projected:=NativeOrdinateMass.divides_of_member seen.1 (fun q h=>pr.vanishes q (mem_filter.mp h).1)
  have topSeed:K1_14_4.seedDegree onEq≤m.seedMass:=((JointProjection.remainder (Or.inl pr) topDiv).2).trans P.seed_cap
  obtain ⟨gcap,vcap⟩:=OrdinaryBounds.sound b.sources Crt (word M) age (by omega) lo hi gcop passes N gp a
    seen lower upper phys weight (⟨b.upperGrade,m.seedMass⟩:OrdinaryBounds.Cap) (ytop.trans E) topSeed
  change onEq.natDegree≤c.grade at gcap
  change K1_14_4.seedDegree onEq≤c.seed at vcap
  have yg: S.onEq.natDegree≤c.grade:=(natDegree_le_of_dvd S.divides seen.1.primitive.ne_zero).trans gcap
  have vz: K1_14_4.seedDegree S.onEq≤c.seed:=((JointProjection.remainder (Or.inl seen.1) S.divides).2).trans vcap
  rw [a] at offBound
  have endD:131071+M.overhead≤(d:ℤ):=by dsimp [d];omega
  have dp:0<d:=by dsimp [d];omega
  have gap:d<179730:=by dsimp [d];omega
  have tame:d<p:=by change 131071+last<2130706433;omega
  have within:S.onLabels⊆Γ:=S.onSub.trans sdiff_subset
  have laws:=OrdinaryGeometry.laws P N S gp
  have cover:=OrdinaryGeometry.owners P N S
  have value (yes:b.upperSeed.isSome=true):seedDegree N.poly≤b.width:=
    upper _ (by cases hs:b.upperSeed <;>simp_all [Row.width])
  have spend (mode:Bool) (K₀ y z:ℤ) (on:(S.onLabels.card:ℤ)≤K₀+y*S.onEq.natDegree+z*K1_14_4.seedDegree S.onEq)
      (paid:OrdinaryLedger.due m GCap b.off b.lowerGrade c.grade c.seed mode K₀ y z ≤target):Γ.card≤target:=by
    have fee:=OrdinaryGeometry.invoice P N S safe gc off offBound offSmall offChar e yg vz mode K₀ y z (by
      have pos:(0:ℤ)≤(GCap:ℤ)^2:=sq_nonneg _
      linarith only [on,pos])
    exact_mod_cast fee.trans paid
  cases tag:b.method with
  | excluded=>
    rw [tag] at pay
    change c.grade<b.lowerGrade-(b.content-b.graph) at pay
    omega
  | marked=>
    rw [tag] at pay
    obtain ⟨legal,char,paid⟩:=pay
    have counted:=JointMarked.owned_count F within safe S.onEq S.primitive S.separable (yg.trans_lt legal) le_rfl
      ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 yg) _) vz).trans_lt char) S.onRoots
    have degreeCap:S.onEq.natDegree≤GCap:=((Nat.le_add_left ..).trans_eq S.degree).trans P.degree_cap
    have marked:=counted.trans (GraphLedger.marked_fee yg degreeCap gc)
    have cost:=OrdinaryGeometry.invoice P N S safe gc off offBound offSmall offChar e yg vz true (c.grade^2:ℕ) 0
      (JointLedger.coefficient c.grade) (by
        by_cases zero:c.grade=0
        · have no:S.onEq.natDegree=0:=by omega
          have cnt:S.onLabels.card=0:=Nat.eq_zero_of_le_zero (by simpa [no,JointMarked.price] using counted)
          rw [cnt];positivity
        · rw [if_neg zero] at marked
          have ma:(S.onLabels.card:ℤ)≤JointLedger.coefficient c.grade*(K1_14_4.seedDegree S.onEq:ℤ)+(GCap:ℤ)^2:=by exact_mod_cast marked
          have sq:(0:ℤ)≤(c.grade:ℤ)^2:=sq_nonneg _
          push_cast
          linarith only [ma,sq])
    exact_mod_cast cost.trans paid
  | affine=>
    rw [tag] at pay
    obtain ⟨lin,yes,char,paid⟩:=pay
    have cap:= (K1_14_2_2_2_1.seedDegree_le ..).mp ((value yes).trans (le_max_right 1 b.width))
    have bound:∀j i,(N.poly.coeff j).coeff i∈MvPolynomial.restrictWeightAtMost (fun _=>1) (max 1 b.width):=by
      intro j i;apply MvPolynomial.mem_restrictWeightAtMost.mpr;intro v hv
      rw [←Finsupp.degree_eq_weight_one];exact (MvPolynomial.le_totalDegree hv).trans (cap j i)
    have all:=NativeAffineTariff.price_floor F within N gp (a.trans lin) _ (by omega) bound char d endD tame dp gap (by decide) cover
    apply spend _ _ _ _ _ paid
    simpa only [d,Int.zero_mul,Int.add_zero] using (show (S.onLabels.card:ℤ)≤(WholeAffine.fee d (max 1 b.width):ℤ) by exact_mod_cast all)
  | surface=>
    rw [tag] at pay
    obtain ⟨nl,yes,char,paid⟩:=pay
    have bound:=(K1_14_2_2_2_1.seedDegree_le ..).mp (value yes)
    have root z (hz:z∈S.onLabels):WordRates.ev F z S.onEq=0:=by
      simpa [WordRates.ev,Research6966.NonlinearMarkRows.evaluate,NativeSurfaceCount.label,K1_14.graphEval,Polynomial.eval_map] using S.onRoots z hz
    have all:=WordRates.on_surface F N gp (nl.trans_eq a.symm) bound (a ▸ char) within endD dp gap tame S.nz laws root
    rw [a,FastHeight.side_eq,FastHeight.ordinate_eq d _ gap] at all
    apply spend _ _ _ _ _ paid
    exact_mod_cast all.trans_eq (by dsimp [Row.bad,Row.x,Row.y,d];ring)
  | ambient=>
    rw [tag] at pay
    obtain ⟨nl,yes,char,paid⟩:=pay
    have all:=WordRates.ambient F N gp (nl.trans_eq a.symm) ((K1_14_2_2_2_1.seedDegree_le ..).mp (value yes))
      (a ▸ char) within endD dp gap tame laws
    rw [a,FastHeight.side_eq,FastHeight.ordinate_eq d _ gap] at all
    apply spend _ _ _ _ _ paid
    simpa [Row.bad,Row.x,Row.y,d] using (show (S.onLabels.card:ℤ)≤
      ((b.bad+3*b.y*b.x^2:ℕ):ℤ) by exact_mod_cast all)
  | node fee cutoff=>
    rw [tag] at pay branch
    obtain ⟨q,yes,char,ok,paid⟩:=pay
    have source:=NodeBudget.family F within rfl age hi stop phys (native_prime N gp) (NativeGraphMarks.slope_degree N gp)
      ((HelperWeightCap.native_degree N gp).trans (a.trans q)) char ((K1_14_2_2_2_1.seedDegree_le ..).mp (value yes))
      nodes (fun z hz=>res z (within hz)) (by intro z hz;obtain ⟨p,hp,hit,atQ⟩:=cover z hz;exact atQ N.poly hit) branch ok
    apply spend _ _ _ _ _ paid
    simpa using (show (S.onLabels.card:ℤ)≤fee by exact_mod_cast source)

end
end Research6969.OrdinaryCell
end Z6969Source0867

-- Source: Research6969.PowerExclusion
section Z6969Source0868
set_option autoImplicit true
namespace Research6969.PowerExclusion
noncomputable section
open Finset Module Polynomial
open K1 (p)
open K1_14 (Shape Equation FX L)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField SeedClosure)
open Research6966
open KoalaRect (area rectDebit rectCapacity rectPower rectEvaluated)
open PowerBox (residual grade_le boundGrade)
open scoped Classical
set_option maxHeartbeats 2400000
set_option maxRecDepth 14000

structure Case where
  bank:P1_7.Bank
  grade:ℕ
  graph:ℕ
  hits:ℕ
  weight:ℕ
  seed:ℕ
abbrev A:ℕ:=179730
abbrev side:ℕ:=265410
abbrev box : Fin 2→ℕ:=fun _=>side
abbrev Case.shape (b:Case):=b.bank.shape
abbrev Case.N (b:Case):=b.shape.m*A
abbrev Case.maxK (b:Case):=b.shape.J+b.shape.B/b.grade+1

def maxW (b:Case) (lo k:ℕ):=b.N-2*lo*(k-1)-1
def caseCost (b:Case) (lo hi k:ℕ):ℕ:=
  let W:=maxW b lo k
  let cap:=boundGrade b.shape.B b.shape.J W (131071-hi)
  let t:=Pade.layers b.graph b.hits cap b.shape.J k
  min (SpreadWindow.lex cap b.shape.J b.grade k * area box)
    (residual (131071-hi) W b.shape.B b.shape.J b.grade k t b.graph b.weight side b.seed)
def total (b:Case) (lo hi:ℕ) := HelperWindowGrouping.sumCount (fun i=>caseCost b lo hi (i+1)) b.maxK
def due (b:Case) (h fee:ℕ):=rectDebit h b.bank.nodeRows b.bank.poleMoment box+2*h*fee
def supply (b:Case) (h:ℕ):=area box*HelperWindowPrefix.volume b.N b.shape.B b.shape.J (131071-h)
def Positive (b:Case) (lo hi:ℕ):Prop:=
  due b lo (total b lo hi)<supply b lo ∧ due b hi (total b lo hi)<supply b hi
instance (b:Case) (lo hi:ℕ):Decidable (Positive b lo hi):=by unfold Positive;infer_instance

private theorem supply_eq (b:Case) {h:ℕ} (narrow:b.shape.J<131071-h):
    supply b h=area box*SpreadBucket.raw b.shape A h := by
  unfold supply SpreadBucket.raw
  rw [HelperWindowPrefix.volume_eq_shapeSum _ _ _ narrow]
  congr 2
  funext q j
  rw [Nat.mul_comm (131071-h)]

theorem positive_height (b:Case) {lo hi h:ℕ} (left:lo≤h) (right:h≤hi)
    (hiD:hi≤131071) (narrow:b.shape.J<131071-hi) (full:b.shape.B*(131071-lo)≤b.N)
    (cert:Positive b lo hi):due b h (total b lo hi)<area box*SpreadBucket.raw b.shape A h := by
  let fee:=total b lo hi
  let B:=(box 0+box 1+2)*b.bank.poleMoment+2*fee
  have charge (t:ℕ):due b t fee=area box*b.bank.nodeRows+t*B:=by unfold due rectDebit B;ring
  have source (t:ℕ) (l:lo≤t) (r:t≤hi):area box*SpreadBucket.raw b.shape A t=
      area box*SpreadBucket.raw b.shape A lo+(t-lo)*(area box*SpreadBucket.slope b.shape):=by
    rw [SpreadBucket.raw_affine l (r.trans hiD) full];ring
  obtain ⟨first,last⟩:=cert
  change due b lo fee<_ at first
  change due b hi fee<_ at last
  rw [charge,supply_eq b (narrow.trans_le (Nat.sub_le_sub_left (left.trans right) _))] at first
  rw [charge,supply_eq b narrow,source hi (left.trans right) le_rfl] at last
  rw [charge,source h left right]
  exact SpreadBucket.affine_pos left right first last

/-- The physical bank alone rules out these actual projected sheets.
The primitive polynomial, the chart, and all of the sheets are fixed
before the interpolation cutoff is chosen. -/
theorem excluded (b:Case) {lo hi h:ℕ} (hp:0<h) (left:lo≤h) (right:h≤hi) (hiD:hi<131071)
    (narrow:b.shape.J<131071-hi) (full:b.shape.B*(131071-lo)≤b.N)
    (size:b.N<p) (nonzero:0<b.N) (rank:P3_7_1.BankOK b.bank) (within:side+side≤b.shape.U)
    (ep:0<b.grade) (cert:Positive b lo hi) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {env:Shape} (fits:TerminalBanks.inside b.shape env) {parents:Finset Surface}
    (geo:∀q∈parents,Parent q) (pass:∀q∈parents,TerminalBanks.Pass Crt word A env q)
    {f:Equation} (pr:ProjectedProduct parents f) (grade:b.grade≤f.natDegree)
    {G:Pade.Row SeedField} (gp:G.primitive) (eq:G.graphDegree=b.graph) (native:PadeNativeQuotient.Native G)
    (physical:HelperPhysicalModel.Model Crt native.poly)
    (wt:b.weight≤RawPhysicalDegree.weight (131071-h) (131071-h-1) physical.raw)
    (seed:b.seed≤K1_14_2_2_2_1.seedDegree native.poly)
    (ys:Finset SeedClosure) (v:SeedClosure→SeedClosure) (num:ys.card=b.hits) (many:2*b.graph-1<b.hits)
    (sheets:∀y∈ys,(∃q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧
      (G.map (algebraMap SeedField SeedClosure)).err v y=0) : False := by
  classical
  obtain ⟨M,same⟩:=SharedPhysicalModel.compatible Crt gp native physical
  let F:=fun W=>finrank FX (rectEvaluated Crt word b.shape W box)
  have hl:h≤131070:=by omega
  have step:0<131071-hi:=by omega
  have sw:131071-hi≤131071-h:=Nat.sub_le_sub_left right _
  have wp:0<131071-h:=step.trans_le sw
  have basis:K1_14_1.rawWidthCond h b.shape (b.N-1):=by
    intro q hq j _
    rw [Nat.sub_add_cancel nonzero]
    exact (Nat.mul_le_mul hq (Nat.sub_le_sub_left left _)).trans (full.trans (Nat.le_add_right ..))
  have floor:=KoalaRect.rectRankFloor hp hl (hl.trans_lt (by decide)) Crt word b.shape (b.N-1) box within
    rank.moment.2 basis rank.nodes.le rank.moment.1
  rw [Nat.sub_add_cancel nonzero] at floor
  have lex (W:ℕ) (hw:W<b.N):F W≤rectCapacity A h b.shape b.grade box (fun _=>0) W:=by
    apply KoalaRect.rectCutoff_finrank_le _ _ _ _ _ _ _ _ pr.primitive.ne_zero grade wp ep
    · intro P hP;exact K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word b.shape W box hP)
    · intro P hP;exact KoalaRect.rectEvaluated_axis Crt word hP
    · intro P hP hn;exact P0_10_1.leading_bound hp hl Crt word b.shape W P (KoalaRect.rectEvaluated_le Crt word b.shape W box hP) hn
    · intro P hP hn;exact KoalaRect.rectDivides hp Crt word A b.shape box size geo (fun q hq=>pass q hq _ fits) pr hw hP hn
    · intro z;simpa [KoalaRect.rectSlots,area] using KoalaRect.rectSlots_antitone box (KoalaRect.axisDegree f) (Nat.zero_le z)
  have live (W:ℕ) (hw:W<b.N) : F W≤caseCost b lo hi (rectPower A h b.shape W):=by
    let k:=rectPower A h b.shape W
    let r:=(b.N-1-W)/(2*h)
    have kr:k=r+1:=Nat.add_comm ..
    have div:r*(2*h)≤b.N-1-W:=Nat.div_mul_le_self ..
    have issued:W+2*h*r<b.N:=by rw [Nat.mul_comm (2*h) r];omega
    have rangeW:W≤maxW b lo k:=by
      unfold maxW;rw [kr,Nat.add_sub_cancel]
      have lower:=Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 left)
      omega
    let cap:=boundGrade b.shape.B b.shape.J (maxW b lo k) (131071-hi)
    apply le_min ((lex W hw).trans (SpreadWindow.rect_lex A h b.grade k W cap b.shape box wp ep rfl
      (fun j hj=>grade_le step sw rangeW hj)))
    have upper:min b.shape.B ((W+b.shape.J)/(131071-h))≤cap:=by
      let n:=min b.shape.B ((W+b.shape.J)/(131071-h))
      have l:n*(131071-h)≤W+b.shape.J:=(Nat.le_div_iff_mul_le wp).mp (min_le_right ..)
      exact le_min (min_le_left ..) ((Nat.le_div_iff_mul_le step).mpr
        (((Nat.mul_le_mul_left n sw).trans l).trans (Nat.add_le_add_right rangeW _)))
    have safe:r+1<p:=by have le:r≤b.N-1-W:=Nat.div_le_self ..;omega
    have ord:2*G.graphDegree-1<ys.card:=by rwa [eq,num]
    have hraw:=PadeResidualBank.concentration_rank hp hl Crt word box fits safe issued geo pass pr grade gp M native ys v sheets ord cap upper
    rw [eq,num,←kr,same] at hraw
    exact hraw.trans (PowerBox.residual_le _ step sw rangeW wt (seed.trans (PowerBox.seed_sum _)))
  have cap:=SpreadBucket.sum_by_order (scale:=1) (K:=b.maxK) hp F (caseCost b lo hi)
    (fun W hw _=>by simpa only [one_mul] using live W hw)
    (fun W hw far=>Nat.eq_zero_of_le_zero ((lex W hw).trans_eq (SpreadWindow.rect_zero A h b.grade W b.shape box wp ep far)))
  have sum_eq:(∑ k∈range b.maxK,caseCost b lo hi (k+1))=total b lo hi:=
    (HelperWindowGrouping.sumCount_eq ..).symm
  rw [one_mul,sum_eq] at cap
  change area box*SpreadBucket.raw b.shape A h≤rectDebit h b.bank.nodeRows b.bank.poleMoment box+∑ W∈range b.N,F W at floor
  exact (Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left cap _))) (positive_height b left right hiD.le narrow full cert)

end
end Research6969.PowerExclusion
end Z6969Source0868

-- Source: Research6969.PowerSheets
section Z6969Source0869
set_option autoImplicit true
namespace Research6969.PowerSheets
noncomputable section
open Research6966 PowerExclusion Finset Polynomial
open K1 (I)
open K1_14 (L Shape Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField SeedClosure)
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

def entry (e a off lower wt:ℕ):Case:=
  ⟨⟨Research6969.SpreadCatalogue.shape,Research6969.SpreadCatalogue.nodes,Research6969.SpreadCatalogue.moment⟩,
  e,a,e-off,wt,lower⟩

theorem prohibit_on {firstHeight lastHeight e a off lower wt:ℕ} {ends:List ℕ}
    (checked:PhysicalWindow.Cover (Positive (entry e a off lower wt)) lastHeight firstHeight ends) (start:2314≤firstHeight) (finish:lastHeight≤2557)
    (ep:0<e) (many:2*a-1<e-off) {h} {D:PoleData h} (Crt:CRTLift D) (word:I→L)
    (lo:firstHeight≤h) (hi:h≤lastHeight) (S:Finset Surface) (has:S.Nonempty) (geo:∀q∈S,Parent q)
    (pass:∀q∈S,TerminalBanks.Pass Crt word A Research6969.SpreadCatalogue.shape q)
    {f:Equation} (whole:ProjectedProduct S f) (degree:e≤f.natDegree)
    {G:Pade.Row SeedField} (native:PadeNativeQuotient.Native G) (gp:G.primitive) (grade:G.graphDegree=a)
    (physical:HelperPhysicalModel.Model Crt native.poly)
    (weight:wt≤RawPhysicalDegree.weight (131071-h) (131071-h-1) physical.raw)
    (seed:lower≤K1_14_2_2_2_1.seedDegree native.poly)
    (control:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) (off+a)) : False := by
  classical
  obtain ⟨f',T,v,pr,size,sheets⟩:=Pade.Native.projected_sheets S has geo
  let on:=T.filter (fun y=>(G.map (algebraMap SeedField Pade.Native.Sep)).err v y=0)
  let away:=T\on
  have miss:=control away v (by
    intro y hy
    obtain ⟨mem,bad⟩:=mem_sdiff.mp hy
    exact ⟨sheets y mem,fun zero=>bad (mem_filter.mpr ⟨mem,zero⟩)⟩)
  rw [Pade.Row.degree_map,grade] at miss
  have total:on.card+away.card=T.card:=by
    rw [Nat.add_comm]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have sz:e≤T.card:=degree.trans_eq ((NearTerminal.same_degree whole pr).trans size.symm)
  obtain ⟨kept,sub,keepSize⟩:=exists_subset_card_eq (show e-off≤on.card by omega)
  let emb:Pade.Native.Sep→+*SeedClosure:=(separableClosure SeedField SeedClosure).val.toRingHom
  let pts:=kept.image emb
  let velocity (z:SeedClosure):=if H:∃y∈kept,emb y=z then emb (v H.choose) else 0
  have atPoint y (hy:y∈kept):velocity (emb y)=emb (v y):=by
    have H:∃z∈kept,emb z=emb y:=⟨y,hy,rfl⟩
    simp only [velocity,dite_eq_left H,emb.injective H.choose_spec.2]
  have n:pts.card=e-off:=(card_image_of_injective _ emb.injective).trans keepSize
  let b:=entry e a off lower wt
  have rank:P3_7_1.BankOK b.bank:=⟨Research6969.SpreadCatalogue.node_eq,Research6969.SpreadCatalogue.pole_cap,
    by change 4184<K1.p;decide⟩
  obtain ⟨l,r,first,lh,hr,rhi,pos⟩:=PhysicalWindow.covered_from checked lo hi
  have wide : b.shape.B*(131071-l)≤b.N := by
    change 4184*(131071-l)≤3000*179730
    exact (Nat.mul_le_mul_left 4184 (Nat.sub_le_sub_left (start.trans first) _)).trans (by decide)
  have narrow:b.shape.J<131071-r:=by change 900<131071-r;omega
  have fits:TerminalBanks.inside b.shape Research6969.SpreadCatalogue.shape:=by
    change 0<3000 ∧ 4184≤4184 ∧ 900≤900 ∧ 530820≤530820
    decide
  refine PowerExclusion.excluded b (by omega) lh hr (by omega) narrow wide (by change 3000*179730<K1.p;decide)
    (by change 0<3000*179730;decide) rank (by change 265410+265410≤530820;decide)
    ep pos Crt word fits geo pass whole degree gp grade native physical weight seed pts velocity n many ?_
  intro y hy
  obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
  obtain ⟨tz,ok⟩:=mem_filter.mp (sub hz)
  rw [atPoint z hz]
  refine ⟨(Pade.Native.sheets_iff S z (v z)).mp (sheets z tz),?_⟩
  change (G.a.map (algebraMap SeedField SeedClosure)).eval (emb z)*velocity (emb z)-
    (G.b.map (algebraMap SeedField SeedClosure)).eval (emb z)=0
  rw [atPoint z hz]
  have lifted (Q:Polynomial SeedField):
      emb ((Q.map (algebraMap SeedField Pade.Native.Sep)).eval z)=(Q.map (algebraMap SeedField SeedClosure)).eval (emb z):=by
    rw [eval_map,eval_map]
    exact (Polynomial.aeval_algHom_apply (separableClosure SeedField SeedClosure).val z Q).symm
  have law:=congrArg emb ok
  simp only [Pade.Row.err,Pade.Row.map,map_sub,map_mul,map_zero] at law
  rwa [lifted,lifted] at law

theorem prohibit {e a off lower wt:ℕ} {ends:List ℕ}
    (checked:PhysicalWindow.Cover (Positive (entry e a off lower wt)) 2411 2314 ends)
    (ep:0<e) (many:2*a-1<e-off) {h} {D:PoleData h} (Crt:CRTLift D) (word:I→L)
    (lo:2314≤h) (hi:h≤2411) (S:Finset Surface) (has:S.Nonempty) (geo:∀q∈S,Parent q)
    (pass:∀q∈S,TerminalBanks.Pass Crt word A Research6969.SpreadCatalogue.shape q)
    {f:Equation} (whole:ProjectedProduct S f) (degree:e≤f.natDegree)
    {G:Pade.Row SeedField} (native:PadeNativeQuotient.Native G) (gp:G.primitive) (grade:G.graphDegree=a)
    (physical:HelperPhysicalModel.Model Crt native.poly)
    (weight:wt≤RawPhysicalDegree.weight (131071-h) (131071-h-1) physical.raw)
    (seed:lower≤K1_14_2_2_2_1.seedDegree native.poly)
    (control:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) (off+a)) : False :=
  prohibit_on checked (by decide) (by decide) ep many Crt word lo hi S has geo pass whole degree native gp grade physical weight seed control


end
end Research6969.PowerSheets
end Z6969Source0869

-- Source: Research6969.OrdinaryRoute
section Z6969Source0870
set_option autoImplicit true
namespace Research6969.OrdinaryRoute
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L)
open K1_14_1 (CRTLift PoleData MarkResidues poleProduct)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface SeedField ProjectedProduct)
open Lower6960
open Far6969RescueGeometry (Model Family word)
open Research6966
open JointLedger (Book)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

structure Context (first last:ℕ) (m:Book) (g:ℕ) where
  words:P1.Words
  del:Finset I
  model:Model words del
  labels:Finset K
  family:Family model labels
  poles:PoleData model.overhead.toNat
  crt:CRTLift poles
  packet:Prefix6969Early.Packet family crt m.fee m.ordinateCredit m.seedCredit g m.seedMass
  projected:ProjectedProduct packet.parents packet.projected
  nonempty:packet.parents.Nonempty
  graph:Pade.Row SeedField
  native:PadeNativeQuotient.Native graph
  primitive:graph.primitive
  physical:HelperPhysicalModel.Model crt native.poly
  content:ℕ
  control:Pade.Controls (graph.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets packet.parents) content
  starts:2314≤first
  stops:last≤2557
  lowHeight:first≤model.overhead.toNat
  highHeight:model.overhead.toNat≤last
  nodes:∀i:I,(poleProduct poles).eval (algebraMap K L (K1.node i))≠0
  residues:∀z∈labels,MarkResidues poles (model.label z) (family.scalar z)

structure Region where
  gradeLo:ℕ
  gradeHi:ℕ
  content:ℕ
  graph:ℕ
  lowSeed:ℕ
  highSeed:Option ℕ
deriving DecidableEq

def region {first last} (x:OrdinaryCell.Row first last):Region:=
  ⟨x.lowerGrade,x.upperGrade,x.content,x.graph,x.lowerSeed,x.upperSeed⟩

def Matches {first last m g} (x:Context first last m g) (r:Region):Prop:=
  r.gradeLo≤x.packet.projected.natDegree ∧ x.packet.projected.natDegree≤r.gradeHi ∧ x.content=r.content ∧
  x.graph.graphDegree=r.graph ∧ r.lowSeed≤seedDegree x.native.poly ∧ ∀v,r.highSeed=some v→seedDegree x.native.poly≤v

abbrev Done (first last:ℕ) (m:Book) (g:ℕ) (r:Region):Prop:=
  ∀x:Context first last m g,Matches x r→x.labels.card≤OrdinaryCell.target

def baseline (last degree:ℕ):ℕ:=degree*(131071-last)-1
def actualWeight {first last m g} (x:Context first last m g):=
  RawPhysicalDegree.weight (131071-x.model.overhead.toNat) (131071-x.model.overhead.toNat-1) x.physical.raw

theorem base {first last m g} (x:Context first last m g):baseline last x.graph.graphDegree≤actualWeight x:=by
  have step:x.model.overhead.toNat<131071:=x.highHeight.trans_lt (x.stops.trans_lt (by decide))
  have raw:=HelperWeightCap.weight_lower x.physical x.native.primitive.ne_zero (131071-x.model.overhead.toNat) (by omega)
  rw [HelperWeightCap.native_degree x.native x.primitive,NativeGraphMarks.slope_degree x.native x.primitive] at raw
  have mul:=Nat.mul_le_mul_right x.graph.graphDegree (Nat.sub_le_sub_left x.highHeight 131071)
  unfold baseline actualWeight
  rw [Nat.mul_comm x.graph.graphDegree]
  omega

def Free (m:OrdinaryCell.Method):Prop:=match m with | .node _ _=>False | _=>True
def Below (m:OrdinaryCell.Method) (cut:ℕ):Prop:=match m with | .node _ c=>cut≤c | _=>True
instance (m:OrdinaryCell.Method):Decidable (Free m):=by cases m <;> unfold Free <;> infer_instance
instance (m:OrdinaryCell.Method) (cut:ℕ):Decidable (Below m cut):=by cases m <;> unfold Below <;> infer_instance
private theorem free_at {m w} (f:Free m):OrdinaryCell.lowBranch m w:=by cases m <;>simp_all [Free,OrdinaryCell.lowBranch]
private theorem below_at {m cut w} (f:Below m cut) (lt:w<cut):OrdinaryCell.lowBranch m w:=by
  cases m <;>simp_all [Below,OrdinaryCell.lowBranch] <;>omega

theorem apply_row {first last m g} (x:Context first last m g) (b:OrdinaryCell.Row first last)
    (ok:b.check m g) (facts:Matches x (region b)) (w:b.weight≤actualWeight x)
    (allowed:OrdinaryCell.lowBranch b.method (actualWeight x)):x.labels.card≤OrdinaryCell.target:=by
  obtain ⟨lo,hi,ct,a,low,upper⟩:=facts
  change x.content=b.content at ct
  exact b.proves ok x.family x.crt x.packet x.starts x.stops x.lowHeight x.highHeight x.projected lo hi x.native x.primitive
    a (by rw [←ct];exact x.control) low upper x.physical w allowed x.nodes x.residues

theorem plain {first last m g} (b:OrdinaryCell.Row first last) (ok:b.check m g)
    (weight:b.weight≤baseline last b.graph) (free:Free b.method):Done first last m g (region b):=by
  intro x h
  have deg:x.graph.graphDegree=b.graph:=h.2.2.2.1
  exact apply_row x b ok h (weight.trans (deg ▸ base x)) (free_at free)

theorem physical {first last m g} (b c:OrdinaryCell.Row first last) (ok:b.check m g) (more:c.check m g)
    (eq:region b=region c) (cut:ℕ) (weight:b.weight≤baseline last b.graph) (above:c.weight≤cut)
    (less:Below b.method cut) (free:Free c.method):Done first last m g (region b):=by
  intro x h
  have deg:x.graph.graphDegree=b.graph:=h.2.2.2.1
  by_cases low:actualWeight x<cut
  · exact apply_row x b ok h (weight.trans (deg ▸ base x)) (below_at less low)
  · exact apply_row x c more (eq ▸ h) (above.trans (by omega)) (free_at free)

theorem power {first last m g} (r:Region) (wt:ℕ) {ends:List ℕ} (floor:wt≤baseline last r.graph)
    (cert:PhysicalWindow.Cover (PowerExclusion.Positive (PowerSheets.entry r.gradeLo r.graph
        (r.content-r.graph) r.lowSeed wt)) last first ends)
    (large:0<r.gradeLo) (many:2*r.graph-1<r.gradeLo-(r.content-r.graph)) (fits:r.graph≤r.content):
    Done first last m g r:=by
  intro x h
  obtain ⟨lo,_,ct,a,seed,_⟩:=h
  have weights:wt≤actualWeight x:=floor.trans (a ▸ base x)
  have eq:r.content-r.graph+r.graph=x.content:=(Nat.sub_add_cancel fits).trans ct.symm
  exact (PowerSheets.prohibit_on cert x.starts x.stops large many x.crt (word x.model) x.lowHeight x.highHeight
    x.packet.parents x.nonempty x.packet.geo x.packet.terminal x.projected lo x.native x.primitive a x.physical weights seed
    (eq ▸ x.control)).elim

/-- The following cells cover all integer seed degrees from `lo` upwards. -/
def Tail (first last:ℕ) (m:Book) (g e top c a lo:ℕ):Prop:=
  Done first last m g ⟨e,top,c,a,lo,none⟩

theorem join {first last m g e top c a lo hi} (left:Done first last m g ⟨e,top,c,a,lo,some hi⟩)
    (tail:Tail first last m g e top c a (hi+1)):Tail first last m g e top c a lo:=by
  intro x h
  obtain ⟨l,t,ct,graph,seed,_⟩:=h
  by_cases atLeft:seedDegree x.native.poly≤hi
  · exact left x ⟨l,t,ct,graph,seed,fun v eq=>by have same:hi=v:=Option.some.inj eq;simpa [←same] using atLeft⟩
  · exact tail x ⟨l,t,ct,graph,by change hi+1≤seedDegree x.native.poly;omega,by simp⟩

end
end Research6969.OrdinaryRoute
end Z6969Source0870

-- Source: Research6969.Ordinary
section Z6969Source0871
set_option autoImplicit true
namespace Research6969.Ordinary
noncomputable section
open Finset Polynomial
open K1 (K p)
open K1_14 (Equation jetAt atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface SeedField ProjectedProduct Parent)
open Lower6960.Far6969RescueGeometry (Model Family OnSurface word)
open Research6966
open JointLedger (Book markedDebit)
open scoped Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem small {u del} {M:Model u del} {Γ} (F:Family M Γ) (hi:M.overhead.toNat≤2557) (paid:Finset K)
    {parents:Finset Surface} {f:Equation} (pr:JointProjection.Product parents f)
    (cover:∀z∈Γ,z∈paid ∨ ∃q∈parents,OnSurface F q z)
    (m:Book) (bill:paid.card+m.ordinateCredit*f.natDegree+m.seedCredit*K1_14_4.seedDegree f≤m.fee)
    (vCap:K1_14_4.seedDegree f≤m.seedMass) {e limit:ℕ} (grade:f.natDegree≤e) (small:e<64)
    (guard:(2*e-1)*m.seedMass<p) (table:∀i:Fin (e+1),m.fee+markedDebit m i.val≤limit+m.ordinateCredit*i.val):
    Γ.card≤limit:=by
  classical
  let S:=Γ\paid
  have sub:S⊆Γ:=sdiff_subset
  have words:=JointMarked.owned_count F sub hi f pr.primitive pr.separable (grade.trans_lt small) le_rfl
    ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 grade) _) vCap).trans_lt guard) (by
      intro z hz
      obtain ⟨q,hq,on⟩:=(cover z (sub hz)).resolve_left (mem_sdiff.mp hz).2
      simpa [jetAt,Polynomial.eval_map] using on (C f) (pr.vanishes hq))
  have count:=words.trans (JointLedger.marked_le m f.natDegree _ vCap)
  have pay:=table ⟨f.natDegree,by omega⟩
  change m.fee+markedDebit m f.natDegree≤limit+m.ordinateCredit*f.natDegree at pay
  have total:Γ.card≤S.card+paid.card:=card_le_card_sdiff_add_card
  omega

theorem choose_graph {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat}
    (Crt:CRTLift D) (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2557)
    {S:Finset Surface} {f:Equation} (pr:JointProjection.Product S f) (large:22≤f.natDegree)
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt (word M) 179730 SpreadCatalogue.shape q):
    ∃G:Pade.Row SeedField, G.primitive ∧ G.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S)
        (TransitionClassification.content (TransitionClassification.band f.natDegree)):=by
  rcases pr with pr|⟨_,rfl⟩
  · have yes:S.Nonempty:=by
      by_contra no
      have dv:=NativeOrdinateMass.divides_of_member (D:=1) pr (fun q h=>False.elim (no ⟨q,h⟩))
      have zero:=natDegree_le_of_dvd dv (one_ne_zero:(1:Equation)≠0)
      simp only [natDegree_one] at zero
      omega
    exact TransitionClassification.graph_above_twenty_one Crt (word M) lo hi S yes geo pass pr large
  · simp at large

end
end Research6969.Ordinary
end Z6969Source0871

-- Source: Research6969.PrefixMiddlePacketView
section Z6969Source0872
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer
noncomputable section

open K1_14_1 (PoleData CRTLift)
open Far6969RescueGeometry (Model Family)

def Packet.toEarlyPacket {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (P : Packet F Crt) :
    Prefix6969Early.Packet F Crt fee ordCredit seedCredit grade width :=
  ⟨P.paid,P.parents,P.projected,P.project,P.geo,P.terminal,P.degree_cap,P.seed_cap,P.bill,P.cover⟩

end
end Lower6960.Prefix6969MiddleTransfer
end Z6969Source0872

-- Source: Research6969.OrdinaryPackets
section Z6969Source0873
set_option autoImplicit true
namespace Research6969.OrdinaryPackets
noncomputable section
open Finset Polynomial
open K1 (p)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (SeedField ProjectedProduct)
open Lower6960
open Far6969RescueGeometry (Model Family)
open Research6966
open JointLedger (Book markedDebit)
set_option maxRecDepth 9000
set_option maxHeartbeats 1200000

abbrev limit:ℕ:=274779381266040419
abbrev middle:Book:=⟨231373953658241386,6105,131528572298280,1592972508796⟩
abbrev near:Book:=⟨234329630343844473,6143,133994566145700,1590006772040⟩

def prices (b:Book) (cap:ℕ):Bool:=GradeTable.first (fun e=>decide
  (b.fee+markedDebit b e≤limit+b.ordinateCredit*e)) (cap+1)
theorem middle_prices:prices middle 21=true:=by decide +kernel
theorem near_prices:prices near 21=true:=by decide +kernel

theorem reduce {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2557) (b:Book) (e:ℕ)
    (P:Prefix6969Early.Packet F Crt b.fee b.ordinateCredit b.seedCredit e b.seedMass)
    (safe:41*b.seedMass<p) (ok:prices b 21=true) :
    Γ.card≤limit ∨ ProjectedProduct P.parents P.projected ∧ 22≤P.projected.natDegree ∧
      ∃G:Pade.Row SeedField,G.primitive ∧ G.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band P.projected.natDegree) ∧
        Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets P.parents)
          (TransitionClassification.content (TransitionClassification.band P.projected.natDegree)):=by
  by_cases low:P.projected.natDegree≤21
  · apply Or.inl
    exact Ordinary.small F hi P.paid P.project P.cover b P.bill P.seed_cap low (by decide) safe
      (fun i=>of_decide_eq_true (GradeTable.entry ok i.isLt))
  · have large:22≤P.projected.natDegree:=by omega
    have pick:=Ordinary.choose_graph F Crt lo hi P.project large P.geo P.terminal
    rcases P.project with actual|⟨_,zero⟩
    · exact Or.inr ⟨actual,large,pick⟩
    · rw [zero,natDegree_one] at large
      omega

theorem middle_or_graph {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (lo:2412≤M.overhead.toNat) (hi:M.overhead.toNat≤2557) (P:Prefix6969MiddleTransfer.Packet F Crt):
    Γ.card≤limit ∨ ProjectedProduct P.parents P.projected ∧ 22≤P.projected.natDegree ∧
      ∃G:Pade.Row SeedField,G.primitive ∧ G.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band P.projected.natDegree) ∧
        Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets P.parents)
          (TransitionClassification.content (TransitionClassification.band P.projected.natDegree)) :=
  reduce F Crt ((by decide:2314≤2412).trans lo) hi middle 342 P.toEarlyPacket (by decide) middle_prices

end
end Research6969.OrdinaryPackets
end Z6969Source0873

-- Source: Research6969.OrdinaryComplete
section Z6969Source0874
set_option autoImplicit true
namespace Research6969.OrdinaryComplete
noncomputable section
open K1 (K I p)
open K1_14 (L)
open K1_14_1 (PoleData CRTLift poleProduct MarkResidues)
open K1_14_3 (SeedField)
open Lower6960
open Far6969RescueGeometry (Model Family)
open Research6966
open Finset Polynomial
open JointLedger (Book)
open OrdinaryRoute
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 13000

def upper (cap:ℕ) (b:Fin 8):ℕ:=![22,24,27,32,40,49,63,cap] b

theorem upper_band {e cap:ℕ} (room:e≤cap):e≤upper cap (TransitionClassification.band e):=by
  unfold TransitionClassification.band
  split_ifs <;>dsimp [upper] <;>omega

def Catalogue (first last:ℕ) (m:Book) (g:ℕ):Prop:=
  ∀(b:Fin 8) (a:ℕ),0<a→a≤TransitionClassification.maxGraph b→
    Tail first last m g (TransitionClassification.grade b) (upper g b) (TransitionClassification.content b) a 0

theorem count {first last:ℕ} {m:Book} {g:ℕ} (valid:Catalogue first last m g)
    (small:OrdinaryPackets.prices m 21=true) (char:41*m.seedMass<p) (firstFit:2314≤first) (lastFit:last≤2557)
    {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (P:Prefix6969Early.Packet F Crt m.fee m.ordinateCredit m.seedCredit g m.seedMass)
    (lo:first≤M.overhead.toNat) (hi:M.overhead.toNat≤last)
    (noPole:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈Γ,MarkResidues D (M.label z) (F.scalar z)) : Γ.card≤OrdinaryCell.target := by
  rcases OrdinaryPackets.reduce F Crt (firstFit.trans lo) (hi.trans lastFit) m g P char small with done|⟨project,large,G,gp,cap,ctrl⟩
  · exact done
  let b:=TransitionClassification.band P.projected.natDegree
  obtain ⟨N⟩:=PadeNativeQuotient.exists_native gp
  obtain ⟨physical⟩:=HelperPhysicalModel.exists_model Crt (NativeWitnessBank.irreducible N gp)
    (by rw [NativeGraphMarks.slope_degree N gp];decide)
  have nonempty:P.parents.Nonempty:=by
    by_contra empty
    have dvd:=NativeOrdinateMass.divides_of_member (D:=1) project (fun q h=>False.elim (empty ⟨q,h⟩))
    have zero:=natDegree_le_of_dvd dvd (one_ne_zero:(1:K1_14.Equation)≠0)
    simp only [natDegree_one] at zero;omega
  let x:Context first last m g:=⟨u,del,M,Γ,F,D,Crt,P,project,nonempty,G,N,gp,physical,
    TransitionClassification.content b,ctrl,firstFit,lastFit,lo,hi,noPole,res⟩
  have positive:0<G.graphDegree:=by
    unfold Pade.Row.graphDegree
    exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact valid b G.graphDegree positive cap x ⟨TransitionClassification.lower_bound large,upper_band P.degree_cap,
    rfl,rfl,Nat.zero_le _,by simp⟩

end
end Research6969.OrdinaryComplete
end Z6969Source0874

-- Source: Research6969.OrdAuxBanks
section Z6969Source0875
set_option autoImplicit true
namespace Research6969.OrdAuxBanks
abbrev bank0 (u : ℕ) : P1_7.Bank := ⟨⟨720,1001,220,u⟩,11385734430720,28064233768⟩
abbrev bank1 (u : ℕ) : P1_7.Bank := ⟨⟨1200,1669,378,u⟩,53798525730816,221264762670⟩
abbrev bank2 (u : ℕ) : P1_7.Bank := ⟨⟨1450,2020,432,u⟩,90926432911360,453693330393⟩
abbrev bank3 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3621,793,u⟩,532875289296896,4763286079225⟩
abbrev bank4 (u : ℕ) : P1_7.Bank := ⟨⟨2600,3621,819,u⟩,546063062138880,4884209183309⟩
abbrev bank5 (u : ℕ) : P1_7.Bank := ⟨⟨2800,3901,834,u⟩,653560508579840,6296101689637⟩
end Research6969.OrdAuxBanks
end Z6969Source0875

-- Source: Research6969.OrdRanks0To3
section Z6969Source0876
set_option autoImplicit true
namespace Research6969.PackedRanks.OrdRanks0To3
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment1001_220 : P1_7_1.groupedPoleMoment 1001 220 ≤ 28064233768 :=
  _root_.PoleAffine6970.certified 1001 220 28064233768 (by decide) (by decide +kernel)

theorem moment1669_378 : P1_7_1.groupedPoleMoment 1669 378 ≤ 221264762670 :=
  _root_.PoleAffine6970.certified 1669 378 221264762670 (by decide) (by decide +kernel)

theorem moment2020_432 : P1_7_1.groupedPoleMoment 2020 432 ≤ 453693330393 :=
  _root_.PoleAffine6970.certified 2020 432 453693330393 (by decide) (by decide +kernel)

theorem moment3621_793 : P1_7_1.groupedPoleMoment 3621 793 ≤ 4763286079225 :=
  _root_.PoleAffine6970.certified 3621 793 4763286079225 (by decide) (by decide +kernel)

end Research6969.PackedRanks.OrdRanks0To3

namespace Research6969.PackedRanks.OrdRanks0To3
open Research6969.OrdAuxBanks
theorem rank0 (u:ℕ) : P3_7_1.BankOK (bank0 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank0 u).shape (by change 2*220≤720;decide) (by change 720+220≤1001+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (720-2*220) 220=6*11385734430720:=by decide
  change 6*P1_7_1.nodeRows (bank0 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank0 u).shape=262144*P1_7_1_2.sixPerNode (720-2*220) 220 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank0 u).shape=11385734430720; omega, moment1001_220,by change 1001<K1.p;decide⟩
theorem rank1 (u:ℕ) : P3_7_1.BankOK (bank1 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank1 u).shape (by change 2*378≤1200;decide) (by change 1200+378≤1669+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1200-2*378) 378=6*53798525730816:=by decide
  change 6*P1_7_1.nodeRows (bank1 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank1 u).shape=262144*P1_7_1_2.sixPerNode (1200-2*378) 378 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank1 u).shape=53798525730816; omega, moment1669_378,by change 1669<K1.p;decide⟩
theorem rank2 (u:ℕ) : P3_7_1.BankOK (bank2 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank2 u).shape (by change 2*432≤1450;decide) (by change 1450+432≤2020+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1450-2*432) 432=6*90926432911360:=by decide
  change 6*P1_7_1.nodeRows (bank2 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank2 u).shape=262144*P1_7_1_2.sixPerNode (1450-2*432) 432 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank2 u).shape=90926432911360; omega, moment2020_432,by change 2020<K1.p;decide⟩
theorem rank3 (u:ℕ) : P3_7_1.BankOK (bank3 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank3 u).shape (by change 2*793≤2600;decide) (by change 2600+793≤3621+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*793) 793=6*532875289296896:=by decide
  change 6*P1_7_1.nodeRows (bank3 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank3 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*793) 793 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank3 u).shape=532875289296896; omega, moment3621_793,by change 3621<K1.p;decide⟩
end Research6969.PackedRanks.OrdRanks0To3
end Z6969Source0876

-- Source: Research6969.OrdRanks4To5
section Z6969Source0877
set_option autoImplicit true
namespace Research6969.PackedRanks.OrdRanks4To5
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3621_819 : P1_7_1.groupedPoleMoment 3621 819 ≤ 4884209183309 :=
  _root_.PoleAffine6970.certified 3621 819 4884209183309 (by decide) (by decide +kernel)

theorem moment3901_834 : P1_7_1.groupedPoleMoment 3901 834 ≤ 6296101689637 :=
  _root_.PoleAffine6970.certified 3901 834 6296101689637 (by decide) (by decide +kernel)

end Research6969.PackedRanks.OrdRanks4To5

namespace Research6969.PackedRanks.OrdRanks4To5
open Research6969.OrdAuxBanks
theorem rank4 (u:ℕ) : P3_7_1.BankOK (bank4 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank4 u).shape (by change 2*819≤2600;decide) (by change 2600+819≤3621+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*819) 819=6*546063062138880:=by decide
  change 6*P1_7_1.nodeRows (bank4 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank4 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*819) 819 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank4 u).shape=546063062138880; omega, moment3621_819,by change 3621<K1.p;decide⟩
theorem rank5 (u:ℕ) : P3_7_1.BankOK (bank5 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank5 u).shape (by change 2*834≤2800;decide) (by change 2800+834≤3901+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*834) 834=6*653560508579840:=by decide
  change 6*P1_7_1.nodeRows (bank5 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank5 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*834) 834 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank5 u).shape=653560508579840; omega, moment3901_834,by change 3901<K1.p;decide⟩
end Research6969.PackedRanks.OrdRanks4To5
end Z6969Source0877
