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

def side (d u:ℕ):ℕ:=FastCell.ceilRatio (2*262144*d*u) 179740+4
def ordinate (d r:ℕ):ℕ:=FastCell.ceilRatio (2*262144*d*r*(179740-d)+(262144-d)*179740) (179740*(179740-d))+4

theorem side_eq (d u:ℕ):seedWeight d u=side d u:=by
  unfold seedWeight side MarkedAdaptive.price
  rw [show Fintype.card K1.I=262144 from Fintype.card_fin (2^18),FastCell.ratio]
  congr 2
  push_cast
  ring

theorem ordinate_eq (d r:ℕ) (gap:d<179740):ordWeight d r=ordinate d r:=by
  unfold ordWeight ordinate MarkedAdaptive.price
  rw [show Fintype.card K1.I=262144 from Fintype.card_fin (2^18),FastCell.ratio]
  congr 2
  have pos:0<179740-d:=by omega
  have nz:((179740-d:ℕ):ℚ)≠0:=by exact_mod_cast pos.ne'
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
abbrev target:ℕ:=274784969259510674

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
    (start:2293≤first) (stop:last≤2534) (lo:first≤M.overhead.toNat) (hi:M.overhead.toNat≤last)
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
  have safe:M.overhead.toNat≤2534:=hi.trans stop
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
  have gap:d<179740:=by dsimp [d];omega
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
abbrev A:ℕ:=179740
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
    (checked:PhysicalWindow.Cover (Positive (entry e a off lower wt)) lastHeight firstHeight ends) (start:2293≤firstHeight) (finish:lastHeight≤2534)
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
    change 4184*(131071-l)≤3000*179740
    exact (Nat.mul_le_mul_left 4184 (Nat.sub_le_sub_left (start.trans first) _)).trans (by decide)
  have narrow:b.shape.J<131071-r:=by change 900<131071-r;omega
  have fits:TerminalBanks.inside b.shape Research6969.SpreadCatalogue.shape:=by
    change 0<3000 ∧ 4184≤4184 ∧ 900≤900 ∧ 530820≤530820
    decide
  refine PowerExclusion.excluded b (by omega) lh hr (by omega) narrow wide (by change 3000*179740<K1.p;decide)
    (by change 0<3000*179740;decide) rank (by change 265410+265410≤530820;decide)
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
    (checked:PhysicalWindow.Cover (Positive (entry e a off lower wt)) 2389 2293 ends)
    (ep:0<e) (many:2*a-1<e-off) {h} {D:PoleData h} (Crt:CRTLift D) (word:I→L)
    (lo:2293≤h) (hi:h≤2389) (S:Finset Surface) (has:S.Nonempty) (geo:∀q∈S,Parent q)
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
  starts:2293≤first
  stops:last≤2534
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

theorem small {u del} {M:Model u del} {Γ} (F:Family M Γ) (hi:M.overhead.toNat≤2534) (paid:Finset K)
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
    (Crt:CRTLift D) (lo:2293≤M.overhead.toNat) (hi:M.overhead.toNat≤2534)
    {S:Finset Surface} {f:Equation} (pr:JointProjection.Product S f) (large:22≤f.natDegree)
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt (word M) 179740 SpreadCatalogue.shape q):
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

abbrev limit:ℕ:=274784969259510674
abbrev middle:Book:=⟨231373953658241386,6105,131528572298280,1592972508796⟩
abbrev near:Book:=⟨234329630343844473,6143,133994566145700,1590006772040⟩

def prices (b:Book) (cap:ℕ):Bool:=GradeTable.first (fun e=>decide
  (b.fee+markedDebit b e≤limit+b.ordinateCredit*e)) (cap+1)
theorem middle_prices:prices middle 21=true:=by decide +kernel
theorem near_prices:prices near 21=true:=by decide +kernel

theorem reduce {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (lo:2293≤M.overhead.toNat) (hi:M.overhead.toNat≤2534) (b:Book) (e:ℕ)
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
    (lo:2390≤M.overhead.toNat) (hi:M.overhead.toNat≤2534) (P:Prefix6969MiddleTransfer.Packet F Crt):
    Γ.card≤limit ∨ ProjectedProduct P.parents P.projected ∧ 22≤P.projected.natDegree ∧
      ∃G:Pade.Row SeedField,G.primitive ∧ G.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band P.projected.natDegree) ∧
        Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets P.parents)
          (TransitionClassification.content (TransitionClassification.band P.projected.natDegree)) :=
  reduce F Crt ((by decide:2293≤2390).trans lo) hi middle 342 P.toEarlyPacket (by decide) middle_prices

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
    (small:OrdinaryPackets.prices m 21=true) (char:41*m.seedMass<p) (firstFit:2293≤first) (lastFit:last≤2534)
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

private def pole1001_220_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 141411256⟩
private theorem pole1001_220_0_checked :
    packedBlock 1001 220 pole1001_220_0.length 220 pole1001_220_0.packed = pole1001_220_0.total := by decide +kernel

private def pole1001_220_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 886296760⟩
private theorem pole1001_220_1_checked :
    packedBlock 1001 220 pole1001_220_1.length 316 pole1001_220_1.packed = pole1001_220_1.total := by decide +kernel

private def pole1001_220_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 2094996127⟩
private theorem pole1001_220_2_checked :
    packedBlock 1001 220 pole1001_220_2.length 412 pole1001_220_2.packed = pole1001_220_2.total := by decide +kernel

private def pole1001_220_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 3181717552⟩
private theorem pole1001_220_3_checked :
    packedBlock 1001 220 pole1001_220_3.length 508 pole1001_220_3.packed = pole1001_220_3.total := by decide +kernel

private def pole1001_220_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 3880318000⟩
private theorem pole1001_220_4_checked :
    packedBlock 1001 220 pole1001_220_4.length 604 pole1001_220_4.packed = pole1001_220_4.total := by decide +kernel

private def pole1001_220_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 4187865136⟩
private theorem pole1001_220_5_checked :
    packedBlock 1001 220 pole1001_220_5.length 700 pole1001_220_5.packed = pole1001_220_5.total := by decide +kernel

private def pole1001_220_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 4104358960⟩
private theorem pole1001_220_6_checked :
    packedBlock 1001 220 pole1001_220_6.length 796 pole1001_220_6.packed = pole1001_220_6.total := by decide +kernel

private def pole1001_220_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 3629799472⟩
private theorem pole1001_220_7_checked :
    packedBlock 1001 220 pole1001_220_7.length 892 pole1001_220_7.packed = pole1001_220_7.total := by decide +kernel

private def pole1001_220_8 : Block := ⟨96, 20062935402790174794682126674279434838709574439458412701113569281392843971064392393508452418688591341063707954229260240747012948937818812526549433931379211013861117889818094878379476079335522888108729904378260749777905819382981837575822613725043166009883424123500000900600927427404029240711397736747866808694882946536648980414516218675281822965425017124561099655093130435010446747489367554055348844266241, 2795812826⟩
private theorem pole1001_220_8_checked :
    packedBlock 1001 220 pole1001_220_8.length 988 pole1001_220_8.packed = pole1001_220_8.total := by decide +kernel

private def pole1001_220_9 : Block := ⟨96, 21633283524733670359978769048639023247888664441797992316786703858021623395715859006006472030619851311486554612358707240808659645262309865174431655269603385005665170631801789483972026437584362712799879753159094858915460446250692045437865801740797803583566307901834563895131998394694849128852782601935962884902017976814137723108137446918630043629807930669682135426692071106946448271456051822063744672219993, 1838067690⟩
private theorem pole1001_220_9_checked :
    packedBlock 1001 220 pole1001_220_9.length 1084 pole1001_220_9.packed = pole1001_220_9.total := by decide +kernel

private def pole1001_220_10 : Block := ⟨96, 22500488476096759892046295123217644903915214289837134817264068563159541516849239092605067161586711443224771243693770649286063626982472422663773744400622758071997069907895807447976300784122095768100449557243899258685498881569030813478653692372427965812875663992112154759837364486573287605098624329755795864995410927891672104232938026545872610481234610567124284122825067424764545406551001979355647418237852, 968074626⟩
private theorem pole1001_220_10_checked :
    packedBlock 1001 220 pole1001_220_10.length 1180 pole1001_220_10.packed = pole1001_220_10.total := by decide +kernel

private def pole1001_220_11 : Block := ⟨96, 23063000723762744440214187067943235075057453901340945656443919393706439147895594053950821122648311607569518669618602146037535547466947349666999217488919675492894745621202214823159638309196728381704399105529164865306890820621439112664110807626526349258073174723201861589184269785300428790657717402187363141472914196491836841963442632968063349992391941944253979467883888711282718815194127075375930902840256, 327220956⟩
private theorem pole1001_220_11_checked :
    packedBlock 1001 220 pole1001_220_11.length 1276 pole1001_220_11.packed = pole1001_220_11.total := by decide +kernel

private def pole1001_220_12 : Block := ⟨69, 38108026419093333160243090595676588661461854304673673508181071605865971929076763480984214001951263336530823807799986862699385039991339634937757534080483136411546997791589153506416612167470735902046111598686723077157654834931417965365065430931278955958792289254879694429120936116402005607384, 28294407⟩
private theorem pole1001_220_12_checked :
    packedBlock 1001 220 pole1001_220_12.length 1372 pole1001_220_12.packed = pole1001_220_12.total := by decide +kernel

private def poleBlocks1001_220 : List Block := [pole1001_220_0, pole1001_220_1, pole1001_220_2, pole1001_220_3, pole1001_220_4, pole1001_220_5, pole1001_220_6, pole1001_220_7, pole1001_220_8, pole1001_220_9, pole1001_220_10, pole1001_220_11, pole1001_220_12]
theorem moment1001_220 : P1_7_1.groupedPoleMoment 1001 220 ≤ 28064233768 := by
  refine grouped_from_blocks 1001 220 _ poleBlocks1001_220 ?_ (by decide) (by decide)
  exact ⟨pole1001_220_0_checked, pole1001_220_1_checked, pole1001_220_2_checked, pole1001_220_3_checked, pole1001_220_4_checked, pole1001_220_5_checked, pole1001_220_6_checked, pole1001_220_7_checked, pole1001_220_8_checked, pole1001_220_9_checked, pole1001_220_10_checked, pole1001_220_11_checked, pole1001_220_12_checked, True.intro⟩

private def pole1669_378_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 243011384⟩
private theorem pole1669_378_0_checked :
    packedBlock 1669 378 pole1669_378_0.length 378 pole1669_378_0.packed = pole1669_378_0.total := by decide +kernel

private def pole1669_378_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 1585056824⟩
private theorem pole1669_378_1_checked :
    packedBlock 1669 378 pole1669_378_1.length 474 pole1669_378_1.packed = pole1669_378_1.total := by decide +kernel

private def pole1669_378_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 4020193592⟩
private theorem pole1669_378_2_checked :
    packedBlock 1669 378 pole1669_378_2.length 570 pole1669_378_2.packed = pole1669_378_2.total := by decide +kernel

private def pole1669_378_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 7293572675⟩
private theorem pole1669_378_3_checked :
    packedBlock 1669 378 pole1669_378_3.length 666 pole1669_378_3.packed = pole1669_378_3.total := by decide +kernel

private def pole1669_378_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 10935696320⟩
private theorem pole1669_378_4_checked :
    packedBlock 1669 378 pole1669_378_4.length 762 pole1669_378_4.packed = pole1669_378_4.total := by decide +kernel

private def pole1669_378_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 14072288192⟩
private theorem pole1669_378_5_checked :
    packedBlock 1669 378 pole1669_378_5.length 858 pole1669_378_5.packed = pole1669_378_5.total := by decide +kernel

private def pole1669_378_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 16538250176⟩
private theorem pole1669_378_6_checked :
    packedBlock 1669 378 pole1669_378_6.length 954 pole1669_378_6.packed = pole1669_378_6.total := by decide +kernel

private def pole1669_378_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 18333582272⟩
private theorem pole1669_378_7_checked :
    packedBlock 1669 378 pole1669_378_7.length 1050 pole1669_378_7.packed = pole1669_378_7.total := by decide +kernel

private def pole1669_378_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 19458284480⟩
private theorem pole1669_378_8_checked :
    packedBlock 1669 378 pole1669_378_8.length 1146 pole1669_378_8.packed = pole1669_378_8.total := by decide +kernel

private def pole1669_378_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 19912356800⟩
private theorem pole1669_378_9_checked :
    packedBlock 1669 378 pole1669_378_9.length 1242 pole1669_378_9.packed = pole1669_378_9.total := by decide +kernel

private def pole1669_378_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 19695799232⟩
private theorem pole1669_378_10_checked :
    packedBlock 1669 378 pole1669_378_10.length 1338 pole1669_378_10.packed = pole1669_378_10.total := by decide +kernel

private def pole1669_378_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 18808611776⟩
private theorem pole1669_378_11_checked :
    packedBlock 1669 378 pole1669_378_11.length 1434 pole1669_378_11.packed = pole1669_378_11.total := by decide +kernel

private def pole1669_378_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 17250794432⟩
private theorem pole1669_378_12_checked :
    packedBlock 1669 378 pole1669_378_12.length 1530 pole1669_378_12.packed = pole1669_378_12.total := by decide +kernel

private def pole1669_378_13 : Block := ⟨96, 31453808418026361895081918702205677172680809795032992922149007768843805587526571299230901327657976636156603803360467977424237174760718451254834998958543982307853231972953692173065129279564286380260115261120871801374662551844718397769504759775162753792486103934777531012418432805516941453601028994714521716360680584394947586837434922341375110044708892012459310459412420891204434690501662799983805677995233, 15034743255⟩
private theorem pole1669_378_13_checked :
    packedBlock 1669 378 pole1669_378_13.length 1626 pole1669_378_13.packed = pole1669_378_13.total := by decide +kernel

private def pole1669_378_14 : Block := ⟨96, 33399163274537891791154479411565230950850611168244279202554191666849763867452109461030136851857275186004870700345319719649608394039965650192047389172173899746823658892063224882069099861861159884007282475823270679998158389814991192721209432820478723819649097970612484390926703674678713470897813667552022902431776252666154078952254383007355324180567078371634425944065765548007956739504010374434524247360831, 12410529090⟩
private theorem pole1669_378_14_checked :
    packedBlock 1669 378 pole1669_378_14.length 1722 pole1669_378_14.packed = pole1669_378_14.total := by decide +kernel

private def pole1669_378_15 : Block := ⟨96, 35063262007303742804950749271104887844273950060259990641623344363232527811591705760229087626032317060901856633754678845028236566046412180917167079690671179211744217542403772328497785689759519490903410341358245245235190383063410140050251683980739314912465716464775960638998984137670109941962560587344202756686647603699667553690026094406090944568756253803928716565578385490077204719251815206181299636438418, 9704839755⟩
private theorem pole1669_378_15_checked :
    packedBlock 1669 378 pole1669_378_15.length 1818 pole1669_378_15.packed = pole1669_378_15.total := by decide +kernel

private def pole1669_378_16 : Block := ⟨96, 36446104616149288152855398182971966776962268147863980697039971112018417026454400532177397475350723088144466082372746701229437352646735097937673195555049440468669189168607255247292362033053914578312841058316507471711248721984823944895378999747495243634301339164792896259317547479849109131192949288367977552605909789985647581551134132317468644630737251529420010080751009909594358705760598597831514777863641, 7089173222⟩
private theorem pole1669_378_16_checked :
    packedBlock 1669 378 pole1669_378_16.length 1914 pole1669_378_16.packed = pole1669_378_16.total := by decide +kernel

private def pole1669_378_17 : Block := ⟨96, 37242998397552054964095961105017490908363304181202662159584379254624398581447145581177576791585993993651018455912952348054757623569234065728576324094467787488475559615957445982788043840841292927563510525070386430886063952165154033155271843628945686710493050442560480707562190331160813638061738482194462701424453717417901771173216483314991076421018971576205861264209295770359758019398061642350586992330259, 4707570393⟩
private theorem pole1669_378_17_checked :
    packedBlock 1669 378 pole1669_378_17.length 2010 pole1669_378_17.packed = pole1669_378_17.total := by decide +kernel

private def pole1669_378_18 : Block := ⟨96, 37805510645218039512263853049743081079505543792706472998764230085171296212493500542523330752647594157995765881837783844806229544053708992731801797182764704909373235329263853357971381365915925541167460073355652037507455891217562332340728958652699683016926818214357020344324337356975663214216785723180958220654756922140080224610415367923953670076568569949712469309588957337950436432740032687956697218385461, 2694684368⟩
private theorem pole1669_378_18_checked :
    packedBlock 1669 378 pole1669_378_18.length 2106 pole1669_378_18.packed = pole1669_378_18.total := by decide +kernel

private def pole1669_378_19 : Block := ⟨96, 38368022892884024060431744994468671250647783404210283837944080915718193843539855503869084713709194322340513307762615341557701464538183919735027270271061622330270911042570260733154718890990558154771409621640917644128847830269970631526186073676453679323360585985958438787439192916679454335312244325578822948025082348111668726204004429785384861157600369745743816231972201522210825160370178347573861749589581, 1191052496⟩
private theorem pole1669_378_19_checked :
    packedBlock 1669 378 pole1669_378_19.length 2202 pole1669_378_19.packed = pole1669_378_19.total := by decide +kernel

private def pole1669_378_20 : Block := ⟨96, 38930535140550008608599636939194261421790023015714094677123931746265091474586210465214838674770794486685260733687446838309173385022658846738252743359358539751168586755876668108338056416065190768375359169926183250750239769322378930711643188700207675629794353757559857230554048476383245456407702927976687675395407774083257227797593491646816052238632169541775163154355445706471213888000324007191026280793701, 279944912⟩
private theorem pole1669_378_20_checked :
    packedBlock 1669 378 pole1669_378_20.length 2298 pole1669_378_20.packed = pole1669_378_20.total := by decide +kernel

private def pole1669_378_21 : Block := ⟨31, 4519402521616125008727608510121798802024559076935799098277664892599578229851792820232990146154325931622646260899144013707611178621, 4727024⟩
private theorem pole1669_378_21_checked :
    packedBlock 1669 378 pole1669_378_21.length 2394 pole1669_378_21.packed = pole1669_378_21.total := by decide +kernel

private def poleBlocks1669_378 : List Block := [pole1669_378_0, pole1669_378_1, pole1669_378_2, pole1669_378_3, pole1669_378_4, pole1669_378_5, pole1669_378_6, pole1669_378_7, pole1669_378_8, pole1669_378_9, pole1669_378_10, pole1669_378_11, pole1669_378_12, pole1669_378_13, pole1669_378_14, pole1669_378_15, pole1669_378_16, pole1669_378_17, pole1669_378_18, pole1669_378_19, pole1669_378_20, pole1669_378_21]
theorem moment1669_378 : P1_7_1.groupedPoleMoment 1669 378 ≤ 221264762670 := by
  refine grouped_from_blocks 1669 378 _ poleBlocks1669_378 ?_ (by decide) (by decide)
  exact ⟨pole1669_378_0_checked, pole1669_378_1_checked, pole1669_378_2_checked, pole1669_378_3_checked, pole1669_378_4_checked, pole1669_378_5_checked, pole1669_378_6_checked, pole1669_378_7_checked, pole1669_378_8_checked, pole1669_378_9_checked, pole1669_378_10_checked, pole1669_378_11_checked, pole1669_378_12_checked, pole1669_378_13_checked, pole1669_378_14_checked, pole1669_378_15_checked, pole1669_378_16_checked, pole1669_378_17_checked, pole1669_378_18_checked, pole1669_378_19_checked, pole1669_378_20_checked, pole1669_378_21_checked, True.intro⟩

private def pole2020_432_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 296397080⟩
private theorem pole2020_432_0_checked :
    packedBlock 2020 432 pole2020_432_0.length 432 pole2020_432_0.packed = pole2020_432_0.total := by decide +kernel

private def pole2020_432_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 1952219672⟩
private theorem pole2020_432_1_checked :
    packedBlock 2020 432 pole2020_432_1.length 528 pole2020_432_1.packed = pole2020_432_1.total := by decide +kernel

private def pole2020_432_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 5011675928⟩
private theorem pole2020_432_2_checked :
    packedBlock 2020 432 pole2020_432_2.length 624 pole2020_432_2.packed = pole2020_432_2.total := by decide +kernel

private def pole2020_432_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 9219961880⟩
private theorem pole2020_432_3_checked :
    packedBlock 2020 432 pole2020_432_3.length 720 pole2020_432_3.packed = pole2020_432_3.total := by decide +kernel

private def pole2020_432_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 14293670300⟩
private theorem pole2020_432_4_checked :
    packedBlock 2020 432 pole2020_432_4.length 816 pole2020_432_4.packed = pole2020_432_4.total := by decide +kernel

private def pole2020_432_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 19355654240⟩
private theorem pole2020_432_5_checked :
    packedBlock 2020 432 pole2020_432_5.length 912 pole2020_432_5.packed = pole2020_432_5.total := by decide +kernel

private def pole2020_432_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 23681386592⟩
private theorem pole2020_432_6_checked :
    packedBlock 2020 432 pole2020_432_6.length 1008 pole2020_432_6.packed = pole2020_432_6.total := by decide +kernel

private def pole2020_432_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 27240937568⟩
private theorem pole2020_432_7_checked :
    packedBlock 2020 432 pole2020_432_7.length 1104 pole2020_432_7.packed = pole2020_432_7.total := by decide +kernel

private def pole2020_432_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 30034307168⟩
private theorem pole2020_432_8_checked :
    packedBlock 2020 432 pole2020_432_8.length 1200 pole2020_432_8.packed = pole2020_432_8.total := by decide +kernel

private def pole2020_432_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 32061495392⟩
private theorem pole2020_432_9_checked :
    packedBlock 2020 432 pole2020_432_9.length 1296 pole2020_432_9.packed = pole2020_432_9.total := by decide +kernel

private def pole2020_432_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 33322502240⟩
private theorem pole2020_432_10_checked :
    packedBlock 2020 432 pole2020_432_10.length 1392 pole2020_432_10.packed = pole2020_432_10.total := by decide +kernel

private def pole2020_432_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 33817327712⟩
private theorem pole2020_432_11_checked :
    packedBlock 2020 432 pole2020_432_11.length 1488 pole2020_432_11.packed = pole2020_432_11.total := by decide +kernel

private def pole2020_432_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 33545971808⟩
private theorem pole2020_432_12_checked :
    packedBlock 2020 432 pole2020_432_12.length 1584 pole2020_432_12.packed = pole2020_432_12.total := by decide +kernel

private def pole2020_432_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 32508434528⟩
private theorem pole2020_432_13_checked :
    packedBlock 2020 432 pole2020_432_13.length 1680 pole2020_432_13.packed = pole2020_432_13.total := by decide +kernel

private def pole2020_432_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 30704715872⟩
private theorem pole2020_432_14_checked :
    packedBlock 2020 432 pole2020_432_14.length 1776 pole2020_432_14.packed = pole2020_432_14.total := by decide +kernel

private def pole2020_432_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 28134815840⟩
private theorem pole2020_432_15_checked :
    packedBlock 2020 432 pole2020_432_15.length 1872 pole2020_432_15.packed = pole2020_432_15.total := by decide +kernel

private def pole2020_432_16 : Block := ⟨96, 38203955390018181802283173440935310275080013281097209344763899022058881965547613522729551610546449515804421213692539367679576147422830507519830828431891554772697887535143871159591807429084755972846635442685322011147326728023061307762886627239972517662043475085000621904216769805366947728735993575332705787974801775650628567358121661846606176485733653217910919706358046881235057706228170021071729515857409, 24807575935⟩
private theorem pole2020_432_16_checked :
    packedBlock 2020 432 pole2020_432_16.length 1968 pole2020_432_16.packed = pole2020_432_16.total := by decide +kernel

private def pole2020_432_17 : Block := ⟨96, 40219624277575267829823072244989172448085363055001693696433673045833053523306216395630040064708214980364275505555717171626296110472625633535810570163650783773883738966733388755371344701671922595273473836159822661564762610558514914962753472167927359462886372409723375916212146808118259731098746912352163326021365034899448436979251900562233692966277258154956287383409494232353053034554873923936039630014047, 20990406565⟩
private theorem pole2020_432_17_checked :
    packedBlock 2020 432 pole2020_432_17.length 2064 pole2020_432_17.packed = pole2020_432_17.total := by decide +kernel

private def pole2020_432_18 : Block := ⟨96, 41977476481986778185058946500586221899574579363898752851042478401702868840281232567678515732498591557129953249197272328792836471696816201832965349307191433088637349832807317557134921270351082645054511404847227290863219730593641229543773639816231679869626474305167935004089768194737724394998735032198699690772530825761890436691956273575199770492445485170381715600730248787199765395998978884177453577504437, 17081549310⟩
private theorem pole2020_432_18_checked :
    packedBlock 2020 432 pole2020_432_18.length 2160 pole2020_432_18.packed = pole2020_432_18.total := by decide +kernel

private def pole2020_432_19 : Block := ⟨96, 43500945722293511027469128441988814368727417352905152095999793831605847993233065865790486118696496780775028387267151939883898554662174211221866479201966320890021434080872352317266112091507615978387313753102589896218170191589087147733446781779280771517411781548846221517519725628824814391172933290423453893226810159780191665267449000436085191854487323522896029878056529403529708856042322164151729526949632, 13263914564⟩
private theorem pole2020_432_19_checked :
    packedBlock 2020 432 pole2020_432_19.length 2256 pole2020_432_19.packed = pole2020_432_19.total := by decide +kernel

private def pole2020_432_20 : Block := ⟨96, 44766598279541976261172133199916297505616388814750833383684919454472789802376121997908936221318338208130367010077833464640898220920024918851607443996694556881188120022680422820191855403810847474230906848743549801776281843736324507452062698415676857411740797753974449736591803936499032852383866317061289051256312410565727205984131523800000279620399328225481322146093422301355338911647515383329824384763712, 9693812594⟩
private theorem pole2020_432_20_checked :
    packedBlock 2020 432 pole2020_432_20.length 2352 pole2020_432_20.packed = pole2020_432_20.total := by decide +kernel

private def pole2020_432_21 : Block := ⟨96, 45352549967982690803578117304812609039923770925409158375504505807774119771927981248774775836953764391949889808585944486059788529661841006440628398775486131736464221209143525746742076411277333621673409287752092834325422707030562719169158388114607639980923105729412673969874333211557456318059249227184281321803244889108960191244142666477831759943569112958732604940614038605820294215777561565119673274320758, 6497285590⟩
private theorem pole2020_432_21_checked :
    packedBlock 2020 432 pole2020_432_21.length 2448 pole2020_432_21.packed = pole2020_432_21.total := by decide +kernel

private def pole2020_432_22 : Block := ⟨96, 45915062215648675351746009249538199211066010536912969214684356638321017402974336210120529798015364556294637234510775982811260450146315933443853871863783049157361896922449933121925413936351966235277358836037358440946814646082971018354615503138361636287356873501014092412989188771261247439154707829582146049173570315080548692837731728339262951024600912754763951862997282790080682943407707224736838073960335, 3826864712⟩
private theorem pole2020_432_22_checked :
    packedBlock 2020 432 pole2020_432_22.length 2544 pole2020_432_22.packed = pole2020_432_22.total := by decide +kernel

private def pole2020_432_23 : Block := ⟨96, 46477574463314659899913901194263789382208250148416780053864207468867915034020691171466283759076964720639384660435607479562732370630790860447079344952079966578259572635756340497108751461426598848881308384322624047568206585135379317540072618162115632593790641272615510856104044330965038560250166431980010776543895741052137194431320790200694142105632712550795298785380526974341071671037852884354002605164455, 1807158728⟩
private theorem pole2020_432_23_checked :
    packedBlock 2020 432 pole2020_432_23.length 2640 pole2020_432_23.packed = pole2020_432_23.total := by decide +kernel

private def pole2020_432_24 : Block := ⟨96, 47040086710980644448081793138989379553350489759920590893044058299414812665067046132812037720138564884984132086360438976314204291115265787450304818040376883999157248349062747872292088986501231462485257932607889654189598524187787616725529733185869628900224409044216929299218899890668829681345625034377875503914221167023725696024909852062125333186664512346826645707763771158601460398667998543971167136368575, 517829960⟩
private theorem pole2020_432_24_checked :
    packedBlock 2020 432 pole2020_432_24.length 2736 pole2020_432_24.packed = pole2020_432_24.total := by decide +kernel

private def pole2020_432_25 : Block := ⟨52, 174098400676923612037908292562194598194471842629141115180514675550424641250186230365943555021052679816767967901895607831529311893774869156079006357491049105194232564809244721579981930098399861856579035127949544203339735, 25458615⟩
private theorem pole2020_432_25_checked :
    packedBlock 2020 432 pole2020_432_25.length 2832 pole2020_432_25.packed = pole2020_432_25.total := by decide +kernel

private def poleBlocks2020_432 : List Block := [pole2020_432_0, pole2020_432_1, pole2020_432_2, pole2020_432_3, pole2020_432_4, pole2020_432_5, pole2020_432_6, pole2020_432_7, pole2020_432_8, pole2020_432_9, pole2020_432_10, pole2020_432_11, pole2020_432_12, pole2020_432_13, pole2020_432_14, pole2020_432_15, pole2020_432_16, pole2020_432_17, pole2020_432_18, pole2020_432_19, pole2020_432_20, pole2020_432_21, pole2020_432_22, pole2020_432_23, pole2020_432_24, pole2020_432_25]
theorem moment2020_432 : P1_7_1.groupedPoleMoment 2020 432 ≤ 453693330393 := by
  refine grouped_from_blocks 2020 432 _ poleBlocks2020_432 ?_ (by decide) (by decide)
  exact ⟨pole2020_432_0_checked, pole2020_432_1_checked, pole2020_432_2_checked, pole2020_432_3_checked, pole2020_432_4_checked, pole2020_432_5_checked, pole2020_432_6_checked, pole2020_432_7_checked, pole2020_432_8_checked, pole2020_432_9_checked, pole2020_432_10_checked, pole2020_432_11_checked, pole2020_432_12_checked, pole2020_432_13_checked, pole2020_432_14_checked, pole2020_432_15_checked, pole2020_432_16_checked, pole2020_432_17_checked, pole2020_432_18_checked, pole2020_432_19_checked, pole2020_432_20_checked, pole2020_432_21_checked, pole2020_432_22_checked, pole2020_432_23_checked, pole2020_432_24_checked, pole2020_432_25_checked, True.intro⟩

private def pole3621_793_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 539902776⟩
private theorem pole3621_793_0_checked :
    packedBlock 3621 793 pole3621_793_0.length 793 pole3621_793_0.packed = pole3621_793_0.total := by decide +kernel

private def pole3621_793_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 3626942520⟩
private theorem pole3621_793_1_checked :
    packedBlock 3621 793 pole3621_793_1.length 889 pole3621_793_1.packed = pole3621_793_1.total := by decide +kernel

private def pole3621_793_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 9534078264⟩
private theorem pole3621_793_2_checked :
    packedBlock 3621 793 pole3621_793_2.length 985 pole3621_793_2.packed = pole3621_793_2.total := by decide +kernel

private def pole3621_793_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 18006506040⟩
private theorem pole3621_793_3_checked :
    packedBlock 3621 793 pole3621_793_3.length 1081 pole3621_793_3.packed = pole3621_793_3.total := by decide +kernel

private def pole3621_793_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 28789421880⟩
private theorem pole3621_793_4_checked :
    packedBlock 3621 793 pole3621_793_4.length 1177 pole3621_793_4.packed = pole3621_793_4.total := by decide +kernel

private def pole3621_793_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 41628021816⟩
private theorem pole3621_793_5_checked :
    packedBlock 3621 793 pole3621_793_5.length 1273 pole3621_793_5.packed = pole3621_793_5.total := by decide +kernel

private def pole3621_793_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 56267501880⟩
private theorem pole3621_793_6_checked :
    packedBlock 3621 793 pole3621_793_6.length 1369 pole3621_793_6.packed = pole3621_793_6.total := by decide +kernel

private def pole3621_793_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 72453058104⟩
private theorem pole3621_793_7_checked :
    packedBlock 3621 793 pole3621_793_7.length 1465 pole3621_793_7.packed = pole3621_793_7.total := by decide +kernel

private def pole3621_793_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 89764370610⟩
private theorem pole3621_793_8_checked :
    packedBlock 3621 793 pole3621_793_8.length 1561 pole3621_793_8.packed = pole3621_793_8.total := by decide +kernel

private def pole3621_793_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 106510393168⟩
private theorem pole3621_793_9_checked :
    packedBlock 3621 793 pole3621_793_9.length 1657 pole3621_793_9.packed = pole3621_793_9.total := by decide +kernel

private def pole3621_793_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 121858857808⟩
private theorem pole3621_793_10_checked :
    packedBlock 3621 793 pole3621_793_10.length 1753 pole3621_793_10.packed = pole3621_793_10.total := by decide +kernel

private def pole3621_793_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 135802361680⟩
private theorem pole3621_793_11_checked :
    packedBlock 3621 793 pole3621_793_11.length 1849 pole3621_793_11.packed = pole3621_793_11.total := by decide +kernel

private def pole3621_793_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 148340904784⟩
private theorem pole3621_793_12_checked :
    packedBlock 3621 793 pole3621_793_12.length 1945 pole3621_793_12.packed = pole3621_793_12.total := by decide +kernel

private def pole3621_793_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 159474487120⟩
private theorem pole3621_793_13_checked :
    packedBlock 3621 793 pole3621_793_13.length 2041 pole3621_793_13.packed = pole3621_793_13.total := by decide +kernel

private def pole3621_793_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 169203108688⟩
private theorem pole3621_793_14_checked :
    packedBlock 3621 793 pole3621_793_14.length 2137 pole3621_793_14.packed = pole3621_793_14.total := by decide +kernel

private def pole3621_793_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 177526769488⟩
private theorem pole3621_793_15_checked :
    packedBlock 3621 793 pole3621_793_15.length 2233 pole3621_793_15.packed = pole3621_793_15.total := by decide +kernel

private def pole3621_793_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 184445469520⟩
private theorem pole3621_793_16_checked :
    packedBlock 3621 793 pole3621_793_16.length 2329 pole3621_793_16.packed = pole3621_793_16.total := by decide +kernel

private def pole3621_793_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 189959208784⟩
private theorem pole3621_793_17_checked :
    packedBlock 3621 793 pole3621_793_17.length 2425 pole3621_793_17.packed = pole3621_793_17.total := by decide +kernel

private def pole3621_793_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 194067987280⟩
private theorem pole3621_793_18_checked :
    packedBlock 3621 793 pole3621_793_18.length 2521 pole3621_793_18.packed = pole3621_793_18.total := by decide +kernel

private def pole3621_793_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 196771805008⟩
private theorem pole3621_793_19_checked :
    packedBlock 3621 793 pole3621_793_19.length 2617 pole3621_793_19.packed = pole3621_793_19.total := by decide +kernel

private def pole3621_793_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 198070661968⟩
private theorem pole3621_793_20_checked :
    packedBlock 3621 793 pole3621_793_20.length 2713 pole3621_793_20.packed = pole3621_793_20.total := by decide +kernel

private def pole3621_793_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 197964558160⟩
private theorem pole3621_793_21_checked :
    packedBlock 3621 793 pole3621_793_21.length 2809 pole3621_793_21.packed = pole3621_793_21.total := by decide +kernel

private def pole3621_793_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 196453493584⟩
private theorem pole3621_793_22_checked :
    packedBlock 3621 793 pole3621_793_22.length 2905 pole3621_793_22.packed = pole3621_793_22.total := by decide +kernel

private def pole3621_793_23 : Block := ⟨96, 54001174345304575867478254153289749865965580889477410725941361893251041970219880745145295515138602395337822043935948032401877441567273503421450836664419675223839941740157703730617515717360449347268364951044137563855607314996071255343987659217872140214086429176526228318893366241748387532916164491565025430369387319635631792599543138993784246342708498155382892944926351902724493735043151083157305827035297, 193537468240⟩
private theorem pole3621_793_23_checked :
    packedBlock 3621 793 pole3621_793_23.length 3001 pole3621_793_23.packed = pole3621_793_23.total := by decide +kernel

private def pole3621_793_24 : Block := ⟨96, 56251223335968514060149821932192110550534539335492654082660765215438632494405300590528311359385003052716811747635274019407765123505173211434352729017607344907430644593383333231350865817658979801684163144185199990341175071205704452085816119312888125439821500262931902091352788480563552017297998901156484339850689023521985798973899386439509010666835697339508280634459328639766048645563733721625963951851777, 189216482128⟩
private theorem pole3621_793_24_checked :
    packedBlock 3621 793 pole3621_793_24.length 3097 pole3621_793_24.packed = pole3621_793_24.total := by decide +kernel

private def pole3621_793_25 : Block := ⟨96, 58501272326632452252821389711094471235103497781507897439380168537626223018590720435911327203631403710095801451334600006413652805443072919447254621370795014591021347446608962732084215917957510256099961337326262416826742827415337648827644579407904110665556571349337575863812210719378716501679833310747943249331990727408339805348255633885233774990962896523633668323992305376807603556084316360094622076668257, 183490535248⟩
private theorem pole3621_793_25_checked :
    packedBlock 3621 793 pole3621_793_25.length 3193 pole3621_793_25.packed = pole3621_793_25.total := by decide +kernel

private def pole3621_793_26 : Block := ⟨96, 60751321317296390445492957489996831919672456227523140796099571859813813542776140281294343047877804367474791155033925993419540487380972627460156513723982684274612050299834592232817566018256040710515759530467324843312310583624970845569473039502920095891291642435743249636271632958193880986061667720339402158813292431294693811722611881330958539315090095707759056013525282113849158466604898998563280201484737, 176359627600⟩
private theorem pole3621_793_26_checked :
    packedBlock 3621 793 pole3621_793_26.length 3289 pole3621_793_26.packed = pole3621_793_26.total := by decide +kernel

private def pole3621_793_27 : Block := ⟨96, 63001370307960328638164525268899192604241414673538384152818975182001404066961560126677358892124205024853780858733251980425428169318872335473058406077170353958202753153060221733550916118554571164931557723608387269797878339834604042311301499597936081117026713522148923408731055197009045470443502129930861068294594135181047818096968128776683303639217294891884443703058258850890713377125481637031938326301217, 167823759184⟩
private theorem pole3621_793_27_checked :
    packedBlock 3621 793 pole3621_793_27.length 3385 pole3621_793_27.packed = pole3621_793_27.total := by decide +kernel

private def pole3621_793_28 : Block := ⟨96, 65251419298624266830836093047801553288810373119553627509538378504188994591146979972060374736370605682232770562432577967431315851256772043485960298430358023641793456006285851234284266218853101619347355916749449696283446096044237239053129959692952066342761784608554597181190477435824209954825336539522319977775895839067401824471324376222408067963344494076009831392591235587932268287646064275500596451117697, 157882930000⟩
private theorem pole3621_793_28_checked :
    packedBlock 3621 793 pole3621_793_28.length 3481 pole3621_793_28.packed = pole3621_793_28.total := by decide +kernel

private def pole3621_793_29 : Block := ⟨96, 67478030278968789000667331995673681049581738248422878747958621375103797714038801694053984165572772999430729123385035975405892203174485296207061129404866655099513422371457047094384977255606855714862989545378626055826456126752604820916337015962420601160272941596100153249754149687839060735787021391373952071103784476153031954234566617071980105535748268726496952001716361452942599794843119584746532752624353, 146562363610⟩
private theorem pole3621_793_29_checked :
    packedBlock 3621 793 pole3621_793_29.length 3577 pole3621_793_29.packed = pole3621_793_29.total := by decide +kernel

private def pole3621_793_30 : Block := ⟨96, 69587451207716231056296926788394644191365136808378117103005628667862442817024444905386272068731566149620854113495643680073638883865138122505616004114932465656492712509323677567001357489300525428803834263228330349026324209783114918943720105802514040909058965655618020380883016511694049158683075207810716455621966782148939945502169566917126210687368722381432486119056668429223446150436503640385047552346944, 134361340173⟩
private theorem pole3621_793_30_checked :
    packedBlock 3621 793 pole3621_793_30.length 3673 pole3621_793_30.packed = pole3621_793_30.total := by decide +kernel

private def pole3621_793_31 : Block := ⟨96, 71556244074547176974884568447701168422022092209202070303017510493967265319617983547480187856841440063824252051416269967060594119703844296806996873061642111553306032232429551854751511645460778039719928505757314641120883913690207004960070254822933080265299431826384413914987113109466557142820657322528412055725958795459222736659319023904070182739147001454666785829780421431333952435310079327268033486293914, 121836628911⟩
private theorem pole3621_793_31_checked :
    packedBlock 3621 793 pole3621_793_31.length 3769 pole3621_793_31.packed = pole3621_793_31.total := by decide +kernel

private def pole3621_793_32 : Block := ⟨96, 73384408879548940148888368152768833578999779919852592373586582137990800307397848144777211502318124287521459887146631676384981192078064912081293283964794046004374200322141644686284681357134124833527780473357049455507337135415565952337383305416728289480896872052029967099361738901031612056292739511020670147524880590700226753732463276368865186059146242629192195146635117025547166345553731460757240636214254, 109181021740⟩
private theorem pole3621_793_32_checked :
    packedBlock 3621 793 pole3621_793_32.length 3865 pole3621_793_32.packed = pole3621_793_32.total := by decide +kernel

private def pole3621_793_33 : Block := ⟨96, 75095383632778996424099469814349676344088995474237335241953075256041624885152940873552959215888964472335095275925729786687653219218389313292754674193035439296118245863315205857246114521544309012425247014855443924488867252187926124436491649549661636240678102928601795540054735020859734961248115733793418744285108383988913783230150522047662318066450982588095596750102223789044699809118613906817933493881916, 96566005652⟩
private theorem pole3621_793_33_checked :
    packedBlock 3621 793 pole3621_793_33.length 3961 pole3621_793_33.packed = pole3621_793_33.total := by decide +kernel

private def pole3621_793_34 : Block := ⟨96, 76642293744403075966230535475384052624845132303139222355261199789566618387009079895296382341797234276872785911167812181613906438077493499596104530912377752177892847375819938992215261971604637369181377903573950070266020661768756222232486042596919216030054003402964134136589040114013851728878255152268367061455182185695761730069140201104118188790947786770545634405352014925562299141372312206446526879321220, 84155366130⟩
private theorem pole3621_793_34_checked :
    packedBlock 3621 793 pole3621_793_34.length 4057 pole3621_793_34.packed = pole3621_793_34.total := by decide +kernel

private def pole3621_793_35 : Block := ⟨96, 78072012373887458688351877837612233698216419739758808952179341123446546903396722125951389547399121199607046243222718316179251707782559801072324423767696262489738004331880458539934408392266555461577856677836993710966139184203798680638941242035835382383344790754522038420914910978002667587130400927944653003287456100681195289225225375442721134755676980712326970757048858716878907618275485798518610726096071, 72105186633⟩
private theorem pole3621_793_35_checked :
    packedBlock 3621 793 pole3621_793_35.length 4153 pole3621_793_35.packed = pole3621_793_35.total := by decide +kernel

private def pole3621_793_36 : Block := ⟨96, 79361102941455339944569983395830360362748396975533968991989119142736110941270832491211199736734034987443813612240425546394781965360386318114461089580345567665366812917591508571265507918463006080289128828185444846296338626667994999519865420567702381102978576494565086412481816618950903513189806912939185456686746887123918665994204840952515909654030795169887697670937554057557446711064111941470392640687364, 60563848773⟩
private theorem pole3621_793_36_checked :
    packedBlock 3621 793 pole3621_793_36.length 4249 pole3621_793_36.packed = pole3621_793_36.total := by decide +kernel

private def pole3621_793_37 : Block := ⟨96, 80368937385277542319162293868818474594464207364898246913579379456757515955787388913768457708116937641915822202925774935626517602757913738372689888140040643400673351342516344484167245785200913615593245443068086919421644655999222591849779391058192529647846933948938675792439194701628245277567788614344121526967018828323447849911645541106833683041066836593536789197573849079697182584208824037569185419562299, 49665052049⟩
private theorem pole3621_793_37_checked :
    packedBlock 3621 793 pole3621_793_37.length 4345 pole3621_793_37.packed = pole3621_793_37.total := by decide +kernel

private def pole3621_793_38 : Block := ⟨96, 80931449632943526867330185813544064765606446976402057752759230287304413586833743875114211669178537806260569628850606432377989665064028667303851115492865324256761728217785622236766939628844956714557987476431974127387821469323654910860900773571807343660256443445707096387822693999466395832619925481606985921055919017919516099497353323073543655136081150021603916979306559363640559340783825266584658403495270, 39460356412⟩
private theorem pole3621_793_38_checked :
    packedBlock 3621 793 pole3621_793_38.length 4441 pole3621_793_38.packed = pole3621_793_38.total := by decide +kernel

private def pole3621_793_39 : Block := ⟨96, 81493961880609511415498077758269654936748686587905868591939081117851311217880098836459965630240137970605317054775437929129461585548503594307076588581162241677659403931092029611950277153919589328161937024717239734009213408376063210046357888595561339966690211217308514830937549559170186953715384084004850648426244443891104601090942384934974846217112949817635263901689803547900948068413970926201822934699390, 30206319100⟩
private theorem pole3621_793_39_checked :
    packedBlock 3621 793 pole3621_793_39.length 4537 pole3621_793_39.packed = pole3621_793_39.total := by decide +kernel

private def pole3621_793_40 : Block := ⟨96, 82056474128275495963665969702995245107890926199409679431118931948398208848926453797805719591301738134950064480700269425880933506032978521310302061669459159098557079644398436987133614678994221941765886573002505340630605347428471509231815003619315336273123978988909933274052405118873978074810842686402715375796569869862693102684531446796406037298144749613666610824073047732161336796044116585818987465903510, 22037548732⟩
private theorem pole3621_793_40_checked :
    packedBlock 3621 793 pole3621_793_40.length 4633 pole3621_793_40.packed = pole3621_793_40.total := by decide +kernel

private def pole3621_793_41 : Block := ⟨96, 82618986375941480511833861647720835279033165810913490270298782778945106479972808759151473552363338299294811906625100922632405426517453448313527534757756076519454755357704844362316952204068854555369836121287770947251997286480879808417272118643069332579557746760511351717167260678577769195906301288800580103166895295834281604278120508657837228379176549409697957746456291916421725523674262245436151997107630, 15033671548⟩
private theorem pole3621_793_41_checked :
    packedBlock 3621 793 pole3621_793_41.length 4729 pole3621_793_41.packed = pole3621_793_41.total := by decide +kernel

private def pole3621_793_42 : Block := ⟨96, 83181498623607465060001753592446425450175405422417301109478633609492004111019163720497227513424938463639559332549932419383877347001928375316753007846052993940352431071011251737500289729143487168973785669573036553873389225533288107602729233666823328885991514532112770160282116238281560317001759891198444830537220721805870105871709570519268419460208349205729304668839536100682114251304407905053316528311750, 9274313788⟩
private theorem pole3621_793_42_checked :
    packedBlock 3621 793 pole3621_793_42.length 4825 pole3621_793_42.packed = pole3621_793_42.total := by decide +kernel

private def pole3621_793_43 : Block := ⟨96, 83744010871273449608169645537172015621317645033921111948658484440038901742065518681842981474486538627984306758474763916135349267486403302319978480934349911361250106784317659112683627254218119782577735217858302160494781164585696406788186348690577325192425282303714188603396971797985351438097218493596309557907546147777458607465298632380699610541240149001760651591222780284942502978934553564670481059515870, 4839101692⟩
private theorem pole3621_793_43_checked :
    packedBlock 3621 793 pole3621_793_43.length 4921 pole3621_793_43.packed = pole3621_793_43.total := by decide +kernel

private def pole3621_793_44 : Block := ⟨96, 84306523118939434156337537481897605792459884645424922787838335270585799373111873643188735435548138792329054184399595412886821187970878229323203954022646828782147782497624066487866964779292752396181684766143567767116173103638104705973643463714331321498859050075315607046511827357689142559192677095994174285277871573749047109058887694242130801622271948797791998513606024469202891706564699224287645590719990, 1807661500⟩
private theorem pole3621_793_44_checked :
    packedBlock 3621 793 pole3621_793_44.length 5017 pole3621_793_44.packed = pole3621_793_44.total := by decide +kernel

private def pole3621_793_45 : Block := ⟨94, 316161794090710972668128186545466328273214785879671088710013876310339861932897632134385375684243350987018631695975948620031367777646350221400029522286149041930310204881871655037148064180352817205156628246575600279413932656728646669341328436632923336729017241613612769539255411478686267789509952238329792095603816448200689361221247398269820710219640465937311672561008269153954842432570808206593550, 259619452⟩
private theorem pole3621_793_45_checked :
    packedBlock 3621 793 pole3621_793_45.length 5113 pole3621_793_45.packed = pole3621_793_45.total := by decide +kernel

private def poleBlocks3621_793 : List Block := [pole3621_793_0, pole3621_793_1, pole3621_793_2, pole3621_793_3, pole3621_793_4, pole3621_793_5, pole3621_793_6, pole3621_793_7, pole3621_793_8, pole3621_793_9, pole3621_793_10, pole3621_793_11, pole3621_793_12, pole3621_793_13, pole3621_793_14, pole3621_793_15, pole3621_793_16, pole3621_793_17, pole3621_793_18, pole3621_793_19, pole3621_793_20, pole3621_793_21, pole3621_793_22, pole3621_793_23, pole3621_793_24, pole3621_793_25, pole3621_793_26, pole3621_793_27, pole3621_793_28, pole3621_793_29, pole3621_793_30, pole3621_793_31, pole3621_793_32, pole3621_793_33, pole3621_793_34, pole3621_793_35, pole3621_793_36, pole3621_793_37, pole3621_793_38, pole3621_793_39, pole3621_793_40, pole3621_793_41, pole3621_793_42, pole3621_793_43, pole3621_793_44, pole3621_793_45]
theorem moment3621_793 : P1_7_1.groupedPoleMoment 3621 793 ≤ 4763286079225 := by
  refine grouped_from_blocks 3621 793 _ poleBlocks3621_793 ?_ (by decide) (by decide)
  exact ⟨pole3621_793_0_checked, pole3621_793_1_checked, pole3621_793_2_checked, pole3621_793_3_checked, pole3621_793_4_checked, pole3621_793_5_checked, pole3621_793_6_checked, pole3621_793_7_checked, pole3621_793_8_checked, pole3621_793_9_checked, pole3621_793_10_checked, pole3621_793_11_checked, pole3621_793_12_checked, pole3621_793_13_checked, pole3621_793_14_checked, pole3621_793_15_checked, pole3621_793_16_checked, pole3621_793_17_checked, pole3621_793_18_checked, pole3621_793_19_checked, pole3621_793_20_checked, pole3621_793_21_checked, pole3621_793_22_checked, pole3621_793_23_checked, pole3621_793_24_checked, pole3621_793_25_checked, pole3621_793_26_checked, pole3621_793_27_checked, pole3621_793_28_checked, pole3621_793_29_checked, pole3621_793_30_checked, pole3621_793_31_checked, pole3621_793_32_checked, pole3621_793_33_checked, pole3621_793_34_checked, pole3621_793_35_checked, pole3621_793_36_checked, pole3621_793_37_checked, pole3621_793_38_checked, pole3621_793_39_checked, pole3621_793_40_checked, pole3621_793_41_checked, pole3621_793_42_checked, pole3621_793_43_checked, pole3621_793_44_checked, pole3621_793_45_checked, True.intro⟩

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

private def pole3621_819_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 539902776⟩
private theorem pole3621_819_0_checked :
    packedBlock 3621 819 pole3621_819_0.length 819 pole3621_819_0.packed = pole3621_819_0.total := by decide +kernel

private def pole3621_819_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 3626942520⟩
private theorem pole3621_819_1_checked :
    packedBlock 3621 819 pole3621_819_1.length 915 pole3621_819_1.packed = pole3621_819_1.total := by decide +kernel

private def pole3621_819_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 9534078264⟩
private theorem pole3621_819_2_checked :
    packedBlock 3621 819 pole3621_819_2.length 1011 pole3621_819_2.packed = pole3621_819_2.total := by decide +kernel

private def pole3621_819_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 18006506040⟩
private theorem pole3621_819_3_checked :
    packedBlock 3621 819 pole3621_819_3.length 1107 pole3621_819_3.packed = pole3621_819_3.total := by decide +kernel

private def pole3621_819_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 28789421880⟩
private theorem pole3621_819_4_checked :
    packedBlock 3621 819 pole3621_819_4.length 1203 pole3621_819_4.packed = pole3621_819_4.total := by decide +kernel

private def pole3621_819_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 41628021816⟩
private theorem pole3621_819_5_checked :
    packedBlock 3621 819 pole3621_819_5.length 1299 pole3621_819_5.packed = pole3621_819_5.total := by decide +kernel

private def pole3621_819_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 56267501880⟩
private theorem pole3621_819_6_checked :
    packedBlock 3621 819 pole3621_819_6.length 1395 pole3621_819_6.packed = pole3621_819_6.total := by decide +kernel

private def pole3621_819_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 72453058104⟩
private theorem pole3621_819_7_checked :
    packedBlock 3621 819 pole3621_819_7.length 1491 pole3621_819_7.packed = pole3621_819_7.total := by decide +kernel

private def pole3621_819_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 89887856895⟩
private theorem pole3621_819_8_checked :
    packedBlock 3621 819 pole3621_819_8.length 1587 pole3621_819_8.packed = pole3621_819_8.total := by decide +kernel

private def pole3621_819_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 107225345120⟩
private theorem pole3621_819_9_checked :
    packedBlock 3621 819 pole3621_819_9.length 1683 pole3621_819_9.packed = pole3621_819_9.total := by decide +kernel

private def pole3621_819_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 123174646880⟩
private theorem pole3621_819_10_checked :
    packedBlock 3621 819 pole3621_819_10.length 1779 pole3621_819_10.packed = pole3621_819_10.total := by decide +kernel

private def pole3621_819_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 137672981600⟩
private theorem pole3621_819_11_checked :
    packedBlock 3621 819 pole3621_819_11.length 1875 pole3621_819_11.packed = pole3621_819_11.total := by decide +kernel

private def pole3621_819_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 150720349280⟩
private theorem pole3621_819_12_checked :
    packedBlock 3621 819 pole3621_819_12.length 1971 pole3621_819_12.packed = pole3621_819_12.total := by decide +kernel

private def pole3621_819_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 162316749920⟩
private theorem pole3621_819_13_checked :
    packedBlock 3621 819 pole3621_819_13.length 2067 pole3621_819_13.packed = pole3621_819_13.total := by decide +kernel

private def pole3621_819_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 172462183520⟩
private theorem pole3621_819_14_checked :
    packedBlock 3621 819 pole3621_819_14.length 2163 pole3621_819_14.packed = pole3621_819_14.total := by decide +kernel

private def pole3621_819_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 181156650080⟩
private theorem pole3621_819_15_checked :
    packedBlock 3621 819 pole3621_819_15.length 2259 pole3621_819_15.packed = pole3621_819_15.total := by decide +kernel

private def pole3621_819_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 188400149600⟩
private theorem pole3621_819_16_checked :
    packedBlock 3621 819 pole3621_819_16.length 2355 pole3621_819_16.packed = pole3621_819_16.total := by decide +kernel

private def pole3621_819_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 194192682080⟩
private theorem pole3621_819_17_checked :
    packedBlock 3621 819 pole3621_819_17.length 2451 pole3621_819_17.packed = pole3621_819_17.total := by decide +kernel

private def pole3621_819_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 198534247520⟩
private theorem pole3621_819_18_checked :
    packedBlock 3621 819 pole3621_819_18.length 2547 pole3621_819_18.packed = pole3621_819_18.total := by decide +kernel

private def pole3621_819_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 201424845920⟩
private theorem pole3621_819_19_checked :
    packedBlock 3621 819 pole3621_819_19.length 2643 pole3621_819_19.packed = pole3621_819_19.total := by decide +kernel

private def pole3621_819_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 202864477280⟩
private theorem pole3621_819_20_checked :
    packedBlock 3621 819 pole3621_819_20.length 2739 pole3621_819_20.packed = pole3621_819_20.total := by decide +kernel

private def pole3621_819_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 202853141600⟩
private theorem pole3621_819_21_checked :
    packedBlock 3621 819 pole3621_819_21.length 2835 pole3621_819_21.packed = pole3621_819_21.total := by decide +kernel

private def pole3621_819_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 201390838880⟩
private theorem pole3621_819_22_checked :
    packedBlock 3621 819 pole3621_819_22.length 2931 pole3621_819_22.packed = pole3621_819_22.total := by decide +kernel

private def pole3621_819_23 : Block := ⟨96, 54001174345304575867478254153289749865965580889477410725941361893251041970219880745145295515138602395337822043935948032401877441567273503421450836664419675223839941740157703730617515717360449347268364951044137563855607314996071255343987659217872140214086429176526228318893366241748387532916164491565025430369387319635631792599543138993784246342708498155382892944926351902724493735043151083157305827035297, 198477569120⟩
private theorem pole3621_819_23_checked :
    packedBlock 3621 819 pole3621_819_23.length 3027 pole3621_819_23.packed = pole3621_819_23.total := by decide +kernel

private def pole3621_819_24 : Block := ⟨96, 56251223335968514060149821932192110550534539335492654082660765215438632494405300590528311359385003052716811747635274019407765123505173211434352729017607344907430644593383333231350865817658979801684163144185199990341175071205704452085816119312888125439821500262931902091352788480563552017297998901156484339850689023521985798973899386439509010666835697339508280634459328639766048645563733721625963951851777, 194113332320⟩
private theorem pole3621_819_24_checked :
    packedBlock 3621 819 pole3621_819_24.length 3123 pole3621_819_24.packed = pole3621_819_24.total := by decide +kernel

private def pole3621_819_25 : Block := ⟨96, 58501272326632452252821389711094471235103497781507897439380168537626223018590720435911327203631403710095801451334600006413652805443072919447254621370795014591021347446608962732084215917957510256099961337326262416826742827415337648827644579407904110665556571349337575863812210719378716501679833310747943249331990727408339805348255633885233774990962896523633668323992305376807603556084316360094622076668257, 188298128480⟩
private theorem pole3621_819_25_checked :
    packedBlock 3621 819 pole3621_819_25.length 3219 pole3621_819_25.packed = pole3621_819_25.total := by decide +kernel

private def pole3621_819_26 : Block := ⟨96, 60751321317296390445492957489996831919672456227523140796099571859813813542776140281294343047877804367474791155033925993419540487380972627460156513723982684274612050299834592232817566018256040710515759530467324843312310583624970845569473039502920095891291642435743249636271632958193880986061667720339402158813292431294693811722611881330958539315090095707759056013525282113849158466604898998563280201484737, 181031957600⟩
private theorem pole3621_819_26_checked :
    packedBlock 3621 819 pole3621_819_26.length 3315 pole3621_819_26.packed = pole3621_819_26.total := by decide +kernel

private def pole3621_819_27 : Block := ⟨96, 63001370307960328638164525268899192604241414673538384152818975182001404066961560126677358892124205024853780858733251980425428169318872335473058406077170353958202753153060221733550916118554571164931557723608387269797878339834604042311301499597936081117026713522148923408731055197009045470443502129930861068294594135181047818096968128776683303639217294891884443703058258850890713377125481637031938326301217, 172314819680⟩
private theorem pole3621_819_27_checked :
    packedBlock 3621 819 pole3621_819_27.length 3411 pole3621_819_27.packed = pole3621_819_27.total := by decide +kernel

private def pole3621_819_28 : Block := ⟨96, 65251419298624266830836093047801553288810373119553627509538378504188994591146979972060374736370605682232770562432577967431315851256772043485960298430358023641793456006285851234284266218853101619347355916749449696283446096044237239053129959692952066342761784608554597181190477435824209954825336539522319977775895839067401824471324376222408067963344494076009831392591235587932268287646064275500596451117697, 162146714720⟩
private theorem pole3621_819_28_checked :
    packedBlock 3621 819 pole3621_819_28.length 3507 pole3621_819_28.packed = pole3621_819_28.total := by decide +kernel

private def pole3621_819_29 : Block := ⟨96, 67454592268649372977827003164643448125784144931276886629659460923831010312745203570664577751264919712360903602177827954032852945064236245755460981387185610520913923690120222361885595609905666453347360781928918730849782066571567190220209830960996306523593692780085903204880170172428104217971812550485168972170373113058122048026931041021145197815871270741644459445910888709135684181317340835749331356650209, 150611069214⟩
private theorem pole3621_819_29_checked :
    packedBlock 3621 819 pole3621_819_29.length 3603 pole3621_819_29.packed = pole3621_819_29.total := by decide +kernel

private def pole3621_819_30 : Block := ⟨96, 69517137176757988316962491697326496468664684988142679392446085426339307116265521311534934284717120589386108479559267073730352799265817247351456522723231932052514748430275234795177925924506195608120009129772197251617354051478679426591998777310943761273409017742320925255022631447022616493725790147473874458443368602485434923709657258722727868370829804211070591333212707058460015141707546776041083458554687, 138337650884⟩
private theorem pole3621_819_30_checked :
    packedBlock 3621 819 pole3621_819_30.length 3699 pole3621_819_30.packed = pole3621_819_30.total := by decide +kernel

private def pole3621_819_31 : Block := ⟨96, 71462492033356826275981404008289659874790975889223973599237209484580834735144783215598995902841417694912875036602540448370362349510303661918781316893418509315415121864409265461034080628417923927741638885105754753847116824745437356604531554319724752154607331105723592002345831996709469386144427467627426936324668602612201180447265588251723782658793910913961985239205312954473589352975228028873356580621207, 125733801383⟩
private theorem pole3621_819_31_checked :
    packedBlock 3621 819 pole3621_819_31.length 3795 pole3621_819_31.packed = pole3621_819_31.total := by decide +kernel

private def pole3621_819_32 : Block := ⟨96, 73290656838183962665394149825021667254354436950722864547729103236956134229878848394297401714610815436533621369360693715424089055745179812053272296001300697086680560031177862427533036763969984667114836114085754028662394260558796482559678250985034845094264233392008604865878781103015144067058376893257616003311547130655831727358797510756184285275750432339785928378457426234086870005118801789604196546956266, 112977937973⟩
private theorem pole3621_819_32_checked :
    packedBlock 3621 819 pole3621_819_32.length 3891 pole3621_819_32.packed = pole3621_819_32.total := by decide +kernel

private def pole3621_819_33 : Block := ⟨96, 74954757001405122321726859641207208158612261427154577181065614946510091854131555118354932753451384326846539487427593892463421958036426082879234762299888145667382046567839015052093425333995637756032621704040079244880510932432806466500676153790254630939538062028148708924448631263662014828914839902796516825288147360297000607136496545251266041284400798173360641556732237814319535820471256891639184747269175, 100240150003⟩
private theorem pole3621_819_33_checked :
    packedBlock 3621 819 pole3621_819_33.length 3987 pole3621_819_33.packed = pole3621_819_33.total := by decide +kernel

private def pole3621_819_34 : Block := ⟨96, 76525102262263379146220812176577857417460282927670816881650179214606780581255566048857876094029377908217209122111906853677038074501881647617142142205691206800989918853499310442170525658741976364770593395493014150502848672537958201690753385746570193152177597377233050563582852461701828659572876581707553953770656885727218795407435211556433572030555181729461602573215147754258993389711415853129146768034943, 87683068870⟩
private theorem pole3621_819_34_checked :
    packedBlock 3621 819 pole3621_819_34.length 4083 pole3621_819_34.packed = pole3621_819_34.total := by decide +kernel

private def pole3621_819_35 : Block := ⟨96, 77931382881515648580237429106484241898702439496269003785198576360644314211541590918949179364072101723820928414557151347558597593432541220289188271996359147877258263948334344636413992984443517040364531420677356990943053285189017735751199082565475202089428832508592656849408338799724218203740749280294451816503052579810545603902218505438957496847701691904535970433498192172831947518613381230267826474880193, 75461869003⟩
private theorem pole3621_819_35_checked :
    packedBlock 3621 819 pole3621_819_35.length 4179 pole3621_819_35.packed = pole3621_819_35.total := by decide +kernel

private def pole3621_819_36 : Block := ⟨96, 79220473449083529836455514814358695488078565019359247220810319239440960145723464550613317350972429784528957023789293941540751480631768499461707593370207458026651870224669506365942566550060974603362033288952986608638114047301078708313259398473778454006175504077271244135579040407824263875651941173934661518655246858692600436523378536158816240382664227844399069935531820943473138129669227973554265630149886, 63724266600⟩
private theorem pole3621_819_36_checked :
    packedBlock 3621 819 pole3621_819_36.length 4275 pole3621_819_36.packed = pole3621_819_36.total := by decide +kernel

private def pole3621_819_37 : Block := ⟨96, 80228309323273732789987417877799199650742626838645430404655257301681772896801988852211521422772974581324230215925497284648723993958150470939336599743375893964619691262219445356414595978501122685411792906143877520614200173904670900674599929895754245398672282986273807843189955038831385570778772153333139607846087745546353787005448751997634288460519451481244959994382728165765944639723118889957359635746101, 52603060366⟩
private theorem pole3621_819_37_checked :
    packedBlock 3621 819 pole3621_819_37.length 4371 pole3621_819_37.packed = pole3621_819_37.total := by decide +kernel

private def pole3621_819_38 : Block := ⟨96, 80790821570939717338155309822524789821884866450149241243835108132228670527848343813557275383834574745668977641850328781402519520183761407643833203338191929253017791147447190383292340490979188278722230829723826051473114867332285567852956634611109407286250475340302035886110233472896296947073141178249759146133746725319035791640253563747996798048572500108707461050758422214224784056476738121001039008615775, 42143051512⟩
private theorem pole3621_819_38_checked :
    packedBlock 3621 819 pole3621_819_38.length 4467 pole3621_819_38.packed = pole3621_819_38.total := by decide +kernel

private def pole3621_819_39 : Block := ⟨96, 81353333818605701886323201767250379993027106061653052083014958962775568158894698774903029344896174910013725067775160278153991440668236334647058676426488846673915466860753597758475678016053820892326180378009091658094506806384693867038413749634863403592684243111903454329225089032600088068168599780647623873504072151290624293233842625609427989129604299904738807973141666398485172784106883780618203539819895, 32608790776⟩
private theorem pole3621_819_39_checked :
    packedBlock 3621 819 pole3621_819_39.length 4563 pole3621_819_39.packed = pole3621_819_39.total := by decide +kernel

private def pole3621_819_40 : Block := ⟨96, 81915846066271686434491093711975970164169345673156862922194809793322465789941053736248783305957775074358472493699991774905463361152711261650284149514785764094813142574060005133659015541128453505930129926294357264715898745437102166223870864658617399899118010883504872772339944592303879189264058383045488600874397577262212794827431687470859180210636099700770154895524910582745561511737029440235368071024015, 24138231544⟩
private theorem pole3621_819_40_checked :
    packedBlock 3621 819 pole3621_819_40.length 4659 pole3621_819_40.packed = pole3621_819_40.total := by decide +kernel

private def pole3621_819_41 : Block := ⟨96, 82478358313937670982658985656701560335311585284660673761374660623869363420987408697594537267019375238703219919624823271656935281637186188653509622603082681515710818287366412508842353066203086119534079474579622871337290684489510465409327979682371396205551778655106291215454800152007670310359516985443353328244723003233801296421020749332290371291667899496801501817908154767005950239367175099852532602228135, 16811000056⟩
private theorem pole3621_819_41_checked :
    packedBlock 3621 819 pole3621_819_41.length 4755 pole3621_819_41.packed = pole3621_819_41.total := by decide +kernel

private def pole3621_819_42 : Block := ⟨96, 83040870561603655530826877601427150506453824896164484600554511454416261052033763658940291228080975403047967345549654768408407202121661115656735095691379598936608494000672819884025690591277718733138029022864888477958682623541918764594785094706125392511985546426707709658569655711711461431454975587841218055615048429205389798014609811193721562372699699292832848740291398951266338966997320759469697133432255, 10706722552⟩
private theorem pole3621_819_42_checked :
    packedBlock 3621 819 pole3621_819_42.length 4851 pole3621_819_42.packed = pole3621_819_42.total := by decide +kernel

private def pole3621_819_43 : Block := ⟨96, 83603382809269640078994769546152740677596064507668295439734362284963158683080118620286045189142575567392714771474486265159879122606136042659960568779676516357506169713979227259209028116352351346741978571150154084580074562594327063780242209729879388818419314198309128101684511271415252552550434190239082782985373855176978299608198873055152753453731499088864195662674643135526727694627466419086861664636375, 5905025272⟩
private theorem pole3621_819_43_checked :
    packedBlock 3621 819 pole3621_819_43.length 4947 pole3621_819_43.packed = pole3621_819_43.total := by decide +kernel

private def pole3621_819_44 : Block := ⟨96, 84165895056935624627162661490878330848738304119172106278914213115510056314126473581631799150204175731737462197399317761911351043090610969663186041867973433778403845427285634634392365641426983960345928119435419691201466501646735362965699324753633385124853081969910546544799366831119043673645892792636947510355699281148566801201787934916583944534763298884895542585057887319787116422257612078704026195840495, 2485534456⟩
private theorem pole3621_819_44_checked :
    packedBlock 3621 819 pole3621_819_44.length 5043 pole3621_819_44.packed = pole3621_819_44.total := by decide +kernel

private def pole3621_819_45 : Block := ⟨96, 84728407304601609175330553435603921019880543730675917118094063946056953945172828542977553111265775896082209623324149258662822963575085896666411514956270351199301521140592042009575703166501616573949877667720685297822858440699143662151156439777387381431286849741511964987914222390822834794741351395034812237726024707120155302795376996778015135615795098680926889507441131504047505149887757738321190727044615, 527876344⟩
private theorem pole3621_819_45_checked :
    packedBlock 3621 819 pole3621_819_45.length 5139 pole3621_819_45.packed = pole3621_819_45.total := by decide +kernel

private def pole3621_819_46 : Block := ⟨24, 30939524626966540572046604875530996644011465144923434818351059993634054579157436900437717848546594335, 4975126⟩
private theorem pole3621_819_46_checked :
    packedBlock 3621 819 pole3621_819_46.length 5235 pole3621_819_46.packed = pole3621_819_46.total := by decide +kernel

private def poleBlocks3621_819 : List Block := [pole3621_819_0, pole3621_819_1, pole3621_819_2, pole3621_819_3, pole3621_819_4, pole3621_819_5, pole3621_819_6, pole3621_819_7, pole3621_819_8, pole3621_819_9, pole3621_819_10, pole3621_819_11, pole3621_819_12, pole3621_819_13, pole3621_819_14, pole3621_819_15, pole3621_819_16, pole3621_819_17, pole3621_819_18, pole3621_819_19, pole3621_819_20, pole3621_819_21, pole3621_819_22, pole3621_819_23, pole3621_819_24, pole3621_819_25, pole3621_819_26, pole3621_819_27, pole3621_819_28, pole3621_819_29, pole3621_819_30, pole3621_819_31, pole3621_819_32, pole3621_819_33, pole3621_819_34, pole3621_819_35, pole3621_819_36, pole3621_819_37, pole3621_819_38, pole3621_819_39, pole3621_819_40, pole3621_819_41, pole3621_819_42, pole3621_819_43, pole3621_819_44, pole3621_819_45, pole3621_819_46]
theorem moment3621_819 : P1_7_1.groupedPoleMoment 3621 819 ≤ 4884209183309 := by
  refine grouped_from_blocks 3621 819 _ poleBlocks3621_819 ?_ (by decide) (by decide)
  exact ⟨pole3621_819_0_checked, pole3621_819_1_checked, pole3621_819_2_checked, pole3621_819_3_checked, pole3621_819_4_checked, pole3621_819_5_checked, pole3621_819_6_checked, pole3621_819_7_checked, pole3621_819_8_checked, pole3621_819_9_checked, pole3621_819_10_checked, pole3621_819_11_checked, pole3621_819_12_checked, pole3621_819_13_checked, pole3621_819_14_checked, pole3621_819_15_checked, pole3621_819_16_checked, pole3621_819_17_checked, pole3621_819_18_checked, pole3621_819_19_checked, pole3621_819_20_checked, pole3621_819_21_checked, pole3621_819_22_checked, pole3621_819_23_checked, pole3621_819_24_checked, pole3621_819_25_checked, pole3621_819_26_checked, pole3621_819_27_checked, pole3621_819_28_checked, pole3621_819_29_checked, pole3621_819_30_checked, pole3621_819_31_checked, pole3621_819_32_checked, pole3621_819_33_checked, pole3621_819_34_checked, pole3621_819_35_checked, pole3621_819_36_checked, pole3621_819_37_checked, pole3621_819_38_checked, pole3621_819_39_checked, pole3621_819_40_checked, pole3621_819_41_checked, pole3621_819_42_checked, pole3621_819_43_checked, pole3621_819_44_checked, pole3621_819_45_checked, pole3621_819_46_checked, True.intro⟩

private def pole3901_834_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 582489656⟩
private theorem pole3901_834_0_checked :
    packedBlock 3901 834 pole3901_834_0.length 834 pole3901_834_0.packed = pole3901_834_0.total := by decide +kernel

private def pole3901_834_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 3919835960⟩
private theorem pole3901_834_1_checked :
    packedBlock 3901 834 pole3901_834_1.length 930 pole3901_834_1.packed = pole3901_834_1.total := by decide +kernel

private def pole3901_834_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 10325004344⟩
private theorem pole3901_834_2_checked :
    packedBlock 3901 834 pole3901_834_2.length 1026 pole3901_834_2.packed = pole3901_834_2.total := by decide +kernel

private def pole3901_834_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 19543190840⟩
private theorem pole3901_834_3_checked :
    packedBlock 3901 834 pole3901_834_3.length 1122 pole3901_834_3.packed = pole3901_834_3.total := by decide +kernel

private def pole3901_834_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 31319591480⟩
private theorem pole3901_834_4_checked :
    packedBlock 3901 834 pole3901_834_4.length 1218 pole3901_834_4.packed = pole3901_834_4.total := by decide +kernel

private def pole3901_834_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 45399402296⟩
private theorem pole3901_834_5_checked :
    packedBlock 3901 834 pole3901_834_5.length 1314 pole3901_834_5.packed = pole3901_834_5.total := by decide +kernel

private def pole3901_834_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 61527819320⟩
private theorem pole3901_834_6_checked :
    packedBlock 3901 834 pole3901_834_6.length 1410 pole3901_834_6.packed = pole3901_834_6.total := by decide +kernel

private def pole3901_834_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 79450038584⟩
private theorem pole3901_834_7_checked :
    packedBlock 3901 834 pole3901_834_7.length 1506 pole3901_834_7.packed = pole3901_834_7.total := by decide +kernel

private def pole3901_834_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 98897568845⟩
private theorem pole3901_834_8_checked :
    packedBlock 3901 834 pole3901_834_8.length 1602 pole3901_834_8.packed = pole3901_834_8.total := by decide +kernel

private def pole3901_834_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 118679231360⟩
private theorem pole3901_834_9_checked :
    packedBlock 3901 834 pole3901_834_9.length 1698 pole3901_834_9.packed = pole3901_834_9.total := by decide +kernel

private def pole3901_834_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 137132704640⟩
private theorem pole3901_834_10_checked :
    packedBlock 3901 834 pole3901_834_10.length 1794 pole3901_834_10.packed = pole3901_834_10.total := by decide +kernel

private def pole3901_834_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 154108668800⟩
private theorem pole3901_834_11_checked :
    packedBlock 3901 834 pole3901_834_11.length 1890 pole3901_834_11.packed = pole3901_834_11.total := by decide +kernel

private def pole3901_834_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 169607123840⟩
private theorem pole3901_834_12_checked :
    packedBlock 3901 834 pole3901_834_12.length 1986 pole3901_834_12.packed = pole3901_834_12.total := by decide +kernel

private def pole3901_834_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 183628069760⟩
private theorem pole3901_834_13_checked :
    packedBlock 3901 834 pole3901_834_13.length 2082 pole3901_834_13.packed = pole3901_834_13.total := by decide +kernel

private def pole3901_834_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 196171506560⟩
private theorem pole3901_834_14_checked :
    packedBlock 3901 834 pole3901_834_14.length 2178 pole3901_834_14.packed = pole3901_834_14.total := by decide +kernel

private def pole3901_834_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 207237434240⟩
private theorem pole3901_834_15_checked :
    packedBlock 3901 834 pole3901_834_15.length 2274 pole3901_834_15.packed = pole3901_834_15.total := by decide +kernel

private def pole3901_834_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 216825852800⟩
private theorem pole3901_834_16_checked :
    packedBlock 3901 834 pole3901_834_16.length 2370 pole3901_834_16.packed = pole3901_834_16.total := by decide +kernel

private def pole3901_834_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 224936762240⟩
private theorem pole3901_834_17_checked :
    packedBlock 3901 834 pole3901_834_17.length 2466 pole3901_834_17.packed = pole3901_834_17.total := by decide +kernel

private def pole3901_834_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 231570162560⟩
private theorem pole3901_834_18_checked :
    packedBlock 3901 834 pole3901_834_18.length 2562 pole3901_834_18.packed = pole3901_834_18.total := by decide +kernel

private def pole3901_834_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 236726053760⟩
private theorem pole3901_834_19_checked :
    packedBlock 3901 834 pole3901_834_19.length 2658 pole3901_834_19.packed = pole3901_834_19.total := by decide +kernel

private def pole3901_834_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 240404435840⟩
private theorem pole3901_834_20_checked :
    packedBlock 3901 834 pole3901_834_20.length 2754 pole3901_834_20.packed = pole3901_834_20.total := by decide +kernel

private def pole3901_834_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 242605308800⟩
private theorem pole3901_834_21_checked :
    packedBlock 3901 834 pole3901_834_21.length 2850 pole3901_834_21.packed = pole3901_834_21.total := by decide +kernel

private def pole3901_834_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 243328672640⟩
private theorem pole3901_834_22_checked :
    packedBlock 3901 834 pole3901_834_22.length 2946 pole3901_834_22.packed = pole3901_834_22.total := by decide +kernel

private def pole3901_834_23 : Block := ⟨96, 54001174345304575867478254153289749865965580889477410725941361893251041970219880745145295515138602395337822043935948032401877441567273503421450836664419675223839941740157703730617515717360449347268364951044137563855607314996071255343987659217872140214086429176526228318893366241748387532916164491565025430369387319635631792599543138993784246342708498155382892944926351902724493735043151083157305827035297, 242574527360⟩
private theorem pole3901_834_23_checked :
    packedBlock 3901 834 pole3901_834_23.length 3042 pole3901_834_23.packed = pole3901_834_23.total := by decide +kernel

private def pole3901_834_24 : Block := ⟨96, 56251223335968514060149821932192110550534539335492654082660765215438632494405300590528311359385003052716811747635274019407765123505173211434352729017607344907430644593383333231350865817658979801684163144185199990341175071205704452085816119312888125439821500262931902091352788480563552017297998901156484339850689023521985798973899386439509010666835697339508280634459328639766048645563733721625963951851777, 240342872960⟩
private theorem pole3901_834_24_checked :
    packedBlock 3901 834 pole3901_834_24.length 3138 pole3901_834_24.packed = pole3901_834_24.total := by decide +kernel

private def pole3901_834_25 : Block := ⟨96, 58501272326632452252821389711094471235103497781507897439380168537626223018590720435911327203631403710095801451334600006413652805443072919447254621370795014591021347446608962732084215917957510256099961337326262416826742827415337648827644579407904110665556571349337575863812210719378716501679833310747943249331990727408339805348255633885233774990962896523633668323992305376807603556084316360094622076668257, 236633709440⟩
private theorem pole3901_834_25_checked :
    packedBlock 3901 834 pole3901_834_25.length 3234 pole3901_834_25.packed = pole3901_834_25.total := by decide +kernel

private def pole3901_834_26 : Block := ⟨96, 60751321317296390445492957489996831919672456227523140796099571859813813542776140281294343047877804367474791155033925993419540487380972627460156513723982684274612050299834592232817566018256040710515759530467324843312310583624970845569473039502920095891291642435743249636271632958193880986061667720339402158813292431294693811722611881330958539315090095707759056013525282113849158466604898998563280201484737, 231447036800⟩
private theorem pole3901_834_26_checked :
    packedBlock 3901 834 pole3901_834_26.length 3330 pole3901_834_26.packed = pole3901_834_26.total := by decide +kernel

private def pole3901_834_27 : Block := ⟨96, 63001370307960328638164525268899192604241414673538384152818975182001404066961560126677358892124205024853780858733251980425428169318872335473058406077170353958202753153060221733550916118554571164931557723608387269797878339834604042311301499597936081117026713522148923408731055197009045470443502129930861068294594135181047818096968128776683303639217294891884443703058258850890713377125481637031938326301217, 224782855040⟩
private theorem pole3901_834_27_checked :
    packedBlock 3901 834 pole3901_834_27.length 3426 pole3901_834_27.packed = pole3901_834_27.total := by decide +kernel

private def pole3901_834_28 : Block := ⟨96, 65251419298624266830836093047801553288810373119553627509538378504188994591146979972060374736370605682232770562432577967431315851256772043485960298430358023641793456006285851234284266218853101619347355916749449696283446096044237239053129959692952066342761784608554597181190477435824209954825336539522319977775895839067401824471324376222408067963344494076009831392591235587932268287646064275500596451117697, 216641164160⟩
private theorem pole3901_834_28_checked :
    packedBlock 3901 834 pole3901_834_28.length 3522 pole3901_834_28.packed = pole3901_834_28.total := by decide +kernel

private def pole3901_834_29 : Block := ⟨96, 67501468289288205023507660826703913973379331565568870866257781826376585115332399817443390580617006339611760266131903954437203533194671751498862190783545693325384158859511480735017616319151632073763154109890512122769013852253870435794958419787968051568496855694960270953649899674639374439207170949113778887257197542953755830845680623668132832287471693260135219082124212324973823198166646913969254575934177, 207021964160⟩
private theorem pole3901_834_29_checked :
    packedBlock 3901 834 pole3901_834_29.length 3618 pole3901_834_29.packed = pole3901_834_29.total := by decide +kernel

private def pole3901_834_30 : Block := ⟨96, 69751517279952143216179228605606274657948290011584114222977185148564175639517819662826406424863406996990749969831229941443091215132571459511764083136733363008974861712737110235750966419450162528178952303031574549254581608463503632536786879882984036794231926781365944726109321913454538923589005358705237796738499246840109837220036871113857596611598892444260606771657189062015378108687229552437912700750657, 195925255040⟩
private theorem pole3901_834_30_checked :
    packedBlock 3901 834 pole3901_834_30.length 3714 pole3901_834_30.packed = pole3901_834_30.total := by decide +kernel

private def pole3901_834_31 : Block := ⟨96, 71978128260296665386335735287328623521688935678060056042839838705592666906236985920216869136526220134403703744979314512479336361919636593816774355966771605284796984714794516694070389188414578945432721186194519496836543648438306027112279168309590985180023486299911212651326827797074471394919132624493524177383076218993832141564568006944789495157418105706055858119732172756514308337401513516848605439757217, 183351065897⟩
private theorem pole3901_834_31_checked :
    packedBlock 3901 834 pole3901_834_31.length 3810 pole3901_834_31.packed = pole3901_834_31.total := by decide +kernel

private def pole3901_834_32 : Block := ⟨96, 74157864650544977544830411652329067642010811515482118424652351645590594337804677846248410297230202102150087520670239943600545729152736133618080997636645629880150262471468836508592405584673301046075459754538301914952767503489850605042974579704645695827097101121904238971208763426960075132783319732429869001520918805518123075922777801847984624591584899016826482409405232420502608803258632695833664644205568, 169503648947⟩
private theorem pole3901_834_32_checked :
    packedBlock 3901 834 pole3901_834_32.length 3906 pole3901_834_32.packed = pole3901_834_32.total := by decide +kernel

private def pole3901_834_33 : Block := ⟨96, 76220408128110965520109985971162278359398966144267183048527669448631223906664383770010975274334244507738686873596537757230779775336796481091501110974342784657098337069245130386744722670046470992483639297971293695267683820428292296005302170747864487358161903370528029983048840126826951744493841165778203644278609462536859747871415265114202706237989055536289626456752739085241850293573457917389556845874269, 155139227413⟩
private theorem pole3901_834_33_checked :
    packedBlock 3901 834 pole3901_834_33.length 4002 pole3901_834_33.packed = pole3901_834_33.total := by decide +kernel

private def pole3901_834_34 : Block := ⟨96, 78142324974303079393016969967196620009145814344041803190559877123316448777213002583498012695031003656353665658015060222201505777488884202867361252747432359449907520272050506143750946711515442354490691990721270235451143827069372053675412382576677648496421822158083762870008107402103571543473871467720867214751292552246963451512778204610221499974513080644106319761825687177634560430891383319209639171427509, 140572691263⟩
private theorem pole3901_834_34_checked :
    packedBlock 3901 834 pole3901_834_34.length 4098 pole3901_834_34.packed = pole3901_834_34.total := by decide +kernel

private def pole3901_834_35 : Block := ⟨96, 79923613758666010521340112011415462094523087388215362754057078584713075581941659984429469919423740551562897198724193928092776062716068385802794861885979833899352814622841836542537001160216269751707563367618386428958335799938396856780393863839872872944762910435982904652851256932248045631547694361864888146087589586935043693871399051046543616024842313452393581008286908322014197420847121569527629894241543, 125980075554⟩
private theorem pole3901_834_35_checked :
    packedBlock 3901 834 pole3901_834_35.length 4194 pole3901_834_35.packed = pole3901_834_35.total := by decide +kernel

private def pole3901_834_36 : Block := ⟨96, 81587712491344548143003478866117241582496684595054345465456840139701276587000012561404191640856705747043487806823089419335011823392197349460499472798217538084761566558413815760154844367809694851067098859045370663682695780742040270914213673951293998343356151571386616259770080985684869980906382285804830139839723199334947305524008959115459915480429510024739622149348345803430540122373631627142297107631443, 111530092491⟩
private theorem pole3901_834_36_checked :
    packedBlock 3901 834 pole3901_834_36.length 4290 pole3901_834_36.packed = pole3901_834_36.total := by decide +kernel

private def pole3901_834_37 : Block := ⟨96, 83111184592561898270161292840939982368975935315734292314132997079449567276461526300847337947898610893952945475670909993296953763393069772820809307240503649445371364918636730044774748045689925605006804805209855289517719933415881168326622083438230644751468889610298752299985581498622568990969321563032519001741715353061293914347160773644479834555042508786909342060982048922015417457069343749132075638623642, 97384131051⟩
private theorem pole3901_834_37_checked :
    packedBlock 3901 834 pole3901_834_37.length 4386 pole3901_834_37.packed = pole3901_834_37.total := by decide +kernel

private def pole3901_834_38 : Block := ⟨96, 84517465211726859640581022702753957801345255423109631923456849281664244011958258443861728503381989907162176695232853180365249436102231620521336721990764592647428404397083600690497982767294233718218887311123695186697673169619089924431155475189888001695302143641921540903351737212791796467475716059131299687862347867732193526389188192279416908674915260877626322804222580773702395847434287588602670082362843, 83696255661⟩
private theorem pole3901_834_38_checked :
    packedBlock 3901 834 pole3901_834_38.length 4482 pole3901_834_38.packed = pole3901_834_38.total := by decide +kernel

private def pole3901_834_39 : Block := ⟨96, 85806554348839432254262668451559241823383630297093254161990154547281599625605826129317194806641389942411709205840141535361073615599825039318032824189970545615311826185388642082283470953730460165667319776629248308125361499573420813194453888579494191596622064510118893781152277093556553102957524832107421346999105383375498662368348812022899385421308996162707614324915351356884715740533278972195409135783447, 70613207743⟩
private theorem pole3901_834_39_checked :
    packedBlock 3901 834 pole3901_834_39.length 4578 pole3901_834_39.packed = pole3901_834_39.total := by decide +kernel

private def pole3901_834_40 : Block := ⟨96, 86744076192158695202870452240869425968880389993538016007411252342751390113526382179603925365006808455988791937298124062184286626203027642012417955864596520527443708532698858859324046244676465507986691128236890534104910675749788697094726462470924788994794330510633970932465328761731572256366804721271743433919432665867231799642586546050308796464360061395237306275766667017119708831745895970482756307357261, 58261746292⟩
private theorem pole3901_834_40_checked :
    packedBlock 3901 834 pole3901_834_40.length 4674 pole3901_834_40.packed = pole3901_834_40.total := by decide +kernel

private def pole3901_834_41 : Block := ⟨96, 87306588439824679751038344185595016140022629605041826846591103173298287744572737140949679326068408620333539363222955558935758546687502569015643428952893437948368698100227702374105083572483595538315020322459025420189946527829492660660955080743051357983098382115281843338431626610909281870617142734193054229243394407639868364846252811729898485207366952000470998479314445552864644464192850734267175964348021, 46688113424⟩
private theorem pole3901_834_41_checked :
    packedBlock 3901 834 pole3901_834_41.length 4770 pole3901_834_41.packed = pole3901_834_41.total := by decide +kernel

private def pole3901_834_42 : Block := ⟨96, 87869100687490664299206236130320606311164869216545637685770954003845185375619092102295433287130008784678286789147787055687230467171977496018868902041190355369266373813534109749288421097558228151918969870744291026811338466881900959846412195766805354289532149886883261781546482170613072991712601336590918956613719833611456866439841873591329676288398751796502345401697689737125033191822996393884340495552141, 36170431760⟩
private theorem pole3901_834_42_checked :
    packedBlock 3901 834 pole3901_834_42.length 4866 pole3901_834_42.packed = pole3901_834_42.total := by decide +kernel

private def pole3901_834_43 : Block := ⟨96, 88431612935156648847374128075046196482307108828049448524950804834392083006665447063641187248191608949023034215072618552438702387656452423022094375129487272790164049526840517124471758622632860765522919419029556633432730405934309259031869310790559350595965917658484680224661337730316864112808059938988783683984045259583045368033430935452760867369430551592533692324080933921385421919453142053501505026756261, 26834508560⟩
private theorem pole3901_834_43_checked :
    packedBlock 3901 834 pole3901_834_43.length 4962 pole3901_834_43.packed = pole3901_834_43.total := by decide +kernel

private def pole3901_834_44 : Block := ⟨96, 88994125182822633395542020019771786653449348439553259364130655664938980637711802024986941209253209113367781640997450049190174308140927350025319848217784190211061725240146924499655096147707493379126868967314822240054122344986717558217326425814313346902399685430086098667776193290020655233903518541386648411354370685554633869627019997314192058450462351388565039246464178105645810647083287713118669557960381, 18759970064⟩
private theorem pole3901_834_44_checked :
    packedBlock 3901 834 pole3901_834_44.length 5058 pole3901_834_44.packed = pole3901_834_44.total := by decide +kernel

private def pole3901_834_45 : Block := ⟨96, 89556637430488617943709911964497376824591588051057070203310506495485878268758156986332695170314809277712529066922281545941646228625402277028545321306081107631959400953453331874838433672782125992730818515600087846675514284039125857402783540838067343208833453201687517110891048849724446354998977143784513138724696111526222371220609059175623249531494151184596386168847422289906199374713433372735834089164501, 12026442512⟩
private theorem pole3901_834_45_checked :
    packedBlock 3901 834 pole3901_834_45.length 5154 pole3901_834_45.packed = pole3901_834_45.total := by decide +kernel

private def pole3901_834_46 : Block := ⟨96, 90119149678154602491877803909222966995733827662560881042490357326032775899804511947678449131376409442057276492847113042693118149109877204031770794394378025052857076666759739250021771197856758606334768063885353453296906223091534156588240655861821339515267220973288935554005904409428237476094435746182377866095021537497810872814198121037054440612525950980627733091230666474166588102343579032352998620368621, 6713552144⟩
private theorem pole3901_834_46_checked :
    packedBlock 3901 834 pole3901_834_46.length 5250 pole3901_834_46.packed = pole3901_834_46.total := by decide +kernel

private def pole3901_834_47 : Block := ⟨96, 90681661925820587040045695853948557166876067274064691881670208156579673530850866909024203092438009606402023918771944539444590069594352131034996267482674942473754752380066146625205108722931391219938717612170619059918298162143942455773697770885575335821700988744890353997120759969132028597189894348580242593465346963469399374407787182898485631693557750776659080013613910658426976829973724691970163151572741, 2900925200⟩
private theorem pole3901_834_47_checked :
    packedBlock 3901 834 pole3901_834_47.length 5346 pole3901_834_47.packed = pole3901_834_47.total := by decide +kernel

private def pole3901_834_48 : Block := ⟨96, 91244174173486571588213587798674147338018306885568502720850058987126571161897221870369957053499609770746771344696776036196061990078827058038221740570971859894652428093372554000388446248006023833542667160455884666539690101196350754959154885909329332128134756516491772440235615528835819718285352950978107320835672389440987876001376244759916822774589550572690426935997154842687365557603870351587327682776861, 668187920⟩
private theorem pole3901_834_48_checked :
    packedBlock 3901 834 pole3901_834_48.length 5442 pole3901_834_48.packed = pole3901_834_48.total := by decide +kernel

private def pole3901_834_49 : Block := ⟨31, 10563324887266038960095753986781617224604186790774605271291652976766663387903096137696431883979573603783668962837350957317226336053, 11101616⟩
private theorem pole3901_834_49_checked :
    packedBlock 3901 834 pole3901_834_49.length 5538 pole3901_834_49.packed = pole3901_834_49.total := by decide +kernel

private def poleBlocks3901_834 : List Block := [pole3901_834_0, pole3901_834_1, pole3901_834_2, pole3901_834_3, pole3901_834_4, pole3901_834_5, pole3901_834_6, pole3901_834_7, pole3901_834_8, pole3901_834_9, pole3901_834_10, pole3901_834_11, pole3901_834_12, pole3901_834_13, pole3901_834_14, pole3901_834_15, pole3901_834_16, pole3901_834_17, pole3901_834_18, pole3901_834_19, pole3901_834_20, pole3901_834_21, pole3901_834_22, pole3901_834_23, pole3901_834_24, pole3901_834_25, pole3901_834_26, pole3901_834_27, pole3901_834_28, pole3901_834_29, pole3901_834_30, pole3901_834_31, pole3901_834_32, pole3901_834_33, pole3901_834_34, pole3901_834_35, pole3901_834_36, pole3901_834_37, pole3901_834_38, pole3901_834_39, pole3901_834_40, pole3901_834_41, pole3901_834_42, pole3901_834_43, pole3901_834_44, pole3901_834_45, pole3901_834_46, pole3901_834_47, pole3901_834_48, pole3901_834_49]
theorem moment3901_834 : P1_7_1.groupedPoleMoment 3901 834 ≤ 6296101689637 := by
  refine grouped_from_blocks 3901 834 _ poleBlocks3901_834 ?_ (by decide) (by decide)
  exact ⟨pole3901_834_0_checked, pole3901_834_1_checked, pole3901_834_2_checked, pole3901_834_3_checked, pole3901_834_4_checked, pole3901_834_5_checked, pole3901_834_6_checked, pole3901_834_7_checked, pole3901_834_8_checked, pole3901_834_9_checked, pole3901_834_10_checked, pole3901_834_11_checked, pole3901_834_12_checked, pole3901_834_13_checked, pole3901_834_14_checked, pole3901_834_15_checked, pole3901_834_16_checked, pole3901_834_17_checked, pole3901_834_18_checked, pole3901_834_19_checked, pole3901_834_20_checked, pole3901_834_21_checked, pole3901_834_22_checked, pole3901_834_23_checked, pole3901_834_24_checked, pole3901_834_25_checked, pole3901_834_26_checked, pole3901_834_27_checked, pole3901_834_28_checked, pole3901_834_29_checked, pole3901_834_30_checked, pole3901_834_31_checked, pole3901_834_32_checked, pole3901_834_33_checked, pole3901_834_34_checked, pole3901_834_35_checked, pole3901_834_36_checked, pole3901_834_37_checked, pole3901_834_38_checked, pole3901_834_39_checked, pole3901_834_40_checked, pole3901_834_41_checked, pole3901_834_42_checked, pole3901_834_43_checked, pole3901_834_44_checked, pole3901_834_45_checked, pole3901_834_46_checked, pole3901_834_47_checked, pole3901_834_48_checked, pole3901_834_49_checked, True.intro⟩

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
