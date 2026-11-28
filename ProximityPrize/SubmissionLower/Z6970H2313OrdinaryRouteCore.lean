import ProximityPrize.SubmissionLower.Z6969Pack0641

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.PowerSheets
noncomputable section
open Research6966 Research6969 PowerExclusion Finset Polynomial
open K1 (I)
open K1_14 (L Shape Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField SeedClosure)
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

open Research6969.PowerSheets (entry)

theorem prohibit_on {firstHeight lastHeight e a off lower wt:ℕ} {ends:List ℕ}
    (checked:PhysicalWindow.Cover (Positive (entry e a off lower wt)) lastHeight firstHeight ends) (start:2308≤firstHeight) (finish:lastHeight≤2557)
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

end
end Research6970.Height2313.PowerSheets

namespace Research6970.Height2313.OrdinaryCell
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation L FX atX jetAt)
open K1_14_1 (PoleData CRTLift poleProduct MarkResidues)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Parent Surface SeedField ProjectedProduct)
open _root_.Lower6960
open Research6969
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6966
open PadeNativeQuotient (Native)
open JointLedger (Book)
open Finset Polynomial
open scoped Classical Differential
set_option maxRecDepth 13000
set_option maxHeartbeats 2000000

open Research6969.OrdinaryCell

theorem proves {first last} (b:Row first last) {m:Book} {GCap:ℕ} (ok:b.check m GCap)
    {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (P:Prefix6969Early.Packet F Crt m.fee m.ordinateCredit m.seedCredit GCap m.seedMass)
    (start:0<first) (stop:last≤2557) (lo:first≤M.overhead.toNat) (hi:M.overhead.toNat≤last)
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
end Research6970.Height2313.OrdinaryCell

namespace Research6970.Height2313.OrdinaryRoute
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L)
open K1_14_1 (CRTLift PoleData MarkResidues poleProduct)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface SeedField ProjectedProduct)
open _root_.Lower6960
open Research6969
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
  starts:2308≤first
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
  exact OrdinaryCell.proves b ok x.family x.crt x.packet (by have := x.starts; omega) x.stops x.lowHeight x.highHeight x.projected lo hi x.native x.primitive
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
    (cert:PhysicalWindow.Cover (PowerExclusion.Positive (Research6969.PowerSheets.entry r.gradeLo r.graph
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

theorem seed_split {first last m g e top c a lo hi middle}
    (left : Done first last m g ⟨e,top,c,a,lo,some (middle-1)⟩)
    (right : Done first last m g ⟨e,top,c,a,middle,hi⟩) :
    Done first last m g ⟨e,top,c,a,lo,hi⟩ := by
  intro x h
  obtain ⟨l,t,ct,graph,seed,upper⟩ := h
  by_cases small : seedDegree x.native.poly < middle
  · exact left x ⟨l,t,ct,graph,seed,fun v eq => by
      have same : middle-1=v := Option.some.inj eq
      omega⟩
  · exact right x ⟨l,t,ct,graph,Nat.le_of_not_lt small,upper⟩

theorem grade_split {first last m g lo hi c a low high middle}
    (left : Done first last m g ⟨lo,middle-1,c,a,low,high⟩)
    (right : Done first last m g ⟨middle,hi,c,a,low,high⟩) :
    Done first last m g ⟨lo,hi,c,a,low,high⟩ := by
  intro x h
  obtain ⟨l,t,ct,graph,seed,upper⟩ := h
  by_cases small : x.packet.projected.natDegree < middle
  · exact left x ⟨l,by change x.packet.projected.natDegree ≤ middle-1; omega,ct,graph,seed,upper⟩
  · exact right x ⟨Nat.le_of_not_lt small,t,ct,graph,seed,upper⟩

end
end Research6970.Height2313.OrdinaryRoute
