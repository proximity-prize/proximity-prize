import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
set_option Elab.async false
set_option autoImplicit true

namespace Research6969.RadiusPowerExclusion
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
  side:ℕ
abbrev A:ℕ:=179730
abbrev Case.box (b : Case) : Fin 2 → ℕ := fun _ => b.side
abbrev Case.shape (b:Case):=b.bank.shape
abbrev Case.N (b:Case):=b.shape.m*A
abbrev Case.maxK (b:Case):=b.shape.J+b.shape.B/b.grade+1

def maxW (b:Case) (lo k:ℕ):=b.N-2*lo*(k-1)-1
def caseCost (b:Case) (lo hi k:ℕ):ℕ:=
  let W:=maxW b lo k
  let cap:=boundGrade b.shape.B b.shape.J W (131071-hi)
  let t:=Pade.layers b.graph b.hits cap b.shape.J k
  min (SpreadWindow.lex cap b.shape.J b.grade k * area b.box)
    (residual (131071-hi) W b.shape.B b.shape.J b.grade k t b.graph b.weight b.side b.seed)
def total (b:Case) (lo hi:ℕ) := HelperWindowGrouping.sumCount (fun i=>caseCost b lo hi (i+1)) b.maxK
def due (b:Case) (h fee:ℕ):=rectDebit h b.bank.nodeRows b.bank.poleMoment b.box+2*h*fee
def supply (b:Case) (h:ℕ):=area b.box*HelperWindowPrefix.volume b.N b.shape.B b.shape.J (131071-h)
def Positive (b:Case) (lo hi:ℕ):Prop:=
  due b lo (total b lo hi)<supply b lo ∧ due b hi (total b lo hi)<supply b hi
instance (b:Case) (lo hi:ℕ):Decidable (Positive b lo hi):=by unfold Positive;infer_instance

private theorem supply_eq (b:Case) {h:ℕ} (narrow:b.shape.J<131071-h):
    supply b h=area b.box*SpreadBucket.raw b.shape A h := by
  unfold supply SpreadBucket.raw
  rw [HelperWindowPrefix.volume_eq_shapeSum _ _ _ narrow]
  congr 2
  funext q j
  rw [Nat.mul_comm (131071-h)]

theorem positive_height (b:Case) {lo hi h:ℕ} (left:lo≤h) (right:h≤hi)
    (hiD:hi≤131071) (narrow:b.shape.J<131071-hi) (full:b.shape.B*(131071-lo)≤b.N)
    (cert:Positive b lo hi):due b h (total b lo hi)<area b.box*SpreadBucket.raw b.shape A h := by
  let fee:=total b lo hi
  let B:=(b.box 0+b.box 1+2)*b.bank.poleMoment+2*fee
  have charge (t:ℕ):due b t fee=area b.box*b.bank.nodeRows+t*B:=by unfold due rectDebit B;ring
  have source (t:ℕ) (l:lo≤t) (r:t≤hi):area b.box*SpreadBucket.raw b.shape A t=
      area b.box*SpreadBucket.raw b.shape A lo+(t-lo)*(area b.box*SpreadBucket.slope b.shape):=by
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
    (size:b.N<p) (nonzero:0<b.N) (rank:P3_7_1.BankOK b.bank) (within:b.side+b.side≤b.shape.U)
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
  let F:=fun W=>finrank FX (rectEvaluated Crt word b.shape W b.box)
  have hl:h≤131070:=by omega
  have step:0<131071-hi:=by omega
  have sw:131071-hi≤131071-h:=Nat.sub_le_sub_left right _
  have wp:0<131071-h:=step.trans_le sw
  have basis:K1_14_1.rawWidthCond h b.shape (b.N-1):=by
    intro q hq j _
    rw [Nat.sub_add_cancel nonzero]
    exact (Nat.mul_le_mul hq (Nat.sub_le_sub_left left _)).trans (full.trans (Nat.le_add_right ..))
  have floor:=KoalaRect.rectRankFloor hp hl (hl.trans_lt (by decide)) Crt word b.shape (b.N-1) b.box within
    rank.moment.2 basis rank.nodes.le rank.moment.1
  rw [Nat.sub_add_cancel nonzero] at floor
  have lex (W:ℕ) (hw:W<b.N):F W≤rectCapacity A h b.shape b.grade b.box (fun _=>0) W:=by
    apply KoalaRect.rectCutoff_finrank_le _ _ _ _ _ _ _ _ pr.primitive.ne_zero grade wp ep
    · intro P hP;exact K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word b.shape W b.box hP)
    · intro P hP;exact KoalaRect.rectEvaluated_axis Crt word hP
    · intro P hP hn;exact P0_10_1.leading_bound hp hl Crt word b.shape W P (KoalaRect.rectEvaluated_le Crt word b.shape W b.box hP) hn
    · intro P hP hn;exact KoalaRect.rectDivides hp Crt word A b.shape b.box size geo (fun q hq=>pass q hq _ fits) pr hw hP hn
    · intro z;simpa [KoalaRect.rectSlots,area] using KoalaRect.rectSlots_antitone b.box (KoalaRect.axisDegree f) (Nat.zero_le z)
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
    apply le_min ((lex W hw).trans (SpreadWindow.rect_lex A h b.grade k W cap b.shape b.box wp ep rfl
      (fun j hj=>grade_le step sw rangeW hj)))
    have upper:min b.shape.B ((W+b.shape.J)/(131071-h))≤cap:=by
      let n:=min b.shape.B ((W+b.shape.J)/(131071-h))
      have l:n*(131071-h)≤W+b.shape.J:=(Nat.le_div_iff_mul_le wp).mp (min_le_right ..)
      exact le_min (min_le_left ..) ((Nat.le_div_iff_mul_le step).mpr
        (((Nat.mul_le_mul_left n sw).trans l).trans (Nat.add_le_add_right rangeW _)))
    have safe:r+1<p:=by have le:r≤b.N-1-W:=Nat.div_le_self ..;omega
    have ord:2*G.graphDegree-1<ys.card:=by rwa [eq,num]
    have hraw:=PadeResidualBank.concentration_rank hp hl Crt word b.box fits safe issued geo pass pr grade gp M native ys v sheets ord cap upper
    rw [eq,num,←kr,same] at hraw
    exact hraw.trans (PowerBox.residual_le _ step sw rangeW wt (seed.trans (PowerBox.seed_sum _)))
  have cap:=SpreadBucket.sum_by_order (scale:=1) (K:=b.maxK) hp F (caseCost b lo hi)
    (fun W hw _=>by simpa only [one_mul] using live W hw)
    (fun W hw far=>Nat.eq_zero_of_le_zero ((lex W hw).trans_eq (SpreadWindow.rect_zero A h b.grade W b.shape b.box wp ep far)))
  have sum_eq:(∑ k∈range b.maxK,caseCost b lo hi (k+1))=total b lo hi:=
    (HelperWindowGrouping.sumCount_eq ..).symm
  rw [one_mul,sum_eq] at cap
  change area b.box*SpreadBucket.raw b.shape A h≤rectDebit h b.bank.nodeRows b.bank.poleMoment b.box+∑ W∈range b.N,F W at floor
  exact (Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left cap _))) (positive_height b left right hiD.le narrow full cert)

end
end Research6969.RadiusPowerExclusion

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0869
set_option autoImplicit true
namespace Research6969.RadiusPowerSheets
noncomputable section
open Research6966 _root_.Research6969.RadiusPowerExclusion Finset Polynomial
open K1 (I)
open K1_14 (L Shape Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField SeedClosure)
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

def entry (radius e a off lower wt:ℕ):Case:=
  ⟨⟨Research6969.SpreadCatalogue.shape,Research6969.SpreadCatalogue.nodes,Research6969.SpreadCatalogue.moment⟩,
  e,a,e-off,wt,lower,radius⟩

theorem prohibit_on {firstHeight lastHeight radius e a off lower wt:ℕ} {ends:List ℕ}
    (checked:PhysicalWindow.Cover (Positive (entry radius e a off lower wt)) lastHeight firstHeight ends) (start:2306≤firstHeight) (finish:lastHeight≤2557)
    (span : radius + radius ≤ 530820) (ep:0<e) (many:2*a-1<e-off) {h} {D:PoleData h} (Crt:CRTLift D) (word:I→L)
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
  let b:=entry radius e a off lower wt
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
  refine _root_.Research6969.RadiusPowerExclusion.excluded b (by omega) lh hr (by omega) narrow wide (by change 3000*179730<K1.p;decide)
    (by change 0<3000*179730;decide) rank span
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

theorem prohibit {radius e a off lower wt:ℕ} {ends:List ℕ}
    (checked:PhysicalWindow.Cover (Positive (entry radius e a off lower wt)) 2313 2306 ends)
    (span : radius + radius ≤ 530820) (ep:0<e) (many:2*a-1<e-off) {h} {D:PoleData h} (Crt:CRTLift D) (word:I→L)
    (lo:2306≤h) (hi:h≤2313) (S:Finset Surface) (has:S.Nonempty) (geo:∀q∈S,Parent q)
    (pass:∀q∈S,TerminalBanks.Pass Crt word A Research6969.SpreadCatalogue.shape q)
    {f:Equation} (whole:ProjectedProduct S f) (degree:e≤f.natDegree)
    {G:Pade.Row SeedField} (native:PadeNativeQuotient.Native G) (gp:G.primitive) (grade:G.graphDegree=a)
    (physical:HelperPhysicalModel.Model Crt native.poly)
    (weight:wt≤RawPhysicalDegree.weight (131071-h) (131071-h-1) physical.raw)
    (seed:lower≤K1_14_2_2_2_1.seedDegree native.poly)
    (control:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) (off+a)) : False :=
  prohibit_on checked (by decide) (by decide) span ep many Crt word lo hi S has geo pass whole degree native gp grade physical weight seed control


end
end Research6969.RadiusPowerSheets
end Z6969Source0869


end Research6970.Height2313
namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1031
set_option autoImplicit true
namespace Research6969.NormalRoute
noncomputable section
open K1 (K I p)
open K1_14 (Equation)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (SeedField)
open _root_.Lower6960.Far6969RescueGeometry (word)
open Research6966
open Research6970.Height2313.Research6969.HighPackets (State)
open Research6970.Height2313.Research6969.BookView (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 15000
theorem radiusPower {i} (r:Region) (radius wt:ℕ) {ends:List ℕ} (floor:wt≤r.graph*(131071-2313)-1)
    (cert:PhysicalWindow.Cover (_root_.Research6969.RadiusPowerExclusion.Positive (Research6970.Height2313.Research6969.RadiusPowerSheets.entry radius r.gradeLo r.graph (r.content-r.graph)
      r.lowSeed wt)) 2313 2306 ends)
    (span : radius + radius ≤ 530820) (pos:0<r.gradeLo) (many:2*r.graph-1<r.gradeLo-(r.content-r.graph)) (fits:r.graph≤r.content):Done i r:=by
  intro s h
  obtain ⟨lo,_,ct,a,seed,_⟩:=h
  have nonempty:(s.pair.main∪s.pair.rescue).Nonempty:=by
    by_contra empty
    have dvd:=NativeOrdinateMass.divides_of_member (D:=1) s.product (fun q h=>False.elim (empty ⟨q,h⟩))
    have zero:=Polynomial.natDegree_le_of_dvd dvd (one_ne_zero:(1:Equation)≠0)
    rw [Polynomial.natDegree_one] at zero
    have high:=s.high;omega
  have geo q (hq:q∈s.pair.main∪s.pair.rescue):K1_14_3.Parent q:=
    (Finset.mem_union.mp hq).elim (fun a=>(s.pair.mainGeo q a).1) (fun a=>(s.pair.rescueGeo q a).1)
  have pass q (hq:q∈s.pair.main∪s.pair.rescue):TerminalBanks.Pass s.crt (word s.model) 179730 SpreadCatalogue.shape q:=
    (Finset.mem_union.mp hq).elim (fun a=>(s.pair.mainGeo q a).2.1) (fun a=>(s.pair.rescueGeo q a).2.1)
  have eq:r.content-r.graph+r.graph=NormalGeometry.content s:=(Nat.sub_add_cancel fits).trans ct.symm
  exact (Research6970.Height2313.Research6969.RadiusPowerSheets.prohibit cert span pos many s.crt (word s.model) (by have age := s.lower; omega) s.higher _ nonempty geo pass s.product lo
    s.native s.gp a s.physical (floor.trans (a ▸ NormalGeometry.base s)) seed (by rw [eq];exact _root_.Research6970.Height2313.Research6969.NormalGeometry.control s)).elim

end
end Research6969.NormalRoute
end Z6969Source1031
end Research6970.Height2313
