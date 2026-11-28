import ProximityPrize.SubmissionLower.Z6969Pack0641

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0869
set_option autoImplicit true
namespace Research6969.PowerSheets
noncomputable section
open Research6966 _root_.Research6969.PowerExclusion Finset Polynomial
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

theorem prohibit {e a off lower wt:ℕ} {ends:List ℕ}
    (checked:PhysicalWindow.Cover (Positive (entry e a off lower wt)) 2313 2308 ends)
    (ep:0<e) (many:2*a-1<e-off) {h} {D:PoleData h} (Crt:CRTLift D) (word:I→L)
    (lo:2308≤h) (hi:h≤2313) (S:Finset Surface) (has:S.Nonempty) (geo:∀q∈S,Parent q)
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


end Research6970.Height2313
