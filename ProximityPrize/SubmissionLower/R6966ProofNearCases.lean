import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.High6966Main13200Books
import ProximityPrize.SubmissionLower.High6966Packets
import ProximityPrize.SubmissionLower.R6960ChartGlobalTests
import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts

section Merged6967_R6966ProofNearCases
set_option Elab.async false







set_option Elab.async false

namespace Research6966.NearCases
open Finset Polynomial
open K1 (K)
open K1_14 (FX Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL poleProduct)
open K1_14_2_2 (mass)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open Lower6960
open Rescue6966 (Model Family OnSurface word)
open NearBook (Packet Paid)
open NearLedger (branch)
open PrefixRows (Common)
open scoped Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

abbrev Fits {u del} {M:Model u del} {D:PoleData M.overhead.toNat} {Crt:CRTLift D}
    (b:Packet M Crt) (s:NearLedger.Book) := Paid b s.fee s.credit s.mass s.grade

structure Cover {u del} {M:Model u del} {Γ:Finset K} (F:Family M Γ)
    {D:PoleData M.overhead.toNat} (Crt:CRTLift D) where
  index : Fin 58
  main : Packet M Crt
  rescue : Packet M Crt
  extra : Finset K
  main_ok : Fits main (branch index).primary
  rescue_ok : Fits rescue (branch index).rescue
  extra_ok : extra.card≤(branch index).extra
  covers : ∀ γ∈Γ,γ∈extra ∨ γ∈main.paid ∨ γ∈rescue.paid ∨
    ∃ q∈NearBook.parents main rescue,OnSurface F q γ

variable {u del} {M:Model u del} {Γ:Finset K} {F:Family M Γ}
variable {D:PoleData M.overhead.toNat} {Crt:CRTLift D}

def Cover.invoice (C:Cover F Crt) : NearLedger.Invoice (branch C.index) :=
  ⟨C.extra.card,C.main.paid.card,C.rescue.paid.card,mass C.main.sources 1,mass C.rescue.sources 1,
   C.extra_ok,C.main_ok.price,C.rescue_ok.price,C.main_ok.seedCap,C.rescue_ok.seedCap⟩

def Cover.leftover (C:Cover F Crt) : Finset K := Γ\((C.extra∪C.main.paid)∪C.rescue.paid)

theorem Cover.remaining (C:Cover F Crt) :
    C.leftover⊆Γ ∧ Γ.card≤C.invoice.paid+C.leftover.card ∧
      ∀ γ∈C.leftover,∃q∈NearBook.parents C.main C.rescue,OnSurface F q γ := by
  refine ⟨sdiff_subset,?_,?_⟩
  · let U:=(C.extra∪C.main.paid)∪C.rescue.paid
    have split:=card_sdiff_add_card_inter Γ U
    have cap:(Γ∩U).card≤C.extra.card+C.main.paid.card+C.rescue.paid.card :=
      (card_le_card inter_subset_right).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le ..) _))
    change Γ.card≤C.extra.card+C.main.paid.card+C.rescue.paid.card+(Γ\U).card
    omega
  · rintro γ h
    have hg:=mem_sdiff.mp h
    rcases C.covers γ hg.1 with e|p|r|s
    · exact (hg.2 (mem_union_left _ (mem_union_left _ e))).elim
    · exact (hg.2 (mem_union_left _ (mem_union_right _ p))).elim
    · exact (hg.2 (mem_union_right _ r)).elim
    · exact s

private theorem solo (r:Fin 58) (b:Packet M Crt) (T:Finset K) (pay:Fits b (branch r).primary)
    (count:T.card≤(branch r).extra)
    (marks:∀γ∈Γ,γ∈T ∨ γ∈b.paid ∨ ∃q∈b.parents, OnSurface F q γ) : Nonempty (Cover F Crt) := by
  refine ⟨⟨r,b,NearBook.empty,T,pay,⟨?_,?_,?_⟩,count,?_⟩⟩
  · simp [NearBook.empty,mass]
  · simp [NearBook.empty,mass]
  · simp [NearBook.empty,mass]
  · intro γ h
    rcases marks γ h with e|p|q
    · exact Or.inl e
    · exact Or.inr (Or.inl p)
    · obtain ⟨s,hs,on⟩:=q
      exact Or.inr (Or.inr (Or.inr ⟨s,mem_union_left _ hs,on⟩))

private def roots (F:Family M Γ) (G:Jet) : Finset K :=
  Γ.filter (fun γ=>jetAt G (M.label γ) (F.scalar γ)=0)

private theorem pinned {G H:Jet} {V:Submodule FX Jet} (g:Common V G) (kind:H=1 ∨ Common V H)
    (unique:∀ Q R,Common V Q → Common V R → IsRelPrime Q R → False) (γ:K)
    (zero:jetAt H (M.label γ) (F.scalar γ)=0) : jetAt G (M.label γ) (F.scalar γ)=0 := by
  let ψ:Jet→+*FX:=eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
    (atX (F.scalar γ).derivative)
  change ψ H=0 at zero
  change ψ G=0
  rcases kind with rfl|hc
  · exact (one_ne_zero ((map_one ψ).symm.trans zero)).elim
  · have dv:H∣G:=by
      by_contra no
      exact unique H G hc g (hc.1.isRelPrime_iff_not_dvd.mpr no)
    obtain ⟨q,eq⟩:=dv
    rw [eq,map_mul,zero,zero_mul]

private theorem either_marks {V:Submodule FX Jet} {G H:Jet} (g:Common V G) (kind:H=1 ∨ Common V H)
    (unique:∀ Q R,Common V Q → Common V R → IsRelPrime Q R → False) (γ:K) (mem:γ∈Γ) :
    γ∈roots F G ∨ γ∈Γ.filter (fun z=>jetAt H (M.label z) (F.scalar z)≠0) := by
  by_cases z:jetAt H (M.label γ) (F.scalar γ)=0
  · exact Or.inl (mem_filter.mpr ⟨mem,pinned g kind unique γ z⟩)
  · exact Or.inr (mem_filter.mpr ⟨mem,z⟩)

private def high (i:Fin 54) : Fin 58 := ⟨4+i.val,by have:=i.isLt;omega⟩
private theorem high_books (i:Fin 54) :
    (branch (high i)).primary=⟨127815628075157321,1729755992975,4460,246⟩ ∧
    (branch (high i)).rescue=⟨Rescue6966.paidCap i,Rescue6966.retainedCredit i,
      (Rescue6966Source.data i).bound 1,(Rescue6966Source.data i).bound 0⟩ := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

private theorem high_pair {v:ℕ} (pos:0<v) (small:v≤92) :
    ∃ i:Fin 12,(Pair6966.row i).cap=8418 ∧ (Pair6966.row i).degree=2 ∧
      (Pair6966.row i).wt=(QuadraticBudget.band v).2 ∧ (Pair6966.row i).seed≤v :=
  (by decide +kernel : ∀ n:Fin 93,0<n.val → ∃ i:Fin 12,(Pair6966.row i).cap=8418 ∧
    (Pair6966.row i).degree=2 ∧ (Pair6966.row i).wt=(QuadraticBudget.band n.val).2 ∧
    (Pair6966.row i).seed≤n.val) ⟨v,by omega⟩ pos

theorem exists_cover (F:Family M Γ) (Crt:CRTLift D) (lo:2317≤M.overhead.toNat) (hi:M.overhead.toNat≤2522)
    (nop:∀ j i,(D.block j).eval (nodeL i)≠0)
    (res:∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (Cover F Crt) := by
  classical
  obtain ⟨R⟩:=High6966Main20142.source_rows F Crt lo (hi.trans (by decide)) nop res
  let G:=R.out.exception
  let T:=roots F G
  have Tsub:T⊆Γ:=filter_subset ..
  have Tzero:∀γ∈T,jetAt G (M.label γ) (F.scalar γ)=0:=fun _ hz=>(mem_filter.mp hz).2
  rcases R.out.kind with one|owner
  · obtain ⟨b,paid,cover⟩:=NearPacket.main20142 R hi nop res
    apply solo 0 b ∅ paid (by decide : (0:ℕ)≤(branch 0).extra)
    intro γ hγ
    apply Or.inr
    apply cover γ (mem_filter.mpr ⟨hγ,?_⟩)
    simp [one,jetAt]
  have known:Common (Pair6966.space Crt (word M) 10280) G:=owner
  obtain ⟨slope,jp,jmax,sp,smax,smix⟩:=Wide6966Helper.helper_common_caps Crt (word M) lo (hi.trans (by decide))
    known.1 known.2.2.1 known.2.1 known.2.2.2
  obtain ⟨phys⟩:=HelperPhysicalModel.exists_model Crt known.1 known.2.1
  let w:=131071-M.overhead.toNat
  let weight:=RawPhysicalDegree.weight w (w-1) phys.raw
  have base (n:ℕ) (le:n≤jetDegree G) : 128549*n-1≤weight := by
    have a:=HelperWeightCap.weight_lower phys known.1.ne_zero w (by dsimp [w];omega)
    have low:128549≤w:=by dsimp [w];omega
    have b:=Nat.mul_le_mul low le
    change w*jetDegree G≤weight+G.natDegree at a
    omega
  have mainWide (γ:K) (hg:γ∈Γ) : γ∈T ∨ γ∈R.marks := by
    by_cases z:jetAt G (M.label γ) (F.scalar γ)=0
    · exact Or.inl (mem_filter.mpr ⟨hg,z⟩)
    · exact Or.inr (mem_filter.mpr ⟨hg,z⟩)
  have medium (k:Fin 12) (cap:(Pair6966.row k).cap=8813) (deg:(Pair6966.row k).degree≤jetDegree G)
      (seed:(Pair6966.row k).seed≤seedDegree G) (wt:(Pair6966.row k).wt≤weight) (index:Fin 58)
      (pay:(branch index).primary=⟨130933022881678518,1729199597045,4592,246⟩)
      (count:T.card≤(branch index).extra) : Nonempty (Cover F Crt) := by
    obtain ⟨Q⟩:=Pair6966.chosen15000 F Crt k cap lo hi nop res known phys deg wt seed
    have uniq:=Pair6966.unique Crt (word M) k lo hi known phys deg wt seed
    rw [cap] at uniq
    have on:Common (Pair6966.space Crt (word M) 8813) G :=
      ⟨known.1,known.2.1,known.2.2.1,fun P hp=>known.2.2.2 P (Pair6966.space_mono Crt (word M) (by decide : 8813≤10280) hp)⟩
    obtain ⟨b,paid,cover⟩:=NearPacket.main15000 Q hi nop res
    apply solo index b T (by unfold Fits;rw [pay];exact paid) count
    intro γ hg
    rcases either_marks (F:=F) on Q.out.kind uniq γ hg with left|right
    · exact Or.inl left
    · exact Or.inr (cover γ right)
  by_cases affine:jetDegree G=1
  · by_cases low:seedDegree G≤19
    · have cap:=NearAffineHelper.helper_bound F Tsub hi known.1 slope affine 19 (by decide) low (by decide) Tzero
      obtain ⟨b,paid,cover⟩:=NearPacket.main20142 R hi nop res
      apply solo 1 b T paid (cap.trans (by decide +kernel))
      intro γ hg
      exact (mainWide γ hg).imp_right (cover γ)
    · have cap:=NearAffineHelper.helper_bound F Tsub hi known.1 slope affine 96 (by decide) smax (by decide) Tzero
      exact medium 0 rfl (by change 1≤jetDegree G;omega) (by change 20≤seedDegree G;omega)
        (base 1 jp) 2 rfl (cap.trans (by decide +kernel))
  have two:2≤jetDegree G:=by omega
  have seed92:=smix two
  by_cases light:jetDegree G=2 ∧ weight<(QuadraticBudget.band (seedDegree G)).2
  · letI : UniqueFactorizationMonoid K1_14.Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
    letI : UniqueFactorizationMonoid K1_14.Equation := Polynomial.uniqueFactorizationMonoid (D:=K1_14.Seeds)
    letI : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=K1_14.Equation)
    have pr:=UniqueFactorizationMonoid.irreducible_iff_prime.mp known.1
    have count:=QuadraticHelper6966.low_count F Tsub lo hi phys pr slope light.1 (seedDegree G) seed92
      ((K1_14_2_2_2_1.seedDegree_le G _).mp le_rfl) light.2 (Int.self_le_toNat _)
      (fun i=>by change (poleProduct D).eval (nodeL i)≠0;rw [poleProduct,eval_mul];exact mul_ne_zero (nop 0 i) (nop 1 i))
      (fun γ h=>res γ (Tsub h)) Tzero
    exact medium 1 rfl two sp (base 2 two) 3 rfl count
  have wtQuad : jetDegree G=2 → (QuadraticBudget.band (seedDegree G)).2≤weight :=
    fun q=>Nat.le_of_not_gt (fun l=>light ⟨q,l⟩)
  obtain ⟨k,cap,degree,seed,wt⟩ : ∃ k:Fin 12,(Pair6966.row k).cap=8418 ∧
      (Pair6966.row k).degree≤jetDegree G ∧ (Pair6966.row k).seed≤seedDegree G ∧ (Pair6966.row k).wt≤weight := by
    by_cases quad:jetDegree G=2
    · obtain ⟨k,h,deg,ww,ss⟩:=high_pair sp seed92
      exact ⟨k,h,deg.le.trans two,ss,ww.le.trans (wtQuad quad)⟩
    · have three:3≤jetDegree G:=by omega
      exact ⟨11,rfl,three,sp,base 3 three⟩
  obtain ⟨Q⟩:=Pair6966.chosen13200 F Crt k cap lo hi nop res known phys degree wt seed
  have uniq:=Pair6966.unique Crt (word M) k lo hi known phys degree wt seed
  rw [cap] at uniq
  have on:Common (Pair6966.space Crt (word M) 8418) G :=
    ⟨known.1,known.2.1,known.2.2.1,fun P hp=>known.2.2.2 P (Pair6966.space_mono Crt (word M) (by decide : 8418≤10280) hp)⟩
  obtain ⟨S,_⟩:=HelperRescueCatalogue.selected F Crt lo hi nop res phys known.1 slope two jmax sp seed92 wtQuad
  obtain ⟨b,bp,bc⟩:=NearPacket.main13200 Q hi nop res
  obtain ⟨c,cp,cc⟩:=NearPacket.rescue S hi nop res
  obtain ⟨left,right⟩:=high_books S.rect
  refine ⟨⟨high S.rect,b,c,∅,by unfold Fits;rw [left];exact bp,
    by unfold Fits;rw [right];exact cp,by simp,?_⟩⟩
  intro γ hg
  rcases either_marks (F:=F) on Q.out.kind uniq γ hg with captured|regular
  · rcases cc γ hg (Tzero γ captured) with paid|⟨q,hq,mark⟩
    · exact Or.inr (Or.inr (Or.inl paid))
    · exact Or.inr (Or.inr (Or.inr ⟨q,mem_union_right _ hq,mark⟩))
  · rcases bc γ regular with paid|⟨q,hq,mark⟩
    · exact Or.inr (Or.inl paid)
    · exact Or.inr (Or.inr (Or.inr ⟨q,mem_union_left _ hq,mark⟩))

#print axioms exists_cover
end
end Research6966.NearCases

end Merged6967_R6966ProofNearCases

section Merged6967_R6966ProofNearTerminalGeometry
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NearTerminal
open Finset Polynomial
open K1 (p I)
open K1_14 (Jet Equation L)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree seedDegree_le)
open K1_14_3 (Surface Parent ProjectedProduct SeedField SeedClosure)
open PadeNativeQuotient (Native axis axis_le)
open NearLedger
open NearBook
open Lower6960.Rescue6966 (terminalShape)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 6500000
set_option maxRecDepth 6500
set_option backward.isDefEq.respectTransparency false

theorem axis_seed (P : Jet) (z : Fin 2) : axis P z≤seedDegree P :=
  (axis_le ..).mpr (fun j i=>
    (MvPolynomial.degreeOf_le_totalDegree ..).trans ((seedDegree_le P _).mp le_rfl j i))

theorem seeded_of_positive {P : Jet} (pos : 0<seedDegree P) : K1_14_2.UsesSeed P := by
  unfold K1_14_2.UsesSeed
  by_contra! none
  exact (Nat.not_le_of_lt pos) ((seedDegree_le P 0).mpr none)

private theorem catalogue_lower (k : Fin 264) : 0<(HelperWindowCatalogue.ordinary k).lower := by
  fin_cases k <;> decide

theorem quotient_bound {h : ℕ} (lo : 2317≤h) (hi : h≤2522) {D : PoleData h}
    (Crt : CRTLift D) (word : I→L)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (phys : HelperPhysicalModel.Model Crt N.poly)
    {S : Finset Surface} {H : Equation} (witness : NativeWitnessBank.witnessed N S H)
    (geo : ∀ q∈S,Parent q) (pass : ∀ q∈S,TerminalBanks.Pass Crt word agreement terminalShape q)
    {i j : Fin 55} (bin₀ : InBin i (axis N.poly 0)) (bin₁ : InBin j (axis N.poly 1))
    (pick : Pick) (legal : pick.Valid G.graphDegree i j) :
    (pick.bank.reserve+1)*H.natDegree≤pick.bank.B+(G.graphDegree-1)*pick.bank.J ∧
      ∀ z u, upper (binAt i j z)=some u →
        (pick.bank.reserve+1)*KoalaRect.axisDegree H z≤pick.seedBudget z+pick.bank.J*u := by
  have bins (z : Fin 2) : InBin (binAt i j z) (axis N.poly z) := by
    fin_cases z
    · exact bin₀
    · exact bin₁
  have lower : if pick.bank.rect then pick.bank.lower≤axis N.poly pick.narrow
      else pick.bank.lower≤seedDegree N.poly := by
    have admission := legal.2
    cases tag : pick.bank.rect
    · simp only [tag,Bool.false_eq_true,ite_false] at admission ⊢
      exact admission.trans (max_le (bin₀.1.trans (axis_seed ..)) (bin₁.1.trans (axis_seed ..)))
    · simp only [tag,ite_true] at admission ⊢
      exact admission.trans (bins pick.narrow).1
  have seed : pick.bank.lower≤seedDegree N.poly := by
    split at lower
    · exact lower.trans (axis_seed ..)
    · exact lower
  have seeded := seeded_of_positive ((catalogue_lower pick.index).trans_le seed)
  have fits : TerminalBanks.inside pick.bank.shape terminalShape :=
    HelperWindowNative.shape_inside pick.verified terminalShape (by decide) (by decide) (by decide)
  have est := HelperWindowNative.projected_bounds pick.verified lo hi Crt word N gp phys legal.1.symm seeded
    witness fits (axis N.poly) pick.narrow
    (fun j i z => (axis_le ..).mp le_rfl j i) lower geo pass
  refine ⟨est.1,fun z u hu => (est.2 z).trans ?_⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ((bins z).2 u hu)) _

/-- A witness of high second-axis degree on a degree-five graph forces
17 distinct actual on-graph ordinates into the physical exclusion. -/
theorem large_graph19g5 {h : ℕ} (lo : 2317≤h) (hi : h≤2522) {D : PoleData h} (Crt : CRTLift D)
    (word : I→L) {S : Finset Surface} (has : S.Nonempty) (geo : ∀ q∈S,Parent q)
    (pass : ∀ q∈S,TerminalBanks.Pass Crt word agreement terminalShape q)
    {f : Equation} (full : ProjectedProduct S f) (degree : 19≤f.natDegree)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (graphDegree : G.graphDegree=5) (large : 4096≤axis N.poly 1)
    (control : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 8) :
    False := by
  classical
  obtain ⟨f',T,v,pr,size,sheets⟩:=Pade.Native.projected_sheets S has geo
  let on := T.filter (fun y=>(G.map (algebraMap SeedField Pade.Native.Sep)).err v y=0)
  let off := T\on
  have miss := control off v (by
    intro y hy
    obtain ⟨mem,bad⟩:=mem_sdiff.mp hy
    exact ⟨sheets y mem,fun zero=>bad (mem_filter.mpr ⟨mem,zero⟩)⟩)
  rw [Pade.Row.degree_map,graphDegree] at miss
  have total : on.card+off.card=T.card := by
    rw [Nat.add_comm]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have many : 19≤T.card := degree.trans_eq ((same_degree full pr).trans size.symm)
  obtain ⟨kept,subset,keepSize⟩:=exists_subset_card_eq (show 16≤on.card by omega)
  let emb : Pade.Native.Sep→+*SeedClosure := (separableClosure SeedField SeedClosure).val.toRingHom
  let pts := kept.image emb
  let slope (z : SeedClosure) := if H:∃y∈kept,emb y=z then emb (v H.choose) else 0
  have atPoint (y : Pade.Native.Sep) (hy : y∈kept) : slope (emb y)=emb (v y) := by
    have H : ∃ z∈kept,emb z=emb y := ⟨y,hy,rfl⟩
    simp only [slope,dite_eq_left H,emb.injective H.choose_spec.2]
  have n : pts.card=16 := (card_image_of_injective _ emb.injective).trans keepSize
  have fit : TerminalBanks.inside LargeSeed19g5.shape terminalShape := by unfold TerminalBanks.inside; decide
  have sheets0 : ∀ y∈pts, (∃ q∈S, K1_14_3.OnSeedFibre q y (slope y)) ∧ (G.map (algebraMap SeedField SeedClosure)).err slope y=0 := by
    intro y hy
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
    have picked : z∈on := subset hz
    obtain ⟨tz,ok⟩:=mem_filter.mp picked
    rw [atPoint z hz]
    refine ⟨(Pade.Native.sheets_iff S z (v z)).mp (sheets z tz),?_⟩
    change (G.a.map (algebraMap SeedField SeedClosure)).eval (emb z)*slope (emb z)-
      (G.b.map (algebraMap SeedField SeedClosure)).eval (emb z)=0
    rw [atPoint z hz]
    have lifted (Q : SeedField[X]) :
        emb ((Q.map (algebraMap SeedField Pade.Native.Sep)).eval z)=
          (Q.map (algebraMap SeedField SeedClosure)).eval (emb z) := by
      rw [eval_map,eval_map]
      exact (Polynomial.aeval_algHom_apply (separableClosure SeedField SeedClosure).val z Q).symm
    have law := congrArg emb ok
    simp only [Pade.Row.err,Pade.Row.map,map_sub,map_mul,map_zero] at law
    rwa [lifted,lifted] at law
  exact LargeSeed19g5At2317.excluded (by omega) (by omega) Crt word fit geo pass full (by omega : 19≤f.natDegree) gp graphDegree N large pts slope n sheets0

theorem large_graph19g6 {h : ℕ} (lo : 2317≤h) (hi : h≤2522) {D : PoleData h} (Crt : CRTLift D)
    (word : I→L) {S : Finset Surface} (has : S.Nonempty) (geo : ∀ q∈S,Parent q)
    (pass : ∀ q∈S,TerminalBanks.Pass Crt word agreement terminalShape q)
    {f : Equation} (full : ProjectedProduct S f) (degree : 19≤f.natDegree)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (graphDegree : G.graphDegree=6) (large : 3968≤axis N.poly 1)
    (control : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 8) :
    False := by
  classical
  obtain ⟨f',T,v,pr,size,sheets⟩:=Pade.Native.projected_sheets S has geo
  let on := T.filter (fun y=>(G.map (algebraMap SeedField Pade.Native.Sep)).err v y=0)
  let off := T\on
  have miss := control off v (by
    intro y hy
    obtain ⟨mem,bad⟩:=mem_sdiff.mp hy
    exact ⟨sheets y mem,fun zero=>bad (mem_filter.mpr ⟨mem,zero⟩)⟩)
  rw [Pade.Row.degree_map,graphDegree] at miss
  have total : on.card+off.card=T.card := by
    rw [Nat.add_comm]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have many : 19≤T.card := degree.trans_eq ((same_degree full pr).trans size.symm)
  obtain ⟨kept,subset,keepSize⟩:=exists_subset_card_eq (show 17≤on.card by omega)
  let emb : Pade.Native.Sep→+*SeedClosure := (separableClosure SeedField SeedClosure).val.toRingHom
  let pts := kept.image emb
  let slope (z : SeedClosure) := if H:∃y∈kept,emb y=z then emb (v H.choose) else 0
  have atPoint (y : Pade.Native.Sep) (hy : y∈kept) : slope (emb y)=emb (v y) := by
    have H : ∃ z∈kept,emb z=emb y := ⟨y,hy,rfl⟩
    simp only [slope,dite_eq_left H,emb.injective H.choose_spec.2]
  have n : pts.card=17 := (card_image_of_injective _ emb.injective).trans keepSize
  have fit : TerminalBanks.inside LargeSeed19g6.shape terminalShape := by unfold TerminalBanks.inside; decide
  have sheets0 : ∀ y∈pts, (∃ q∈S, K1_14_3.OnSeedFibre q y (slope y)) ∧ (G.map (algebraMap SeedField SeedClosure)).err slope y=0 := by
    intro y hy
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
    have picked : z∈on := subset hz
    obtain ⟨tz,ok⟩:=mem_filter.mp picked
    rw [atPoint z hz]
    refine ⟨(Pade.Native.sheets_iff S z (v z)).mp (sheets z tz),?_⟩
    change (G.a.map (algebraMap SeedField SeedClosure)).eval (emb z)*slope (emb z)-
      (G.b.map (algebraMap SeedField SeedClosure)).eval (emb z)=0
    rw [atPoint z hz]
    have lifted (Q : SeedField[X]) :
        emb ((Q.map (algebraMap SeedField Pade.Native.Sep)).eval z)=
          (Q.map (algebraMap SeedField SeedClosure)).eval (emb z) := by
      rw [eval_map,eval_map]
      exact (Polynomial.aeval_algHom_apply (separableClosure SeedField SeedClosure).val z Q).symm
    have law := congrArg emb ok
    simp only [Pade.Row.err,Pade.Row.map,map_sub,map_mul,map_zero] at law
    rwa [lifted,lifted] at law
  by_cases h2331 : h≤2331
  · exact LargeSeed19g6At2317.excluded (by omega) (by omega) Crt word fit geo pass full (by omega : 19≤f.natDegree) gp graphDegree N large pts slope n sheets0
  exact LargeSeed19g6At2332.excluded (by omega) (by omega) Crt word fit geo pass full (by omega : 19≤f.natDegree) gp graphDegree N large pts slope n sheets0

theorem large_graph21g5 {h : ℕ} (lo : 2317≤h) (hi : h≤2522) {D : PoleData h} (Crt : CRTLift D)
    (word : I→L) {S : Finset Surface} (has : S.Nonempty) (geo : ∀ q∈S,Parent q)
    (pass : ∀ q∈S,TerminalBanks.Pass Crt word agreement terminalShape q)
    {f : Equation} (full : ProjectedProduct S f) (degree : 21≤f.natDegree)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (graphDegree : G.graphDegree=5) (large : 4096≤axis N.poly 1)
    (control : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 8) :
    False := by
  classical
  obtain ⟨f',T,v,pr,size,sheets⟩:=Pade.Native.projected_sheets S has geo
  let on := T.filter (fun y=>(G.map (algebraMap SeedField Pade.Native.Sep)).err v y=0)
  let off := T\on
  have miss := control off v (by
    intro y hy
    obtain ⟨mem,bad⟩:=mem_sdiff.mp hy
    exact ⟨sheets y mem,fun zero=>bad (mem_filter.mpr ⟨mem,zero⟩)⟩)
  rw [Pade.Row.degree_map,graphDegree] at miss
  have total : on.card+off.card=T.card := by
    rw [Nat.add_comm]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have many : 21≤T.card := degree.trans_eq ((same_degree full pr).trans size.symm)
  obtain ⟨kept,subset,keepSize⟩:=exists_subset_card_eq (show 17≤on.card by omega)
  let emb : Pade.Native.Sep→+*SeedClosure := (separableClosure SeedField SeedClosure).val.toRingHom
  let pts := kept.image emb
  let slope (z : SeedClosure) := if H:∃y∈kept,emb y=z then emb (v H.choose) else 0
  have atPoint (y : Pade.Native.Sep) (hy : y∈kept) : slope (emb y)=emb (v y) := by
    have H : ∃ z∈kept,emb z=emb y := ⟨y,hy,rfl⟩
    simp only [slope,dite_eq_left H,emb.injective H.choose_spec.2]
  have n : pts.card=17 := (card_image_of_injective _ emb.injective).trans keepSize
  have fit : TerminalBanks.inside LargeSeed21g5.shape terminalShape := by unfold TerminalBanks.inside; decide
  have sheets0 : ∀ y∈pts, (∃ q∈S, K1_14_3.OnSeedFibre q y (slope y)) ∧ (G.map (algebraMap SeedField SeedClosure)).err slope y=0 := by
    intro y hy
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
    have picked : z∈on := subset hz
    obtain ⟨tz,ok⟩:=mem_filter.mp picked
    rw [atPoint z hz]
    refine ⟨(Pade.Native.sheets_iff S z (v z)).mp (sheets z tz),?_⟩
    change (G.a.map (algebraMap SeedField SeedClosure)).eval (emb z)*slope (emb z)-
      (G.b.map (algebraMap SeedField SeedClosure)).eval (emb z)=0
    rw [atPoint z hz]
    have lifted (Q : SeedField[X]) :
        emb ((Q.map (algebraMap SeedField Pade.Native.Sep)).eval z)=
          (Q.map (algebraMap SeedField SeedClosure)).eval (emb z) := by
      rw [eval_map,eval_map]
      exact (Polynomial.aeval_algHom_apply (separableClosure SeedField SeedClosure).val z Q).symm
    have law := congrArg emb ok
    simp only [Pade.Row.err,Pade.Row.map,map_sub,map_mul,map_zero] at law
    rwa [lifted,lifted] at law
  exact LargeSeed21g5At2317.excluded (by omega) (by omega) Crt word fit geo pass full (by omega : 19≤f.natDegree) gp graphDegree N large pts slope n sheets0

#print axioms quotient_bound
end
end Research6966.NearTerminal

end Merged6967_R6966ProofNearTerminalGeometry
