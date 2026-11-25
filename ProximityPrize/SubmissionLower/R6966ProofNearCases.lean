import ProximityPrize.SubmissionLower.R6966ProofNearLedgerBudget
import ProximityPrize.SubmissionLower.R6966ProofNearAffineHelper
import ProximityPrize.SubmissionLower.R6966ProofQuadraticHelper6966
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueCatalogue
import ProximityPrize.SubmissionLower.High6966Packets
import ProximityPrize.SubmissionLower.High6966WideRows

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
    (branch (high i)).primary=⟨167997887646643864,1849635312035,5608,220⟩ ∧
    (branch (high i)).rescue=⟨Rescue6966.paidCap i,Rescue6966.retainedCredit i,
      (Rescue6966Source.data i).bound 1,(Rescue6966Source.data i).bound 0⟩ := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

private theorem high_pair {v:ℕ} (pos:0<v) (small:v≤92) :
    ∃ i:Fin 12,(Pair6966.row i).cap=13200 ∧ (Pair6966.row i).degree=2 ∧
      (Pair6966.row i).wt=(QuadraticBudget.band v).2 ∧ (Pair6966.row i).seed≤v :=
  (by decide +kernel : ∀ n:Fin 93,0<n.val → ∃ i:Fin 12,(Pair6966.row i).cap=13200 ∧
    (Pair6966.row i).degree=2 ∧ (Pair6966.row i).wt=(QuadraticBudget.band n.val).2 ∧
    (Pair6966.row i).seed≤n.val) ⟨v,by omega⟩ pos

theorem exists_cover (F:Family M Γ) (Crt:CRTLift D) (lo:2330≤M.overhead.toNat) (hi:M.overhead.toNat≤2499)
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
  have known:Common (Pair6966.space Crt (word M) 20142) G:=owner
  obtain ⟨slope,jp,jmax,sp,smax,smix⟩:=Wide6966Helper.helper_common_caps Crt (word M) lo (hi.trans (by decide))
    known.1 known.2.2.1 known.2.1 known.2.2.2
  obtain ⟨phys⟩:=HelperPhysicalModel.exists_model Crt known.1 known.2.1
  let w:=131071-M.overhead.toNat
  let weight:=RawPhysicalDegree.weight w (w-1) phys.raw
  have base (n:ℕ) (le:n≤jetDegree G) : 128572*n-1≤weight := by
    have a:=HelperWeightCap.weight_lower phys known.1.ne_zero w (by dsimp [w];omega)
    have low:128572≤w:=by dsimp [w];omega
    have b:=Nat.mul_le_mul low le
    change w*jetDegree G≤weight+G.natDegree at a
    omega
  have mainWide (γ:K) (hg:γ∈Γ) : γ∈T ∨ γ∈R.marks := by
    by_cases z:jetAt G (M.label γ) (F.scalar γ)=0
    · exact Or.inl (mem_filter.mpr ⟨hg,z⟩)
    · exact Or.inr (mem_filter.mpr ⟨hg,z⟩)
  have medium (k:Fin 12) (cap:(Pair6966.row k).cap=15000) (deg:(Pair6966.row k).degree≤jetDegree G)
      (seed:(Pair6966.row k).seed≤seedDegree G) (wt:(Pair6966.row k).wt≤weight) (index:Fin 58)
      (pay:(branch index).primary=⟨185233047747540462,1838347228855,6160,220⟩)
      (count:T.card≤(branch index).extra) : Nonempty (Cover F Crt) := by
    obtain ⟨Q⟩:=Pair6966.chosen15000 F Crt k cap lo hi nop res known phys deg wt seed
    have uniq:=Pair6966.unique Crt (word M) k lo hi known phys deg wt seed
    rw [cap] at uniq
    have on:Common (Pair6966.space Crt (word M) 15000) G :=
      ⟨known.1,known.2.1,known.2.2.1,fun P hp=>known.2.2.2 P (Pair6966.space_mono Crt (word M) (by decide : 15000≤20142) hp)⟩
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
  obtain ⟨k,cap,degree,seed,wt⟩ : ∃ k:Fin 12,(Pair6966.row k).cap=13200 ∧
      (Pair6966.row k).degree≤jetDegree G ∧ (Pair6966.row k).seed≤seedDegree G ∧ (Pair6966.row k).wt≤weight := by
    by_cases quad:jetDegree G=2
    · obtain ⟨k,h,deg,ww,ss⟩:=high_pair sp seed92
      exact ⟨k,h,deg.le.trans two,ss,ww.le.trans (wtQuad quad)⟩
    · have three:3≤jetDegree G:=by omega
      exact ⟨11,rfl,three,sp,base 3 three⟩
  obtain ⟨Q⟩:=Pair6966.chosen13200 F Crt k cap lo hi nop res known phys degree wt seed
  have uniq:=Pair6966.unique Crt (word M) k lo hi known phys degree wt seed
  rw [cap] at uniq
  have on:Common (Pair6966.space Crt (word M) 13200) G :=
    ⟨known.1,known.2.1,known.2.2.1,fun P hp=>known.2.2.2 P (Pair6966.space_mono Crt (word M) (by decide : 13200≤20142) hp)⟩
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
