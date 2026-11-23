import ProximityPrize.SubmissionLower.ZfWgThc
import ProximityPrize.SubmissionLower.ZTbQzvb
import ProximityPrize.SubmissionLower.ZoqNZ8b
import ProximityPrize.SubmissionLower.CmpCSum
import ProximityPrize.SubmissionLower.ZjZ6ihd
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.Z2L10ra
import ProximityPrize.SubmissionLower.ZIo6oRc
import ProximityPrize.SubmissionLower.ZON5THe
import ProximityPrize.SubmissionLower.Z3ozsyb
set_option Elab.async false
open _root_ renaming Finset → zJe, IsFractionRing.injective → zxb, LinearMap.ker → z83, LinearMap.range → zWl, Module.finrank → zsE, Nat.cast_nonneg → zqJ, Nat.mul_le_mul_left → zBI
section
section
set_option autoImplicit true
theorem qm7o3Fa.proof :qSxbgdc.c1 := fun q _ k _ p=>rank_le qSxbgdc.T8 q k p
end
end
section
set_option autoImplicit true
namespace qm7o3Fa
noncomputable section
open aR (ao)
open Rj (lK adf kJ yE Jd m5)
open baj (alQ aIL aJM aT5
  a9V bAa bqh cJ1 ezV ec2)
open P5_7_2 (TopRow)
open qSxbgdc
open Finset MvPolynomial
open scoped BigOperators
open private exponent cxO.exponent_injective eLR eLT from ProximityPrize.SubmissionLower.A3
open private vo aVQ dFD from ProximityPrize.SubmissionLower.Z2L10ra
open private gGU diD eQh eQi from ProximityPrize.SubmissionLower.C
open private product b2K d5V cN8 cEp aIu from ProximityPrize.SubmissionLower.C
variable (b:TopRow)
private theorem bnD (q:ℕ) (g:ℤ) :
    (↑((vo (iO b q) b.YM b.shape.J g).image (exponent (iO b q))) :
      Set adf)=cbQ b q g:= by
  ext e
  simp only [mem_coe,mem_image,vo,mem_sdiff,aVQ,cbQ,
    Set.mem_ofPred_eq,eLR,eLT]
  constructor
  · rintro ⟨p,hp,rfl⟩
    simp [exponent]
    omega
  · intro he
    refine ⟨(e 2,e 1),?_,?_⟩
    · dsimp
      omega
    · ext j
      fin_cases j <;> simp [exponent]
      omega
private theorem gte (q:ℕ) (g:ℤ) :
    (zsE ao (aqz b q g) :ℤ)=Bb b q g:= by
  unfold aqz Bb
  rw [← bnD b q g,finrank_restrictSupport_finset,
    card_image_of_injective _ (cxO.exponent_injective _),dFD]
private theorem eIi {q:ℕ} {g:ℤ} {f :lK}
    (hd:f.IsWeightedHomogeneous alQ (iO b q))
    (hf :bAa (pT b q g) f) :
    ∃ hsrc :f∈aqz b q g,(⟨f,hsrc⟩:aqz b q g) ∈
      z83 (aPi b q g) := by
  have hP:f∈restrictWeightedOrder Fin.val (-g).toNat := by
    rw [← gGU f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 0).2
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hQo:f∈restrictWeightedOrder eQh ((iO b q:ℤ) - b.YM).toNat := by
    rw [← diD f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 1).1
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hQw:f∈restrictWeightedOrder eQi (2*(iO b q:ℤ) - b.shape.J).toNat := by
    rw [← diD f]
    apply bind₁_mem_restrictWeightedOrder _ (hf 1).2
    intro i
    fin_cases i <;> apply X_mem_restrictWeightedOrder <;> decide
  have hsrc :f∈aqz b q g:= by
    apply (mem_restrictSupport_iff ao).mpr
    intro e he
    have hdeg:=hd (mem_support_iff.mp he)
    have hn:=mem_restrictWeightedOrder.mp hP e he
    have ho:=mem_restrictWeightedOrder.mp hQo e he
    have hw:=mem_restrictWeightedOrder.mp hQw e he
    change e.weight alQ=iO b q ∧ -g≤(e.weight Fin.val :ℤ) ∧
      e.weight Fin.val≤b.shape.J∧e 2≤b.YM
    rw [aT5] at hdeg
    simp [Finsupp.weight_eq_sum,Fin.sum_univ_three,smul_eq_mul,Nat.mul_comm] at hn ho hw ⊢
    omega
  refine ⟨hsrc,LinearMap.mem_ker.mpr ?_⟩
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  exact (hf 2).2
private theorem eO0 (q:ℕ) (p:kJ) {f :lK}
    (hn:0≤K6 b q p)
    (hf :f.IsWeightedHomogeneous alQ (K6 b q p).toNat) :
    (product p*f).IsWeightedHomogeneous alQ (iO b q) := by
  have hp: (product p).IsWeightedHomogeneous alQ (∑ j,p j*(yE j).toNat) := by
    apply IsWeightedHomogeneous.prod
    intro j _
    simpa only [Nat.nsmul_eq_mul] using (d5V j).pow (p j)
  have hc:=cEp p yE (by intro j; unfold yE; split <;> decide)
  have hsum: (∑ j,p j*(yE j).toNat)+(K6 b q p).toNat =
      iO b q:= by
    unfold K6 at hn ⊢
    omega
  rw [← hsum]
  exact hp.mul hf
private theorem eO1 (q:ℕ) (g:ℤ) (p:kJ) {f :lK}
    (hf :bAa (D8 b q g p) f) :bAa (pT b q g) (product p*f) := by
  intro i
  exact ⟨aIu p i aIL (pT b q g i).iy
      (fun j=>(Jd j i).iy)
      (by intro j; fin_cases j <;> fin_cases i <;> decide)
      (fun j=>(cN8 j i).1) (hf i).1,
    aIu p i aJM (pT b q g i).HE
      (fun j=>(Jd j i).HE)
      (by intro j; fin_cases j <;> fin_cases i <;> decide)
      (fun j=>(cN8 j i).2) (hf i).2⟩
private theorem ewc (q:ℕ) (g:ℤ) (p:kJ) (hn:0≤K6 b q p) :
    zsE ao (z83 (bqh (K6 b q p).toNat (D8 b q g p))) ≤
      zsE ao (z83 (aPi b q g)) := by
  let S:=z83 (bqh (K6 b q p).toNat (D8 b q g p))
  have h (f :S) :=eIi b (q:=q) (g:=g)
    (eO0 b q p hn (cJ1 f.val))
    (eO1 b q g p (ezV f))
  let L:S →ₗ[ao] lK :=
    (LinearMap.mulLeft ao (product p)).comp
      (((a9V (K6 b q p).toNat).subtype).comp S.subtype)
  let M:=L.codRestrict (aqz b q g) (fun f=>(h f).choose)
  let N :=M.codRestrict (z83 (aPi b q g)) (fun f=>(h f).choose_spec)
  apply LinearMap.finrank_le_finrank_of_injective (f :=N)
  intro f f' hff'
  apply Subtype.ext
  apply Subtype.ext
  have hp:product p≠0 :=
    Finset.prod_ne_zero_iff.mpr fun j _=>pow_ne_zero _ (b2K j)
  exact mul_left_cancel₀ hp (congrArg (fun a=>(a.val :lK)) hff')
private theorem plane_kernel_lower (q:ℕ) (g:ℤ) (p:kJ) :
    m5 (K6 b q p) (D8 b q g p) ≤
      (zsE ao (z83 (aPi b q g)) :ℤ) := by
  let d:=K6 b q p
  by_cases hn:K6 b q p<0
  · simp [m5,hn]
  have hnonneg:0≤d:=le_of_not_gt hn
  have hres :=ec2 d.toNat (D8 b q g p)
  rw [Int.toNat_of_nonneg hnonneg] at hres
  have hl:=ewc b q g p hnonneg
  simp only [m5,hn,ite_false]
  exact hres.trans (by exact_mod_cast hl)
private theorem c4g (q k :ℕ) (p:kJ) :
    zsE ao (zWl (aPi b q (offset b k)))≤xR b q (offset b k) p:= by
  let f :=aPi b q (offset b k)
  by_cases hcut:Ic b q (offset b k)≤0
  · have hz :f=0:= by
      ext L:1
      simp [f,aPi,Int.toNat_of_nonpos hcut,weightedTruncation_eq_zero_iff]
    change zsE ao (zWl f)≤_
    simp [hz,xR,hcut]
  have hdim:=f.finrank_range_add_finrank_ker
  have hcols :=gte b q (offset b k)
  have hshift:=plane_kernel_lower b q (offset b k) p
  have hbase :=plane_kernel_lower b q (offset b k) (fun _=>0)
  have hdeg:K6 b q (fun _=>0)=iO b q:= by simp [K6]
  have hflag:D8 b q (offset b k) (fun _=>0)=pT b q (offset b k) := by
    funext i
    simp only [D8,Nat.cast_zero,zero_mul,Finset.sum_const_zero,sub_zero]
  rw [hdeg,hflag] at hbase
  change _≤(zsE ao (z83 f) :ℤ) at hshift hbase
  have hlower :=max_le (Int.natCast_nonneg (zsE ao (z83 f)))
    (max_le hbase hshift)
  change zsE ao (zWl f)≤_
  simp only [xR,hcut,ite_false]
  change (zsE ao f.range :ℤ).toNat≤_
  exact Int.toNat_le_toNat (by omega)
end
end qm7o3Fa
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P5_7_2_3Q122
open qSDZN5b
def tot:List ℕ→ℕ→ℕ
  | [],_=>0
  | c :: l,q=>Sk q (c % 256) (c/256)+tot l (q+1)
theorem win : ∀ (l:List ℕ) (q:ℕ),Window q l.length (tot l q)
  | [],_=>⟨⟨fun _ _=>0,by simp [tot]⟩⟩
  | c :: l,q=> by
    rw [List.length_cons,Nat.add_comm]
    exact join (row q _ _ _ rfl) (win l (q+1))
theorem w (l:List ℕ) (q r :ℕ) (h:tot l q=r) :Window q l.length r :=h ▸ win l q
set_option quotPrecheck false in
local notation "c!" l=>w l _ _ (by decide +kernel)
theorem c0:Window 0 13 54145:=c! [0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem c1 :Window 13 13 302723:=c! [0,0,0,0,0,0,0,0,0,0,0,0,620]
theorem c2 :Window 26 13 616292 :=c! [0x126a,0x9368,0x49d66,0x24ee64,0,0,0,0,0,0,0,0,0]
theorem c3:Window 39 13 730197:=c! [0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem c4 :Window 52 13 648830:=c! [0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem c5:Window 65 13 528334 :=c! [0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem c6:Window 78 13 408840:=c! [0,561,560,815,0x452e,0x462d,0x662c,0x8a72b,0x8c82a,0xcc929,0x114eb28,0x1190c27,0x1992d26]
theorem c7:Window 91 13 296758:=c! [0x229d6e25,0x23218e24,0x3325af23,0x453add022,0x46431d121,0x664b5f220,0x8a75ba131f,0x8c863a341e,0x18324a6b7d961e,0x10283a5a73859e1d,0x10304262738d1d,0x18304a6a7b951c,0x1028385a72831c]
theorem c8:Window 104 13 200083:=c! [0x10304062728b1b,0x1830486a7a1b,0x1028385872821a,0x10304060721a,0x183048687a19,0x102838587019,0x103040607018,0x1830486818,0x102838587017,0x1030406017,0x1830486816,0x1028385816,0x1030406015]
theorem c9:Window 117 13 122370:=c! [0x18304815,0x1028385814,0x400030001000014,0x600030001200113,0x400028000e00013,0x400030001020212,0x18000c00112,0x400028000e20311,0x10000c20211,0x18004c40410,0x10000a20310,0x10808c4050f,0x464040f]
theorem c10 :Window 130 13 64401 :=c! [0x1080ca6060e,0x80844050e,0x10101067070d,0x80c46060d,0x2020101447080c,0x10101007070c,0x2030181849090b,0x80880a7080b,0x9010e0ea0a0a,0x80cc0c9090a,0x1011014e10b0b09,0x9010e0ea0a09,0x1019819212b0c08]
theorem c11 :Window 143 13 26129:=c! [0x1011014e10b0b08,0x12021c1d414d0d07,0x1019819212b0c07,0x2022029c21616e0e06,0x12021c1d414d0d06,0x2033032425618f4f05,0x2022029c21616e4e05,0x2404383a829a9b05004,0x2033032425698f4f04,0x4044053842d2dc9d07103,0x2404383a929a9b07003,0x4066064a4ad31edf2b202,0x4044053a42d2dcdd0b102]
theorem c12 :Window 156 13 6340:=c! [0x480874752535b61613d301,0x4066464a4adb1f5f2d201,0x80888a7485b5baba1a34d400,0x488874753536b61a13d300,0x4866464b4aeb1f9f2d200,0x4844453b42eadd9d0d100,0x824443b3aaa9b9b0d000,0x8024333326a5798fcf00,0x802422329ea1796ece00,0x800412321e9d594dcd00,0x800401319a99392bcc00,0x800401311294f90bcb00,0x800400309290f8eaca00]
theorem c13:Window 169 6 406:=c! [0x800400300a8cd8c9c900,0x800400300a8898a7c800,0x8004003002849887c700,0x8004003002805866c600,0x8004003002805844c500,0x8004003002801824c400]
theorem proof :qSxbgdc.c2 := by
  obtain ⟨p,hp⟩:=(join c0 <| join c1 <| join c2 <| join c3 <| join c4 <| join c5 <| join c6 <| join c7 <| join c8 <| join c9 <| join c10 <| join c11 <| join c12 <| c13).witness
  refine ⟨p,?_⟩
  change (∑ q∈Finset.range 175,gradeSum q (p q))≤4005848
  simpa only [Nat.zero_add] using hp.le
end P5_7_2_3Q122
end
section
set_option autoImplicit true
namespace qSJanHc
theorem proof :qAFIJ5c.c1 :=
  qSxbgdc.of_children qm7o3Fa.proof P5_7_2_3Q122.proof
end qSJanHc
end
section
set_option autoImplicit true
namespace qy95ATd
noncomputable section
open Polynomial Finset
open P5 (K)
open P6_7_3 (Input degree)
open qXdgDRd (StrongMarks)
open P5_7_7 (phys dualValue mL sites mem_sites atX_injective)
open qQ9yWTb (embed height)
open qVXVW4b (constant_height)
open cu (Equation vm kr yq qD)
open Qt (Qc acG)
open private changeOrd changed_primitive change_caps change_eval from ProximityPrize.SubmissionLower.Za7Od9d
theorem marks (x :Input) (T:zJe K) (hT:T⊆x.Γ) :
    StrongMarks degree x.M.word T x.M.label x.F.scalar := by
  have hh:x.M.iF.toNat≤P6_7_3.hi:=(P6_7_3.emz x).2
  have ha (γ) (hγ:γ∈T) :P6.dw≤(sites x.M.word x.F.scalar γ).card:= by
    let m:=x.F.mark γ (hT hγ)
    exact m.bad.dw.trans (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi))
  exact ⟨⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,
    fun γ hγ=>(P6_7.aic x.F (hT hγ)).trans (Nat.add_le_add_left hh _),
    fun γ hγ=>(by decide :P5_7.farAgreement≤P6.dw).trans (ha γ hγ)⟩,ha⟩
private theorem chart_det {x :Input} {U:zJe K} (J:WordChart x U) :
    phys J.a₀*phys J.b₁ -
      phys J.a₁*phys J.b₀≠0:= by
  obtain ⟨c,hc,h⟩:=J.determinant
  have hn:mL (univ :zJe P5.I)≠0 :=
    prod_ne_zero_iff.mpr fun i _=>X_sub_C_ne_zero _
  rw [← map_mul,← map_mul,← map_sub,h]
  exact (map_ne_zero_iff _ (zxb _ _)).mpr (mul_ne_zero (C_ne_zero.mpr hc) hn)
private theorem chart_identity {x :Input} {U:zJe K} (J:WordChart x U)
    {γ:K} (hγ:γ∈U) :
    phys J.b₀*dualValue J γ - phys J.b₁ =
      (phys J.a₁ - phys J.a₀*dualValue J γ)*kr (x.F.scalar γ) := by
  let P:=phys (J.P γ)
  let Q:=phys (J.Q γ)
  let loc:=phys (mL (sites x.M.word x.F.scalar γ))
  have hp:loc*P=phys J.a₁*kr (x.F.scalar γ)+phys J.b₁:= by
    simpa only [P,loc,kr,phys,map_mul,map_add] using congrArg phys (J.numerator_id γ hγ)
  have hq:loc*Q=phys J.a₀*kr (x.F.scalar γ)+phys J.b₀:= by
    simpa only [Q,loc,kr,phys,map_mul,map_add] using congrArg phys (J.denominator_id γ hγ)
  have hn:Q≠0:=(map_ne_zero_iff _ (zxb _ _)).mpr (J.denominator γ hγ)
  have h: (phys J.a₀*kr (x.F.scalar γ)+phys J.b₀) *
      dualValue J γ=phys J.a₁*kr (x.F.scalar γ)+phys J.b₁:= by
    change _ *(P/Q)= _
    rw [← hq,← hp,mul_assoc,← mul_div_assoc,mul_div_cancel_left₀ _ hn]
  linear_combination h
private theorem chart_inj {x :Input} {U:zJe K} (J:WordChart x U) (hU:U⊆x.Γ) :
    Set.InjOn (dualValue J) (U:Set K) := by
  intro γ hγ δ hδ he
  have h₁:=chart_identity J hγ
  have h₂:=chart_identity J hδ
  rw [← he] at h₂
  have hn:phys J.a₁ - phys J.a₀*dualValue J γ≠0:= by
    intro hz
    apply chart_det J
    have hA:=sub_eq_zero.mp hz
    rw [hz,zero_mul] at h₁
    rw [hA,← sub_eq_zero.mp h₁]
    ring
  exact x.F.distinct (hU hγ) (hU hδ)
    (atX_injective (mul_left_cancel₀ hn (h₁.symm.trans h₂)))
private theorem transported {x :Input} {U:zJe K} (J:WordChart x U) {f :Equation} {e u:ℕ}
    (hp:f.IsPrimitive) (he :f.natDegree≤e) (hs :vm f u)
    (hr : ∀ γ∈U,yq f (x.M.label γ) (x.F.scalar γ)=0) :
    ∃ g:Equation,g.IsPrimitive∧g.natDegree≤e∧vm g u ∧
      ∀ γ∈U,g.eval₂ (qD (x.M.label γ)) (dualValue J γ)=0:= by
  let a :=phys J.b₀
  let b := -phys J.b₁
  let c := -phys J.a₀
  let d:=phys J.a₁
  have hm:a*d-b*c≠0:= by
    have h:=chart_det J
    rwa [show a*d-b*c = -(phys J.a₀*phys J.b₁ -
        phys J.a₁*phys J.b₀) by dsimp [a,b,c,d]; ring,neg_ne_zero]
  obtain ⟨hd,hcap⟩:=change_caps a b c d (n:=e) hs
  refine ⟨changeOrd a b c d f e,changed_primitive hm hp he,hd,hcap,?_⟩
  intro γ hγ
  rw [change_eval a b c d he _ _ (kr (x.F.scalar γ)) ?_]
  · change yq f (x.M.label γ) (x.F.scalar γ)*_=0
    rw [hr γ hγ,zero_mul]
  · have h:=chart_identity J hγ
    dsimp [a,b,c,d]
    linear_combination h
theorem allocation (x :Input) (T:zJe K) (hT:T⊆x.Γ) {e u W:ℕ} {f :Equation}
    (hf :Dt.Reduced f) (he :f.natDegree=e) (hs :vm f u)
    (hr : ∀ γ∈T,yq f (x.M.label γ) (x.F.scalar γ)=0) :
    T.card≤e+1∨Nonempty (SplitData x T e u W) := by
  rcases q20JTGa.proof degree x.M.word T x.M.label x.F.scalar (marks x T hT).toUJ with
    hsmall | ⟨U,hU,hcard,⟨J⟩⟩
  · exact Or.inl (hsmall.trans (Nat.le_add_left 1 e))
  obtain ⟨g,hg,hd,hv,hroot⟩:=transported J hf.2.1 he.le hs (fun γ hγ=>hr γ (hU hγ))
  obtain ⟨r,a,ha,hrepr,hdeg,_,_⟩:=Y3.normalize g e u hg.ne_zero hd hv
  have hrepr' : embed r=Y3.constant a*g:=hrepr
  have hu:=ha.isUnit.map Y3.constant
  have hprim: (embed r).IsPrimitive := by
    intro b hb
    rw [hrepr'] at hb
    exact hg b (hu.dvd_mul_left.mp hb)
  have hcap:height r≤u:= by
    change Qt.gY (embed r)≤u
    rw [hrepr',acG hu.ne_zero hg.ne_zero,constant_height,zero_add]
    exact (Qc g u).mpr hv
  refine Or.inr (allocate hU hcard J (chart_inj J (hU.trans hT)) r hprim hdeg hcap ?_)
  intro γ hγ
  unfold root
  rw [hrepr',eval₂_mul,hroot γ hγ,mul_zero]
end
end qy95ATd
end
section
set_option autoImplicit true
namespace qy95ATd
noncomputable section
open Polynomial
open P6 (K p)
open P6_7_3 (Input)
open qQ9yWTb (Raw embed height Moving Witness highRate highDigits count_resultant)
open q4Pefpa (stock j3 inputSize dhP)
open cu (L qD)
open private height_rect rescale proper_output embed_degree embed_rect from ProximityPrize.SubmissionLower.ZagvXJe
private theorem proper (kernel:q4Pefpa.c1) (quotient:q4Pefpa.c2)
    {x :Input} {U T:zJe K} (hU:U⊆x.Γ) (J:WordChart x U) (hT:T⊆U)
    {e u:ℕ} {w:Witness} (hw:Good e u w) {F:Raw} (hF:Moving F)
    (he :F.natDegree≤e) (hv :height F≤u)
    (hhigh : ∀ q:Raw,Irreducible q→q∣F→w.W<weight J q)
    (hroot : ∀ γ∈T,root J F γ) (hne :T.Nonempty) :
    ∃ f :cu.Equation,
      0<(embed F).natDegree∧f.natDegree≤e+w.g∧(embed F).resultant f≠0 ∧
      (∀ j (i:Fin 2),(f.coeff j).degreeOf i≤(if i=0 then w.cz+1 else w.ct+1)*height F) ∧
      ∀ γ∈T,f.eval₂ (qD (x.M.label γ)) (P5_7_7.dualValue J γ)=0:= by
  classical
  obtain ⟨γ,hγ⟩:=hne
  have hnu : ¬ IsUnit F:= fun hu =>
    (hu.map ((eval₂RingHom (qD (x.M.label γ)) (P5_7_7.dualValue J γ)).comp embed)).ne_zero
      (hroot γ hγ)
  obtain ⟨q,hq,hqF⟩:=WfDvdMonoid.exists_irreducible_factor hnu hF.1
  have hpos :=(hF.2 q hq hqF).1.trans_le (natDegree_le_of_dvd hqF hF.1)
  obtain ⟨_,_,_,_,_,_,hj,_,hM,hs,_,_,_,_⟩:=hw
  obtain ⟨hl,hdeg⟩:=qXdgDRd.chart_bounds J (marks x U hU) ⟨γ,hT hγ⟩
  have hl' : left J+right J=width := calc
    _=2*(J.u₀-qXdgDRd.shift)+(J.u₁-J.u₀) := by dsimp only [left,right]; ring
    _ = _:=hl
  have ho:left J≤ right J:=Nat.le_add_right _ _
  let v :=height F
  have hr :stock ((w.cz+1)*v) ((w.ct+1)*v)* (j3 width (e+w.g)+j3 width w.j) <
      inputSize w.g (modulus w) (w.cz*v) (w.ct*v) :=
    rescale hv (by simpa only [stock,j3,inputSize,Nat.mul_assoc] using hs)
  obtain ⟨d,hdM,V,hV,hrow⟩:=kernel (left J) (right J) e w.g (modulus w)
    (w.cz*v) (w.ct*v) v ho (hl'.symm ▸ hM) F hF.1 he (height_rect F)
  have hsz (c:ℕ) :c*v+v=(c+1)*v := by ring
  have hlower :stock (w.cz*v+v) (w.ct*v+v)*j3 (left J+right J) w.j<zsE L V:= by
    rw [hsz,hsz,hl'] at hV ⊢
    rw [Nat.mul_add] at hr
    omega
  have hm:modulus w=w.W+1+w.j*(left J+right J) := by rw [hl']; rfl
  obtain ⟨G,hGV,hproper⟩:=proper_output hF V (by
    intro q hq hqF
    by_contra! ha
    apply hlower.not_ge
    apply quotient (left J) (right J) e w.g w.j w.W (w.cz*v+v) (w.ct*v+v) ho hj q hq.ne_zero
      ((natDegree_le_of_dvd hqF hF.1).trans he) (hhigh q hq hqF) V _ ha
    intro g hg
    rw [← hm]
    exact ⟨(hrow g hg).1,(hrow g hg).2.1⟩)
  obtain ⟨hpad,hrect,H,B,hB,hcong⟩:=hrow G hGV
  refine ⟨embed G,(embed_degree F).symm ▸ hpos,(embed_degree G).symm ▸ hpad.1,
    hproper,?_,?_⟩
  · intro j i
    rw [embed_rect]
    by_cases hi:i=0 <;> simpa [hi,hsz,v] using hrect i j
  · intro η hη
    obtain ⟨hQ,hP⟩:=hdeg η (hT hη)
    apply dhP ho hdM (J.denominator η (hT hη)) hP hQ hpad hB hcong
    rw [map_mul,eval₂_mul]
    exact mul_eq_zero.mpr (Or.inl (hroot η hη))
theorem high_count (kernel:q4Pefpa.c1) (quotient:q4Pefpa.c2)
    {x :Input} {T:zJe K} (hT:T⊆x.Γ) {e u:ℕ} {w:Witness}
    (hw:Good e u w) (s :SplitData x T e u w.W) :s.high.card≤highRate e w*height s.F:= by
  by_cases hn:s.high.Nonempty
  · have hu:height s.F≤u:=(Nat.le_add_right _ _).trans s.seed
    obtain ⟨f,hp,he,hproper,hs,hr⟩:=proper kernel quotient (s.sub.trans hT) s.bY s.high_sub
      hw s.F_moving s.F_degree hu s.high_weight s.high_root hn
    have hdigit :highDigits e w.cz w.g*u<p:= by
      rcases hw with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,h⟩
      exact h
    have hguard :=(zBI (highDigits e w.cz w.g) hu).trans_lt hdigit
    have hc:=count_resultant hp (natDegree_map_le.trans s.F_degree) he
      ((Qt.Qc (embed s.F) _).mp (le_refl (height s.F))) hs hproper
      (by simpa only [highDigits,Nat.add_assoc] using hguard)
      (z :=x.M.label) (y :=P5_7_7.dualValue s.bY)
      (fun _ _ _ _ h=>sub_left_inj.mp h) s.high_root hr
    exact hc.trans_eq (by unfold highRate highDigits; ring)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
end
end qy95ATd
end
section
set_option autoImplicit true
set_option maxHeartbeats 650000
namespace qy95ATd
open P6_7_3 (retainedFee)
open qQ9yWTb (Witness base highRate)
open private convex_fee from ProximityPrize.SubmissionLower.ZON5THe
theorem paid_sum {e u h v a z :ℕ} {w:Witness} (hu:0< u) (hw:gu e u w)
    (hv :h+v≤u) (ha :a≤highRate e w*h) (hz :3*(z :ℚ)≤10*(B e w.W v)^2) :
    a+z+(e+1)≤ retainedFee := by
  let g:ℚ:=(G:ℕ)
  let b:ℚ:=(base e :ℕ)*g
  let c:ℚ:=(lowRate e w.W:ℕ)
  let d:ℚ:=3*g^2
  let R:ℚ:=(highRate e w:ℕ)
  have hG:0<G:= by decide
  have hg:0<g:=Nat.cast_pos.mpr hG
  have hd:0<d:= by dsimp only [d]; positivity
  have hb:g*B e w.W v=c*v+b:= by
    dsimp only [B,b,c,g]
    field_simp
  have hv' : (h:ℚ)+v≤u:= by exact_mod_cast hv
  have hle : (h:ℚ)≤(u:ℚ)-v := by linarith
  have ha' : (a :ℚ)≤R*h:= by
    dsimp only [R]
    exact_mod_cast ha
  have hR:0≤R:=zqJ _
  have hz' : d*z≤10*(c*v+b)^2 := by
    calc
      d*z=g^2*(3*z) := by dsimp only [d]; ring
      _≤g^2*(10*(B e w.W v)^2) :=mul_le_mul_of_nonneg_left hz (sq_nonneg g)
      _=10*(g*B e w.W v)^2 := by ring
      _ = _:= by rw [hb]
  obtain ⟨hhi,hlo⟩:=hw
  have hf :d*(R*u+(e+1))+10*b^2≤d*(retainedFee :ℚ) := by
    dsimp only [d,R,b,g]
    exact_mod_cast hhi
  have hl:d*(e+1)+10*(c*u+b)^2≤d*(retainedFee :ℚ) := by
    dsimp only [d,c,b,g]
    exact_mod_cast hlo
  have hvu: (v :ℚ)≤u:= by linarith [zqJ (α:=ℚ) h]
  have hmix :=convex_fee (Nat.cast_pos.mpr hu) (zqJ v) hvu
    hd (ha'.trans (mul_le_mul_of_nonneg_left hle hR)) hz' hf hl
  exact_mod_cast hmix
end qy95ATd
end
section
set_option autoImplicit true
namespace qy95ATd
noncomputable section
open Polynomial
open P6 (K p)
open P6_7_3 (Input degree retainedFee)
open qQ9yWTb (Raw Curve height Moving Witness Usable)
open qXdgDRd (Guards NodeBound PoleBound native_count)
open cu (L Equation vm yq)
open scoped Classical
def c1 :Prop :=NodeBound 2
def c2 :Prop :=PoleBound width 2
def c3:Prop :=q4Pefpa.c1
def c4 :Prop :=q4Pefpa.c2
def c5:Prop :=
  ∀ (x :Input) (U:zJe K),U⊆x.Γ → ∀ (J:WordChart x U) (T:zJe K),T⊆U →
    ∀ e u (w:Witness),Good e u w →
    ∀ F:Raw,Moving F→F.natDegree≤e→height F≤u →
      (∀ q:Raw,Irreducible q→q∣F→weight J q≤w.W) →
      (∀ γ∈T,root J F γ) →
      ∀ q:Curve,Irreducible q →
        ((T.filter fun γ=>Usable q (site x γ)).card:ℚ)≤B e w.W (height F)*q.totalDegree
def c6:Prop :=qQ9yWTb.c5
private theorem small_guard :Guards degree 2 2700000:= by
  refine ⟨by decide,?_⟩
  intro l hl hu
  have he :l=1∨l = 2 := by omega
  rcases he with rfl | rfl
  · exact ⟨⟨0,0,0,0⟩,Or.inl rfl,by decide⟩
  · refine ⟨⟨4,25,4,88360⟩,Or.inr ?_,by decide⟩
    unfold qXdgDRd.Witness
    decide
private theorem small_count (hn:c1) (hp:c2)
    {x :Input} {T:zJe K} (hT:T⊆x.Γ) {f :Equation} (hf :f≠0)
    {u:ℕ} (hu:u≤3611) (he :f.natDegree≤2) (hs :vm f u)
    (hr : ∀ γ∈T,yq f (x.M.label γ) (x.F.scalar γ)=0) :T.card≤ retainedFee := by
  obtain ⟨g,hg,hge,hgs,hgr⟩:=P5_7.native_restriction hf (hu.trans_lt (by decide :3611<p)) hs
  have hcap:P5_7.NativeSeedBound g ((p+1)*3611) :=
    fun j=>(hgs j).trans (zBI _ hu)
  exact native_count small_guard (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hn hp (marks x T hT) g hg (hge.trans he) hcap (fun γ hγ=>(hgr _ _).trans (hr γ hγ))
private theorem site_inj (x :Input) :Function.Injective (site x) := by
  intro a b h
  have hz :=congrFun h 0
  change algebraMap K L (x.M.label a)=algebraMap K L (x.M.label b) at hz
  exact sub_left_inj.mp (FaithfulSMul.algebraMap_injective K L hz)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :P6_7_3.c6:= by
  intro x T hT i f hf he hs hr
  obtain ⟨hu,hsmall | ⟨w,hw,hp⟩⟩:=bHu i
  · exact small_count h1 h2 hT (fun hz=> by simpa [hz] using hf.1) hu (he.le.trans hsmall) hs hr
  rcases allocation x T hT (W:=w.W) hf he hs hr with hsmall | hsData
  · exact hsmall.trans ((Nat.add_le_add_right hw.2.1.le 1).trans (by decide))
  obtain ⟨s⟩:=hsData
  have hlow:=h5 x s.U (s.sub.trans hT) s.bY s.low s.low_sub _ _ w hw s.Q s.Q_moving
    s.Q_degree ((Nat.le_add_left _ _).trans s.seed) s.low_weight s.low_root
  have hn:0≤B (i.val+1) w.W (height s.Q) := by unfold B; positivity
  have hplane :=h6 s.low (site x) (site_inj x).injOn _ hn hlow
  exact s.card.trans (paid_sum hw.2.2.1 hp s.seed (high_count h3 h4 hT hw s) hplane)
end
end qy95ATd
end
