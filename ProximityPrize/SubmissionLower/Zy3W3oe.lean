import ProximityPrize.SubmissionLower.ZlUbT2c
import ProximityPrize.SubmissionLower.Z6Xnfpd
import ProximityPrize.SubmissionLower.ZsJdCMc
import ProximityPrize.SubmissionLower.Zewe3yc
import ProximityPrize.SubmissionLower.ZIn6UHe
import ProximityPrize.SubmissionLower.Zt1WHxc
import ProximityPrize.SubmissionLower.Z4WdLEc
import ProximityPrize.SubmissionLower.Zly0pSc
import ProximityPrize.SubmissionLower.ZHbP8jb
import ProximityPrize.SubmissionLower.ZMIybKd
import ProximityPrize.SubmissionLower.Zxv8lVc
import ProximityPrize.SubmissionLower.ZRSUmIe
import ProximityPrize.SubmissionLower.ZPNuIWc
import ProximityPrize.SubmissionLower.ZnaG81a
import ProximityPrize.SubmissionLower.ZvOdgMc
import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.ZJ6ikSc
import ProximityPrize.SubmissionLower.Zc9uAjc
import ProximityPrize.SubmissionLower.ZNc08Oa
set_option Elab.async false
section
open _root_ renaming Finset.card_filter_add_card_filter_not→lI,Nat.le_of_mul_le_mul_right→lz,P5_7_2.A→c9,True.intro→aU,qMHqmcc.appendGrades→cy
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt)
private abbrev kA:fO:=⟨6,by decide⟩
local notation "kU" => receipt 2539 rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)
private theorem dK:GG kA 12 3:=⟨kU,kU,kU,aU⟩
private theorem gx :GG kA 15 3:=⟨kU,kU,kU,aU⟩
private theorem lH :GG kA 18 3:=⟨kU,kU,kU,aU⟩
private theorem lp:GG kA 21 3:=⟨kU,kU,kU,aU⟩
theorem b:GG kA 12 12 :=
 cy (cy (cy dK gx) lH) lp
end qyV6B3d
end
section
set_option autoImplicit true
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipts)
private theorem band6:GG (⟨6,by decide⟩:fO) 0 93:= by
 have p24 :=cy  a b
 have p36:=cy  p24 c
 have p48:=cy  p36 d
 have p60:=cy  p48 e
 have p72 :=cy  p60 f
 have p84 :=cy  p72 g
 exact cy  p84 h
private theorem band7:GG (⟨7,by decide⟩:fO) 0 121 := by
 have p24 :=cy  j k
 have p36:=cy  p24 l
 have p48:=cy  p36 m
 have p60:=cy  p48 n
 have p72 :=cy  p60 o
 have p84 :=cy  p72 p
 have p96:=cy  p84 q
 have p108:=cy  p96 r
 exact cy  p108 s
theorem proof :qMHqmcc.c4 := by
 intro b hl hu x
 rcases (show b.val=6∨b.val = 7 by omega) with h6 | h7
 · have hb:b=⟨6,by decide⟩:=Fin.ext h6
   subst b
   exact receipts _ band6 x
 · have hb:b=⟨7,by decide⟩:=Fin.ext h7
   subst b
   exact receipts _ band7 x
end qyV6B3d
end
section
set_option autoImplicit true
namespace qwtjEYd
open P5_7_2 (fO)
open qMHqmcc (GG receipts)
private theorem zo:GG (⟨12,by decide⟩:fO) 0 51 :=
 cy  (cy  (cy  earlyA earlyB) earlyC) earlyD
private theorem be1 :GG (⟨13,by decide⟩:fO) 0 51 :=
 cy  (cy  (cy  lateA lateB) lateC) lateD
theorem proof :qMHqmcc.c7:= by
 intro b hb
 have hu:b.val<14 :=b.isLt
 have h:b.val=12∨b.val=13:= by omega
 rcases h with h | h
 · have he :b=(⟨12,by decide⟩:fO) :=Fin.ext h
   subst b
   exact receipts _ zo
 · have he :b=(⟨13,by decide⟩:fO) :=Fin.ext h
   subst b
   exact receipts _ be1
end qwtjEYd
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qJrKOKe
open qMHqmcc (GG receipt)
open P5_7_2 (fO)
abbrev b11 :fO:=⟨11,by decide⟩
local notation "az" => (receipt 2575 rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl))
private theorem r1 :GG b11 0 4 :=⟨az,az,az,az,aU⟩
private theorem r2 :GG b11 4 4 :=⟨az,az,az,az,aU⟩
private theorem r3:GG b11 8 4 :=⟨az,az,az,az,aU⟩
private theorem r4 :GG b11 12 4 :=⟨az,az,az,az,aU⟩
private theorem r5:GG b11 16 4 :=⟨az,az,az,az,aU⟩
theorem e :GG b11 0 20 :=
 cy (cy (cy (cy r1 r2) r3) r4) r5
end qJrKOKe
end
section
set_option autoImplicit true
namespace qWdRihc
noncomputable section
open Finset Polynomial
open P5 (I K node blockLength)
open ProximityPrize.Benchmark
open scoped BigOperators
private theorem difference_hits (J:UJ) {γ η:K} (hγ:γ∈J.CF)
    (hη:η∈J.CF) (hne :γ≠η) :
    c9-d≤(univ.filter fun i:I=>J.hit γ i ∧ ¬ J.hit η i).card:= by
  classical
  obtain ⟨s,hs,hf⟩:=J.lg γ hγ
  let g:=J.scalar γ-J.scalar η
  have hg:g≠0:=sub_ne_zero.mpr fun h=>hne (J.scalar_injective hγ hη h)
  have hc: (s.filter (J.hit η)).card≤d :=
    (gR.kL.agd node IRSProfile.domain.injective g hg _ (by
      intro i hi
      obtain ⟨him,hh⟩:=mem_filter.mp hi
      change (J.scalar η).eval (node i)=J.word i at hh
      rw [show g= _ from rfl,Polynomial.eval_sub,hf i him,hh,sub_self])).trans
        ((natDegree_sub_le _ _).trans (max_le (J.degree γ hγ) (J.degree η hη)))
  have hp:=lI (s :=s) (J.hit η)
  have hsub:s.filter (fun i => ¬ J.hit η i)⊆univ.filter (fun i=>J.hit γ i ∧ ¬ J.hit η i) := by
    intro i hi
    obtain ⟨him,hm⟩:=mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_univ _,hf i him,hm⟩
  have hle :=card_le_card hsub
  omega
private theorem product_bound {m a b B:ℕ} (h:a+b=m) (hcap:a≤B∨b≤B) :
   a*b≤B*(m-1) := by
 by_cases ha :a=0
 · simp [ha]
 by_cases hb:b=0
 · simp [hb]
 rcases hcap with hac | hbc
 · exact Nat.mul_le_mul hac (by omega)
 · rw [Nat.mul_comm a b]
   exact Nat.mul_le_mul hbc (by omega)
theorem exceptional_count (J:UJ) (T:Finset K) (hT:T⊆J.CF) (B:ℕ)
    (hcap:asT J T B) :T.card≤6*B+1 := by
  classical
  by_cases hmin:T.card≤1
  · omega
  let rel (a :K×K) (i:I) :=J.hit a.1 i ∧ ¬ J.hit a.2 i
  have hrows (a :K×K) (ha :a∈T.offDiag) :
      c9-d≤((univ :Finset I).bipartiteAbove rel a).card:= by
    obtain ⟨hγ,hη,hneq⟩:=mem_offDiag.mp ha
    exact difference_hits J (hT hγ) (hT hη) hneq
  have hcols (i:I) (_:i∈univ) :
      (T.offDiag.bipartiteBelow rel i).card≤B*(T.card-1) := by
    have hprod:T.offDiag.bipartiteBelow rel i =
        (T.filter fun γ=>J.hit γ i) ×ˢ (T.filter fun γ => ¬ J.hit γ i) := by
      ext a
      simp only [mem_bipartiteBelow,mem_offDiag,mem_product,mem_filter,rel]
      constructor
      · rintro ⟨⟨h₁,h₂,_⟩,h₃,h₄⟩
        exact ⟨⟨h₁,h₃⟩,h₂,h₄⟩
      · rintro ⟨⟨h₁,h₃⟩,h₂,h₄⟩
        exact ⟨⟨h₁,h₂,fun h=>h₄ (h ▸ h₃)⟩,h₃,h₄⟩
    rw [hprod,card_product]
    exact product_bound (lI _) (hcap i)
  have hc:=card_nsmul_le_card_nsmul (R:=ℕ) rel hrows hcols
  rw [nsmul_eq_mul,nsmul_eq_mul,offDiag_card,← Nat.mul_sub_one,
    card_univ,IRSProfile.card_index] at hc
  have hpos :0<T.card-1 := by omega
  have hm:T.card*(c9-d)≤blockLength*B:= by
    apply lz _ hpos
    calc
      _=T.card*(T.card-1)*(c9-d) := by ring
      _≤blockLength*(B*(T.card-1)) :=hc
      _ = _:= by ring
  have hgap:0<c9-d:= by decide
  have hn:blockLength≤6*(c9-d) := by decide
  have hfin:T.card≤6*B:= by
    apply lz _ hgap
    exact hm.trans ((Nat.mul_le_mul_right B hn).trans_eq (by ring))
  omega
end
end qWdRihc
end
end
section
set_option autoImplicit true
namespace P6_7_3
noncomputable section
open Finset Polynomial
open P6 (K p dw)
open P5_7_1 (aT2 boi bDM)
open cu (L Shape ku Equation FX Jet triangle j9 rD)
open DP (jF ad0 d3q d3r)
open qQ (zI N5 aLQ wU)
open Qt (gY)
theorem emz (x :Input) :lo≤x.h∧x.h≤hi:= by
  obtain ⟨hl,hh⟩:=x.kA
  change (lo:ℤ)≤x.M.iF at hl
  change x.M.iF≤(hi:ℤ) at hh
  change lo≤x.M.iF.toNat∧x.M.iF.toNat≤hi
  omega
theorem poles (x :Input) :Nonempty (Poles x) := by
  let M:=x.M
  let H :=x.H
  let σ:=frobenius L p
  rcases x.bY with ⟨hm,hd,_,hm',hd',_,hcop,hnode,hdet,hdet',hmarks⟩
  let A:=j9 (M.factor*M.A₀)
  let B:=j9 (M.factor*M.A₁)
  let Q:=j9 M.Q
  have hdet0:IsCoprime (Q*A) H := by
    simpa [Q,A,H,M,j9,mul_assoc] using hdet
  have hdet1 :IsCoprime (Q.map σ*A.map σ) (H.map σ) := by
    simpa [Q,A,H,M,j9,mul_assoc,σ,Polynomial.map_mul] using hdet'
  let D:jF x.h :=
    ⟨![H,H.map σ],![Q,Q.map σ],![A,A.map σ],![B,B.map σ],
      fun i=> by fin_cases i <;> first | exact hm | exact hm',
      fun i=> by fin_cases i <;> first | exact hd | exact hd',
      hcop,fun i=> by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  obtain ⟨crt⟩:=atp.dRH D
  refine ⟨⟨D,crt,rfl,rfl,rfl,rfl,rfl,?_,?_⟩⟩
  · intro i j
    fin_cases i
    · exact (hnode j).1
    · exact (hnode j).2
  · intro γ hγ i
    let z :=algebraMap K L (M.label γ)
    have hz :j9 (M.factor*M.wK γ)=A+(@Polynomial.C L _) z*B:= by
      simp [A,B,z,P1.FJ.wK,j9,mul_add,mul_left_comm]
    obtain ⟨h₀,h₁,hr₀,hr₁⟩:=hmarks γ hγ
    fin_cases i
    · change IsCoprime (A+(@Polynomial.C L _) z*B) H ∧
        H∣(A+(@Polynomial.C L _) z*B)*j9 (x.F.scalar γ)+(@Polynomial.C L _) z*Q
      rw [← hz]
      exact ⟨h₀,hr₀⟩
    · have hσ: (j9 (M.factor*M.wK γ)).map σ =
          A.map σ+(@Polynomial.C L _) (z^p)*B.map σ:= by
        rw [hz,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ+(@Polynomial.C L _) (z^p)*B.map σ) (H.map σ) ∧
        H.map σ∣(A.map σ+(@Polynomial.C L _) (z^p)*B.map σ)*j9 (x.F.scalar γ) +
          (@Polynomial.C L _) (z^p)*Q.map σ
      rw [← hσ]
      exact ⟨h₁,hr₁⟩
theorem necessary {x :Input} (P:Poles x) {s :Shape} {W:ℕ} (hW:W<s.m*dw)
    {G:Jet} (hG:G∈P.rows s W) {γ:K} (hγ:γ∈x.Γ) :
    rD G (x.M.label γ) (x.F.scalar γ)=0:= by
  let B:=x.F.mark γ hγ
  have hd: (j9 (x.F.scalar γ)).natDegree≤131071+x.h:= by
    rw [j9,Polynomial.natDegree_map]
    exact P6_7.aic x.F hγ
  refine atp.dPr P.crt x.word P.nodes _ _ (P.marks γ hγ) hd B.bad.support
    B.bad.dw ?_ s W hW G hG
  intro i hit
  rw [j9,ad0,Polynomial.eval_map,Polynomial.eval₂_hom,B.scalar_hits i hit]
theorem ctc (t:Test) :
    (Lc t).m=terminal.m∧(Lc t).B=terminal.B∧(Lc t).J=terminal.J ∧
      (Lc t).U≤terminal.U:= by
  cases t with
  | none=>exact ⟨rfl,rfl,rfl,le_rfl⟩
  | some i=>exact ⟨rfl,rfl,rfl,min_le_right _ _⟩
private theorem eHv {x :Input} (P:Poles x) (t:Test)
    {q:zI} (hq:N5 q) (hv :agA P.rows terminal q)
    {W} (hW:W<(Lc t).m*dw) {G:Jet}
    (hG:G∈P.rows (Lc t) W) :
    wU q G (P5_7_1.contactPowerAt dw x.h (Lc t) W) := by
  let s :=Lc t
  obtain ⟨hm,hb,hj,hu⟩:=ctc t
  have hpos :0<x.h:=(show 0<lo by decide).trans_le (emz x).1
  have ht:s.m*dw<p:=hm ▸ (show terminal.m*dw<p by decide)
  apply baD.proof _ _ _ hq
  · have hle : (cutoff s-W)/(2*x.h)≤ cutoff s :=
      (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    change W<s.m*dw at hW
    have htop:1+cutoff s=s.m*dw:= by
      unfold cutoff
      omega
    change 1+(cutoff s-W)/(2*x.h)<p
    exact (Nat.add_le_add_left hle 1).trans_lt (htop ▸ ht)
  intro a c hac
  change a+c<1+(cutoff s-W)/(2*x.h) at hac
  have hc:=(Nat.le_div_iff_mul_le (by omega :0<2*x.h)).mp
    (show a+c≤(cutoff s-W)/(2*x.h) by omega)
  rw [Nat.mul_comm (a+c),Nat.mul_add] at hc
  have hcut:cutoff s=cutoff terminal:=congrArg (fun m=>m*dw - 1) hm
  have hW' : W≤ cutoff s := by
    change W<s.m*dw at hW
    unfold cutoff
    omega
  have hw:W+2*x.h*a+2*x.h*c≤ cutoff terminal:= by omega
  have ha :=atp.d3s P.crt x.word hG 0 a
  have hc' := atp.d3s P.crt x.word ha 1 c
  exact hv _ (d3q P.crt x.word hm hb hj hu hw hc')
theorem eqx {x :Input} (P:Poles x) (t:Test)
    (hfloor :bbk x.h (Lc t) P.rows)
    {qs :Finset zI} (geom : ∀ q∈qs,N5 q)
    (pass : ∀ q∈qs,agA P.rows terminal q) {f :Equation} (hf :aLQ qs f)
    (hE :ordinateThreshold t≤f.natDegree) (hv :apo t≤gY f) :
    ZN x.h (Lc t) (ordinateThreshold t) (apo t)≤j3 x.h (Lc t) := by
  let s :=Lc t
  have hh:0<2*x.h:= by
    have :=(emz x).1
    change 2407≤x.h at this
    omega
  have hk :0<131071-x.h:= by
    have :=(emz x).2
    change x.h≤2534 at this
    omega
  have he :0<ordinateThreshold t:= by cases t <;> exact Nat.succ_pos _
  have hn:f≠0:= by
    intro hz
    have h:=hf.positive
    simp [hz] at h
  have hmax : (∑ W∈range (s.m*dw),Module.finrank FX (P.rows s W)) ≤
      ∑ W∈range (s.m*dw),aT2 dw x.h s (ordinateThreshold t) (apo t) W:= by
    apply sum_le_sum
    intro W hW
    apply boi dw x.h s _ _ W _ hn hE hv hk he
    · intro G hG j i hji
      exact d3r P.crt x.word hG j i hji
    · intro G hG hne
      exact atp.eu5 (by omega) (by omega) P.crt x.word s W G hG hne
    · intro G hG hne
      exact hf.divides_leading G _ hne
        (fun q hq=>eHv P t (geom q hq) (pass q hq) (mem_range.mp hW) hG)
  have htot:=bDM dw x.h s (ordinateThreshold t) (apo t) hh hk
  change triangle s.U*ku s (fun q j=>s.m*dw+j-q*(131071-x.h)) ≤
    j3 x.h s + ∑ W∈range (s.m*dw),Module.finrank FX (P.rows s W) at hfloor
  change P5_7_1.jointGainAt dw x.h s (ordinateThreshold t) (apo t)≤j3 x.h s
  omega
end
end P6_7_3
end
section
set_option autoImplicit true
namespace q3u9Tnc
noncomputable section
open Polynomial
open P6 (I K p k jG)
open P5_7_2 (A)
open qe6nVeb (Raw phys width)
open P5_7_7 (base mL ic)
open cu (L FX j9 qD)
structure Input where
  words :P6.e9
  deleted:Finset I
  model :jG words deleted
  CF:Finset K
  family :P1.bje A model CF
  shift_not_mem:model.shift∉CF
  block :L[X]
  bY:P6_7.YQ model family block
  positive_height:0< model.iF.toNat
  D:ℕ
  degree_lo:k≤D
  degree_hi:D <A
  degree : ∀ γ∈CF,(family.scalar γ).natDegree≤D
abbrev hit (J:Input) :=P5_7_7.hit J.model.word J.family.scalar
abbrev sites (J:Input) :=P5_7_7.sites J.model.word J.family.scalar
structure DualWord (J:Input) (U:Finset K) where
  a₀:L[X]
  a₁:L[X]
  b₀:L[X]
  b₁:L[X]
  u₀:ℕ
  u₁:ℕ
  order :u₀≤u₁
  gMz :u₀+u₁=width J.D
  row₀:ic J.D a₀ b₀ (A+u₀)
  row₁:ic J.D a₁ b₁ (A+u₁)
  determinant : ∃ c:L,c≠0∧a₀*b₁-a₁*b₀=C c*mL Finset.univ
  rows_hit : ∀ i,a₀.eval (base i)*algebraMap K L (J.model.word i)+b₀.eval (base i)=0 ∧
    a₁.eval (base i)*algebraMap K L (J.model.word i)+b₁.eval (base i)=0
  target : ∀ i,a₀.eval (base i)≠0∨a₁.eval (base i)≠0
  P:K→ L[X]
  Q:K→ L[X]
  denominator : ∀ γ∈U,Q γ≠0
  coprime : ∀ γ∈U,IsCoprime (P γ) (Q γ)
  numerator_id : ∀ γ∈U,mL (sites J γ)*P γ=a₁*j9 (J.family.scalar γ)+b₁
  denominator_id : ∀ γ∈U,mL (sites J γ)*Q γ=a₀*j9 (J.family.scalar γ)+b₀
  degrees : ∀ γ∈U,
    (sites J γ).card≤A+u₀ ∧
    (Q γ).natDegree≤A+u₀-(sites J γ).card ∧
    (P γ).natDegree≤A+u₁-(sites J γ).card
  dual_hits : ∀ γ∈U,∀ i,
    (P γ).eval (base i)*a₀.eval (base i)=(Q γ).eval (base i)*a₁.eval (base i) ↔ ¬ hit J γ i
def atDual {J U} (B:DualWord J U) (g:Raw) (γ:K) :FX :=
  (Y3.embed g).eval₂ (qD (J.model.label γ)) (phys (B.P γ)/phys (B.Q γ))
def below {J U} (B:DualWord J U) (g:Raw) (W:ℕ) :Prop :=
  ∀ i j,(g.coeff i).coeff j≠0 →
    ((g.coeff i).coeff j).natDegree+g.natDegree*B.u₀+i*(B.u₁-B.u₀)≤W
structure LowSheets {J U} (B:DualWord J U) (T:Finset K) (e h W:ℕ) where
  size :ℕ
  sheet:Fin size→Raw
  irreducible : ∀ i,Irreducible (sheet i)
  positive : ∀ i,0<(sheet i).natDegree
  moving : ∀ i,0<Qt.gY (Y3.embed (sheet i))
  weight : ∀ i,below B (sheet i) W
  ordinate_sum : ∑ i,(sheet i).natDegree≤e
  seed_sum : ∑ i,Qt.gY (Y3.embed (sheet i))≤h
  roots : ∀ γ∈T,∃ i,atDual B (sheet i) γ=0
def dcQ (J:Input) (γ:K) :Fin 2→L :=
  ![algebraMap K L (J.model.label γ),(algebraMap K L (J.model.label γ))^p]
end
end q3u9Tnc
end
