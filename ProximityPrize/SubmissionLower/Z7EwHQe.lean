import ProximityPrize.SubmissionLower.ZEGTqPa
import ProximityPrize.SubmissionLower.ZVHUUZd
import ProximityPrize.SubmissionLower.Zqby9gc
import ProximityPrize.SubmissionLower.Z0Ff26b
import ProximityPrize.SubmissionLower.ZnXcxbb
import ProximityPrize.SubmissionLower.ZUkTKja
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace q7EwHQe
noncomputable section
open Polynomial Finset
open P6 (K p blockLength)
open P5_7 (midAgreement)
open P6_7_1 (Input degree heights)
open q3rjQGe (marks rankPrice memberCap)
open TD (FP)
open aR (af ao extend embed cK jet)
open oR (qg)
open gT (tK FW)
open pI (abM d2l pN)
open private c3F from ProximityPrize.SubmissionLower.U
open qkOaTje (cover)
open bz3 (Mt)
open private aUW aUV aDh Ka aYc from ProximityPrize.SubmissionLower.BG
open scoped Classical BigOperators
local notation "Dmax" => P6_7_1.degree
abbrev lambdaD:ℚ:=(262144 :ℚ)*Dmax/midAgreement
abbrev μ:ℚ:=((blockLength - Dmax :ℕ) :ℚ)/(midAgreement - Dmax :ℕ)
private theorem regular_price (x :Input) {T:Finset K} (hT:T⊆x.Γ)
    (f :af 2) (hf :Irreducible f) (hj:0<f.degreeOf 1)
    (hreg : ∀ γ∈T,qg 1 f (extend (x.F.scalar γ))) :
    let b:ℚ:=f.totalDegree
    let j:ℚ:=f.degreeOf 1
    (T.card:ℚ)≤lambdaD*(4*b*j-2*j*j-b-j)+μ*j+1 := by
  have h:=qkOaTje.regular_price (D:=Dmax) (by decide) (by decide) (by decide) x.F
    (fun γ hγ=>(P6_7.aic x.F hγ).trans (Nat.add_le_add_left (heights x).2 _)) hT f hf hj hreg
  have e :qkOaTje.lam Dmax=lambdaD:= by
    show ((262144 :ℕ) :ℚ)/((179740:ℕ) :ℚ)*((133440:ℕ) :ℚ) =
      (262144 :ℚ)*((133440:ℕ) :ℚ)/((179740:ℕ) :ℚ)
    norm_num
  rw [e] at h
  exact h
private def transfer (B:ℚ) :ℚ:=4*B/5
private def residual (B s :ℚ) :ℚ:=4*s-(2*s*s+transfer B*s)/B
private def aoF (B J:ℚ) :ℚ:=residual B (min J (B-transfer B/4))
private def ordRate (B:ℚ) :ℚ:=max 0 (lambdaD*(transfer B-1)+μ)
private def mixRate (B J:ℚ) :ℚ:=lambdaD*(aoF B J-1)+1
private theorem peak_bound {B J j:ℚ} (hB:0<B) (hj:j≤J) :
    residual B j≤aoF B J:= by
  let c:=B-transfer B/4
  let a :=min J c
  have hprod:0≤(a-j)*(2*c-a-j) := by
    dsimp only [a]
    by_cases h:J≤ c
    · rw [min_eq_left h]
      exact mul_nonneg (sub_nonneg.mpr hj) (by linarith only [h,hj])
    · rw [min_eq_right (le_of_not_ge h)]
      nlinarith only [sq_nonneg (c-j)]
  dsimp only [aoF,residual]
  apply sub_nonneg.mp
  have he : (4*a-(2*a*a+transfer B*a)/B)-(4*j-(2*j*j+transfer B*j)/B) =
      2*((a-j)*(2*c-a-j))/B:= by
    dsimp only [c]
    field_simp [hB.ne']
    ring
  exact he.symm ▸ div_nonneg (mul_nonneg (by decide) hprod) hB.le
private theorem peak_one {B J:ℚ} (hB:1≤B) (hJ:1≤J) :
    1≤aoF B J:= by
  have hp:0<B:= by linarith only [hB]
  apply le_trans _ (peak_bound hp hJ)
  have h: (2+transfer B)/B≤3:=(div_le_iff₀ hp).mpr (by
    unfold transfer
    linarith only [hB])
  unfold residual
  simp only [mul_one]
  linarith only [h]
private theorem linearize {b j B J:ℚ} (hb:0≤b) (hj:0≤j)
    (hB:0<B) (hbB:b≤B) (hjJ:j≤J) :
    4*b*j-2*j*j≤transfer B*j+aoF B J*b:= by
  let t:=transfer B
  have ht:0≤t:= by unfold t transfer; positivity
  have hk :0≤2*j*j+t*j:= by positivity
  have hdiv :b/B*(2*j*j+t*j)≤1*(2*j*j+t*j) :=
    mul_le_mul_of_nonneg_right ((div_le_one hB).mpr hbB) hk
  have hm:=mul_le_mul_of_nonneg_left (peak_bound hB hjJ) hb
  change b*(4*j-(2*j*j+t*j)/B)≤b*aoF B J at hm
  change 4*b*j-2*j*j≤t*j+aoF B J*b
  rw [show b/B*(2*j*j+t*j)=b*((2*j*j+t*j)/B) by ring,one_mul] at hdiv
  calc
    _=t*j+(b*(4*j)-(2*j*j+t*j)) := by ring
    _≤t*j+(b*(4*j)-b*((2*j*j+t*j)/B)) :=add_le_add le_rfl (sub_le_sub_left hdiv _)
    _=t*j+b*(4*j-(2*j*j+t*j)/B) := by ring
    _≤t*j+b*aoF B J:=add_le_add le_rfl hm
    _ = _:= by ring
private theorem price_regular {n b j B J:ℚ} (hb:1≤b) (hj:0≤j)
    (hB:0<B) (hbB:b≤B) (hjJ:j≤J)
    (h:n≤lambdaD*(4*b*j-2*j*j-b-j)+μ*j+1) :
    n≤ordRate B*j+mixRate B J*b:= by
  have hp:=mul_le_mul_of_nonneg_left (linearize (by linarith only [hb]) hj hB hbB hjJ)
    (show 0≤lambdaD by positivity)
  have hu:=mul_le_mul_of_nonneg_right (le_max_right 0 (lambdaD*(transfer B-1)+μ)) hj
  unfold ordRate mixRate
  linarith only [h,hp,hu,hb]
private theorem root_count (x :Input) {T:Finset K} (hT:T⊆x.Γ)
    {R:ao[X][X]} (hR:R≠0)
    (hz : ∀ γ∈T,R.eval (extend (x.F.scalar γ))=0) :
    T.card≤R.natDegree := by
  let s (γ:K) :=extend (x.F.scalar γ)
  have hi:Set.InjOn s (T:Set K) := fun _ ha _ hb he =>
    x.F.distinct (hT ha) (hT hb) (Polynomial.map_injective embed embed.injective he)
  rw [← card_image_of_injOn hi]
  apply Polynomial.card_le_degree_of_subset_roots
  intro z hz'
  obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz'
  exact (Polynomial.mem_roots hR).mpr (hz γ hγ)
private theorem ordinate_count (x :Input) {T:Finset K} (hT:T⊆x.Γ)
    {q:af 2} (hq:q≠0) (hj:q.degreeOf 1=0)
    (hz : ∀ γ∈T,cK q (extend (x.F.scalar γ))=0) :
    T.card≤q.totalDegree := by
  let A:=Mt ao[X] q
  have hc:A=Polynomial.C (A.coeff 0) :=
    eq_C_of_natDegree_eq_zero ((aUW q).trans hj)
  have hA:A≠0:=(map_ne_zero_iff _ (Mt ao[X]).injective).mpr hq
  have hA0:A.coeff 0≠0:= fun h=>hA (by simpa only [h,Polynomial.C_0] using hc)
  have hR:Ka (A.coeff 0)≠0:=(map_ne_zero_iff _ Ka.injective).mpr hA0
  apply (root_count x hT hR ?_).trans
  · simpa only [A,Nat.zero_add] using aUV q 0 (Nat.zero_le _)
  · intro γ hγ
    let S:=extend (x.F.scalar γ)
    have he : (A.map (MvPolynomial.eval (jet S))).eval (jet S (1 :Fin 2))=0 :=
      (aDh q S).trans (hz γ hγ)
    conv at he=>lhs; rw [hc]
    simpa only [aYc,Polynomial.map_C,Polynomial.eval_C] using he
private theorem equation_price (x :Input) {T:Finset K} (hT:T⊆x.Γ)
    {b j:ℕ} {B J:ℚ} (hbB: (b:ℚ)≤B) (hjJ: (j:ℚ)≤J)
    (hp:b<p) (G:tK) (hG:abM G b j)
    (hz : ∀ γ∈T,FW G (x.F.scalar γ)=0) :
    (T.card:ℚ)≤ if B=0 then 0 else
      ordRate B*j+max 1 (mixRate B (min J B)+B)*b:= by
  classical
  obtain ⟨q,hq,hb,hj,hsolve⟩:=bz3.cFG G hG.1 hG.2.1 hG.2.2
  have hroot γ (hγ:γ∈T) :=hsolve _ (hz γ hγ)
  by_cases h0:q.degreeOf 1=0
  · have hn: (T.card:ℚ)≤b:= by exact_mod_cast (ordinate_count x hT hq h0 hroot).trans hb
    split_ifs with hB
    · exact hn.trans (hbB.trans_eq hB)
    · exact hn.trans (by
        have ha :=mul_nonneg (le_max_left 0 (lambdaD*(transfer B-1)+μ)) (Nat.cast_nonneg (α:=ℚ) j)
        have hb' := mul_le_mul_of_nonneg_right (le_max_left 1 (mixRate B (min J B)+B))
          (Nat.cast_nonneg (α:=ℚ) b)
        simp only [one_mul] at hb'
        unfold ordRate
        linarith only [ha,hb'])
  have hqj:1≤q.degreeOf 1 :=Nat.pos_of_ne_zero h0
  have hB₁:1≤B:=(Nat.cast_le.mpr (hqj.trans
    ((q.degreeOf_le_totalDegree 1).trans hb)) : (1 :ℚ)≤b).trans hbB
  have hB:0<B:= by linarith only [hB₁]
  have hJ:1≤ min J B:=le_min ((show (1 :ℚ)≤j by exact_mod_cast hqj.trans hj).trans hjJ) hB₁
  let u:=ordRate B
  let v :=mixRate B (min J B)
  have hu:0≤u:=le_max_left _ _
  have hv :0≤v :=add_nonneg
    (mul_nonneg (by positivity) (sub_nonneg.mpr (peak_one hB₁ hJ))) (by decide)
  obtain ⟨A,R,hA,hAb,hAj,hR,hRd,hcover⟩:=cover q hq hp hb hj
  let iy :=T.filter fun γ=>R.eval (extend (x.F.scalar γ))=0
  let reg (f :af 2) :=T.filter fun γ=>qg 1 f (extend (x.F.scalar γ))
  have hord: (iy.card:ℚ)≤(b:ℚ)^2 := by
    exact_mod_cast (root_count x ((filter_subset _ _).trans hT) hR
      (fun γ (hγ:γ∈iy)=>(mem_filter.mp hγ).2)).trans hRd
  have hsub:T⊆iy∪A.biUnion reg:= by
    intro γ hγ
    rcases hcover _ (hroot γ hγ) with hr | ⟨f,hf,hr⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨hγ,hr⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨hγ,hr⟩⟩)
  have hall:=(Nat.cast_le (α:=ℚ)).mpr (card_le_card hsub)
  have hreg: (∑ f∈A,((reg f).card:ℚ))≤u*j+v*b:= calc
    _ ≤ ∑ f∈A,(u*f.degreeOf 1+v*f.totalDegree) := by
      apply sum_le_sum
      intro f hf
      have hfb: (f.totalDegree :ℚ)≤B :=
        (Nat.cast_le.mpr ((single_le_sum (fun g _=>Nat.zero_le g.totalDegree) hf).trans hAb)).trans hbB
      have hfj: (f.degreeOf 1 :ℚ)≤J :=
        (Nat.cast_le.mpr ((single_le_sum (fun g _=>Nat.zero_le (g.degreeOf 1)) hf).trans hAj)).trans hjJ
      have hjb:=f.degreeOf_le_totalDegree 1
      exact price_regular (by exact_mod_cast (hA f hf).2.trans_le hjb) (Nat.cast_nonneg _) hB hfb
        (le_min hfj ((Nat.cast_le.mpr hjb).trans hfb))
        (regular_price x ((filter_subset _ _).trans hT) f (hA f hf).1 (hA f hf).2
          (fun _ hγ=>(mem_filter.mp hγ).2))
    _≤_:= by
      simp only [sum_add_distrib,← mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hAj) hu)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hAb) hv)
  have hreserve : (b:ℚ)^2≤B*b:= by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hbB (Nat.cast_nonneg _)
  rw [ite_eq_right hB.ne']
  have hfee :=mul_le_mul_of_nonneg_right (le_max_right 1 (v+B)) (Nat.cast_nonneg (α:=ℚ) b)
  change (T.card:ℚ)≤u*j+max 1 (v+B)*b
  linarith only [hall,q3rjQGe.card_union_q iy (A.biUnion reg),
    q3rjQGe.card_biUnion_q A reg,hreg,hord,hreserve,hfee]
theorem proof :q3rjQGe.c3:= by
  classical
  intro x o q ha _ hn hfit
  obtain ⟨G,hG,hGon⟩:=c3F bzS.proof cy5.proof ha hn
  have h:=equation_price x (T:=marks x q) (filter_subset _ _) (hfit 2) (hfit 1)
    ha.mixed_lt G hG (fun γ hγ=> by
      have hz :=RingHom.mem_ker.mp ((mem_filter.mp hγ).2 hGon)
      simpa only [d2l] using hz)
  let B:=memberCap o 0 2
  let J:=memberCap o 0 1
  unfold rankPrice
  change _≤FP (if B=0 then 0 else
    ![0,ordRate B,max 1 (lambdaD*(aoF B (min J B)-1)+B+1),0]) _
  change _≤(if B=0 then 0 else _) at h
  by_cases hB:B=0
  · simpa only [ite_eq_left hB,FP,Pi.zero_apply,zero_mul,Finset.sum_const_zero] using h
  · have he :mixRate B (min J B)+B=lambdaD*(aoF B (min J B)-1)+B+1 := by
      unfold mixRate
      ring
    rw [ite_eq_right hB,he] at h
    rw [ite_eq_right hB,FP,Fin.sum_univ_four]
    change _≤0*(pN q 0:ℚ)+ordRate B*(pN q 1 :ℚ) +
      max 1 (lambdaD*(aoF B (min J B)-1)+B+1)*(pN q 2 :ℚ) +
      0*(pN q 3:ℚ)
    simpa only [zero_mul,zero_add,add_zero] using h
end
end q7EwHQe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qBckyjc
noncomputable section
open Polynomial MvPolynomial
open P6 (dw p)
open P6_7 (RectTail)
open P6_7_2
open cu (L FX Jet Equation A5)
open DP (complete dOu VY U4 Source)
open axj (BA ds6)
open qQ (zI N5 aLQ)
open P6_7_1 (axisDegree)
open private aUq cNg cEw from ProximityPrize.SubmissionLower.Z
open private cleared_seedBox from ProximityPrize.SubmissionLower.Zqby9gc
open private a2f dGs from ProximityPrize.SubmissionLower.Z
theorem height {b:RectTail} (x :Input b) :0<x.h∧x.h≤131070:= by
  obtain ⟨hl,hu⟩:=x.kA
  change (b.kA.lo:ℤ)≤x.M.iF at hl
  change x.M.iF≤(b.kA.hi:ℤ) at hu
  have hlo:0<b.kA.lo:= by cases b <;> decide
  have hhi:b.kA.hi≤131070:= by cases b <;> decide
  change 0<x.M.iF.toNat∧x.M.iF.toNat≤131070
  omega
theorem rows_le {b x} (P : @Poles b x) (r :sk) (W:ℕ) :
    rectRows P r W≤VY P.crt x.word (rectShape b r) W :=
  Submodule.span_mono (Set.image_mono inf_le_left)
private theorem rows_full {b x} (P : @Poles b x) {r :sk} (hr :Subrect b r)
    {W:ℕ} (hW:W≤ rectCutoff b x.h) :
    rectRows P r W≤ rectRows P (full b) (rectCutoff b x.h) := by
  obtain ⟨_,_,hz,ht⟩:=hr
  apply Submodule.span_mono (Set.image_mono ?_)
  intro g hg
  rcases SetLike.mem_coe.mp hg with ⟨hG,hs⟩
  refine ⟨dOu P.crt x.word (s :=rectShape b r) (s' := rectShape b (full b))
    rfl rfl rfl (Nat.add_le_add hz ht) hW hG,?_⟩
  intro j i a e he
  exact hs j i a e (he.imp (lt_of_le_of_lt hz) (lt_of_le_of_lt ht))
private theorem rows_shift {b x} (P : @Poles b x) {r :sk} {W:ℕ} {g:Jet}
    (hg:g∈rectRows P r W) (i:Fin 2) (k :ℕ) :
    A5 i k g∈rectRows P r (W+2*x.h*k) := by
  let T:=rectRows P r (W+2*x.h*k)
  have hl:rectRows P r W≤T.comap (aUq i k) :=Submodule.span_le.mpr (by
    rintro _ ⟨Q,hQ,rfl⟩
    change aUq i k (U4 Q)∈T
    have hm:BA P.D i k Q ∈
        (complete P.crt x.word (rectShape b r) (W+2*x.h*k) ⊓ r.seedSpace :Submodule L Source) :=
      ⟨⟨⟨ds6 P.D hQ.1.1.1 i k,
        cyS.proof x.h P.D x.word (rectShape b r) Q hQ.1.1.2 i k⟩,
        bay.proof x.h P.D P.crt (rectShape b r) Q hQ.1.2 i k⟩,
        cleared_seedBox P.D hQ.2 i k⟩
    have he :U4 (BA P.D i k Q)∈T :=
      Submodule.subset_span ⟨_,hm,rfl⟩
    rw [cEw] at he
    have hn:algebraMap L[X] FX (P.D.block i^(2*k))≠0:= by
      rw [← map_zero (algebraMap L[X] FX)]
      exact (IsFractionRing.injective L[X] FX).ne (pow_ne_zero _ (P.D.monic i).ne_zero)
    exact (T.smul_mem_iff hn).mp he)
  rw [← cNg]
  exact hl hg
theorem row_caps {b x} (P : @Poles b x) {r :sk} {W:ℕ} {g:Jet}
    (hg:g∈rectRows P r W) (hn:g≠0) :
    g.leadingCoeff.natDegree+g.natDegree≤(Bs b).terminal.B ∧
      g.natDegree≤(Bs b).terminal.J:= by
  have hc: ((g.coeff g.natDegree).coeff g.leadingCoeff.natDegree)≠0:= by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
  have h:=DP.d3r P.crt x.word (rows_le P r W hg) _ _ hc
  exact ⟨h.1,h.2.1⟩
theorem Kw {b x} (P : @Poles b x) {r :sk} {W:ℕ} {g:Jet}
    (hg:g∈rectRows P r W) (j:ℕ) :
    axisDegree (g.coeff j) 0≤ r.z∧axisDegree (g.coeff j) 1≤ r.t:= by
  have hz (i:ℕ) (d:Fin 2 →₀ ℕ) (hd:r.z<d 0∨r.t<d 1) :
      a2f j i d g=0:= by
    have hle :rectRows P r W≤LinearMap.ker (a2f j i d) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨Q,hQ,rfl⟩
        exact LinearMap.mem_ker.mpr (dGs Q j i d (fun a=>hQ.2 j i a d hd)))
    exact LinearMap.mem_ker.mp (hle hg)
  constructor <;> rw [axisDegree,Finset.sup_le_iff] <;> intro i _ <;>
    apply degreeOf_le_iff.mpr <;> intro d hd <;> by_contra! h
  · exact MvPolynomial.mem_support_iff.mp hd (hz i d (Or.inl h))
  · exact MvPolynomial.mem_support_iff.mp hd (hz i d (Or.inr h))
theorem trace {b x} (P : @Poles b x) {r :sk} (hr :Subrect b r)
    {Q:Finset zI} {f :Equation}
    (geom : ∀ q∈Q,N5 q∧TerminalPass P q) (hf :aLQ Q f)
    {W:ℕ} (hW:W≤ rectCutoff b x.h) {g:Jet} (hg:g∈rectRows P r W) (hn:g≠0) :
    f^(1+(rectCutoff b x.h-W)/(2*x.h)-g.natDegree)∣g.leadingCoeff := by
  let N :=rectCutoff b x.h
  apply hf.divides_leading g _ hn
  intro q hq
  obtain ⟨hp,hpass⟩:=geom q hq
  apply baD.proof q g _ hp
  · have hN :N≤(Bs b).terminal.m*dw-1 :=Nat.sub_le _ _
    have hm: (Bs b).terminal.m≤3700:= by cases b <;> decide
    have hm0:0<(Bs b).terminal.m:= by cases b <;> decide
    have hpos :=Nat.mul_pos hm0 (by decide :0<dw)
    have hbound:1+((Bs b).terminal.m*dw-1)<p:= by
      rw [Nat.add_comm 1,Nat.sub_add_cancel hpos]
      exact (Nat.mul_le_mul_right dw hm).trans_lt (by change 3700*179827<0x7f000001; decide)
    exact (Nat.add_le_add_left
      (((Nat.div_le_self _ _).trans (Nat.sub_le N W)).trans hN) 1).trans_lt hbound
  · intro a c hac
    have hh:0<2*x.h:= by have :=(height x).1; omega
    have hd:=(Nat.le_div_iff_mul_le hh).mp
      (show a+c≤(N-W)/(2*x.h) by change a+c<1+(N-W)/(2*x.h) at hac; omega)
    rw [Nat.mul_comm (a+c),Nat.mul_add] at hd
    have hw:W+2*x.h*a+2*x.h*c≤N := by omega
    exact hpass _ (rows_full P hr hw (rows_shift P (rows_shift P hg 0 a) 1 c))
end
end qBckyjc
end
section
set_option autoImplicit true
namespace qBckyjc
noncomputable section
open Finset
open P6_7 (RectTail)
open P6_7_2
open cu (Shape ku)
open P6_7_1 (Rectangle)
open qiFSOoc (aT2)
open private caps Bp bKE from ProximityPrize.SubmissionLower.ZnXcxbb
def asRectangle (b:RectTail) (r :sk) :Rectangle :=
  let s :=(Bs b).terminal
  ⟨s.m,s.B,s.J,r.z,r.t⟩
private theorem scale (s :Shape) (u:ℕ) (F:ℕ→ℕ→ℕ) :
    u*ku s F=ku s (fun q j=>u*F q j) := by
  simp only [ku,Finset.mul_sum]
theorem total (b:RectTail) (h:ℕ) (r :sk) (kd:Fin 2) (E v :ℕ)
    (hh:0<2*h) (hk :1≤131071-h) :
    let N :=rectCutoff b h+1
    (∑ W∈range N,aT2 N h (asRectangle b r) kd E v W) +
      ZN b h r kd E v=rectVolume b h r := by
  let s :=asRectangle b r
  let N :=rectCutoff b h+1
  let u:=(caps s kd).1+1
  let U:=(caps s kd).2
  let F W q j:=if q*(131071-h)≤W+j then Bp U v ((q-j)/E) (1+(N-1-W)/(2*h)-j) else 0
  let G q j :=
    let g:=(q-j)/E
    let w:=amv b h q j
    (∑ i∈range g,(U+1-i*v-(U+1-(i+1)*v))*(w-2*h*(j+i))) +
      (U+1-g*v)*(w-2*h*(j+g))
  have hshape (H :ℕ→ℕ→ℕ) :
      ku (Bs b).terminal H=ku s.box H :=rfl
  have hstock (d:ℕ) :seedStock r kd d=u*(U+1-d) := by
    by_cases ha :kd=0 <;> simp [seedStock,u,U,caps,s,asRectangle,ha]
  have hvol:rectVolume b h r=u*((U+1)*ku s.box (amv b h)) := by
    unfold rectVolume
    rw [hshape,← Nat.mul_assoc]
    congr 1
    by_cases ha :kd=0 <;> simp [u,U,caps,s,asRectangle,ha,Nat.mul_comm]
  have hgain:ZN b h r kd E v=u*ku s.box G:= by
    rw [ZN,hshape,scale]
    refine sum_congr rfl fun q _=>sum_congr rfl fun j _ => ?_
    simp only [G,hstock,← Nat.mul_sub_left_distrib,Nat.mul_assoc,
      ← Finset.mul_sum,← Nat.mul_add]
  change (∑ W∈range N,u*ku s.box (F W))+ZN b h r kd E v= _
  rw [hgain,hvol,← mul_sum,← Nat.mul_add]
  congr 1
  have hswap: (∑ W∈range N,ku s.box (F W)) =
      ku s.box (fun q j => ∑ W∈range N,F W q j) := by
    unfold ku
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  rw [hswap,scale]
  simp only [ku,← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq:=(Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left q s.box.J)
  have hq:q≤q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact bKE N (2*h) (q*(131071-h)) j U v ((q-j)/E) (hjq.trans hq) hh
end
end qBckyjc
end
section
set_option autoImplicit true
namespace qBckyjc
noncomputable section
open Finset Polynomial
open P6_7_2

open P6_7_1 (axisDegree axis_degree_le)
open qiFSOoc (aT2 boi)
theorem proof :P6_7_2.c5:= by
  intro b x P r hr Q f geom hf a E v he hE hv
  let s :=asRectangle b r
  let N :=rectCutoff b x.h+1
  obtain ⟨hl,hu⟩:=height x
  have hk :0<131071-x.h:= by omega
  have hn:f≠0:= by
    intro hz
    have hp:=hf.positive
    simp [hz] at hp
  have ha :v≤axisDegree f a := by
    rcases hv with rfl | ⟨l,hv⟩
    · exact Nat.zero_le _
    · exact hv.trans (axis_degree_le le_rfl l)
  have hmax :rankSum P r ≤ ∑ W∈range N,aT2 N x.h s a E v W:= by
    apply sum_le_sum
    intro W hW
    refine boi N x.h s a E v W _ hn hE ha hk he
      (fun _ hg hn=>row_caps P hg hn) ?_ (fun _ hg j=>Kw P hg j) ?_
    · intro g hg hn
      exact atp.eu5 hl hu P.crt x.word _ W g (rows_le P r W hg) hn
    · intro g hg hn
      have hw:W≤ rectCutoff b x.h:=Nat.le_of_lt_succ (mem_range.mp hW)
      change f^(1+(N-1-W)/(2*x.h)-g.natDegree)∣g.leadingCoeff
      simpa only [N,Nat.add_sub_cancel] using trace P hr geom hf hw hg hn
  exact (Nat.add_le_add_right hmax _).trans_eq (total b x.h r a E v (by omega) hk)
end
end qBckyjc
end
