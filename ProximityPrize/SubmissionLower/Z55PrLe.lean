import ProximityPrize.SubmissionLower.ZX8w26c
import ProximityPrize.SubmissionLower.ZjU0F6a
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 4000
namespace q82zwcd
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (K I p blockLength)
open q7F2qKe (wX scalarWitness weakAgreement)
open qxRSHvb (nativeSlope)
open cu (L)
open Cu (oO zT Wt)
open P5_7_7 (base base_injective hit index_card mem_sites sites)
open qK3TPae (regular)
open qb0hmCe (SiteTarget)


set_option backward.isDefEq.respectTransparency true in
def c1 :Prop :=
  ∀ {D w U s z q e H J} [Fact (Irreducible q)] (C:WordChart D w U s)
    (S:quN7Z4a.Sheet q J e H U z s),
    Set.InjOn z (U:Set K)→3≤e→q.totalDegree*e<p →
    ∃ (F:DualSheet C q z) (i:oO q →+* F.curve.E),
      F.d=e∧F.h≤H∧Function.Surjective i∧(∀ a,i (zT q a)=algebraMap L F.curve.E a) ∧
      (∀ j,i (Wt q j)=F.curve.seed j) ∧
      F.aEA S.root.equation i
def c3:Prop :=
  ∀ {D w U s z q} {J:WordChart D w U s} (F:DualSheet J q z),
    3≤F.d→F.d<p → ∃ V:Variation F,
      ((regular q z U) \ V.good).card≤(3+2*F.d)*F.h
def c4 :Prop :=
  ∀ {D w U s z q} {J:WordChart D w U s} {F:DualSheet J q z}
    (V:Variation F),F.d<p → ∀ R:SiteTarget,
      (V.good.filter (exception V R)).card≤2*F.d*(F.h+F.d*R.height q)
def c5:Prop :=
  ∀ {D w U s z q} {J:WordChart D w U s} {F:DualSheet J q z}
    (V:Variation F) (W:ℕ),
    3≤F.d→F.d<p→F.d*width D ≤W→polar D F.d W<p→F.Jm W →
    ∑ γ∈V.good,V.DG γ≤(poles D F.d W+(2*F.d-2))*F.h
private theorem on_word (hlocal:c4) {D w U s z q} {J:WordChart D w U s}
   {F:DualSheet J q z} (V:Variation F) (hp:F.d<p) (i:I) :
   (V.good.filter fun γ => ¬ hit w s γ i∧(V.num γ).eval (base i)≠0).card≤2*F.d*F.h:= by
 let y :=base i
 let R:SiteTarget :=⟨y,0,J.a₁.eval y,0,J.a₀.eval y,0⟩
 have h:=hlocal V hp R
 have h0:R.height q=0:= by simp [SiteTarget.height,R]
 rw [h0,Nat.mul_zero,Nat.add_zero] at h
 refine (card_le_card ?_).trans h
 intro γ hγ
 obtain ⟨hV,hm,hn⟩:=mem_filter.mp hγ
 have hu:=(mem_filter.mp (V.Bp hV)).1
 have hmatch :targetHit J z R γ:= by
   simpa only [targetHit,R,y,zero_mul,add_zero] using
     ⟨(J.target i).symm,(J.dual_hits γ hu i).mpr hm⟩
 exact mem_filter.mpr ⟨hV,hmatch,fun he=>hn (he.mpr (Or.inl (by simp [SiteTarget.det,R])))⟩
private theorem on_poles (hlocal:c4) {D w U s z q} {J:WordChart D w U s}
   {F:DualSheet J q z} (V:Variation F) (hp:F.d<p)
   (R:Fin 2→SiteTarget) (hR : ∀ i,(R i).coord=i∧(R i).det≠0)
   (hroot : ∀ γ∈U,∀ i,targetHit J z (R i) γ) :
   (V.good.filter fun γ=>V.num γ=0).card≤4*F.d*(F.h+F.d*q.totalDegree) := by
 let bad (i:Fin 2) :=V.good.filter (exception V (R i))
 have hb (i:Fin 2) : (bad i).card≤2*F.d*(F.h+F.d*q.totalDegree) := by
   have h: (R i).height q≤q.totalDegree := by unfold SiteTarget.height; split <;> omega
   exact (hlocal V hp (R i)).trans (by gcongr)
 have hc:V.good.filter (fun γ=>V.num γ=0)⊆bad 0∪bad 1 := by
   intro γ hγ
   obtain ⟨hv,hz⟩:=mem_filter.mp hγ
   obtain ⟨hU,hr⟩:=mem_filter.mp (V.Bp hv)
   obtain ⟨a,ha,_,hi⟩:=F.arc γ hU
   obtain ⟨i,hi⟩:=hi hr
   have hd:F.direction γ (R i).coord≠0:= by
     rw [(hR i).1,DualSheet.direction,dite_eq_left hU,ha i]
     exact fun h=>hi ((LaurentSeries.coeff_coe_powerSeries (a i) 1).symm.trans h)
   have he :γ∈bad i:=mem_filter.mpr ⟨hv,hroot γ hU i,fun ht =>
     (ht.mp (by simp [hz])).elim (hR i).2 hd⟩
   fin_cases i
   · exact mem_union_left _ he
   · exact mem_union_right _ he
 exact ((card_le_card hc).trans (card_union_le _ _)).trans
   ((Nat.add_le_add (hb 0) (hb 1)).trans_eq (by ring))
private theorem incidence {D w U s z q} {J:WordChart D w U s}
    {F:DualSheet J q z} (V:Variation F)
    (hD:D ≤weakAgreement) (hagr : ∀ γ∈U,weakAgreement≤(sites w s γ).card)
    (n a t:ℕ)
    (hn : ∀ i:I,(V.good.filter fun γ => ¬ hit w s γ i∧(V.num γ).eval (base i)≠0).card≤n)
    (ha : (V.good.filter fun γ=>V.num γ=0).card≤a)
    (ht : ∑ γ∈V.good,V.DG γ≤t) :
    gap D*V.good.card≤blockLength*n+t+gap D*a := by
  let G:=V.good.filter fun γ=>V.num γ≠0
  let bad (γ:K) :=univ.filter fun i:I =>
    ¬ hit w s γ i∧(V.num γ).eval (base i)≠0
  have each (γ:K) (hm:γ∈G) :gap D ≤(bad γ).card+V.DG γ:= by
    obtain ⟨hV,hne⟩:=mem_filter.mp hm
    let miss :=univ \ sites w s γ
    have hcard:miss.card=blockLength-(sites w s γ).card:= by
      change (univ \ sites w s γ).card= _
      rw [card_sdiff_of_subset (subset_univ _),card_univ,index_card]
    have heq :miss.filter (fun i=>(V.num γ).eval (base i)≠0)=bad γ:= by
      ext i
      simp [miss,bad,mem_sites]
    have hsum:=card_filter_add_card_filter_not
      (s :=miss) (fun i=>(V.num γ).eval (base i)≠0)
    rw [heq,hcard] at hsum
    have hz :=gR.kL.agd base base_injective
      (V.num γ) hne (miss.filter (fun i => ¬ (V.num γ).eval (base i)≠0))
      (fun _ hi=>not_ne_iff.mp (mem_filter.mp hi).2)
    have hU:=(mem_filter.mp (V.Bp hV)).1
    have ⟨hh,hq,hp⟩:=J.degree γ hU
    have ho:=J.order
    have hw:=J.xF
    have hag:=hagr γ hU
    have hmax :max (J.Q γ).natDegree ((J.P γ).natDegree-(J.u₁-J.u₀)) ≤
        weakAgreement+J.u₀-(sites w s γ).card:=max_le hq (by omega)
    have hrel :relativeDegree J γ+(sites w s γ).card+gap D ≤blockLength:= by
      simp only [relativeDegree,gap]
      omega
    unfold Variation.DG
    omega
  have hswap : ∑ γ∈G,(bad γ).card =
      ∑ i:I,(G.filter fun γ => ¬ hit w s γ i∧(V.num γ).eval (base i)≠0).card:= by
    simp only [bad,card_filter]
    rw [sum_comm]
  have hb : ∑ γ∈G,(bad γ).card≤blockLength*n:= by
    rw [hswap,← index_card,← card_univ,← sum_const_nat (s :=(univ :Finset I))
      (f := fun _=>n) (fun _ _=>rfl)]
    exact sum_le_sum fun i _=>(card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hn i)
  have hG:gap D*G.card≤blockLength*n+t:= by
    rw [Nat.mul_comm (gap D),← sum_const_nat (s :=G) (f := fun _=>gap D) (fun _ _=>rfl)]
    exact (sum_le_sum fun γ hm=>each γ hm).trans (sum_add_distrib.trans_le
      (Nat.add_le_add hb ((sum_le_sum_of_subset (filter_subset _ _)).trans ht)))
  have hsum:=card_filter_add_card_filter_not (s :=V.good) (fun γ=>V.num γ=0)
  change (V.good.filter fun γ=>V.num γ=0).card+G.card=V.good.card at hsum
  rw [← hsum,Nat.mul_add]
  exact (Nat.add_le_add (Nat.mul_le_mul_left _ ha) hG).trans_eq (by ac_rfl)
private def lowRate (D g W:ℕ) :ℚ :=
 7+6*(g:ℚ)+((2*g+1)*262144+poles D g W:ℕ)/(weakAgreement-D:ℕ)
private theorem width_pos {D:ℕ} (hD:131071≤D) :0<width D:= by
 change 0<262144+D-359480
 omega
private abbrev aPJ (D g k c:ℕ) :=
 let e :=g+k
 let j:=((k+1)*c)/(c+1)
 width D*(e*(e+1)+j*(j+1))/2
private abbrev weightCut (D g k c:ℕ) :=
 let j:=((k+1)*c)/(c+1)
 let a :=aPJ D g k c
 max (g*width D) (max ((c+1)*a/((k+1)*c)-j*width D) ((g+k-j)*width D))
private abbrev modulus (D g k c:ℕ) :=
 weightCut D g k c+1+(((k+1)*c)/(c+1))*width D
private theorem scalar_eq (b:P5_7_2.fO) (g:ℕ) (v :ℚ) :
    scalarWitness b g true v =
      (∃ k c,0<c ∧
        let D:=wX b
        let B:=modulus D g k c
        let W:=weightCut D g k c
        (g+k)*width D <B∧(c+1)*aPJ D g k c<((k+1)*c)*B ∧
          polar D g W<p∧lowRate D g W≤v∧(highFee g k c:ℚ)≤v) := by
  simp only [scalarWitness,ite_true,modulus,weightCut,aPJ,width,
    lowRate,highFee,polar,poles]
private theorem unpack {b g v} (hw:scalarWitness b g true v) :
  ∃ k c j W B,CompressionOK (wX b) g k c j W B∧polar (wX b) g W<p ∧
  lowRate (wX b) g W≤v∧(highFee g k c:ℚ)≤v := by
 rw [scalar_eq] at hw
 obtain ⟨k,c,hc,hE,hR,hp,hv,hh⟩:=hw
 let D:=wX b
 refine ⟨k,c,((k+1)*c)/(c+1),weightCut D g k c,modulus D g k c,?_,hp,hv,hh⟩
 refine ⟨width_pos (Nat.le_add_right _ _),hc,?_,le_max_left _ _,rfl,hE,hR⟩
 exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.succ_pos c)).mpr
  (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self c) (Nat.succ_pos k)))
private theorem slope {g:ℕ} (hg:0<g) (d:ℕ) :
  nativeSlope d g true*((g:ℚ)*d)=(d:ℚ)^2/3+(4*(g:ℚ)^2+9*g)*d:= by
 have hn: (g:ℚ)≠0:=Nat.cast_ne_zero.mpr hg.ne'
 simp only [nativeSlope,ite_true]
 field_simp [hn]
 ring
end
end q82zwcd
