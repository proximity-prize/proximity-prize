import ProximityPrize.SubmissionLower.ZHcXm6a
import ProximityPrize.SubmissionLower.ZKfhfIb
import ProximityPrize.SubmissionLower.ZbsVARc
import ProximityPrize.SubmissionLower.Z8rcaBc
set_option Elab.async false
section
set_option autoImplicit true
namespace qigFtUb
open Finset cu P6_7_2
open P6 (dw)
open P6_7 (RectTail)
open Y2 (aOy aIy Tb bg5 aYm PG)
open aZD (Core aT)
open private bfq biQ from ProximityPrize.SubmissionLower.D9
open private bid from ProximityPrize.SubmissionLower.CN
open private bhM dgC from ProximityPrize.SubmissionLower.E7
abbrev stop (s :Shape) (E v :ℕ) :=s.J+Tb s E v
private def B4 (s :Shape) (v d:ℕ) :PG :=
  ⟨((s.U:ℤ)+1)-(d:ℤ)*v,-(v :ℤ),0⟩
private theorem seedLine_eq (s :Shape) (v d a :ℕ) (ha : (a+d)*v≤ s.U) :
    (B4 s v d).eval a=stock s.U ((a+d)*v) := by
  unfold B4 PG.eval stock
  push_cast [Nat.cast_sub (show (a+d)*v≤ s.U+1 by omega)]
  ring
private def core (b:RectTail) (s :Shape) (h E v d k :ℕ) :Core :=
  let D:ℤ:=131071-(h:ℤ)
  let p:ℤ:=(E-1 :ℕ)
  let w:ℤ:=(E*d:ℕ)
  ⟨k,E*d,E-1,bg5 s v d (Tb s E v),B4 s v d,
    ⟨(k :ℤ)-w,-p⟩,⟨2*((Bs b).terminal.m*dw:ℕ)-4*(h:ℤ)*(Bs b).dI-D*(w+k-1),-2-D*p⟩,
    2-4*(h:ℤ)-D⟩
private theorem core_term (b:RectTail) (s :Shape) (h E v d k t a :ℕ)
    (he :0<E) (hat :a≤t) (hk :t-a+E*(a+d)≤k) :
    (core b s h E v d k).term a t =
      2*(∑ q∈Ico (t-a+E*(a+d)) k,width b h q (t-a) t) := by
  let l:=t-a+E*(a+d)
  let D:ℤ:=131071-(h:ℤ)
  have hk' : l≤k :=hk
  have hl: (l:ℤ)=(t:ℤ)+(E*d:ℕ)+((E-1 :ℕ) :ℤ)*a := by
    rw [show l=aYm E d t+(E-1)*a from biQ E d t a he hat]
    push_cast [aYm]
    ring
  change _=2*(∑ q∈Ico l k,width b h q (t-a) t)
  rw [sum_Ico_eq_sum_range]
  have hw (i:ℕ) :width b h (l+i) (t-a) t=width b h l (t-a) t+(-D)*(i:ℤ) := by
    simp only [width,D,Nat.cast_add]
    ring
  simp_rw [hw]
  rw [bid]
  simp only [core,Core.term,aT.at,width,D,Nat.cast_sub hat,Nat.cast_sub hk']
  rw [hl]
  ring
private theorem order_pos (s :Shape) (E v :ℕ) :0<Tb s E v := by
  unfold Tb
  split
  · exact Nat.succ_pos _
  · exact lt_min (Nat.succ_pos _) (Nat.succ_pos _)
private def diag (b:RectTail) (s :Shape) (h E v d t k :ℕ) :ℤ :=
  ∑ a∈Ico (t-s.J) (min t (Tb s E v-1)+1),
    (stock s.U ((a+d)*v) :ℤ) * ∑ q∈Ico (t-a+E*(a+d)) k,width b h q (t-a) t
private theorem diag_eq (b:RectTail) (s :Shape) (h E v d k t:ℕ) (he :0<E) :
    let C:=core b s h E v d k
    (∑ a∈range C.cap,
      if a≤t∧t<a+(s.J+1)∧t+(C.offset+C.step*a)<C.column
      then C.seed.eval a*C.term a t else 0)=2*diag b s h E v d t k := by
  dsimp only
  let C:=core b s h E v d k
  let S:=(range C.cap).filter (fun a=>a≤t∧t<a+(s.J+1)∧t+(C.offset+C.step*a)<C.column)
  let T:=Ico (t-s.J) (min t (Tb s E v-1)+1)
  have hn:=order_pos s E v
  have hm (a :ℕ) :a∈S↔a∈T∧(a+d)*v≤ s.U∧t-a+E*(a+d)<k := by
    simp only [S,T,C,core,mem_filter,mem_range,mem_Ico,bfq,Nat.lt_succ_iff,le_min_iff]
    constructor
    · rintro ⟨⟨ha,hv⟩,ht,hj,hk⟩
      rw [biQ E d t a he ht]
      exact ⟨⟨by omega,ht,by omega⟩,hv,by simpa [aYm,Nat.add_assoc] using hk⟩
    · rintro ⟨⟨hj,ht,ha⟩,hv,hk⟩
      rw [biQ E d t a he ht] at hk
      exact ⟨⟨by omega,hv⟩,ht,by omega,by simpa [aYm,Nat.add_assoc] using hk⟩
  rw [← sum_filter,diag,mul_sum]
  change (∑ a∈S,C.seed.eval a*C.term a t)= _
  calc
    _ = ∑ a∈S,2*((stock s.U ((a+d)*v) :ℤ) *
          ∑ q∈Ico (t-a+E*(a+d)) k,width b h q (t-a) t) := by
      apply sum_congr rfl
      intro a ha
      obtain ⟨ht,hv,hk⟩:=(hm a).mp ha
      have hat :a≤t:=(le_min_iff.mp (Nat.le_of_lt_succ (mem_Ico.mp ht).2)).1
      change (B4 s v d).eval a*(core b s h E v d k).term a t= _
      rw [seedLine_eq _ _ _ _ hv,core_term b s h E v d k t a he hat hk.le]
      ring
    _ = _:= by
      apply sum_subset (fun a ha=>((hm a).mp ha).1)
      intro a ha hn
      by_cases hv : (a+d)*v≤ s.U
      · have hz :k≤t-a+E*(a+d) :=
          Nat.le_of_not_gt (fun hk=>hn ((hm a).mpr ⟨ha,hv,hk⟩))
        simp [Ico_eq_empty_of_le hz]
      · simp [stock,Nat.sub_eq_zero_of_le (by omega :s.U+1≤(a+d)*v)]
private def group (b:RectTail) (s :Shape) (h E v d l r k :ℕ) :ℤ :=
  let C:=core b s h E v d k
  (C.vo r 0 - C.vo r (s.J+1))-(C.vo l 0 - C.vo l (s.J+1))
private theorem group_eq (b:RectTail) (s :Shape) (h E v d l r k :ℕ) (he :0<E) (hl:l≤ r) :
    group b s h E v d l r k=720*(∑ t∈Ico l r,diag b s h E v d t k) := by
  rw [group,Core.azU,Core.azU,← mul_sub,← sum_Ico_eq_sub _ hl]
  simp_rw [diag_eq b s h E v d k _ he]
  rw [← mul_sum]
  ring
private def column (b:RectTail) (pin l:ℕ) :ℕ :=
  aOy (2*pin*((Bs b).dI+l)) (131071-pin)
    ((Bs b).terminal.m*dw) ((Bs b).terminal.B+1)
private theorem column_le (b:RectTail) (pin l:ℕ) :
    column b pin l≤(Bs b).terminal.B+1 := by
  simp only [column,aOy]
  split_ifs <;> omega
private def edge (b:RectTail) (pin n k :ℕ) :ℕ :=
  if k<(Bs b).terminal.B+1 then
    aOy (2*pin*(Bs b).dI+(131071-pin)*k) (2*pin)
      ((Bs b).terminal.m*dw) n
  else 0
private theorem lt_edge (b:RectTail) (pin n k t:ℕ) :
    t<edge b pin n k↔t<n∧k<column b pin t:= by
  unfold edge column
  rw [aIy]
  split
  · rw [aIy]
    simp only [Nat.mul_add] at *
    omega
  · omega
private theorem edge_anti (b:RectTail) (pin n k :ℕ) :
    edge b pin n (k+1)≤edge b pin n k := by
  by_contra! h
  obtain ⟨ht,hk⟩:=(lt_edge b pin n (k+1) _).mp h
  exact (Nat.lt_irrefl _) ((lt_edge b pin n k _).mpr ⟨ht,by omega⟩)
private def start (b:RectTail) (pin n:ℕ) :ℕ:=column b pin (n-1)-1
private def clip (b:RectTail) (pin n t:ℕ) :ℕ :=
  let k :=column b pin t
  if start b pin n<k then k else 0
private def segments (b:RectTail) (u pin h E v d n:ℕ) :ℤ :=
  let a :=start b pin n
  bhM (fun k =>
    let l:=edge b pin n (k+1)
    let r :=edge b pin n k
    if l< r then group b (active b u) h E v d l r (k+1) else 0)
    a ((Bs b).terminal.B+1-a)
private theorem segments_eq (b:RectTail) (u pin h E v d n:ℕ) (he :0<E) :
    segments b u pin h E v d n =
      720*(∑ t∈range n,diag b (active b u) h E v d t (clip b pin n t)) := by
  let a :=start b pin n
  let e :=edge b pin n
  let D:=diag b (active b u) h E v d
  let N :=(Bs b).terminal.B+1
  have hband (k :ℕ) :
      Ico (e (k+1)) (e k)=(range n).filter (fun t=>column b pin t=k+1) := by
    ext t
    simp only [mem_Ico,mem_filter,mem_range,e,← not_lt,lt_edge]
    omega
  have hterm (k :ℕ) :
      (if e (k+1)<e k then group b (active b u) h E v d (e (k+1)) (e k) (k+1) else 0) =
        720*(∑ t∈Ico (e (k+1)) (e k),D t (k+1)) := by
    split
    · exact group_eq _ _ _ _ _ _ _ _ _ he (edge_anti b pin n k)
    · rw [Ico_eq_empty_of_le (by omega),sum_empty,mul_zero]
  unfold segments
  rw [dgC]
  change (∑ i∈range (N-a),_)= _
  rw [← sum_Ico_eq_sum_range (fun k =>
      if e (k+1)<e k then group b (active b u) h E v d (e (k+1)) (e k) (k+1) else 0)]
  simp_rw [hterm,hband,sum_filter]
  rw [← mul_sum,sum_comm]
  congr 1
  apply sum_congr rfl
  intro t _
  let k :=column b pin t
  have hk :k≤N :=column_le b pin t
  change (∑ i∈Ico a N,if k=i+1 then D t (i+1) else 0)=D t (clip b pin n t)
  by_cases hl:a<k
  · have hz :k-1+1=k := by omega
    rw [sum_eq_single_of_mem (k-1) (mem_Ico.mpr ⟨by omega,by omega⟩)]
    · rw [hz,ite_eq_left rfl]
      unfold clip
      exact congrArg (D t) (ite_eq_left hl).symm
    · intro i _ hi
      exact ite_eq_right (by omega)
  · rw [show clip b pin n t=0 from ite_eq_right hl]
    rw [show D t 0=0 by simp [D,diag]]
    apply sum_eq_zero
    intro i hi
    have :=(mem_Ico.mp hi).1
    exact ite_eq_right (by omega)
private def endSlot (b:RectTail) (u E v :ℕ) :=stop (active b u) E v
def masked (b:RectTail) (u pin E v h q j t:ℕ) :ℤ :=
  if q<clip b pin (endSlot b u E v) t then width b h q j t else 0
private theorem clip_le (b:RectTail) (pin n t:ℕ) :
    clip b pin n t≤(Bs b).terminal.B+1 := by
  unfold clip
  dsimp only
  split
  · exact column_le b pin t
  · omega
def scaledGain (b:RectTail) (u pin h E v :ℕ) :ℤ :=
  let n:=endSlot b u E v
  segments b u pin h E v 0 n - segments b u pin h E v 1 n
theorem scaledGain_eq (b:RectTail) (u pin h E v :ℕ) (he :0<E) :
    scaledGain b u pin h E v=720*O3 (active b u) E v (masked b u pin E v h) := by
  have eq (d:ℕ) :
      segments b u pin h E v d (endSlot b u E v) =
        720*phase (active b u) E v d (masked b u pin E v h) := by
    rw [segments_eq _ _ _ _ _ _ _ _ he]
    congr 1
    apply sum_congr rfl
    intro t _
    unfold diag
    apply sum_congr rfl
    intro a _
    congr 1
    simp only [masked,← sum_filter]
    congr 1
    ext q
    simp only [mem_Ico,mem_filter]
    have hk :=clip_le b pin (endSlot b u E v) t
    change _≤(active b u).B+1 at hk
    omega
  rw [scaledGain,eq 0,eq 1,← mul_sub,gain_phases _ _ _ _ he]
end qigFtUb
end
section
set_option autoImplicit true
namespace qigFtUb
open P6_7 (RectTail)
open P6_7_2
open private cck from ProximityPrize.SubmissionLower.E7
def x5 (b:RectTail) (r :sk) (E v h:ℕ) :ℤ :=
  ((r.t:ℤ)+1)*scaledGain b r.z b.kA.lo h E v -
    720*((((r.z :ℤ)+1)*((r.t:ℤ)+1)*amm b)+(h:ℤ)*pole b*(r.z+r.t+2))
def check (b:RectTail) (r :sk) (E v :ℕ) :Bool :=
  let s :=(Bs b).terminal
  decide (s.B≤ r.z∧s.B≤ r.t∧r.z≤ s.U∧r.t≤ s.U) &&
  Nat.blt 0 (x5 b r E v b.kA.lo).toNat &&
  Nat.blt 0 (x5 b r E v (Bs b).hi).toNat
private theorem sW (b:RectTail) (r :sk) (E v :ℕ) (he :0<E) :
    ∃ d:ℤ,∀ h,x5 b r E v h=x5 b r E v b.kA.lo+((h:ℤ)-b.kA.lo)*d:= by
  let lo:=b.kA.lo
  let f :=masked b r.z lo E v
  let g:= fun q j t=>f (lo+1) q j t - f lo q j t
  let G:=O3 (active b r.z) E v
  have hw (h:ℕ) :f h=fun q j t=>f lo q j t+((h:ℤ)-lo)*g q j t:= by
    funext q j t
    simp only [f,g,masked]
    split <;> (try simp only [width,Nat.cast_add,Nat.cast_one]) <;> ring
  have hG (h:ℕ) :G (f h)=G (f lo)+((h:ℤ)-lo)*G g:= by
    unfold G
    rw [hw h,gain_add,gain_mul]
  refine ⟨720*((r.t:ℤ)+1)*G g - 720*(pole b:ℤ)*(r.z+r.t+2),fun h => ?_⟩
  unfold x5
  rw [scaledGain_eq b r.z lo h E v he,scaledGain_eq b r.z lo lo E v he]
  change ((r.t:ℤ)+1)*(720*G (f h))-_=((r.t:ℤ)+1)*(720*G (f lo))-_+_
  rw [hG]
  ring
theorem checked (b:RectTail) (r :sk) (E v :ℕ) (he :0<E)
    (hc:check b r E v=true) (h:ℕ) (hl:b.kA.lo≤h) (hh:h≤(Bs b).hi) :
    Subrect b r∧rectDebit b h r<ZN b h r 0 E v := by
  obtain ⟨u,x⟩:=r
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,Nat.blt_eq] at hc
  obtain ⟨⟨hr,hz⟩,hw⟩:=hc
  replace hz :0<x5 b ⟨u,x⟩ E v b.kA.lo:= by omega
  replace hw:0<x5 b ⟨u,x⟩ E v (Bs b).hi:= by omega
  refine ⟨hr,?_⟩
  obtain ⟨d,hd⟩:=sW b ⟨u,x⟩ E v he
  rw [hd _] at hw
  have hpos :0<x5 b ⟨u,x⟩ E v h:= by
    rw [hd _]
    exact cck (Int.ofNat_le.mpr hl) (Int.ofNat_le.mpr hh) hz hw
  have hk : (Bs b).hi≤131071 := by cases b <;> decide
  have hwidth :O3 (active b u) E v (masked b u b.kA.lo E v h) ≤
      O3 (active b u) E v (fun q j t=>(↑(amv b h q j-2*h*t:ℕ) :ℤ)) := by
    apply gain_le
    intro q j t
    unfold masked
    split
    · exact dma b h q j t (hh.trans hk)
    · exact Int.natCast_nonneg _
  have hx :0≤(x :ℤ)+1 := by positivity
  have hGain:=mul_le_mul_of_nonneg_left hwidth hx
  rw [← gain_rect] at hGain
  unfold x5 at hpos
  rw [scaledGain_eq _ _ _ _ _ _ he] at hpos
  have hDebit :=congrArg (fun n:ℕ=>(n:ℤ)) (Fi b h u x)
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hDebit
  apply Int.ofNat_lt.mp
  dsimp only at hpos
  nlinarith only [hpos,hDebit,hGain]
end qigFtUb
end
section
set_option autoImplicit true
namespace qigFtUb
open P6_7 (RectTail)
open P6_7_2
def gradeTest (b:RectTail) (j:ℕ) :Bool :=
  if h:j<(Bs b).ordinateCap then
    let i:jJ b:=⟨j,h⟩
    check b (Lc i 0) (j+1) (seedCap i+1)
  else false
theorem gradeTest_eq {b:RectTail} {j:ℕ} (hj:j<(Bs b).ordinateCap) :
    gradeTest b j=check b (Lc (⟨j,hj⟩:jJ b) 0) (j+1) (seedCap (⟨j,hj⟩:jJ b)+1) := by
  simp only [gradeTest,hj,dite_true]
def Prefix (b:RectTail) (a :ℕ) :ℕ→Prop
  | 0=>True
  | n+1=>Prefix b a n∧gradeTest b (a+n)=true
theorem prefix_get {b:RectTail} {a n:ℕ} (hn:Prefix b a n) {j:ℕ}
    (hj:j<n) :gradeTest b (a+j)=true := by
  induction n with
  | zero=>omega
  | succ n ih =>
    obtain ⟨hn,ht⟩:=(show Prefix b a n∧gradeTest b (a+n)=true from hn)
    by_cases h:j=n
    · subst j
      exact ht
    · exact ih hn (by omega)
theorem prefix_add {b:RectTail} {a n m:ℕ} (h₀:Prefix b a n) (h₁:Prefix b (a+n) m) :
    Prefix b a (n+m) := by
  induction m with
  | zero=>exact h₀
  | succ m ih =>
    obtain ⟨hm,ht⟩:=(show Prefix b (a+n) m∧gradeTest b (a+n+m)=true from h₁)
    change Prefix b a (n+m)∧gradeTest b (a+(n+m))=true
    exact ⟨ih hm,by simpa only [Nat.add_assoc] using ht⟩
end qigFtUb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qvucQ1a
theorem proof1 :qy95ATd.c1 := fun F l h _ H=>q4atxtd.node_bound F l h H
theorem proof2 :qy95ATd.c2 := fun F l h u s W _ =>
  qrKC9pb.of_children qWIOgVd.proof qazuAoe.proof
    (qyUzJvd.of_children qnCt0Qc.proof qc2iTLd.proof
      q6lciJe.proof)
    (qj0Yp9c.of_children
      (qO4AyGb.of_children qWz9F7b.proof qW0d9ye.proof)
      qBTXDtb.proof) F l h u s qy95ATd.width W
end qvucQ1a
end
section
set_option autoImplicit true
namespace qH2fULd
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P6 (K I blockLength dw)
open P5_7 (farAgreement)
open P6_7_3 (Input)
open qQ9yWTb (Curve)
open qy95ATd (G WordChart marks)
open qb0hmCe (CurveModel)
open P5_7_7 (base base_injective hit index_card mem_sites relativeDegree sites)
open scoped Classical
theorem count {x :Input} {U:Finset K} (hU:U⊆x.Γ) {J:WordChart x U}
    {q:Curve} {C:CurveModel q} (S:Sheet J C) (n v a :ℕ)
    (hn : ∀ i:I,
      (S.marks.filter fun γ => ¬ hit x.M.word x.F.scalar γ i ∧
        (S.num γ).eval (base i)≠0).card≤n)
    (hv : ∑ γ∈S.marks,poleOrderAt S γ≤v)
    (ha : (S.marks.filter fun γ=>S.num γ=0).card≤a) :
    G*S.marks.card≤blockLength*n+v+G*a := by
  let good:=S.marks.filter fun γ=>S.num γ≠0
  let lg (γ:K) :=sites x.M.word x.F.scalar γ
  let bad (γ:K) :=univ.filter fun i:I =>
    ¬ hit x.M.word x.F.scalar γ i∧(S.num γ).eval (base i)≠0
  have each (γ:K) (hm:γ∈good) :G≤(bad γ).card+poleOrderAt S γ:= by
    have hg:=mem_filter.mp hm
    let miss :=univ \ lg γ
    have hcard:miss.card=blockLength-(lg γ).card:= by
      change (univ \ lg γ).card= _
      rw [card_sdiff_of_subset (subset_univ _),card_univ,index_card]
    have heq :miss.filter (fun i=>(S.num γ).eval (base i)≠0)=bad γ:= by
      ext i
      simp [miss,bad,lg,mem_sites]
    have hsum:=card_filter_add_card_filter_not
      (s :=miss) (fun i=>(S.num γ).eval (base i)≠0)
    rw [heq,hcard] at hsum
    have hzero :=gR.kL.agd base base_injective
      (S.num γ) hg.2 (miss.filter (fun i => ¬ (S.num γ).eval (base i)≠0))
      (fun _ hi=>not_ne_iff.mp (mem_filter.mp hi).2)
    have hJ:=S.Bp hg.1
    have ⟨hh,hq,hp⟩:=J.degree γ hJ
    change (lg γ).card≤farAgreement+J.u₀ at hh
    change (J.Q γ).natDegree≤farAgreement+J.u₀-(lg γ).card at hq
    change (J.P γ).natDegree≤farAgreement+J.u₁-(lg γ).card at hp
    have horder :=J.order
    have hwidth :=J.gMz
    have hAgr :dw≤(lg γ).card:=(marks x U hU).strong γ hJ
    have hmax :max (J.Q γ).natDegree ((J.P γ).natDegree-(J.u₁-J.u₀)) ≤
        farAgreement+J.u₀-(lg γ).card:=max_le hq (by omega)
    have hrel :relativeDegree J γ+(lg γ).card+G≤blockLength:= by
      have hD:P6_7_3.degree≤dw:= by decide
      change relativeDegree J γ+(lg γ).card+(dw-P6_7_3.degree)≤blockLength
      simp only [relativeDegree]
      omega
    unfold poleOrderAt
    omega
  have hswap : ∑ γ∈good,(bad γ).card =
      ∑ i:I,(good.filter fun γ => ¬ hit x.M.word x.F.scalar γ i ∧
        (S.num γ).eval (base i)≠0).card:= by
    simp only [bad,card_filter]
    rw [sum_comm]
  have hb : ∑ γ∈good,(bad γ).card≤blockLength*n:= by
    rw [hswap,← index_card,← card_univ,← sum_const_nat (s :=(univ :Finset I))
      (f := fun _=>n) (fun _ _=>rfl)]
    exact sum_le_sum fun i _=>(card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hn i)
  have hs : ∑ γ∈good,poleOrderAt S γ≤v :=
    (sum_le_sum_of_subset (filter_subset _ _)).trans hv
  have hgood:G*good.card≤blockLength*n+v := by
    rw [Nat.mul_comm G,← sum_const_nat (s :=good) (f := fun _=>G) (fun _ _=>rfl)]
    exact (sum_le_sum fun γ hm=>each γ hm).trans
      (sum_add_distrib.trans_le (Nat.add_le_add hb hs))
  have hp:=card_filter_add_card_filter_not (s :=S.marks) (fun γ=>S.num γ=0)
  change (S.marks.filter fun γ=>S.num γ=0).card+good.card=S.marks.card at hp
  rw [← hp,Nat.mul_add]
  exact (Nat.add_le_add (Nat.mul_le_mul_left G ha) hgood).trans_eq (by ac_rfl)
end
end qH2fULd
end
section
set_option autoImplicit true
namespace qH2fULd
noncomputable section
open Polynomial Finset
open P5 (K)
open P6_7_3 (Input)
open qy95ATd (WordChart site)
open P5_7_7 (base mL sites)
open cu (L j9)
open DP (Tj)
private theorem no_common_root {f g:L[X]} (h:IsCoprime f g) {y :L}
    (hg:g.eval y=0) :f.eval y≠0:= by
  intro hf
  obtain ⟨a,b,hab⟩:=h
  have he :=congrArg (fun p:L[X]=>p.eval y) hab
  simp only [eval_add,eval_mul,hf,hg,mul_zero,add_zero,eval_one,zero_ne_one] at he
theorem starts {x :Input} {U:Finset K} (hU:U⊆x.Γ) (J:WordChart x U) :
    Nonempty (Starts J) := by
  obtain ⟨R⟩:=P6_7_3.poles x
  have hh:0<x.h:=(show 0<P6_7_3.lo by decide).trans_le (P6_7_3.emz x).1
  have he (i:Fin 2) : ∃ y,(R.D.block i).eval y=0:= by
    apply IsAlgClosed.exists_root
    rw [degree_eq_natDegree (R.D.monic i).ne_zero,R.D.degree]
    exact_mod_cast hh.ne'
  choose y hy using he
  have hnode (i:Fin 2) (j:P5.I) :y i≠base j:= by
    intro h
    have hz :=hy i
    rw [h] at hz
    exact R.nodes i j hz
  have hloc (i:Fin 2) (A:Finset P5.I) : (mL A).eval (y i)≠0:= by
    rw [mL,eval_prod]
    exact prod_ne_zero_iff.mpr fun j _=> by
      simpa only [eval_sub,eval_X,eval_C] using sub_ne_zero.mpr (hnode i j)
  let M (i:Fin 2) :=(R.D.constant i).eval (y i)
  let N (i:Fin 2) :=(R.D.slope i).eval (y i)
  let O (i:Fin 2) :=(R.D.offset i).eval (y i)
  let a₀ (i:Fin 2) :=J.a₀.eval (y i)
  let a₁ (i:Fin 2) :=J.a₁.eval (y i)
  let b₀ (i:Fin 2) :=J.b₀.eval (y i)
  let b₁ (i:Fin 2) :=J.b₁.eval (y i)
  have hc (i:Fin 2) :O i*M i≠0:= by
    simpa only [M,O,eval_mul] using no_common_root (R.D.determinant i) (hy i)
  have hdet (i:Fin 2) :a₁ i*b₀ i-a₀ i*b₁ i≠0:= by
    obtain ⟨c,hc,hJ⟩:=J.determinant
    have hj:=congrArg (fun p:L[X]=>p.eval (y i)) hJ
    have hn:a₀ i*b₁ i-a₁ i*b₀ i≠0:= by
      simp only [eval_sub,eval_mul,eval_C] at hj
      change a₀ i*b₁ i-a₁ i*b₀ i= _ at hj
      rw [hj]
      exact mul_ne_zero hc (hloc i univ)
    intro h
    exact hn (sub_eq_zero.mpr (sub_eq_zero.mp h).symm)
  refine ⟨⟨y,?_,fun i=>b₁ i*M i,fun i=>b₁ i*N i-a₁ i*O i,
    fun i=>b₀ i*M i,fun i=>b₀ i*N i-a₀ i*O i,?_,?_⟩⟩
  · intro h
    have hz :=hy 0
    rw [h] at hz
    exact no_common_root R.D.coprime (hy 1) hz
  · intro i
    convert mul_ne_zero (hdet i) (hc i) using 1
    ring
  · intro γ hγ i
    have hm:=(R.marks γ (hU hγ) i).2
    have hr :=eval_eq_zero_of_dvd_of_eval_eq_zero hm (hy i)
    simp only [eval_add,eval_mul,eval_C,Tj] at hr
    change (M i+site x γ i*N i)*(j9 (x.F.scalar γ)).eval (y i)+site x γ i*O i=0 at hr
    have hP:=congrArg (fun p:L[X]=>p.eval (y i)) (J.numerator_id γ hγ)
    have hQ:=congrArg (fun p:L[X]=>p.eval (y i)) (J.denominator_id γ hγ)
    simp only [eval_add,eval_mul] at hP hQ
    apply mul_left_cancel₀ (hloc i (sites x.M.word x.F.scalar γ))
    rw [← mul_assoc,← mul_assoc,hP,hQ]
    change (a₁ i*_+b₁ i)*_=(a₀ i*_+b₀ i)*_
    linear_combination (a₁ i*b₀ i-a₀ i*b₁ i)*hr
end
end qH2fULd
end
