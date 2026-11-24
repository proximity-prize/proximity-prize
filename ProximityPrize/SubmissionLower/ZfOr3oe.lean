import ProximityPrize.SubmissionLower.ZV7VOqb
import ProximityPrize.SubmissionLower.ZGAUtmc
import ProximityPrize.SubmissionLower.ZZjPLVd
import ProximityPrize.SubmissionLower.ZgLUh9d
import ProximityPrize.SubmissionLower.ZLt6Io
set_option Elab.async false
set_option maxHeartbeats 900000
section
set_option autoImplicit true
namespace qdWtcWb
open qoWrama qrcA6ce MvPolynomial
open qHde8fc (Ground)
open GN (Interpolant ord b9 mC BD)
open fP (cF)
open qEofLDb (Term cap apA Io)
open private B C₂ F lU sO B0 y4 GN.const_mem mul_bounded from ProximityPrize.SubmissionLower.B0
open private u7 zA Ep n7 value_mem ur top_mem from ProximityPrize.SubmissionLower.ZZjPLVd
open private cU vT fall_bound from ProximityPrize.SubmissionLower.C0
open private ajh Nm from ProximityPrize.SubmissionLower.BU
open private aEI from ProximityPrize.SubmissionLower.BW
open private nY from ProximityPrize.SubmissionLower.C0
open private coeffTop_cast coeffTop denom denom_ne from ProximityPrize.SubmissionLower.ZV7VOqb
noncomputable section
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def CK:Interpolant:=C 56 - u7
private theorem coordinate_eval (v :aY) (hhi:ord v.val≤56) :
    b9 v.val CK=((56 - ord v.val :ℕ) :Ground) ∧
    b9 v.val (n7 56)=((56 - ord v.val+v.val 0:ℕ) :Ground) := by
  constructor
  · rw [CK,map_sub,mC,Ep,Nat.cast_sub hhi]
    norm_num
  · rw [Nat.cast_add,Nat.cast_sub hhi]
    have h:=v.property
    rw [cF] at h
    have hc:=congrArg (fun n:ℕ=>(n:Ground)) h
    push_cast at hc
    simp [n7,B,C₂,ord]
    linear_combination 2*hc
private def poly (b:Term) :Interpolant :=
  C ((b.q:Ground)*(denom b)⁻¹)*cU b.i CK *
    cU (b.n - b.i) (n7 56 - C (b.i:Ground)) *
    sO (C ((↑(b.c+b.n) :Ground)-4) - B)
      (C ((b.c:Ground) - b.n) - ur 56) b.k
private theorem btT {d:ℕ} (b:Term) (hb:b.i≤b.n∧2*b.n+b.i+b.k≤d) :
    poly b∈Bounded d:= by
  obtain ⟨hi,hd⟩:=hb
  have hD:CK∈Bounded 3:=(Bounded 3).sub_mem (GN.const_mem _ _) zA
  have hZ:=(Bounded 2).sub_mem (value_mem 56) (GN.const_mem 2 (b.i:Ground))
  have hA:=(Bounded 1).sub_mem (GN.const_mem 1 ((↑(b.c+b.n) :Ground)-4)) lU.1
  have hH :=(Bounded 2).sub_mem (GN.const_mem 2 ((b.c:Ground) - b.n)) (top_mem 56)
  exact restrictWeightedDegree_mono _ (by omega) (mul_bounded
    (mul_bounded (mul_bounded (GN.const_mem 0 ((b.q:Ground)*(denom b)⁻¹)) (fall_bound hD _)) (fall_bound hZ _))
    (B0 hA hH _))
private theorem ccd (v :aY) (hv :ord v.val≤56) (b:Term)
    (h:2*b.n+b.i+b.k≤56) (hc:cap b.n≤b.c) :
    b9 v.val (poly b) =
      (apA (56 - ord v.val) (v.val 0) (v.val 3) b:Ground) := by
  let t:=56 - ord v.val
  let a :=v.val 0
  let f :=v.val 3
  obtain ⟨h0,h1⟩:=coordinate_eval v hv
  change b9 v.val CK=(t:Ground) at h0
  change b9 v.val (n7 56)=((t+a :ℕ) :Ground) at h1
  change _=(apA t a f b:Ground)
  have harg :b9 v.val (n7 56 - C (b.i:Ground)) =
      ((t+a :ℕ) :Ground)-(b.i:Ground) := by
    rw [map_sub,h1,mC]
  simp only [poly,apA,map_mul,mC,Nm,h0,harg]
  by_cases hi:b.i≤t
  · have hi' : b.i≤t+a := by omega
    rw [← Nat.cast_sub hi']
    by_cases hn:b.n≤t+a
    · rw [ite_eq_left ⟨hn,hi⟩]
      let s :=b.c-(a+f)
      let u:=t+a - b.n
      have hcap:a+f≤b.c:= by
        dsimp [cap,t,a,f,ord] at *
        omega
      have hb:v.val 1+4=t+2*a+f := by
        have hd:=v.property
        rw [cF] at hd
        dsimp [t,a,f,ord] at *
        omega
      have hb' := congrArg (fun n:ℕ=>(n:Ground)) hb
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hb'
      have hT:b9 v.val (ur 56)=(f :Ground) - t:= by
        have ht:=congrArg (fun i:ℕ=>(i:Ground)) (show t+ord v.val=56 by omega)
        rw [Nat.cast_add,← Ep v] at ht
        simp [ur,u7,B,C₂,F,f] at ht ⊢
        linear_combination ht
      have hA:b9 v.val (C ((↑(b.c+b.n) :Ground)-4) - B) =
          (s :Ground) - u:= by
        simp only [map_sub,mC,B,BD]
        change (↑(b.c+b.n) :Ground)-4-(v.val 1 :Ground)= _
        dsimp only [s,u]
        rw [Nat.cast_sub hcap,Nat.cast_sub hn]
        push_cast
        linear_combination (-1 :Ground)*hb'
      have hH :b9 v.val (C ((b.c:Ground) - b.n) - ur 56) =
          (s :Ground)+u:= by
        rw [map_sub,mC,hT]
        dsimp only [s,u]
        rw [Nat.cast_sub hcap,Nat.cast_sub hn,Nat.cast_add,Nat.cast_add]
        ring
      rw [y4 _ _ _ s u hA hH]
      change (_ *nY ((1+Polynomial.X)^s*(1-Polynomial.X)^u) b.k :Ground)= _
      by_cases hk :b.k≤ s+u
      · rw [ite_eq_left hk]
        change _=((b.q*(t.fast_choose b.i:ℤ) *
          ((t+a-b.i).fast_choose (b.n-b.i) :ℤ)*coeffTop s u b.k :ℤ) :Ground)
        simp only [Int.cast_mul,Int.cast_natCast,coeffTop_cast hk,← Nat.choose_eq_fast_choose,
          ← ajh,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,nY]
        have hh:=inv_mul_cancel₀ (denom_ne b h)
        unfold denom at hh ⊢
        linear_combination ((b.q:Ground)*(t.choose b.i:Ground) *
          ((t+a-b.i).choose (b.n-b.i) :Ground) *
          (((1+Polynomial.X)^s*(1-Polynomial.X)^u:Polynomial Ground).coeff b.k))*hh
      · rw [ite_eq_right hk,aEI (Nat.lt_of_not_ge hk),mul_zero,Int.cast_zero]
    · rw [ite_eq_right (fun h=>hn h.1),vT (by omega :t+a - b.i<b.n - b.i),
        mul_zero,zero_mul,Int.cast_zero]
  · rw [ite_eq_right (fun h=>hi h.2),vT (by omega :t<b.i),
      mul_zero,zero_mul,zero_mul,Int.cast_zero]
def aV (bs :List Term) :Interpolant:=(bs.map poly).sum
theorem aaH {d:ℕ} (bs :List Term)
    (h : ∀ b∈bs,b.i≤b.n∧2*b.n+b.i+b.k≤d) :aV bs∈Bounded d:= by
  induction bs with
  | nil=>exact Submodule.zero_mem _
  | cons b bs ih =>
    exact (Bounded d).add_mem (btT b (h _ List.mem_cons_self))
      (ih fun y hy=>h y (List.mem_cons_of_mem _ hy))
theorem W6 (v :aY) (hv :ord v.val≤56) (bs :List Term)
    (h : ∀ b∈bs,2*b.n+b.i+b.k≤56∧cap b.n≤b.c) :
    b9 v.val (aV bs)=(Io (56 - ord v.val) (v.val 0) (v.val 3) bs :Ground) := by
  induction bs with
  | nil=>simp [aV,qEofLDb.Io]
  | cons b bs ih =>
    simp only [aV,qEofLDb.Io,List.map_cons,List.sum_cons,map_add,Int.cast_add]
    have hb:=h b List.mem_cons_self
    rw [ccd v hv b hb.1 hb.2]
    exact congrArg ((apA (56 - ord v.val) (v.val 0) (v.val 3) b:Ground) + ·)
      (ih fun y hy=>h y (List.mem_cons_of_mem _ hy))
end
end qdWtcWb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qT7fytc
open MvPolynomial
open GN (Interpolant ord weights b9)
open fP (cF)
open qEofLDb (Term cap Io aS3)
structure Rec where
  w:ℕ
  f :ℕ
  a :ℕ
  cut:ℕ
  m:ℕ
  code :ℕ
def decode :ℕ→ℕ→List Term
  | 0,_=>[]
  | m+1,z =>
    let width :=4*((z >>> 19) % 8+1)
    let v :=(z >>> 22) % 2^width
    ⟨z % 32,(z >>> 5) % 32,(z >>> 10) % 64,cap (z % 32)+(z >>> 16) % 8,
      if v % 2=0 then ((v/2 :ℕ) :ℤ) else -((v/2 :ℕ) :ℤ)⟩ :: decode m (z >>> (22+width))
def fitsB (d strip:ℕ) (b:Term) :Bool :=
  decide (b.i≤b.n∧2*b.n+b.i+b.k≤d∧b.c+8≤ strip+b.n+b.k∧cap b.n≤b.c)
def stripB (bs :List Term) :ℕ:=(bs.map fun b=>b.c+8-(b.n+b.k)).foldl max 0
def lowerB (F T A t a :ℕ) :ℕ:=if t<T then 0 else if a<A then F else F+1
def lineB (S F T A strip:ℕ) (bs :List Term) (t a :ℕ) :Bool :=
  let lo:=lowerB F T A t a
  let hi:=min ((56 - t - 3*a)/2+1) (t+strip+1-8)
  (List.range (hi-lo)).all fun j =>
    decide (t+2*a+(lo+j)<S) || qL60i.IoR t a (lo+j) bs == 0
def headOk (T A F d:ℕ) (bs :List Term) :Bool :=
  decide (d≤56) && decide (T≤56) && bs.all (fitsB d (stripB bs)) &&
    (qL60i.IoR T A F bs != 0)
def planeOk (S T A F:ℕ) (bs :List Term) (t:ℕ) :Bool :=
  (List.range 17).all (lineB S F T A (stripB bs) bs t)
def cellOk (S T A F d:ℕ) (bs :List Term) :Bool :=
  headOk T A F d bs && (List.range (T+1)).all (planeOk S T A F bs)
theorem cellOk_of_parts {S T A F d:ℕ} {bs :List Term} (hh:headOk T A F d bs=true)
    (hp : ∀ t≤T,planeOk S T A F bs t=true) :cellOk S T A F d bs=true := by
  unfold cellOk
  rw [Bool.and_eq_true,List.all_eq_true]
  exact ⟨hh,fun t ht=>hp t (by have :=List.mem_range.mp ht; omega)⟩
theorem cellOk_parts {S T A F d:ℕ} {bs :List Term} (h:cellOk S T A F d bs=true) :
    headOk T A F d bs=true ∧ ∀ t≤T,planeOk S T A F bs t=true := by
  unfold cellOk at h
  rw [Bool.and_eq_true,List.all_eq_true] at h
  exact ⟨h.1,fun t ht=>h.2 t (List.mem_range.mpr (by omega))⟩
def recOK52 (q:Rec) :Bool:=cellOk 4 (56-(q.w - 52)) q.a q.f (q.cut - 1) (decode q.m q.code)
def headOk52 (q:Rec) :Bool:=headOk (56-(q.w - 52)) q.a q.f (q.cut - 1) (decode q.m q.code)
def planeOk52 (q:Rec) (t:ℕ) :Bool:=planeOk 4 (56-(q.w - 52)) q.a q.f (decode q.m q.code) t
def recOK54 (q:Rec) :Bool:=cellOk 2 (56-(q.w - 54)) q.a q.f (q.cut - 1) (decode q.m q.code)
def headOk54 (q:Rec) :Bool:=headOk (56-(q.w - 54)) q.a q.f (q.cut - 1) (decode q.m q.code)
def planeOk54 (q:Rec) (t:ℕ) :Bool:=planeOk 2 (56-(q.w - 54)) q.a q.f (decode q.m q.code) t
theorem recOK52_of_parts {q:Rec} (hh:headOk52 q=true)
    (hp : ∀ t≤56-(q.w - 52),planeOk52 q t=true) :recOK52 q=true :=
  cellOk_of_parts hh hp
theorem recOK54_of_parts {q:Rec} (hh:headOk54 q=true)
    (hp : ∀ t≤56-(q.w - 54),planeOk54 q t=true) :recOK54 q=true :=
  cellOk_of_parts hh hp
def linesB (S F T A strip:ℕ) (bs :List Term) (t:ℕ) :ℕ→ℕ→Bool
  | _,0=>true
  | a,n+1=>lineB S F T A strip bs t a && linesB S F T A strip bs t (a+1) n
theorem linesB_join {S F T A strip t:ℕ} {bs :List Term} (n:ℕ) :
    ∀ {a m:ℕ},linesB S F T A strip bs t a n=true→linesB S F T A strip bs t (a+n) m=true →
      linesB S F T A strip bs t a (n+m)=true := by
  induction n with
  | zero=>intro a m _ h2; simpa using h2
  | succ n ih =>
    intro a m h1 h2
    simp only [linesB,Bool.and_eq_true] at h1
    rw [show n+1+m=(n+m)+1 by omega]
    simp only [linesB,Bool.and_eq_true]
    exact ⟨h1.1,ih h1.2 (by rw [show a+1+n=a+(n+1) by omega]; exact h2)⟩
theorem linesB_spec {S F T A strip t:ℕ} {bs :List Term} (n:ℕ) :
    ∀ {a :ℕ},linesB S F T A strip bs t a n=true →
      ∀ b,a≤b→b<a+n→lineB S F T A strip bs t b=true := by
  induction n with
  | zero=>intro a _ b h1 h2; omega
  | succ n ih =>
    intro a h b h1 h2
    simp only [linesB,Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with h3 | h3
    · subst h3; exact h.1
    · exact ih h.2 b (by omega) (by omega)
theorem planeOk_of_linesB {S T A F:ℕ} {bs :List Term} {t:ℕ}
    (h:linesB S F T A (stripB bs) bs t 0 17=true) :planeOk S T A F bs t=true := by
  unfold planeOk
  rw [List.all_eq_true]
  intro a ha
  exact linesB_spec 17 h a (Nat.zero_le _) (by have :=List.mem_range.mp ha; omega)
def chunk52 (q:Rec) (t a n:ℕ) :Bool :=
  linesB 4 q.f (56-(q.w - 52)) q.a (stripB (decode q.m q.code)) (decode q.m q.code) t a n
def chunk54 (q:Rec) (t a n:ℕ) :Bool :=
  linesB 2 q.f (56-(q.w - 54)) q.a (stripB (decode q.m q.code)) (decode q.m q.code) t a n
theorem chunk52_join {q:Rec} {t a n m:ℕ} (h1 :chunk52 q t a n=true) (h2 :chunk52 q t (a+n) m=true) :
    chunk52 q t a (n+m)=true :=linesB_join n h1 h2
theorem chunk54_join {q:Rec} {t a n m:ℕ} (h1 :chunk54 q t a n=true) (h2 :chunk54 q t (a+n) m=true) :
    chunk54 q t a (n+m)=true :=linesB_join n h1 h2
theorem planeOk52_of_chunk {q:Rec} {t:ℕ} (h:chunk52 q t 0 17=true) :planeOk52 q t=true :=
  planeOk_of_linesB h
theorem planeOk54_of_chunk {q:Rec} {t:ℕ} (h:chunk54 q t 0 17=true) :planeOk54 q t=true :=
  planeOk_of_linesB h
theorem check_zeroB {S F T A strip t a f :ℕ} {bs :List Term}
    (hb : ∀ b∈bs,b.c+8≤ strip+b.n+b.k∧cap b.n≤b.c)
    (h : ∀ a<17,lineB S F T A strip bs t a=true) (ha :a≤16) (ht:t≤56)
    (hbudget:3*a+2*f≤56 - t) (hreal:S≤t+2*a+f)
    (hlater :t<T∨F<f∨f=F∧a<A) :
    (Io t a f bs :qHde8fc.Ground)=0:= by
  by_cases hs :t+strip<f+8
  · rw [aS3 _ _ _ _ hbudget ht hs _ hb,Int.cast_zero]
  let lo:=lowerB F T A t a
  have hlo:lo≤f := by
    unfold lo lowerB
    split
    · omega
    · split <;> omega
  have hmem:f-lo∈List.range (min ((56 - t - 3*a)/2+1) (t+strip+1-8)-lo) :=
    List.mem_range.mpr (by omega)
  have hh:=List.all_eq_true.mp (h a (by omega)) _ hmem
  change (decide (t+2*a+(lo+(f-lo))<S) ||
    (qL60i.IoR t a (lo+(f-lo)) bs == 0))=true at hh
  rw [Nat.add_sub_of_le hlo] at hh
  rcases Bool.or_eq_true_iff.mp hh with h1 | h1
  · have :=of_decide_eq_true h1
    omega
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero (by rw [qL60i.Io_emod,beq_iff_eq.mp h1,Nat.cast_zero]))
theorem head_parts {T A F d:ℕ} {bs :List Term} (hh:headOk T A F d bs=true) :
    d≤56∧T≤56∧(∀ b∈bs,b.i≤b.n∧2*b.n+b.i+b.k≤d ∧
      b.c+8≤ stripB bs+b.n+b.k∧cap b.n≤b.c)∧Io T A F bs % (P1.p:ℤ)≠0:= by
  unfold headOk at hh
  simp only [Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne,ne_eq,List.all_eq_true] at hh
  obtain ⟨⟨⟨hd,hT⟩,hb⟩,hn⟩:=hh
  exact ⟨hd,hT,fun b hm=>of_decide_eq_true (hb b hm),by rw [qL60i.Io_emod]; exact_mod_cast hn⟩
section D52
open qHde8fc (Ground aD)
open qoWrama qrcA6ce
open qdWtcWb (aV aaH W6)
theorem key_cases52 (e v :aY) (h:dZ e<dZ v) :
    ord e.val<ord v.val ∨
      ord e.val=ord v.val∧(e.val 3<v.val 3∨e.val 3=v.val 3∧v.val 0<e.val 0) := by
  have he :=e.property
  have hv :=v.property
  rw [cF] at he hv
  have key (r :aY) :dZ r =
      (((52+ord r.val)*53+r.val 3)*53+r.val 2)*53+r.val 1 := by
    simp only [dZ,show cP (aD r.val)=52+ord r.val from nG r]
  rw [key,key] at h
  unfold ord at *
  omega
theorem rec_sound52 {q:Rec} (hq:recOK52 q=true) (hc:0<q.cut) (hwq:q.w≤108) (e :aY)
    (hw:cP (aD e.val)=q.w) (ha :e.val 0=q.a) (hf :e.val 3=q.f) :
    cE q.cut (aD e.val) ∈
      Submodule.span Ground (Set.range fun v :iw e=>cE q.cut (aD v.val.val)) := by
  obtain ⟨hh,hz⟩:=cellOk_parts hq
  obtain ⟨hd,-,hb,hn⟩:=head_parts hh
  let bs :=decode q.m q.code
  have ho:=nG e
  change cost e=q.w at hw
  have hT:56 - ord e.val=56-(q.w - 52) := by omega
  apply Ae e q.cut hc (aV bs)
    (aaH bs (fun b hm=>⟨(hb b hm).1,(hb b hm).2.1⟩))
  have hdeg b (hm:b∈bs) :2*b.n+b.i+b.k≤56∧cap b.n≤b.c :=
    ⟨(hb b hm).2.1.trans hd,(hb b hm).2.2.2⟩
  constructor
  · rw [W6 e (by omega) bs hdeg,hT,ha,hf]
    intro hz'
    exact hn (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz'))
  · intro v hv hk
    obtain ⟨hv₁,hv₂⟩:=hv
    have hvp:=v.property
    rw [cF] at hvp
    have hkey :=key_cases52 e v hk
    have hvlo:ord e.val≤ord v.val :=hkey.elim Nat.le_of_lt (fun h=>h.1.le)
    have hbudget:3*v.val 0+2*v.val 3≤56-(56 - ord v.val) := by
      have :3*v.val 0+2*v.val 3≤ord v.val := by unfold ord; omega
      omega
    have hreal:4≤(56 - ord v.val)+2*v.val 0+v.val 3:= by
      unfold ord at hv₁ ⊢
      omega
    have hlater :56 - ord v.val<56-(q.w - 52)∨q.f<v.val 3∨v.val 3=q.f∧v.val 0<q.a := by
      rcases hkey with h | ⟨_,h | ⟨h₁,h₂⟩⟩
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (hf.symm ▸ h))
      · exact Or.inr (Or.inr ⟨h₁.symm.trans hf,h₂.trans_eq ha⟩)
    rw [W6 v hv₁ bs hdeg]
    exact check_zeroB (fun b hm=>(hb b hm).2.2) (fun a ha=>List.all_eq_true.mp
      (hz _ (by omega)) a (List.mem_range.mpr ha)) hv₂ (by omega) hbudget hreal hlater
end D52
section D54
open qwzqCne qzVXMPd
noncomputable def pad54 (e :aY) :qHde8fc.aY :=
  ⟨e.val+Finsupp.single 1 2,by rw [map_add,Finsupp.degree_single,e.property]⟩
@[simp] theorem pad54_zero (e :aY) : (pad54 e).val 0=e.val 0:= by simp [pad54]
@[simp] theorem pad54_one (e :aY) : (pad54 e).val 1=e.val 1+2 := by simp [pad54]
@[simp] theorem pad54_two (e :aY) : (pad54 e).val 2=e.val 2 := by simp [pad54]
@[simp] theorem pad54_three (e :aY) : (pad54 e).val 3=e.val 3:= by simp [pad54]
@[simp] theorem pad54_ord (e :aY) :ord (pad54 e).val=ord e.val := by
  simp only [ord,pad54_zero,pad54_two,pad54_three]
noncomputable def shift2 (j:Fin 3) :Interpolant:=MvPolynomial.X j+C (if j=0 then 2 else 0)
theorem shift2_eval (e :aY) (P:Interpolant) :
    b9 e.val (bind₁ shift2 P)=b9 (pad54 e).val P:= by
  have h :
      (fun i:Fin 3=>aeval (fun j:Fin 3=>(e.val j.succ:Ground)) (shift2 i)) =
      (fun j:Fin 3=>((pad54 e).val j.succ:Ground)) := by
    funext j
    fin_cases j <;> simp [shift2]
  simp only [b9,aeval_bind₁,h]
theorem key_cases54 (e v :aY) (h:dZ e<dZ v) :
    ord e.val<ord v.val ∨
      ord e.val=ord v.val∧(e.val 3<v.val 3∨e.val 3=v.val 3∧v.val 0<e.val 0) := by
  have he :=e.property
  have hv :=v.property
  rw [cF] at he hv
  have key (r :aY) :dZ r =
      (((54+ord r.val)*55+r.val 3)*55+r.val 2)*55+r.val 1 := by
    simp only [dZ,show cP (aD r.val)=54+ord r.val from nG r]
  rw [key,key] at h
  unfold ord at *
  omega
theorem rec_sound54 {q:Rec} (hq:recOK54 q=true) (hc:0<q.cut) (hwq:q.w≤110) (e :aY)
    (hw:cP (aD e.val)=q.w) (ha :e.val 0=q.a) (hf :e.val 3=q.f) :
    cE q.cut (aD e.val) ∈
      Submodule.span Ground (Set.range fun v :iw e=>cE q.cut (aD v.val.val)) := by
  obtain ⟨hh,hz⟩:=cellOk_parts hq
  obtain ⟨hd,-,hb,hn⟩:=head_parts hh
  let bs :=decode q.m q.code
  have ho:=nG e
  change cost e=q.w at hw
  have hT:56 - ord e.val=56-(q.w - 54) := by omega
  have hdeg b (hm:b∈bs) :2*b.n+b.i+b.k≤56∧cap b.n≤b.c :=
    ⟨(hb b hm).2.1.trans hd,(hb b hm).2.2.2⟩
  have hshift (j:Fin 3) :shift2 j∈Bounded (weights j) :=
    (Bounded (weights j)).add_mem (X_mem_restrictWeightedDegree weights _ j le_rfl)
      (C_mem_restrictWeightedDegree weights _ _)
  have hB:qEofLDb.aV bs∈Bounded (q.cut - 1) :=
    qEofLDb.aaH bs (fun b hm=>⟨(hb b hm).1,(hb b hm).2.1⟩)
  apply Ae e q.cut hc (bind₁ shift2 (qEofLDb.aV bs))
    (bind₁_mem_restrictWeightedDegree hshift hB)
  constructor
  · rw [shift2_eval,qEofLDb.W6 (pad54 e) (by simp only [pad54_ord]; omega) bs hdeg,
      pad54_ord,pad54_zero,pad54_three,hT,ha,hf]
    intro hz'
    exact hn (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz'))
  · intro v hv hk
    obtain ⟨hv₁,hv₂⟩:=(abJ _).mp hv
    have hvp:=v.property
    rw [cF] at hvp
    have hkey :=key_cases54 e v hk
    have hvlo:ord e.val≤ord v.val :=hkey.elim Nat.le_of_lt (fun h=>h.1.le)
    have hbudget:3*v.val 0+2*v.val 3≤56-(56 - ord v.val) := by
      have :3*v.val 0+2*v.val 3≤ord v.val := by unfold ord; omega
      omega
    have hreal:2≤(56 - ord v.val)+2*v.val 0+v.val 3:= by
      unfold ord at hv₁ ⊢
      omega
    have hlater :56 - ord v.val<56-(q.w - 54)∨q.f<v.val 3∨v.val 3=q.f∧v.val 0<q.a := by
      rcases hkey with h | ⟨_,h | ⟨h₁,h₂⟩⟩
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (hf.symm ▸ h))
      · exact Or.inr (Or.inr ⟨h₁.symm.trans hf,h₂.trans_eq ha⟩)
    rw [shift2_eval,qEofLDb.W6 (pad54 v) (by simp only [pad54_ord]; omega) bs hdeg,
      pad54_ord,pad54_zero,pad54_three]
    exact check_zeroB (fun b hm=>(hb b hm).2.2) (fun a ha=>List.all_eq_true.mp
      (hz _ (by omega)) a (List.mem_range.mpr ha)) hv₂ (by omega) hbudget hreal hlater
end D54
end qT7fytc
end
