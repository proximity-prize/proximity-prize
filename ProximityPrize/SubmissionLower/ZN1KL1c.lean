import ProximityPrize.SubmissionLower.ZLkly3d
import ProximityPrize.SubmissionLower.ZxlLGHd
import ProximityPrize.SubmissionLower.ZkYlUGe
set_option Elab.async false
set_option autoImplicit true
namespace qDoysbd
open qHde8fc qokB5pc MvPolynomial
open qhonTAe (Bounded)
open GN (Interpolant ord b9 mC BD)
open fP (cF)
open private B C₂ F GN.const_mem mul_bounded lU sO B0 y4 from ProximityPrize.SubmissionLower.B0
open private u7 zA Ep n7 value_mem ur top_mem from ProximityPrize.SubmissionLower.ZxlLGHd
open private cU fall_bound vT ajh Nm bG5 eer aEI fastFall fastFall_eq from ProximityPrize.SubmissionLower.ZLkly3d
structure Block where
  n:ℕ
  k :ℕ
  i:ℕ
  len:ℕ
  zs :ℕ
private abbrev cap (n:ℕ) :=(56 - n)/2
def unpack (q:ℕ) :ℕ→ℕ→List Block
  | 0,_=>[]
  | groups+1,code =>
    let n:=code % 32
    let k :=cap n+q-(n+(code >>> 5)%16)
    let len:=(code >>> 13)%16+1
    let zs :=code >>> 17
    let bits :=31*len
    ⟨n,k,(code >>> 9)%16,len,zs % (2^bits)⟩ :: unpack q groups (zs >>> bits)
private def wK (t u n:ℕ) :ℕ→ℕ→ℕ→ℕ
  | 0,_,_=>0
  | len+1,i,zs =>
    if i≤t then (zs % 0x80000000)*fastFall t i*fastFall (t+u-i) (n-i) +
      wK t u n len (i+1) (zs >>> 31)
    else 0
private structure EvalTerm where
  s :ℕ
  u:ℕ
  k :ℕ
  z :ℕ
private def prep (t u:ℕ) :List Block→List EvalTerm
  | []=>[]
  | b::bs =>
    let es :=prep t u bs
    if b.n≤t+u then
      if b.k+b.n≤ cap b.n+t then match wK t u b.n b.len b.i b.zs % P1.p with
      | 0=>es
      | z+1=>⟨cap b.n-u,t+u-b.n,b.k,z+1⟩ :: es
      else es
    else es
private def value (f :ℕ) :List EvalTerm→ℤ
  | []=>0
  | v::vs =>
    let rest:=value f vs
    if f+v.k≤v.s+v.u then (v.z :ℤ)*bG5 (v.s-f) v.u v.k+rest else rest
def dM (q cut n code :ℕ) :Prop :=
  (unpack q n code).all
    (fun b=>decide (b.i+b.len≤b.n+1∧2*b.n+(b.i+b.len-1)+b.k<cut))=true
def Head (q a f n code :ℕ) :Prop :=
  value f (prep q a (unpack q n code)) % (P1.p:ℤ)=1
private def start (q a f t u:ℕ) :ℕ :=
  if t<q then 0 else f+(if u<a then 0 else 1)
private def extent:List EvalTerm→ℕ
  | []=>0
  | v::vs=>max (v.s+v.u+1-v.k) (extent vs)
private theorem gK3 {k :ℕ} {vs :List EvalTerm}
    (h:extent vs≤k) :value k vs=0:= by
  induction vs with
  | nil=>rfl
  | cons v vs ih =>
    have h' := max_le_iff.mp h
    rw [value,ite_eq_right (by omega),ih h'.2]
private def lineTest (q a f t u:ℕ) (bs :List Block) :Bool :=
  let lo:=start q a f t u
  let vs :=prep t u bs
  (List.range (min ((56-t-3*u)/2+1) (extent vs)-lo)).all
    (fun j=>value (lo+j) vs % (P1.p:ℤ) == 0)
def aT (q a f n code t u:ℕ) :Prop :=
  lineTest q a f t u (unpack q n code)=true
def lK (q a f n code t:ℕ) :Prop :=
  (List.range (min 16 ((56-t)/3)+1)).all (lineTest q a f t · (unpack q n code))=true
theorem plane_of_lines {q a f n code t:ℕ}
    (h : ∀ u≤ min 16 ((56-t)/3),aT q a f n code t u) :lK q a f n code t :=
  List.all_eq_true.mpr fun u hu=>h u (Nat.le_of_lt_succ (List.mem_range.mp hu))
private theorem line_sound {q a f n code t u k :ℕ}
    (h:aT q a f n code t u) (hk :start q a f t u≤k)
    (hdom:3*u+2*k+t≤56) :value k (prep t u (unpack q n code)) % (P1.p:ℤ)=0:= by
  by_cases he :extent (prep t u (unpack q n code))≤k
  · rw [gK3 he,Int.zero_emod]
  · unfold aT lineTest at h
    have hi:k-start q a f t u <
        min ((56-t-3*u)/2+1) (extent (prep t u (unpack q n code)))-start q a f t u:= by omega
    have hm:=beq_iff_eq.mp (List.all_eq_true.mp h _ (List.mem_range.mpr hi))
    rwa [Nat.add_sub_of_le hk] at hm
noncomputable section
private def gap:Interpolant:=C 56 - u7
private def ampPoly (n:ℕ) :ℕ→ℕ→ℕ→ Interpolant
  | 0,_,_=>0
  | len+1,i,zs =>
    C ((zs % 0x80000000:ℕ) :Ground)*cU i gap *
      cU (n-i) (n7 56 - C (i:Ground))+ampPoly n len (i+1) (zs >>> 31)
private def poly (b:Block) :Interpolant :=
  ampPoly b.n b.len b.i b.zs *
    sO (C (↑(cap b.n+b.n) :Ground) - B)
      (C ((cap b.n:Ground)-b.n) - ur 56) b.k
private def aV:List Block→ Interpolant
  | []=>0
  | b::bs=>poly b+aV bs
private theorem amp_bound {n k cut len i zs :ℕ}
    (hi:i+len≤n+1) (hd:2*n+(i+len-1)+k<cut) :
    ampPoly n len i zs∈Bounded (cut-1-k) := by
  induction len generalizing i zs with
  | zero=>exact Submodule.zero_mem _
  | succ len ih =>
    have hh:=(Bounded 3).sub_mem (GN.const_mem 3 (56:Ground)) zA
    have hz :=(Bounded 2).sub_mem (value_mem 56) (GN.const_mem _ (i:Ground))
    apply (Bounded _).add_mem _ (ih (by omega) (by omega))
    exact restrictWeightedDegree_mono _ (by omega)
      (mul_bounded (mul_bounded (GN.const_mem 0 ((zs % 0x80000000:ℕ) :Ground)) (fall_bound hh i))
        (fall_bound hz (n-i)))
private theorem btT {cut:ℕ} (b:Block)
    (hi:b.i+b.len≤b.n+1) (hd:2*b.n+(b.i+b.len-1)+b.k<cut) :
    poly b∈Bounded (cut-1) := by
  have hA:=(Bounded 1).sub_mem (GN.const_mem 1 (↑(cap b.n+b.n) :Ground)) lU.1
  have hH :=(Bounded 2).sub_mem (GN.const_mem 2 ((cap b.n:Ground)-b.n)) (top_mem 56)
  simpa only [poly,Nat.sub_add_cancel (show b.k≤ cut-1 by omega)] using
    mul_bounded (amp_bound hi hd) (B0 hA hH b.k)
private theorem aaH {cut:ℕ} (bs :List Block)
    (h : ∀ b∈bs,b.i+b.len≤b.n+1∧2*b.n+(b.i+b.len-1)+b.k<cut) :
    aV bs∈Bounded (cut-1) := by
  induction bs with
  | nil=>exact Submodule.zero_mem _
  | cons b bs ih =>
    have hb:=h b List.mem_cons_self
    exact (Bounded _).add_mem (btT b hb.1 hb.2)
      (ih fun u hu=>h u (List.mem_cons_of_mem _ hu))
private theorem amp_eval (e :aY) {t a :ℕ}
    (hgap:b9 e.val gap=(t:Ground))
    (hZ:b9 e.val (n7 56)=((t+a :ℕ) :Ground))
    (n len i zs :ℕ) :
    b9 e.val (ampPoly n len i zs)=(wK t a n len i zs :Ground) := by
  induction len generalizing i zs with
  | zero=>simp [ampPoly,wK]
  | succ len ih =>
    simp only [ampPoly,map_add,map_mul,map_sub,mC,Nm,hgap,hZ,ih]
    rw [wK]
    by_cases hi:i≤t
    · simp only [ite_eq_left hi,fastFall_eq,Nat.cast_add,Nat.cast_mul,ajh,
        Nat.cast_sub (by omega :i≤t+a)]
    · rw [ite_eq_right hi,vT (Nat.lt_of_not_ge hi),mul_zero,zero_mul,zero_add]
      have hz :wK t a n len (i+1) (zs >>> 31)=0:= by
        cases len with
        | zero=>rfl
        | succ len=>rw [wK,ite_eq_right (by omega : ¬i+1≤t)]
      rw [hz,Nat.cast_zero]
private theorem amp_zero {t u n len i zs :ℕ} (hn:t+u<n) :
    wK t u n len i zs=0:= by
  induction len generalizing i zs with
  | zero=>rfl
  | succ len ih =>
    rw [wK]
    split
    · rename_i hi
      rw [fastFall_eq (t+u-i),Nat.descFactorial_eq_zero_iff_lt.mpr (by omega :t+u-i<n-i),mul_zero,
        zero_add,ih]
    · rfl
private theorem ccd (e :aY) (he :ord e.val≤56) (b:Block) (bs :List Block) :
    b9 e.val (poly b)+(value (e.val 3) (prep (56-ord e.val) (e.val 0) bs) :Ground) =
      (value (e.val 3) (prep (56-ord e.val) (e.val 0) (b::bs)) :Ground) := by
  let t:=56-ord e.val
  let a :=e.val 0
  let f :=e.val 3
  have hsum:t+ord e.val=56:= by dsimp only [t]; omega
  have hgap:b9 e.val gap=(t:Ground) := by
    rw [gap,map_sub,mC,Ep,Nat.cast_sub he,Nat.cast_ofNat]
  have hZ:b9 e.val (n7 56)=((t+a :ℕ) :Ground) := by
    have hd:=e.property
    rw [cF] at hd
    have h1 :=congrArg (fun x :ℕ=>(x :Ground)) hd
    have h2 :=congrArg (fun x :ℕ=>(x :Ground)) hsum
    simp only [ord] at h2
    push_cast at h1 h2
    simp [n7,B,C₂,a,Nat.cast_add]
    linear_combination 2*h1 - h2
  change b9 e.val (poly b)+_=(value f (prep t a (b::bs)) :Ground)
  rw [poly,map_mul,amp_eval e hgap hZ,prep]
  by_cases h:b.n≤t+a
  · rw [ite_eq_left h]
    let s :=cap b.n-a-f
    let u:=t+a-b.n
    have hcap:a+f≤ cap b.n:= by
      have h0:ord e.val=3*a+e.val 2+2*f :=rfl
      unfold cap
      omega
    have hb:t+2*a+f=e.val 1 := by
      have hd:=e.property
      rw [cF] at hd
      have h0:ord e.val=3*a+e.val 2+2*f :=rfl
      dsimp only [a,f] at h0 ⊢
      omega
    have hTop:b9 e.val (ur 56)=(f :Ground) - t:= by
      have ht:=congrArg (fun x :ℕ=>(x :Ground)) hsum
      rw [Nat.cast_add,← Ep e] at ht
      simp [ur,u7,B,C₂,F,f] at ht ⊢
      linear_combination ht
    have hA:b9 e.val (C (↑(cap b.n+b.n) :Ground)-B)=(s :Ground)-u:= by
      simp only [map_sub,mC,B,BD]
      change (↑(cap b.n+b.n) :Ground)-(e.val 1 :Ground)= _
      rw [← hb]
      dsimp only [s,u]
      rw [Nat.sub_sub,Nat.cast_sub hcap,Nat.cast_sub h]
      push_cast
      ring
    have hH :b9 e.val (C ((cap b.n:Ground)-b.n)-ur 56)=(s :Ground)+u:= by
      rw [map_sub,mC,hTop]
      dsimp only [s,u]
      rw [Nat.sub_sub,Nat.cast_sub hcap,Nat.cast_sub h]
      push_cast
      ring
    rw [y4 _ _ _ s u hA hH]
    by_cases hline :b.k+b.n≤ cap b.n+t
    · rw [ite_eq_left hline]
      generalize hz :wK t a b.n b.len b.i b.zs % P1.p=z
      have hz' : (wK t a b.n b.len b.i b.zs :Ground)=(z :Ground) := by
        rw [← hz,ZMod.natCast_mod]
      rw [hz']
      cases z with
      | zero=>rw [Nat.cast_zero,zero_mul,zero_add]
      | succ z =>
        rw [value]
        by_cases hk :b.k≤ s+u
        · have hk' : f+b.k≤ cap b.n-a+u:= by omega
          rw [ite_eq_left hk',Int.cast_add,Int.cast_mul,Int.cast_natCast,eer _ _ _ hk]
        · have hk' : ¬ f+b.k≤ cap b.n-a+u:= by omega
          rw [ite_eq_right hk',aEI (Nat.lt_of_not_ge hk),mul_zero,zero_add]
    · rw [ite_eq_right hline,aEI (show s+u<b.k by omega),mul_zero,zero_add]
  · rw [ite_eq_right h,amp_zero (Nat.lt_of_not_ge h),Nat.cast_zero,zero_mul,zero_add]
private theorem W6 (e :aY) (he :ord e.val≤56) (bs :List Block) :
    b9 e.val (aV bs)=(value (e.val 3) (prep (56-ord e.val) (e.val 0) bs) :Ground) := by
  induction bs with
  | nil=>simp [aV,prep,value]
  | cons b bs ih=>rw [aV,map_add,ih,ccd e he]
end
end qDoysbd
