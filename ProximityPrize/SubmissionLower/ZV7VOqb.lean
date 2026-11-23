import ProximityPrize.SubmissionLower.AT
import ProximityPrize.SubmissionLower.ZxlLGHd
set_option Elab.async false
set_option autoImplicit true
namespace qEofLDb
open qHde8fc qhonTAe MvPolynomial
open GN (Interpolant ord b9 mC BD)
open fP (cF)
open private B C₂ F lU sO B0 y4 GN.const_mem mul_bounded from ProximityPrize.SubmissionLower.B0
open private u7 zA Ep n7 value_mem ur top_mem from ProximityPrize.SubmissionLower.ZxlLGHd
open private cU vT fall_bound from ProximityPrize.SubmissionLower.C0
open private ajh Nm from ProximityPrize.SubmissionLower.BU
open private aEI from ProximityPrize.SubmissionLower.BW
open private nY from ProximityPrize.SubmissionLower.C0
open private fVl from ProximityPrize.SubmissionLower.AT
noncomputable section
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
structure Term where
  n:ℕ
  i:ℕ
  k :ℕ
  c:ℕ
  q:ℤ
def cap (n:ℕ) :ℕ:=(56 - n)/2
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
private def denom (b:Term) :Ground :=
  (b.i.factorial:Ground)*((b.n-b.i).factorial:Ground)*(b.k.factorial:Ground)
private theorem denom_ne (b:Term) (h:2*b.n+b.i+b.k≤56) :denom b≠0 :=
  mul_ne_zero (mul_ne_zero (factorial_ne_zero (by omega)) (factorial_ne_zero (by omega)))
    (factorial_ne_zero (by omega))
private def poly (b:Term) :Interpolant :=
  C ((b.q:Ground)*(denom b)⁻¹)*cU b.i CK *
    cU (b.n - b.i) (n7 56 - C (b.i:Ground)) *
    sO (C (↑(b.c+b.n) :Ground) - B)
      (C ((b.c:Ground) - b.n) - ur 56) b.k
private theorem btT {d:ℕ} (b:Term) (hb:b.i≤b.n∧2*b.n+b.i+b.k≤d) :
    poly b∈Bounded d:= by
  obtain ⟨hi,hd⟩:=hb
  have hD:CK∈Bounded 3:=(Bounded 3).sub_mem (GN.const_mem _ _) zA
  have hZ:=(Bounded 2).sub_mem (value_mem 56) (GN.const_mem 2 (b.i:Ground))
  have hA:=(Bounded 1).sub_mem (GN.const_mem 1 (↑(b.c+b.n) :Ground)) lU.1
  have hH :=(Bounded 2).sub_mem (GN.const_mem 2 ((b.c:Ground) - b.n)) (top_mem 56)
  exact restrictWeightedDegree_mono _ (by omega) (mul_bounded
    (mul_bounded (mul_bounded (GN.const_mem 0 ((b.q:Ground)*(denom b)⁻¹)) (fall_bound hD _)) (fall_bound hZ _))
    (B0 hA hH _))
private def negOne (n:ℕ) :ℤ:=if n % 2=0 then 1 else -1
private theorem cast_negOne (n:ℕ) : (negOne n:Ground)=(-1 :Ground)^n:= by
  rw [neg_one_pow_eq_pow_mod_two n]
  unfold negOne
  split <;> rename_i h
  · simp [h]
  · have h' : n % 2=1 := by omega
    simp [h']
private def sumN (g:ℕ→ℤ) :ℕ→ℤ
  | 0=>0
  | n+1=>sumN g n+g n
private theorem sumN_cast (g:ℕ→ℤ) (n:ℕ) :
    (sumN g n:Ground) = ∑ i∈Finset.range n,(g i:Ground) := by
  induction n with
  | zero=>simp [sumN]
  | succ n ih=>rw [sumN,Int.cast_add,Finset.sum_range_succ,ih]
private def coeffTop (s u k :ℕ) :ℤ :=
  let j:=s+u - k
  negOne u*sumN (fun i=>(s.fast_choose i:ℤ)*negOne (j-i) *
    (u.fast_choose (j-i) :ℤ)) (j+1)
private theorem coeff_minus (u i:ℕ) :
    (((1-Polynomial.X:Polynomial Ground)^u).coeff i)=(-1 :Ground)^i*(u.choose i:Ground) := by
  rw [show (1-Polynomial.X:Polynomial Ground)=Polynomial.C (-1)*(Polynomial.X+Polynomial.C (-1)) by
    simp; ring,mul_pow,← Polynomial.C_pow,Polynomial.coeff_C_mul,Polynomial.coeff_X_add_C_pow,← mul_assoc]
  by_cases h:i≤u
  · rw [← pow_add]
    congr 1
    rw [neg_one_pow_eq_pow_mod_two (u+(u-i)),neg_one_pow_eq_pow_mod_two i,
      show (u+(u-i)) % 2=i % 2 by omega]
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,mul_zero,mul_zero]
private theorem coeffTop_cast {s u k :ℕ} (hk :k≤ s+u) :
    (coeffTop s u k :Ground) =
      (((1+Polynomial.X)^s*(1-Polynomial.X)^u:Polynomial Ground).coeff k) := by
  rw [fVl s u k hk,coeffTop,Int.cast_mul,cast_negOne,sumN_cast]
  congr 1
  rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Int.cast_mul,cast_negOne,Int.cast_natCast,← Nat.choose_eq_fast_choose,
    Polynomial.coeff_one_add_X_pow,coeff_minus]
  ring
def apA (t a f :ℕ) (b:Term) :ℤ :=
  if b.n≤t+a∧b.i≤t then
    let s :=b.c-(a+f)
    let u:=t+a - b.n
    if b.k≤ s+u then
      b.q*(t.fast_choose b.i:ℤ)*((t+a - b.i).fast_choose (b.n - b.i) :ℤ) *
        coeffTop s u b.k
    else 0
  else 0
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
      have hb:t+2*a+f=v.val 1 := by
        have hd:=v.property
        rw [cF] at hd
        dsimp [t,a,f,ord] at *
        omega
      have hT:b9 v.val (ur 56)=(f :Ground) - t:= by
        have ht:=congrArg (fun i:ℕ=>(i:Ground)) (show t+ord v.val=56 by omega)
        rw [Nat.cast_add,← Ep v] at ht
        simp [ur,u7,B,C₂,F,f] at ht ⊢
        linear_combination ht
      have hA:b9 v.val (C (↑(b.c+b.n) :Ground) - B) =
          (s :Ground) - u:= by
        simp only [map_sub,mC,B,BD]
        change (↑(b.c+b.n) :Ground)-(v.val 1 :Ground)= _
        rw [← hb,Nat.cast_add,Nat.cast_add,Nat.cast_add]
        dsimp only [s,u]
        rw [Nat.cast_sub hcap,Nat.cast_sub hn,Nat.cast_add,Nat.cast_add,Nat.cast_mul]
        ring
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
def Io (t a f :ℕ) :List Term→ℤ
  | []=>0
  | b :: bs=>apA t a f b+Io t a f bs
theorem W6 (v :aY) (hv :ord v.val≤56) (bs :List Term)
    (h : ∀ b∈bs,2*b.n+b.i+b.k≤56∧cap b.n≤b.c) :
    b9 v.val (aV bs)=(Io (56 - ord v.val) (v.val 0) (v.val 3) bs :Ground) := by
  induction bs with
  | nil=>simp [aV,Io]
  | cons b bs ih =>
    simp only [aV,Io,List.map_cons,List.sum_cons,map_add,Int.cast_add]
    have hb:=h b List.mem_cons_self
    rw [ccd v hv b hb.1 hb.2]
    exact congrArg ((apA (56 - ord v.val) (v.val 0) (v.val 3) b:Ground) + ·)
      (ih fun y hy=>h y (List.mem_cons_of_mem _ hy))
theorem aS3 (t a f strip:ℕ) (hbudget:3*a+2*f≤56 - t)
    (ht:t≤56) (hcut:t+strip<f+8) (bs :List Term)
    (hb : ∀ b∈bs,b.c+8≤ strip+b.n+b.k∧cap b.n≤b.c) :Io t a f bs=0:= by
  have hz (b:Term) (h:b.c+8≤ strip+b.n+b.k∧cap b.n≤b.c) :
      apA t a f b=0:= by
    unfold apA
    split
    · next hn =>
      have hcap:a+f≤b.c:= by
        have hh:=h.2
        unfold cap at hh
        omega
      rw [ite_eq_right (show ¬ b.k≤b.c-(a+f)+(t+a - b.n) by omega)]
    · rfl
  induction bs with
  | nil=>rfl
  | cons b bs ih =>
    change apA t a f b+Io t a f bs=0
    rw [hz b (hb _ List.mem_cons_self),ih fun u hu=>hb u (List.mem_cons_of_mem _ hu),zero_add]
end
end qEofLDb
