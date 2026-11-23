import ProximityPrize.SubmissionLower.ZLcmX9d
import ProximityPrize.SubmissionLower.Z3wMysc
import ProximityPrize.SubmissionLower.ZnMb5gd
import ProximityPrize.SubmissionLower.ZUCbske
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
section
set_option autoImplicit true
namespace qDkTmWc
open P6_6_2 qwbsesc
open xE (gd U1 denominator oldCount)
open aAZ (anW bwI Jc)
open private clipped_sum from ProximityPrize.SubmissionLower.ZeuEwuc
open private df6 from ProximityPrize.SubmissionLower.Z0rImdc
open Finset
open scoped BigOperators
local notation "D" => denominator
private theorem cum_den (u:ℤ) (hu:u≤1710) :gd 1710 u=D u :=
  (anW _ _ (by decide) (by omega)).trans (bwI _ _ hu)
private theorem cap_den (u:ℤ) (hu:u≤1710) :U1 1710 u 570=D u :=
  (bCi _ _ hu).trans (cum_den u hu)
private theorem den_mono {u v :ℤ} (h:u≤v) (hv :v≤1710) :D u≤D v := by
  rw [← cum_den u (h.trans hv),← cum_den v hv]
  exact GI.anX _ h
private theorem degree_eq {q:ℕ} (hl:1710≤q) (hh:q<2150) :
    iO q=1710 := by
  unfold iO P6_6.Dj
  rw [ite_eq_left (by omega),min_eq_right hl,min_eq_right hl]
private theorem ng (t j:ℤ) (ht:t<860) (h0:0≤j) (hj:j<t) :
    latticeAllowance ⟨1710,j+1,1710,570,1711-t+j⟩=D j - D (4*j-3*t) := by
  let x :ℤ:=1710-(1711-t+j+2)/3+1
  let z :ℤ:=3*(min 570 (t-j-1)+1)
  have hx :j<x := by dsimp [x]; omega
  have hz :0≤z := by dsimp [z]; omega
  simp only [latticeAllowance,min_self,show (1710 :ℤ)/2=855 by decide,
    show min (1710 :ℤ) 855=855 by decide,show min (570:ℤ) 1710=570 by decide,
    show max 0 ((1711-t+j-1710+1)/2)=0 by omega,
    show (1710 :ℤ)-(1711-t+j)=t-j-1 by omega,
    max_eq_right (by omega :0≤ min (570:ℤ) (t-j-1)+1),
    show max (0:ℤ) (855 - 0+1)=856 by decide,
    show 2*(856:ℤ)=1712 by decide,add_sub_cancel_right]
  rw [show max 0 (1710-(1711-t+j+2)/3+1)=x from max_eq_right (by omega)]
  change D j - D (j-x) - D (j-1712) - D (j-z) +
    D (j-x-1712)+D (j-x-z)+D (j-1712-z) - D (j-x-1712-z)= _
  simp only [Jc (j-x) (by omega),Jc (j-1712) (by omega),
    Jc (j-x-1712) (by omega),Jc (j-x-z) (by omega),
    Jc (j-1712-z) (by omega),Jc (j-x-1712-z) (by omega),
    sub_zero,add_zero]
  by_cases h:t-j-1≤570
  · rw [show j-z=4*j-3*t by dsimp [z]; rw [min_eq_right h]; ring]
  · rw [Jc (j-z) (by dsimp [z]; omega),
      Jc (4*j-3*t) (by omega)]
private def base (q r :ℕ) :ℤ:=D (min 1710 (4709-(q:ℤ) - r)) - D (1709-(r :ℤ))
private def pad (q r :ℕ) :ℤ :=
  if r<3000-q then 0 else D (1709-(r :ℤ)) - D (4*(1709-(r :ℤ))-3*((q-1290:ℕ) :ℤ))
private theorem base_nonneg (q r :ℕ) (hh:q<2150) :0≤base q r :=
  sub_nonneg.mpr (den_mono (le_min (by omega) (by omega)) (min_le_left _ _))
private theorem pad_nonneg (q r :ℕ) :0≤pad q r := by
  unfold pad
  split
  · exact le_rfl
  · exact sub_nonneg.mpr (den_mono (by omega) (by omega))
private theorem bBL {q:ℕ} (hl:1710≤q) (hh:q<2150) (r :Offset)
    (p:Fin 11→ℕ) :xR q r p≤(base q r.val+pad q r.val).toNat := by
  let j:ℤ:=1709-(r.val :ℤ)
  let t:ℤ:=((q-1290:ℕ) :ℤ)
  let o:ℤ:=4710-(q:ℤ) - r.val
  have hf :pT q r=⟨1710,j+1,1710,570,o⟩:= by
    rw [b3v,degree_eq hl hh]
    congr 1
    dsimp [j]
    ring
  have ho:oldCount (pT q r)=D 1710 - D j:= by
    rw [hf,oldCount]
    dsimp only
    rw [add_sub_cancel_right,min_eq_right (by dsimp [j]; omega),cap_den _ (by decide),
      cap_den _ (by dsimp [j]; omega)]
  have hv :base q r.val=D (min 1710 (o-1)) - D j:= by
    unfold base
    rw [show 4709-(q:ℤ) - r.val=o - 1 by dsimp [o]; ring]
  rw [hv]
  by_cases hea :r.val<3000-q
  · rw [pad,ite_eq_left hea,add_zero,min_eq_left (by dsimp [o]; omega),← ho]
    exact block_le_old q r p
  have hp:pad q r.val=D j - D (4*j-3*t) :=ite_eq_right hea
  rw [hp]
  refine (min_le_right _ _).trans ?_
  rw [hf,oppositeBound]
  dsimp only
  by_cases h0:o≤0
  · rw [ite_eq_left h0]; exact Nat.zero_le _
  rw [ite_eq_right h0,cap_den _ (min_le_left _ _)]
  by_cases hj:j+1≤0
  · rw [ite_eq_left hj,Jc j (by omega),Jc (4*j-3*t)
      (by dsimp [t]; omega),sub_zero,sub_zero,add_zero]
  rw [ite_eq_right hj,cap_den _ (by decide)]
  apply Int.toNat_le_toNat
  have ht:t<860:= by dsimp [t]; omega
  have h0j:0≤j:= by omega
  have hjt:j<t:= by dsimp [j,t]; omega
  have hot:o=1711-t+j:= by dsimp [o,t,j]; omega
  rw [← hf,ho,hf,hot,ng t j ht h0j hjt,← hot]
  linarith only [min_le_left (D j - D (4*j-3*t)) (D 1710 - D (min 1710 (o-1)))]
def Fy (t:ℕ) :ℤ := ∑ i∈range t,D ((t:ℤ)-4*((i:ℤ)+1))
def row (t:ℕ) :ℤ :=
  (1710-(t:ℤ))*D 1710+(∑ i∈range t,D i)-Fy t
private theorem sum_base (q:ℕ) (hh:q<2150) :
    (∑ r∈range 4710,base q r)=(3000-(q:ℤ))*D 1710 := by
  unfold base
  rw [sum_sub_distrib]
  have h1 (r :ℕ) :D (min 1710 (4709-(q:ℤ) - r)) =
      gd 1710 (min 1710 (4709-(q:ℤ) - r)) :=
    (cum_den _ (min_le_left _ _)).symm
  have h2 (r :ℕ) :D (1709-(r :ℤ))=gd 1710 (1709-(r :ℤ)) :=
    (cum_den _ (by omega)).symm
  simp_rw [h1,h2]
  have hclip:=clipped_sum 1710 (4709-q) 4710 (by omega) (by omega)
  have href :=df6 1710 1709 4710 (by decide)
  norm_num only [Nat.cast_ofNat] at hclip href
  rw [show (4709:ℤ) - q=((4709-q:ℕ) :ℤ) by omega,hclip,href,
    add_sub_cancel_left,cum_den _ (by decide),
    show ((4709 - q+1 - 1710 :ℕ) :ℤ)=3000-(q:ℤ) by omega]
private theorem sum_pad (q:ℕ) (hl:1710≤q) (hh:q<2150) :
    (∑ r∈range 4710,pad q r)=(∑ i∈range (q-1290),D i)-Fy (q-1290) := by
  let a :=3000-q
  let t:=q-1290
  let f (i:ℕ) :ℤ:=D ((t:ℤ)-1-i) - D ((t:ℤ)-4*((i:ℤ)+1))
  rw [show (4710 :ℕ)=a+(4710-a) by dsimp [a]; omega,sum_range_add]
  have hz : (∑ r∈range a,pad q r)=0 :=
    sum_eq_zero fun r hr=>ite_eq_left (mem_range.mp hr)
  rw [hz,zero_add]
  have he (i:ℕ) :pad q (a+i)=f i:= by
    rw [pad,ite_eq_right (by dsimp [a]; omega)]
    have h:1709-((a+i:ℕ) :ℤ)=(t:ℤ)-1-i:= by dsimp [t,a]; omega
    rw [h]
    change D ((t:ℤ)-1-i) - D (4*((t:ℤ)-1-i)-3*(t:ℤ))=f i
    rw [show 4*((t:ℤ)-1-i)-3*(t:ℤ)=(t:ℤ)-4*((i:ℤ)+1) by ring]
  simp_rw [he]
  have htrim: (∑ i∈range t,f i) = ∑ i∈range (4710-a),f i:= by
    apply sum_subset (range_mono (by dsimp [a,t]; omega))
    intro i _ hi
    have hh:=Nat.le_of_not_gt (fun h:i<t=>hi (mem_range.mpr h))
    simp only [f,Jc ((t:ℤ)-1-i) (by omega),
      Jc ((t:ℤ)-4*((i:ℤ)+1)) (by omega),sub_zero]
  rw [← htrim]
  change (∑ i∈range t,(D ((t:ℤ)-1-i) - D ((t:ℤ)-4*((i:ℤ)+1)))) =
    (∑ i∈range t,D i) - ∑ i∈range t,D ((t:ℤ)-4*((i:ℤ)+1))
  rw [sum_sub_distrib]
  refine congrArg (fun x=>x - ∑ i∈range t,D ((t:ℤ)-4*((i:ℤ)+1))) ?_
  rw [← sum_range_reflect (fun i=>D (i:ℤ)) t]
  refine sum_congr rfl fun i hi=>congrArg D ?_
  have h:=mem_range.mp hi
  omega
theorem aH4 {q:ℕ} (hl:1710≤q) (hh:q<2150) (p:Offset→Fin 11→ℕ) :
    (al2 q p:ℤ)≤ row (q-1290) := by
  have h: (al2 q p:ℤ) ≤ ∑ r :Offset,(base q r.val+pad q r.val) := by
    rw [al2,Nat.cast_sum]
    refine sum_le_sum fun r _ => ?_
    have hb:=Int.ofNat_le.mpr (bBL hl hh r (p r))
    rwa [Int.toNat_of_nonneg (add_nonneg (base_nonneg q r.val hh) (pad_nonneg q r.val))] at hb
  refine h.trans_eq ?_
  change (∑ r :Fin 4710,(base q r.val+pad q r.val))= _
  rw [Fin.sum_univ_eq_sum_range (fun r=>base q r+pad q r),sum_add_distrib,
    sum_base q hh,sum_pad q hl hh,row,
    show (3000:ℤ) - q=1710-((q-1290:ℕ) :ℤ) by omega]
  ring
end qDkTmWc
end
section
set_option autoImplicit true
namespace qDkTmWc
open xE (denominator)
open aRR (DW b0n afw)
open private b0m c5h from ProximityPrize.SubmissionLower.BH
open private antiderivative sum_six from ProximityPrize.SubmissionLower.ZF5THYd
open Finset
open scoped BigOperators
private def stridePrefix (n:ℕ) :ℤ :=
  ∑ i∈range n,DW ((n:ℤ)-4*((i:ℤ)+1))
private theorem stride_step (n:ℕ) :stridePrefix (n+1)=stridePrefix n+24*Fy n:= by
  unfold stridePrefix Fy
  rw [sum_range_succ,afw _ (by omega),add_zero,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have h:=b0m ((n:ℤ)-4*((i:ℤ)+1))
  rw [show (n:ℤ)-4*((i:ℤ)+1)+1=((n+1 :ℕ) :ℤ)-4*((i:ℤ)+1) by omega] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
private theorem stride_prefix (n:ℕ) :24*(∑ t∈range n,Fy t)=stridePrefix n:= by
  induction n with
  | zero=>simp [stridePrefix]
  | succ n ih=>rw [sum_range_succ,mul_add,ih,stride_step]
private theorem stride_mul (n:ℕ) :
    stridePrefix (4*n) = ∑ i∈range n,DW (4*(i:ℤ)) := by
  unfold stridePrefix
  have ht :
      (∑ i∈range n,DW (((4*n:ℕ) :ℤ)-4*((i:ℤ)+1))) =
      ∑ i∈range (4*n),DW (((4*n:ℕ) :ℤ)-4*((i:ℤ)+1)) := by
    apply sum_subset (range_mono (by omega))
    intro i _ hi
    have h:n≤ i:= by simpa only [mem_range,not_lt] using hi
    exact afw _ (by omega)
  rw [← ht,← sum_range_reflect (fun i=>DW (4*(i:ℤ))) n]
  refine sum_congr rfl fun i hi=>congrArg DW ?_
  have h:=mem_range.mp hi
  omega
private def trend (n:ℕ) :ℤ:=(n:ℤ)*(3421-n)*denominator 1710
private theorem trend_sum (n:ℕ) :
    2*(∑ t∈range n,(1710-(t:ℤ))*denominator 1710)=trend n:= by
  induction n with
  | zero=>simp [trend]
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih]
    simp only [trend,Nat.cast_succ]
    ring
private theorem row_prefix (n:ℕ) :
    24*(∑ t∈range n,row t) =
    12*trend n+(∑ t∈range n,DW t) - stridePrefix n:= by
  have hp (t:ℕ) :24*(∑ i∈range t,denominator i)=DW t:= by
    simpa only [zero_add,afw 0 le_rfl,sub_zero] using b0n 0 t
  have h:24*(∑ t∈range n,∑ i∈range t,denominator i) = ∑ t∈range n,DW t:= by
    rw [mul_sum]
    exact sum_congr rfl fun t _=>hp t
  have ht:24*(∑ t∈range n,(1710-(t:ℤ))*denominator 1710)=12*trend n:= by
    rw [show (24 :ℤ)=12*2 by decide,mul_assoc,trend_sum]
  simp only [row,sum_add_distrib,sum_sub_distrib,mul_add,mul_sub,ht,h,stride_prefix]
private def poly (s r :ℕ) (k :ℤ) :ℤ :=
  c5h (70+(s*(r :ℤ))/6+s*k) ((s*(r :ℤ))%6)
private def dO (s r m:ℕ) :ℤ:=antiderivative (poly s r) m
private theorem sum_poly (s r m:ℕ) :
    120*(∑ k∈range m,poly s r k)=dO s r m:= by
  induction m with
  | zero=>simp [dO,antiderivative]
  | succ m ih =>
    rw [sum_range_succ,mul_add,ih]
    simp only [dO,Nat.cast_succ]
    unfold antiderivative poly c5h
    ring
private theorem prefix_affine (s r k :ℕ) :
    DW (420+s*((6*k+r :ℕ) :ℤ))=poly s r k := by
  have h: (420:ℤ)+s*((6*k+r :ℕ) :ℤ)=420+s*(r :ℤ)+6*(s*(k :ℤ)) := by
    push_cast
    ring
  rw [DW,ite_eq_right (not_lt_of_ge (by positivity)),h,poly]
  rw [show ((420:ℤ)+s*(r :ℤ)+6*(s*(k :ℤ)))/6 =
      70+(s*(r :ℤ))/6+s*k by omega,
    show ((420:ℤ)+s*(r :ℤ)+6*(s*(k :ℤ)))%6=(s*(r :ℤ))%6 by omega]
private def edge (s r m:ℕ) :ℤ:=120*poly s r m
private theorem crM (s m:ℕ) :
    120*(∑ k∈range (6*m+2),DW (420+s*(k :ℤ))) =
      (∑ r :Fin 6,dO s r.val m)+edge s 0 m+edge s 1 m:= by
  rw [sum_range_add,sum_six,mul_add,mul_sum]
  simp_rw [prefix_affine,sum_poly]
  rw [sum_range_succ,sum_range_one,mul_add,← add_assoc] <;> rfl
local notation "v![" f "," s "," r "," m "," n "]" => (rfl :f s r m=n)
private theorem prefix_one :
    120*(∑ k∈range 440,DW (420+(k :ℤ)))=0x6976ad17e8cc0:= by
  have h:=crM 1 73
  simp only [Nat.cast_one,one_mul,Fin.sum_univ_succ,Fin.val_succ,Fin.val_zero,
    Fin.sum_univ_zero,add_zero] at h
  rw [v![dO,1,0,73,0x111fe68fa3c40],v![dO,1,1,73,0x1138bb6c3d240],
    v![dO,1,2,73,0x1151ac0f96780],v![dO,1,3,73,0x116ab88f23dc0],
    v![dO,1,4,73,0x1183e100596c0],v![dO,1,5,73,0x119d2578ab440],
    v![edge,1,0,73,0x9ff0bb78e00],v![edge,1,1,73,0xa0af48d0000]] at h
  exact h
private theorem bt1 :
    120*(∑ k∈range 110,DW (420+4*(k :ℤ)))=0x1a24d51c67680:= by
  have h:=crM 4 18
  simp only [Nat.cast_ofNat,Fin.sum_univ_succ,Fin.val_succ,Fin.val_zero,
    Fin.sum_univ_zero,add_zero] at h
  rw [v![dO,4,0,18,0x3eb768114500],v![dO,4,1,18,0x402c63037800],
    v![dO,4,2,18,0x41a806364a80],v![dO,4,3,18,0x432a6686ac80],
    v![dO,4,4,18,0x44b398f39180],v![dO,4,5,18,0x4643b29d2600],
    v![edge,4,0,18,0x9b8748d4740],v![edge,4,1,18,0x9e759d6c3c0]] at h
  exact h
private theorem range_diff (f :ℕ→ℤ) {a b:ℕ} (h:a≤b) :
    (∑ k∈range b,f k)-(∑ k∈range a,f k) = ∑ k∈range (b-a),f (a+k) := by
  conv_lhs=>rw [← Nat.add_sub_of_le h,sum_range_add]
  rw [add_sub_cancel_left]
theorem total: (∑ k∈range 440,row (420+k))=0x3c4eceda6f99:= by
  have h₁:=row_prefix 860
  have h₂:=row_prefix 420
  have hr :=range_diff row (show 420≤860 by decide)
  have hd:=range_diff (fun t=>DW (t:ℤ)) (show 420≤860 by decide)
  have hs :=range_diff (fun t=>DW (4*(t:ℤ))) (show 105≤215 by decide)
  have htrend:12*(trend 860 - trend 420)=0x59ccff258eda0:=rfl
  have hS:stridePrefix 860 - stridePrefix 420 =
      ∑ k∈range 110,DW (420+4*(k :ℤ)) := by
    rw [show stridePrefix 860= _ from stride_mul 215,show stridePrefix 420= _ from stride_mul 105,hs]
    refine sum_congr rfl fun k _=>congrArg DW ?_
    push_cast
    ring
  have hD: (∑ t∈range 860,DW (t:ℤ))-(∑ t∈range 420,DW (t:ℤ)) =
      ∑ k∈range 440,DW (420+(k :ℤ)) := by
    rw [hd]
    refine sum_congr rfl fun k _=>congrArg DW ?_
    push_cast
    rfl
  have he :
      24*(∑ k∈range 440,row (420+k)) =
      12*(trend 860 - trend 420) +
        ((∑ t∈range 860,DW (t:ℤ))-(∑ t∈range 420,DW (t:ℤ))) -
        (stridePrefix 860 - stridePrefix 420) := by
    rw [← hr]
    linear_combination h₁ - h₂
  rw [htrend,hD,hS] at he
  apply mul_left_cancel₀ (show (2880:ℤ)≠0 by decide)
  calc
    _=120*(24*(∑ k∈range 440,row (420+k))) :=mul_assoc 120 24 _
    _ = _:=congrArg (120 * ·) he
    _=120*0x59ccff258eda0 +
        120*(∑ k∈range 440,DW (420+(k :ℤ))) -
        120*(∑ k∈range 110,DW (420+4*(k :ℤ))) := by rw [mul_sub,mul_add]
    _=120*0x59ccff258eda0+0x6976ad17e8cc0 - 0x1a24d51c67680 :=
      congrArg₂ (fun x y=>120*0x59ccff258eda0 + x - y) prefix_one bt1
    _ = _:=rfl
end qDkTmWc
end
section
set_option autoImplicit true
namespace qDkTmWc
open P6_6_2 qwbsesc Finset
open scoped BigOperators
theorem proof :qwbsesc.c2 := by
  refine ⟨fun _ _ _=>0,Int.ofNat_le.mp ?_⟩
  have h: (rankBand (fun _ _ _=>0) 1710 2150:ℤ) ≤ ∑ q∈Ico 1710 2150,row (q-1290) := by
    rw [rankBand,Nat.cast_sum]
    exact sum_le_sum fun q hq=>aH4 (mem_Ico.mp hq).1 (mem_Ico.mp hq).2 _
  refine h.trans_eq (Eq.trans ?_ total)
  rw [sum_Ico_eq_sum_range]
  exact sum_congr rfl fun k _=>congrArg row (by omega)
end qDkTmWc
end
section
set_option autoImplicit true
namespace qoWrama
open qxuyiwe (Pivot PivotIndex h52 FF)
open fP (Qg)
open scoped BigOperators
noncomputable section
private theorem histogram (g:ℕ) (hg:g<99) :JL g=h52[g]! := by
  interval_cases g <;> rfl
private def groupEquiv (g:Gap) :Group g ≃ Fin h52[g.val] :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    change (∑ i:Fin 57,groupCount g.val i.val)=h52[g.val]
    rw [← Qg,← getElem!_pos h52 g.val g.isLt]
    exact histogram g.val g.isLt)
private def Tg:GroupedPivot ≃ Pivot h52 :=
  Equiv.sigmaCongrRight groupEquiv
def index :PivotIndex h52 := fun j=>(Tg.symm j).2.1
theorem visible_card_le (g w:ℤ) :
    Fintype.card (Visible g w)≤Fintype.card (FF index g w) := by
  let f (x :Visible g w) :FF index g w :=
    ⟨Tg x.val,by
      have hi:index (Tg x.val)=x.val.2.1 := by
        unfold index
        rw [Equiv.symm_apply_apply]
      change ((x.val.1.val :ℤ)+(index (Tg x.val)).val<w) ∧
        -g≤(index (Tg x.val)).val
      rw [hi]
      exact ⟨by simpa only [c37,Nat.cast_add] using x.property.1,x.property.2⟩⟩
  exact Fintype.card_le_of_injective f (fun x y h =>
    Subtype.ext (Tg.injective (congrArg Subtype.val h)))
end
end qoWrama
end
section
set_option autoImplicit true
namespace qoWrama
open qK9H6va (offset)
open qHde8fc (aD)
open qxuyiwe (profileCutoff)
def c1 :Prop :=aGq 52 79
def c2 :Prop :=aGq 80 88
def c3:Prop :=aGq 89 94
def c4 :Prop :=aGq 95 98
def c5:Prop :=aGq 99 102
def c6:Prop :=aGq 103 105
def c7:Prop :=aGq 106 108
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
    (h6:c6) (h7:c7) :qxuyiwe.c2 := by
  have head:aGq 52 (tailCost - 1) := by
    intro e hlo hhi
    let R:=cP (aD e.val)
    change 52≤R at hlo
    change R≤108 at hhi
    by_cases h79:R≤79
    · exact h1 e hlo h79
    by_cases h88:R≤88
    · exact h2 e (by omega) h88
    by_cases h94 :R≤94
    · exact h3 e (by omega) h94
    by_cases h98:R≤98
    · exact h4 e (by omega) h98
    by_cases h102 :R≤102
    · exact h5 e (by omega) h102
    by_cases h105:R≤105
    · exact h6 e (by omega) h105
    · exact h7 e (by omega) hhi
  exact ⟨index,fun q hd r =>
    (rank_le_visible head tailWitness q (offset r) hd).trans
      (visible_card_le (offset r) (profileCutoff q 52 (offset r)))⟩
end qoWrama
end
section
set_option autoImplicit true
namespace qKVdmob
open qHde8fc
open fP (cF)
def ee (r a f :ℕ) :Triple :=
  let c:=r-(56+3*a+2*f)
  (56-(a+c+f),c,f)
def code (r a f :ℕ) :ℕ :=
  ((addressBlock r)[f]?.getD 0 >>> (9*a)) % 512
def oldIndex (r a f :ℕ) :ℕ:=56-a - code r a f % 16
def cutoff (e :aY) :ℕ :=
  oldIndex (cP (aD e.val)) (e.val 0) (e.val 3)+1
theorem nG (e :aY) :
    cP (aD e.val)=56+3*e.val 0+e.val 2+2*e.val 3:= by
  have hd:=e.property
  rw [cF] at hd
  dsimp only [cP,aD]
  omega
theorem bnW (e :aY) :
    ee (cP (aD e.val)) (e.val 0) (e.val 3)=aD e.val := by
  have hd:=e.property
  rw [cF] at hd
  rw [nG e]
  simp only [ee,aD]
  rw [show 56+3*e.val 0+e.val 2+2*e.val 3 -
      (56+3*e.val 0+2*e.val 3)=e.val 2 by omega,
    show 56-(e.val 0+e.val 2+e.val 3)=e.val 1 by omega]
abbrev iG (r c f t j k :ℕ) :Prop :=
  t< r∨t=r∧(k<f∨k=f∧j<c)
abbrev Lr (r cut c f j k :ℕ) :Prop :=
  iG r c f (56+3*(56 - cut)+j+2*k) j k
abbrev b8 (e :aY) (cut j k :ℕ) :Prop :=
  Lr (cP (aD e.val)) cut (e.val 2) (e.val 3) j k
abbrev gP (e :aY) (cut:ℕ) :=
  {m:gU cut // ¬ b8 e cut (m.val 2) (m.val 3)}
def cZ (e :aY) (cut:ℕ) (v :Triple) (m:gP e cut) :Ground :=
  cE cut v m.val
def fG (e :aY) (cut:ℕ) :Prop :=
  cZ e cut (aD e.val) ∈
    Submodule.span Ground (Set.range fun v :iw e =>
      cZ e cut (aD v.val.val))
end qKVdmob
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qxJEhle
open aR (Shape)
open P6_6 (AdmissibleEarly)
local notation "chunk" h "," width "," value=>appendMass h (d:=width) (c:=value) rfl rfl rfl
private abbrev p1 :Shape :=⟨3,8,1⟩
private theorem r1 :mass p1 0 16=0x5cffb41e8bb:=rfl
private theorem r2 :mass p1 0 32=0xa679cb16fcd:=chunk r1,16,0x497a16f8712
private theorem r3:mass p1 0 48=0xdf38a0b5ec2 :=chunk r2,16,0x38bed59eef5
private theorem r4 :mass p1 0 64=0x109e47b09676:=chunk r3,16,0x2aabda537b4
private theorem r5:mass p1 0 80=0x128faac8af0a :=chunk r4,16,0x1f163181894
private theorem r6:mass p1 0 96=0x13ec4d231e5b:=chunk r5,16,0x15ca25a6f51
private theorem r7:mass p1 0 112=0x14d50f8697eb:=chunk r6,16,0xe8c2637990
private theorem r8:mass p1 0 128=0x1566d8bf6939:=chunk r7,16,0x91c938d14e
private theorem r9:mass p1 0 144=0x15ba8200649a :=chunk r8,16,0x53a940fb61
private theorem dz :mass p1 0 160=0x15e4c85987fb:=chunk r9,16,0x2a46592361
private theorem dD:mass p1 0 176=0x15f63e7c9cd9:=chunk dz,16,0x11762314de
private theorem dK:mass p1 0 192=0x15fb3e8454aa :=chunk dD,16,0x50007b7d1
private theorem e8:mass p1 0 208=0x15fbdbbb580b:=chunk dK,16,0x9d370361
private theorem gD:mass p1 0 213=0x15fbdc77b31d:=chunk e8,5,0xbc5b12
theorem boundary1 : ¬ AdmissibleEarly ⟨3,8,1⟩ :=
  exclude gD rfl (by decide) (by decide)
private abbrev p2 :Shape :=⟨25,3,1⟩
private theorem gx :mass p2 0 16=0x5dc818ad1ad:=rfl
private theorem iu:mass p2 0 32=0xa92b3316681 :=chunk gx,16,0x4b631a694d4
private theorem kD:mass p2 0 48=0xe465673e015:=chunk iu,16,0x3b3a3427994
private theorem lH :mass p2 0 64=0x111882300c3e :=chunk kD,16,0x2d22bbc2c29
private theorem kR:mass p2 0 80=0x1327b9eada02 :=chunk lH,16,0x20f37bacdc4
private theorem jV:mass p2 0 96=0x149005dd0937:=chunk kR,16,0x1684bf22f35
private theorem lp:mass p2 0 112=0x156b3ead0c0a :=chunk jV,16,0xdb38d002d3
private theorem kZ:mass p2 0 128=0x15d2aa73700f :=chunk lp,16,0x676bc66405
private theorem lQ:mass p2 0 144=0x15eb07741cbe :=chunk kZ,16,0x185d00acaf
private theorem nJ:mass p2 0 160=0x15ebfb46beba :=chunk lQ,16,0xf3d2a1fc
private theorem nP:mass p2 0 161=0x15ebfb46bebb:=chunk nJ,1,0x1
theorem boundary2 : ¬ AdmissibleEarly ⟨25,3,1⟩ :=
  exclude nP rfl (by decide) (by decide)
end qxJEhle
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qxJEhle
open aR (Shape)
open P6_6 (AdmissibleEarly)
local notation "chunk" h "," width "," value=>appendMass h (d:=width) (c:=value) rfl rfl rfl
private abbrev p3:Shape :=⟨23,4,1⟩
private theorem qA:mass p3 0 16=0x5d131994930:=rfl
private theorem tj:mass p3 0 32=0xa6e03b7a175:=chunk qA,16,0x49cd21e5845
private theorem qH :mass p3 0 48=0xe037c1ea72b:=chunk tj,16,0x395786705b6
private theorem oQ:mass p3 0 64=0x10ba65335c72 :=chunk qH,16,0x2b6e914b547
private theorem xM:mass p3 0 80=0x12b77cae0901 :=chunk oQ,16,0x1fd177aac8f
private theorem xd:mass p3 0 96=0x141ba40badac:=chunk xM,16,0x164275da4ab
private theorem r32 :mass p3 0 112=0x1504115d1c09:=chunk xd,16,0xe86d516e5d
private theorem A4 :mass p3 0 128=0x158a84a0d5c2 :=chunk r32,16,0x867343b9b9
private theorem BY:mass p3 0 144=0x15c631189c9e :=chunk A4,16,0x3bac77c6dc
private theorem Cp:mass p3 0 160=0x15d2f4f36b4d:=chunk BY,16,0xcc3daceaf
private theorem EZ:mass p3 0 175=0x15d351121f12 :=chunk Cp,15,0x5c1eb3c5
theorem boundary3 : ¬ AdmissibleEarly ⟨23,4,1⟩ :=
  exclude EZ rfl (by decide) (by decide)
private abbrev p6:Shape :=⟨11,7,1⟩
private theorem WZ:mass p6 0 16=0x5c5951fabe6:=rfl
private theorem r66:mass p6 0 32=0xa480455e12a :=chunk WZ,16,0x4826f363544
private theorem r67:mass p6 0 48=0xdbd83432376:=chunk r66,16,0x3757eed424c
private theorem r68:mass p6 0 64=0x1056883282c8:=chunk r67,16,0x29904ef5f52
private theorem r69:mass p6 0 80=0x123dee78c200:=chunk r68,16,0x1e766463f38
private theorem r70:mass p6 0 96=0x13991b260aa7:=chunk r69,16,0x15b2cad48a7
private theorem W7:mass p6 0 112=0x148823b13c89:=chunk r70,16,0xef088b31e2
private theorem Vo:mass p6 0 128=0x152601d62dd1 :=chunk W7,16,0x9dde24f148
private theorem r73:mass p6 0 144=0x1588ee563b62 :=chunk Vo,16,0x62ec800d91
private theorem r74 :mass p6 0 160=0x15c2cebd113b:=chunk r73,16,0x39e066d5d9
private theorem r75:mass p6 0 176=0x15e1a48be699:=chunk r74,16,0x1ed5ced55e
private theorem r76:mass p6 0 192=0x15effc9336ca :=chunk r75,16,0xe58075031
private theorem r77:mass p6 0 208=0x15f55e4dde83:=chunk r76,16,0x561baa7b9
private theorem r78:mass p6 0 224=0x15f6bb3c3f21 :=chunk r77,16,0x15cee609e
private theorem r79:mass p6 0 240=0x15f6de3f53f2 :=chunk r78,16,0x230314d1
private theorem Xe :mass p6 0 244=0x15f6de4f6c8b:=chunk r79,4,0x101899
theorem boundary6 : ¬ AdmissibleEarly ⟨11,7,1⟩ :=
  exclude Xe rfl (by decide) (by decide)
end qxJEhle
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qxJEhle
open aR (Shape)
open P6_6 (AdmissibleEarly)
local notation "chunk" h "," width "," value=>appendMass h (d:=width) (c:=value) rfl rfl rfl
private abbrev p4 :Shape :=⟨20,5,1⟩
private theorem Iz :mass p4 0 16=0x5c9c0cb3cae :=rfl
private theorem IB:mass p4 0 32=0xa565a54ed81 :=chunk Iz,16,0x48c9989b0d3
private theorem Ku:mass p4 0 48=0xdd95541e1d6:=chunk IB,16,0x382faecf455
private theorem Hz :mass p4 0 64=0x1080a3fee376:=chunk Ku,16,0x2a74ebd01a0
private theorem ID :mass p4 0 80=0x1274e9cb5e7c:=chunk Hz,16,0x1f445cc7b06
private theorem LU:mass p4 0 96=0x13d9c4123a04 :=chunk ID,16,0x164da46db88
private theorem Vr :mass p4 0 112=0x14ce12ecccef :=chunk LU,16,0xf44eda92eb
private theorem Xv :mass p4 0 128=0x156c422239ab:=chunk Vr,16,0x9e2f356cbc
private theorem Xw:mass p4 0 144=0x15ca9273b208:=chunk Xv,16,0x5e5051785d
private theorem Cw:mass p4 0 160=0x15fb641bd70a :=chunk Xw,16,0x30d1a82502
private theorem Cx :mass p4 0 176=0x160dcc6fd21a :=chunk Cw,16,0x126853fb10
private theorem zB:mass p4 0 192=0x16107d31445f :=chunk Cx,16,0x2b0c17245
private theorem CR:mass p4 0 201=0x1610818581e1 :=chunk zB,9,0x4543d82
theorem boundary4 : ¬ AdmissibleEarly ⟨20,5,1⟩ :=
  exclude CR rfl (by decide) (by decide)
private abbrev p5:Shape :=⟨17,6,1⟩
private theorem Db:mass p5 0 16=0x5c2054d30ef :=rfl
private theorem LB:mass p5 0 32=0xa3c938e1be2 :=chunk Db,16,0x47a8e40eaf3
private theorem De :mass p5 0 48=0xda8845069f1 :=chunk LB,16,0x36bf0c24e0f
private theorem LD:mass p5 0 64=0x1038069996cd:=chunk De,16,0x28f82492cdc
private theorem OD:mass p5 0 80=0x1216f6056029:=chunk LD,16,0x1deef6bc95c
private theorem OK :mass p5 0 96=0x136b32bed9fa :=chunk OD,16,0x1543cb979d1
private theorem LH :mass p5 0 112=0x1454f9ae93fc:=chunk OK,16,0xe9c6efba02
private theorem Vb:mass p5 0 128=0x14ef3da499d9:=chunk LH,16,0x9a43f605dd
private theorem Vc:mass p5 0 144=0x1550072f1120:=chunk Vb,16,0x60c98a7747
private theorem WV:mass p5 0 160=0x1588e93f16d8:=chunk Vc,16,0x38e21005b8
private theorem OL:mass p5 0 176=0x15a780741f90:=chunk WV,16,0x1e973508b8
private theorem OM:mass p5 0 192=0x15b5f32d2b48:=chunk OL,16,0xe72b90bb8
private theorem OP:mass p5 0 208=0x15bb71c53a00:=chunk OM,16,0x57e980eb8
private theorem Vd:mass p5 0 224=0x15bcb8de74c0:=chunk OP,16,0x147193ac0
private theorem r64 :mass p5 0 236=0x15bcc43802e7:=chunk Vd,12,0xb598e27
theorem boundary5 : ¬ AdmissibleEarly ⟨17,6,1⟩ :=
  exclude r64 rfl (by decide) (by decide)
end qxJEhle
end
section
set_option autoImplicit true
namespace q33KzTa
open Finset
open P6_6 (Gq Dj V7)
open wV (HY)
open private bgn eO4 ow from ProximityPrize.SubmissionLower.Zqd3kta
open private bSj.aTY bSj.ay9 total from ProximityPrize.SubmissionLower.E6
open scoped BigOperators
def cV (j t:ℕ) :ℕ:=HY (j+1) j t - HY j j t
private theorem grade_eq_at (j t:ℕ) :cV j t=V7 j j t:= by
  simp only [cV,bSj.aTY,sum_range_succ,Nat.add_sub_cancel_left]
private theorem inert {r j t c:ℕ} (h:j≤ c) :
    V7 (min r c) j t=V7 r j t:= by
  simp only [bSj.ay9,total]
  refine sum_congr rfl fun z hz=>sum_congr rfl fun y hy=>sum_congr rfl fun x hx => ?_
  simp only [mem_range] at hz hy hx
  simp only [le_min_iff,show z+y + x≤ c by omega,and_true]
private theorem saturated {r j t:ℕ} (h:j≤ r) :V7 r j t=cV j t:= by
  rw [grade_eq_at,← inert (r :=r) (c:=j) (t:=t) le_rfl,min_eq_right h]
private theorem grade_enough {q j bound start stop:ℕ} {bs :List (ℕ×ℕ×ℕ)}
    (hc:ow start stop bs) (hq:start≤q) (hs :q<stop) (hb:q<bound)
    (h : ∀ lo hi c,(lo,hi,c)∈bs→c<j→bound≤lo) :
    min q j≤Dj q:= by
  induction bs generalizing start with
  | nil =>
    change start=stop at hc
    omega
  | cons kA tail ih =>
    obtain ⟨lo,hi,c⟩:=kA
    obtain ⟨hstart,_,hcap,htail⟩:=hc
    subst start
    by_cases hhi:q<hi
    · have h' := hcap q 0 (by simpa only [Nat.add_zero]) (by simpa only [Nat.add_zero])
      simp only [Nat.add_zero] at h'
      have hj:j≤ c:= by
        by_contra! hcj
        exact (Nat.not_le_of_gt (hq.trans_lt hb)) (h lo hi c (List.mem_cons_self ..) hcj)
      exact (min_le_min_left q hj).trans (h' ▸ min_le_right q (Dj q))
    · exact ih htail (by omega) fun a b c hm=>h a b c (List.mem_cons_of_mem _ hm)
private theorem cofactor_affine (u x w:ℕ) (hx :x≤1710) (hw:w≤570)
    (hu:u+(1710 - x)≤4025)
    (h : ∀ lo hi c,(lo,hi,c)∈bgn→c<1710 - x→u+(1710 - x)≤lo) :
    Gq ⟨u,x,w⟩+u*cV (1710 - x) (570 - w)=Gq ⟨0,x,w⟩:= by
  let j:=1710 - x
  let t:=570 - w
  let m:=4025 - u - j+1
  let f := fun r=>V7 (min r (Dj r)) j t
  let g:= fun r=>V7 (min r (Dj (r+u))) j t
  change u+j≤4025 at hu
  have hlow (q:ℕ) (hq:q< u+j) :min q j≤Dj q :=
    grade_enough eO4 (Nat.zero_le q) (by omega) hq h
  have hfit :u≤4025∧x≤1710∧w≤570:=⟨by omega,hx,hw⟩
  have hzero :0≤4025∧x≤1710∧w≤570:=⟨Nat.zero_le _,hx,hw⟩
  unfold Gq
  change (if u≤4025∧x≤1710∧w≤570 then ∑ r∈range (4025 - u+1),g r else 0) +
    u*cV j t =
    (if 0≤4025∧x≤1710∧w≤570 then ∑ r∈range (4025+1),f r else 0)
  rw [ite_eq_left hfit,ite_eq_left hzero,show 4025 - u+1=j+m by dsimp [m]; omega,
    show 4025+1=j+u+m by dsimp [m]; omega,sum_range_add g,sum_range_add f,sum_range_add f]
  have hfirst: (∑ r∈range j,g r) = ∑ r∈range j,f r := by
    refine sum_congr rfl fun r hr => ?_
    have hrj:=mem_range.mp hr
    have ha :r≤Dj (r+u) :=(le_min (Nat.le_add_right _ _) hrj.le).trans
      (hlow _ (by omega))
    have hb:r≤Dj r := by simpa only [min_eq_left hrj.le] using hlow r (by omega)
    simp only [f,g,min_eq_left ha,min_eq_left hb]
  have hmid : (∑ r∈range u,f (j+r))=u*cV j t:= by
    calc
      _ = ∑ _∈range u,cV j t:=sum_congr rfl fun r hr=> by
        have hru:=mem_range.mp hr
        have hjr :j≤j+r :=Nat.le_add_right _ _
        have hjc:j≤Dj (j+r) := by
          simpa only [min_eq_right hjr] using hlow (j+r) (by omega)
        exact saturated (le_min hjr hjc)
      _ = _:= by simp
  have hlast : (∑ r∈range m,g (j+r)) = ∑ r∈range m,f (j+u+r) := by
    refine sum_congr rfl fun r _ => ?_
    let cap:=Dj (j+u+r)
    simp only [g,f,show j+r+u=j+u+r by omega]
    change V7 (min (j+r) cap) j t=V7 (min (j+u+r) cap) j t
    by_cases hi:j≤ cap
    · rw [saturated (le_min (by omega :j≤j+r) hi),
        saturated (le_min (by omega :j≤j+u+r) hi)]
    · rw [min_eq_right (by omega :cap≤j+r),min_eq_right (by omega :cap≤j+u+r)]
  rw [hfirst,hmid,hlast]
  ac_rfl
def AffineFits (b j n:ℕ) :Prop :=
  j*n≤1710∧n≤570∧1710+(b - j)*n≤4025 ∧
    bgn.all (fun (lo,_,c)=>decide (1710≤ c ∨
      1710+(b - j)*min n ((1709 - c)/j)≤lo))=true
instance (b j n:ℕ) :Decidable (AffineFits b j n) := by
  unfold AffineFits
  infer_instance
theorem entry_affine {b j n d:ℕ} (hj:0<j) (hf :AffineFits b j n) (hd:d≤n) :
    Gq ⟨d*b,d*j,d⟩+d*b*cV (1710-d*j) (570-d)=Gq ⟨0,d*j,d⟩:= by
  obtain ⟨hindex,htop,hroom,hbands⟩:=hf
  have hi:=(Nat.mul_le_mul_left j hd).trans hindex
  rw [Nat.mul_comm j d] at hi
  have hm (s :ℕ) (hs :d≤ s) :d*b+(1710-d*j)≤1710+(b-j)*s := by
    have hdj:d*b≤d*j+d*(b-j) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega)
    have hds :=Nat.mul_le_mul_left (b-j) hs
    rw [Nat.mul_comm (b-j) d] at hds
    omega
  refine cofactor_affine _ _ _ hi (hd.trans htop) ((hm _ hd).trans hroom) ?_
  intro lo hi' c hc hc'
  have hbound:d≤(1709-c)/j :=
    (Nat.le_div_iff_mul_le hj).2 (by omega)
  have hband:1710≤ c∨1710+(b-j)*min n ((1709-c)/j)≤lo :=
    of_decide_eq_true (List.all_eq_true.mp hbands _ hc)
  exact (hm _ (le_min hd hbound)).trans (hband.resolve_left (by omega))
end q33KzTa
end
