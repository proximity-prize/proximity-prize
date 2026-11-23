import ProximityPrize.SubmissionLower.Z2dBXLe
import ProximityPrize.SubmissionLower.Z0rImdc
set_option Elab.async false
set_option autoImplicit true
namespace qwbsesc
open P6_6_2
open xE (gd U1 oldCount)
open GI (anX)
open private df6 saturated from ProximityPrize.SubmissionLower.Z0rImdc
open Finset
open scoped BigOperators
private theorem cumulative_neg (d u:ℤ) (hu:u<0) :gd d u=0:= by
  simp [gd,hu]
theorem bCi (d u:ℤ) (hu:u≤1710) :
    U1 d u 570=gd d u:= by
  simp only [U1,show ¬ (570:ℤ)<0 by decide,ite_false]
  rw [cumulative_neg (d - 570 - 1) (u-3*(570+1)) (by omega),sub_zero]
private def term (q r :ℕ) :ℤ :=
  gd q (min 1710 (4709-(q:ℤ) - r)) - gd q (1709-(r :ℤ))
private theorem term_nonneg (q r :ℕ) (hq:q≤1290) :0≤term q r :=
  sub_nonneg.mpr (anX q (le_min (by omega) (by omega)))
private theorem degree_eq {q:ℕ} (hq:q≤1290) :iO q=q:= by
  unfold iO P6_6.Dj
  rw [ite_eq_left (by omega),min_eq_left (by omega :q≤1710),min_self]
private theorem bBL (q:ℕ) (r :Offset) (hq:q≤1290) (p:Fin 11→ℕ) :
    xR q r p≤(term q r.val).toNat := by
  by_cases hr :1710≤(4709:ℤ) - q - r.val
  · refine (block_le_old q r p).trans ?_
    rw [b3v,degree_eq hq,oldCount,term,min_eq_left hr]
    dsimp only
    rw [show (1710 :ℤ) - r.val - 1=1709 - r.val by ring,min_eq_right (by omega),
      bCi _ _ (by decide),bCi _ _ (by omega)]
  · unfold xR
    refine (min_le_right _ _).trans ?_
    rw [b3v,degree_eq hq]
    unfold oppositeBound
    dsimp only
    by_cases ho: (4710 :ℤ) - q - r.val≤0
    · rw [ite_eq_left ho]
      exact Nat.zero_le _
    · rw [ite_eq_right ho,ite_eq_left (by omega : (1710 :ℤ) - r.val≤0)]
      rw [term,cumulative_neg _ (1709-(r.val :ℤ)) (by omega),sub_zero,
        show (4710 :ℤ) - q - r.val - 1=4709 - q - r.val by ring,
        bCi _ _ (min_le_left _ _)]
private theorem clipped_sum (q a n:ℕ) (ha :a<n) (hj:1710≤a+1) :
    (∑ r∈range n,gd q (min 1710 ((a :ℤ) - r))) =
      (∑ r∈range 1710,gd q r) +
        ((a+1 - 1710 :ℕ) :ℤ)*gd q 1710 := by
  have eqTrim: (∑ r∈range n,gd q (min 1710 ((a :ℤ) - r))) =
      ∑ r∈range (a+1),gd q (min 1710 ((a :ℤ) - r)) := by
    symm
    apply sum_subset (range_mono (by omega))
    intro r _ hr
    rw [mem_range] at hr
    exact cumulative_neg _ _ ((min_le_right _ _).trans_lt (by omega))
  have eqRev : (∑ r∈range (a+1),gd q (min 1710 ((a :ℤ) - r))) =
      ∑ r∈range (a+1),gd q (min 1710 r) := by
    conv_rhs=>rw [← sum_range_reflect (fun r :ℕ=>gd q (min 1710 r)) (a+1)]
    apply sum_congr rfl
    intro r hr
    have h:=mem_range.mp hr
    rw [show a+1 - 1 - r=a - r by omega,Nat.cast_sub (by omega)]
  rw [eqTrim,eqRev]
  conv_lhs=>rw [← Nat.add_sub_of_le hj,sum_range_add]
  have e1 : (∑ r∈range 1710,gd q (min 1710 r)) = ∑ r∈range 1710,gd q r :=
    sum_congr rfl fun r hr=> by rw [min_eq_right (by have :=mem_range.mp hr; omega)]
  have e2 (r :ℕ) :min (1710 :ℤ) ((1710+r :ℕ) :ℤ)=1710 := by omega
  rw [e1]
  simp_rw [e2]
  rw [sum_const,card_range,nsmul_eq_mul]
private theorem sum_term (q:ℕ) (hq:q≤1290) :
    (∑ r :Offset,term q r.val)=(3000-(q:ℤ))*gd q 1710 := by
  simp only [term,sum_sub_distrib]
  change ((∑ r :Fin 4710,gd q (min 1710 (4709-(q:ℤ) - r.val))) -
    ∑ r :Fin 4710,gd q (1709-(r.val :ℤ)))= _
  rw [Fin.sum_univ_eq_sum_range (fun r :ℕ=>gd q (min 1710 (4709-(q:ℤ) - r))),
    Fin.sum_univ_eq_sum_range (fun r :ℕ=>gd q (1709-(r :ℤ))),
    show (4709:ℤ)-(q:ℤ)=((4709 - q:ℕ) :ℤ) by omega,
    clipped_sum q (4709-q) 4710 (by omega) (by omega)]
  have h:=df6 q 1709 4710 (by decide)
  norm_num only [Nat.cast_ofNat] at h
  rw [h,add_sub_cancel_left,
    show ((4709 - q+1 - 1710 :ℕ) :ℤ)=3000-(q:ℤ) by omega]
theorem prefix_grade_le (q:ℕ) (hq:q≤1290) (p:Offset→Fin 11→ℕ) :
    (al2 q p:ℤ)≤(3000-(q:ℤ))*gd q 1710 := by
  rw [← sum_term q hq,al2,Nat.cast_sum]
  exact sum_le_sum fun r _ =>
    (Int.toNat_of_nonneg (term_nonneg q r.val hq)) ▸ Int.ofNat_le.mpr (bBL q r hq (p r))
private theorem bZg (q:ℕ) :0≤gd q (3*(q:ℤ)) := by
  calc
    0=gd q (-1) :=(cumulative_neg _ _ (by decide)).symm
    _≤_:=anX q (by omega)
private def row (q:ℕ) :ℕ:=(3000 - q)*(gd q (3*(q:ℤ))).toNat
private theorem aH4 (q:ℕ) (hq:q≤570) (p:Offset→Fin 11→ℕ) :
    al2 q p≤ row q:= by
  have h:=prefix_grade_le q (by omega) p
  have he :gd q 1710=gd q (3*(q:ℤ)) := by
    simp [gd,min_eq_right (show 3*(q:ℤ)≤1710 by omega),
      show ¬ 3*(q:ℤ)<0 by omega]
  rw [he] at h
  apply Int.ofNat_le.mp
  simpa only [row,Nat.cast_mul,Nat.cast_sub (show q≤3000 by omega),
    Nat.cast_ofNat,Int.toNat_of_nonneg (bZg q)] using h
private def primitive (n:ℤ) :ℤ:=n*(n+1)*(n+2)*(n+3)*(15004-4*n)
private theorem gxb (n:ℕ) (hn:n≤3000) :
    120*(↑(∑ q∈range n,row q) :ℤ)=primitive n:= by
  induction n with
  | zero=>simp [primitive]
  | succ n ih =>
    rw [sum_range_succ,Nat.cast_add,mul_add,ih (by omega),Nat.cast_succ]
    simp only [row,Nat.cast_mul,Nat.cast_sub (show n≤3000 by omega),
      Int.toNat_of_nonneg (bZg n),primitive]
    linear_combination 20*(3000-(n:ℤ))*saturated n
theorem saturated_cap:aak 0 571 0xa5b369518b0:= by
  refine ⟨fun _ _ _=>0,?_⟩
  unfold rankBand
  rw [Nat.Ico_zero_eq_range]
  refine (sum_le_sum fun q hq=>aH4 q (by have :=mem_range.mp hq; omega) _).trans ?_
  have h:=gxb 571 (by decide)
  have hnum :primitive 571=(120:ℤ)*0xa5b369518b0:= by
    change (571 :ℤ)*572*573*574*12720=120*0xa5b369518b0
    exact_mod_cast (show (571 :ℕ)*572*573*574*12720=120*0xa5b369518b0 by decide)
  change 120*(↑(∑ q∈range 571,row q) :ℤ)=primitive 571 at h
  rw [hnum] at h
  omega
end qwbsesc
