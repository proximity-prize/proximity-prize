import ProximityPrize.SubmissionLower.MergedInfra6815_20
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open scoped BigOperators
open RCN100
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem coefficientCount_mono_caps (D w : ℕ) {L L' s s' : ℕ}
    (hL : L≤L') (hs : s≤s') : coefficientCount D w L s≤coefficientCount D w L' s' := by
  unfold coefficientCount
  calc
    _≤∑ i∈Finset.range (L+1), ∑ j∈Finset.range (s+1),
        (L'+1-i-j)*(D-w*i-(w-1)*j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_right _ (by omega)
    _≤∑ i∈Finset.range (L+1), ∑ j∈Finset.range (s'+1),
        (L'+1-i-j)*(D-w*i-(w-1)*j) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)

theorem coefficientCount_strictMono_cutoff (w L s : ℕ) :
    StrictMono (fun D => coefficientCount D w L s) := by
  intro D D' hD
  unfold coefficientCount
  apply Finset.sum_lt_sum
  · intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.sub_le_sub_right hD.le _) _)
  · refine ⟨0,by simp,?_⟩
    apply Finset.sum_lt_sum
    · intro j _
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.sub_le_sub_right hD.le _) _)
    · refine ⟨0,by simp,?_⟩
      simpa using Nat.mul_lt_mul_of_pos_left hD (by omega : 0<L+1)

theorem multiple_count_lt_source (D w L s nu T R : ℕ) (hD : 0<D) (hnu : 0<nu) :
    coefficientCount (D-nu) w (L-T) (s-R)<coefficientCount D w L s :=
  (coefficientCount_mono_caps (D-nu) w (Nat.sub_le _ _) (Nat.sub_le _ _)).trans_lt
    (coefficientCount_strictMono_cutoff w L s (by omega))

theorem row_test_of_rearranged (source multiple outer inner n : ℕ)
    (hbase : multiple<source) (h : multiple+n*outer<source+n*inner) :
    multiple+n*(outer-inner)<source := by
  by_cases hio : inner≤outer
  · have he := congrArg (fun v : ℕ => n*v) (Nat.sub_add_cancel hio)
    rw [Nat.mul_add] at he
    omega
  · rw [Nat.sub_eq_zero_of_le (by omega : outer ≤ inner),mul_zero,add_zero]
    exact hbase

end ProximityPrize.SubmissionLower.RelativeCertificate6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open scoped BigOperators
open LocatorFastKernelArithmetic ClosedRank
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem rankRow_twice_general (m L s r : ℕ) (hr : r<m) (hshape : m+s≤L+1) :
    2*(rankRow m L s r : ℤ)=
      (r+1 : ℤ)*(s+1)*(2*L+2-r-s)-
        if r<m-min s (m/2) then 0 else
          (2*r+1-m : ℤ)*(s+1-m+r)*(2*L+2-r-s) := by
  let h := min (r+1) (m-r)
  have hl : r+s≤L := by omega
  have hle := rectangularCount_shift_le (r+1) (s+1) h L (by omega)
  have hsource := rectangularCount_twice (r+1) (s+1) 0 L (by omega)
  have hsource' : 2*(rectangularCount (r+1) (s+1) 0 L : ℤ)=
      (r+1 : ℤ)*(s+1)*(2*L+2-r-s) := by
    push_cast at hsource
    nlinarith only [hsource]
  unfold rankRow
  change 2*((rectangularCount (r+1) (s+1) 0 L-
    rectangularCount (r+1-h) (s+1-h) h L : ℕ) : ℤ)=_
  rw [Nat.cast_sub hle,mul_sub,hsource']
  by_cases hearly : r<m-min s (m/2)
  · rw [if_pos hearly]
    have hzero : r+1-h=0 ∨ s+1-h=0 := by dsimp [h]; omega
    rcases hzero with hh | hh <;> simp [hh,rectangularCount]
  · rw [if_neg hearly]
    have heqh : h=m-r := by dsimp [h]; omega
    have hhr : h≤r+1 := by dsimp [h]; omega
    have hhs : h≤s+1 := by omega
    have hkernel := rectangularCount_twice (r+1-h) (s+1-h) h L (by omega)
    simp only [Nat.cast_sub hhr,Nat.cast_sub hhs,Nat.cast_add,Nat.cast_one] at hkernel
    have hhcast : (h : ℤ)=m-r := by rw [heqh,Nat.cast_sub (by omega : r≤m)]
    rw [hhcast] at hkernel
    nlinarith only [hkernel]

theorem sum_removed_rows_general (m L s k : ℕ) (hk : k≤m) :
    (∑ r∈Finset.range m, if r<m-k then (0 : ℤ) else removedTwice m L s ((m : ℤ)-r))=
      ∑ j∈Finset.range k, removedTwice m L s (j+1) := by
  let f : ℕ → ℤ := fun r => if r<m-k then 0 else removedTwice m L s ((m : ℤ)-r)
  change (∑ r∈Finset.range m, f r)=_
  have hsplit := Finset.sum_range_add f (m-k) k
  rw [Nat.sub_add_cancel hk] at hsplit
  rw [hsplit]
  have hz : (∑ r∈Finset.range (m-k), f r)=0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [f,Finset.mem_range.mp hr]
  rw [hz,zero_add]
  calc
    _=∑ j∈Finset.range k, f (m-k+(k-1-j)) :=
      (Finset.sum_range_reflect (fun r => f (m-k+r)) k).symm
    _=_ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hlate : ¬m-k+(k-1-j)<m-k := by omega
      have hindex : (m : ℤ)-(m-k+(k-1-j) : ℕ)=(j : ℤ)+1 := by
        have he : m-k+(k-1-j)+j+1=m := by omega
        have hi : ((m-k+(k-1-j) : ℕ) : ℤ)+j+1=m := by exact_mod_cast he
        omega
      simp only [f,if_neg hlate,hindex]

def rankTwelve (m L s : ℕ) : ℤ :=
  sourceTwelve m L s-removedPartialTwelve m L s (min s (m/2) : ℕ)

theorem localRankBound_twelve (m L s : ℕ) (hshape : m+s≤L+1) :
    12*(RCN119.localRankBound m L s : ℤ)=rankTwelve m L s := by
  rw [localRankBound_eq_fastLocalRankBound m L s hshape]
  have hfast : fastLocalRankBound m L s=∑ r∈Finset.range m, rankRow m L s r := by
    unfold fastLocalRankBound
    rw [LocatorLowQuotient.kernelSumRange_eq]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have he : min r L=r := min_eq_left (by omega)
    simp only [he,rankRow]
  have hrow (r : ℕ) (hr : r∈Finset.range m) :
      2*(rankRow m L s r : ℤ)=sourceTwice L s r-
        (if r<m-min s (m/2) then 0 else removedTwice m L s ((m : ℤ)-r)) := by
    rw [rankRow_twice_general m L s r (Finset.mem_range.mp hr) hshape]
    split_ifs <;> simp only [sourceTwice,removedTwice] <;> ring
  have hsum : 2*(fastLocalRankBound m L s : ℤ)=
      (∑ r∈Finset.range m, sourceTwice L s r)-
        ∑ j∈Finset.range (min s (m/2)), removedTwice m L s (j+1) := by
    rw [hfast,Nat.cast_sum,Finset.mul_sum]
    rw [Finset.sum_congr rfl hrow,Finset.sum_sub_distrib,
      sum_removed_rows_general m L s (min s (m/2)) (by omega)]
  have hh := congrArg (fun z : ℤ => 6*z) hsum
  rw [mul_sub,sum_sourceTwice,sum_removedTwice] at hh
  unfold rankTwelve
  nlinarith only [hh]

end ProximityPrize.SubmissionLower.RelativeCertificate6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open RCN100 ClosedRank
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def rankAffine (m s : ℕ) (L : ℤ) : ℤ :=
  sourceTwelve m L s-removedPartialTwelve m L s (min s (m/2) : ℕ)
def rankSlope (m s : ℕ) : ℤ := rankAffine m s 1-rankAffine m s 0
def rankIntercept (m s : ℕ) : ℤ := rankAffine m s 0

theorem rankAffine_eq (m s : ℕ) (L : ℤ) :
    rankAffine m s L=rankSlope m s*L+rankIntercept m s := by
  unfold rankSlope rankIntercept rankAffine sourceTwelve removedPartialTwelve
  ring

theorem rank_formula (m L s : ℕ) (hshape : m+s≤L+1) :
    12*(RCN119.localRankBound m L s : ℤ)=rankSlope m s*L+rankIntercept m s := by
  rw [localRankBound_twelve m L s hshape]
  exact rankAffine_eq m s L

def countSlope (D s : ℕ) : ℤ := coefficientSlope (D/131071) (D%131071) 131071 s
def countIntercept (D s : ℕ) : ℤ := coefficientIntercept (D/131071) (D%131071) 131071 s

theorem coefficient_formula (D L s : ℕ) (hs : s<131071) (hsq : s≤D/131071) (hL : D/131071+1≤L) :
    (coefficientCount D 131071 L s : ℤ)=countSlope D s*L+countIntercept D s := by
  have he : (D/131071)*131071+D%131071=D := by have := Nat.div_add_mod D 131071; omega
  simpa only [he,countSlope,countIntercept] using coefficientCount_affine (D/131071) (D%131071)
    131071 L s (by decide) (Nat.mod_lt _ (by decide)) hs hsq hL

def marginA (D nu s R m mu : ℕ) : ℤ :=
  12*(countSlope D s-countSlope (D-nu) (s-R))-
    262144*(rankSlope m s-rankSlope (m-mu) (s-R))
def marginB (D nu s R m mu : ℕ) : ℤ :=
  12*countSlope (D-nu) (s-R)-262144*rankSlope (m-mu) (s-R)
def marginC (D nu s R m mu : ℕ) : ℤ :=
  12*(countIntercept D s-countIntercept (D-nu) (s-R))-
    262144*(rankIntercept m s-rankIntercept (m-mu) (s-R))

theorem margin_identity (D nu L s T R m mu : ℕ)
    (hs : s<131071) (hR : R≤s) (hT : T≤L)
    (hsq : s≤D/131071) (hsq' : s-R≤(D-nu)/131071)
    (hL : D/131071+1≤L) (hL' : (D-nu)/131071+1≤L-T)
    (hm : m+s≤L+1) (hm' : (m-mu)+(s-R)≤L-T+1) :
    marginA D nu s R m mu*L+marginB D nu s R m mu*T+marginC D nu s R m mu=
      12*((coefficientCount D 131071 L s : ℤ)-coefficientCount (D-nu) 131071 (L-T) (s-R))-
        262144*(12*(RCN119.localRankBound m L s : ℤ)-12*RCN119.localRankBound (m-mu) (L-T) (s-R)) := by
  rw [coefficient_formula D L s hs hsq hL,
    coefficient_formula (D-nu) (L-T) (s-R) (by omega) hsq' hL',
    rank_formula m L s hm,rank_formula (m-mu) (L-T) (s-R) hm',Nat.cast_sub hT]
  unfold marginA marginB marginC
  ring

theorem row_test_of_margin (D nu L s T R m mu : ℕ)
    (hD : 0<D) (hnu : 0<nu) (hs : s<131071) (hR : R≤s) (hT : T≤L)
    (hsq : s≤D/131071) (hsq' : s-R≤(D-nu)/131071)
    (hL : D/131071+1≤L) (hL' : (D-nu)/131071+1≤L-T)
    (hm : m+s≤L+1) (hm' : (m-mu)+(s-R)≤L-T+1)
    (hmargin : 0<marginA D nu s R m mu*L+marginB D nu s R m mu*T+marginC D nu s R m mu) :
    coefficientCount (D-nu) 131071 (L-T) (s-R)+
      262144*(RCN119.localRankBound m L s-RCN119.localRankBound (m-mu) (L-T) (s-R))<
      coefficientCount D 131071 L s := by
  have hh := margin_identity D nu L s T R m mu hs hR hT hsq hsq' hL hL' hm hm'
  have hi : (coefficientCount (D-nu) 131071 (L-T) (s-R) : ℤ)+
      262144*RCN119.localRankBound m L s <
      (coefficientCount D 131071 L s : ℤ)+262144*RCN119.localRankBound (m-mu) (L-T) (s-R) := by
    nlinarith only [hh,hmargin]
  apply row_test_of_rearranged _ _ _ _ 262144 (multiple_count_lt_source _ _ _ _ _ _ _ hD hnu)
  exact_mod_cast hi

end ProximityPrize.SubmissionLower.RelativeCertificate6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.RelativeCertificate6815
open RelativeCertificate6814
open RCN100 RelativeBounded6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 20000

structure Band where
  R : ℕ
  B : ℕ
  T0 : ℕ
  T1 : ℕ
  count : ℕ
  deriving DecidableEq

structure Rectangle where
  lo : ℕ
  hi : ℕ
  alpha : ℕ
  beta : ℕ
  s : ℕ
  L0 : ℕ
  L1 : ℕ
  U : ℕ
  deriving DecidableEq

def tail (b : Band) : ℕ := (b.B+b.R-1)*181245+131071-1
def cutoff (b : Band) (d : Rectangle) : ℕ :=
  d.alpha*181245-d.beta*min (d.hi-131071+1) ((b.B+b.R-1)*181245)
def lowerTotal (b : Band) (d : Rectangle) (T : ℕ) : ℕ :=
  max (T+d.alpha+d.s) (max (cutoff b d/131071+1) (T+(cutoff b d-d.lo)/131071+1))
def total (b : Band) (d : Rectangle) (T : ℕ) : ℕ :=
  if b.T0=b.T1 then d.L0 else ceilBlend b.T0 b.T1 d.L0 d.L1 T

def Shape (b : Band) (d : Rectangle) : Prop :=
  b.T0≤b.T1 ∧ b.R≤d.s ∧ d.s<131071 ∧ 131071≤d.lo ∧ d.lo≤d.hi ∧
  d.hi≤tail b ∧ 0<cutoff b d ∧ d.s≤cutoff b d/131071 ∧
  d.s-b.R≤(cutoff b d-d.lo)/131071 ∧
  lowerTotal b d b.T0≤d.L0 ∧ lowerTotal b d b.T1≤d.L1

def rowGood (b : Band) (d : Rectangle) (mu : ℕ) : Prop :=
  let m := d.alpha-d.beta*(mu-1)
  let a := marginA (cutoff b d) d.lo d.s b.R m mu
  let v := marginB (cutoff b d) d.lo d.s b.R m mu
  let c := marginC (cutoff b d) d.lo d.s b.R m mu
  max 0 (-a)<a*d.L0+v*b.T0+c ∧ max 0 (-a)<a*d.L1+v*b.T1+c

instance shapeDecidable (b : Band) (d : Rectangle) : Decidable (Shape b d) := by
  unfold Shape
  infer_instance
instance rowGoodDecidable (b : Band) (d : Rectangle) (mu : ℕ) : Decidable (rowGood b d mu) := by
  unfold rowGood
  infer_instance

def checkRows (b : Band) (d : Rectangle) : ℕ → Bool
  | 0 => true
  | n+1 => checkRows b d n && decide (rowGood b d n)

theorem checkRows_spec (b : Band) (d : Rectangle) (n : ℕ) (hc : checkRows b d n=true) :
    ∀ mu<n, rowGood b d mu := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checkRows,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro mu hmu
    rcases Nat.lt_or_eq_of_le (show mu≤n by omega) with h | h
    · exact ih hc.1 mu h
    · simpa only [h] using hc.2

theorem total_lower (b : Band) (d : Rectangle) (T : ℕ) (hshape : Shape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) : lowerTotal b d T≤total b d T := by
  rcases hshape with ⟨h01,_,_,_,_,_,_,_,_,hL0,hL1⟩
  unfold total
  split_ifs with he
  · have ht : T=b.T0 := by omega
    simpa only [ht] using hL0
  · have hstrict : b.T0<b.T1 := by omega
    simp only [lowerTotal,max_le_iff] at hL0 hL1 ⊢
    refine ⟨?_,?_,?_⟩
    · simpa only [Nat.add_assoc] using ceilBlend_affine_lower b.T0 b.T1 d.L0 d.L1 T (d.alpha+d.s)
        hstrict hT0 hT1 (by omega) (by omega)
    · exact ceilBlend_const_lower _ _ _ _ _ _ hstrict hT0 hT1 hL0.2.1 hL1.2.1
    · simpa only [Nat.add_assoc] using ceilBlend_affine_lower b.T0 b.T1 d.L0 d.L1 T
        ((cutoff b d-d.lo)/131071+1) hstrict hT0 hT1 (by omega) (by omega)

theorem total_upper (b : Band) (d : Rectangle) (T : ℕ) (hshape : Shape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) : total b d T≤max d.L0 d.L1 := by
  unfold total
  split_ifs with he
  · exact le_max_left _ _
  · exact ceilBlend_upper _ _ _ _ _ (by have := hshape.1; omega) hT0 hT1

theorem margin_positive (b : Band) (d : Rectangle) (T mu : ℕ) (hshape : Shape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hgood : rowGood b d mu) :
    0<marginA (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*total b d T+
      marginB (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      marginC (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu := by
  unfold rowGood at hgood
  unfold total
  split_ifs with he
  · have ht : T=b.T0 := by omega
    rw [ht]
    exact lt_of_le_of_lt (le_max_left _ _) hgood.1
  · have hstrict : b.T0<b.T1 := by have := hshape.1; omega
    let p := b.T1-T
    let q := T-b.T0
    have hsum : p+q=b.T1-b.T0 := by dsimp [p,q]; omega
    have ht : (p+q)*T=p*b.T0+q*b.T1 := by
      rw [hsum]
      exact total_blend_identity _ _ _ hT0 hT1
    have hb := ceilBlend_bounds b.T0 b.T1 d.L0 d.L1 T hstrict hT0 hT1
    apply rounded_affine_positive (p : ℤ) (q : ℤ) d.L0 d.L1 b.T0 b.T1
      (ceilBlend b.T0 b.T1 d.L0 d.L1 T) T _ _ _
      (by exact_mod_cast Nat.zero_le p) (by exact_mod_cast Nat.zero_le q)
      (by exact_mod_cast (show 0<p+q by omega)) (by exact_mod_cast ht) ?_ ?_ hgood.1 hgood.2
    · exact_mod_cast (show p*d.L0+q*d.L1≤(p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T by simpa only [hsum] using hb.1)
    · exact_mod_cast (show (p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T≤p*d.L0+q*d.L1+(p+q) by simpa only [hsum] using hb.2.le)

theorem rectangle_rows (b : Band) (d : Rectangle) (T : ℕ) (hshape : Shape b d)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hcheck : checkRows b d (b.B+b.R+1)=true) :
    ∀ mu≤b.B+b.R, coefficientCount (cutoff b d-d.lo) 131071 (total b d T-T) (d.s-b.R)+
      262144*profileRowRank d.alpha d.beta (total b d T) d.s T b.R mu <
        coefficientCount (cutoff b d) 131071 (total b d T) d.s := by
  intro mu hmu
  have hmargin := margin_positive b d T mu hshape hT0 hT1 (checkRows_spec _ _ _ hcheck mu (by omega))
  have hl := total_lower b d T hshape hT0 hT1
  rcases hshape with ⟨_,hR,hs,hlo,_,_,hD,hsq,hsq',_,_⟩
  simp only [lowerTotal,max_le_iff] at hl
  exact row_test_of_margin _ _ _ _ _ _ _ _ hD (by omega) hs hR (by omega)
    hsq hsq' hl.2.1 (by omega) (by omega) (by omega) hmargin

end
end ProximityPrize.SubmissionLower.RelativeCertificate6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.RelativeCertificate6815
open RelativeCertificate6814
open scoped BigOperators
open MvPolynomial RCN100 RCN119 RCN122 RCN260 RelativeBounded6814 ContactOrderBridge
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

def pair (b : Band) (d : Rectangle) : UnequalParameters :=
  ⟨262144,131071,181245,b.B,b.R,b.T1,d.U,d.s,max d.L0 d.L1⟩

def Valid (b : Band) (d : Rectangle) : Prop :=
  Shape b d ∧ 1≤b.R ∧ b.B<2130706433 ∧ b.R<2130706433 ∧ b.T1<2130706433 ∧
  cutoff b d≤131071*(d.U+1) ∧
  (pair b d).mixedCost.y<2130706433 ∧ (pair b d).mixedCost.r<2130706433 ∧
  (pair b d).mixedCost.z<2130706433 ∧
  AsymmetricHelper.leftRegularCountCap (pair b d)≤b.count ∧
  checkRows b d (b.B+b.R+1)=true

instance validDecidable (b : Band) (d : Rectangle) : Decidable (Valid b d) := by
  unfold Valid
  infer_instance

theorem cutoff_of_clipped_weight (b : Band) (d : Rectangle) (nu : ℕ)
    (hhi : min nu (tail b)≤d.hi) :
    cutoff b d≤d.alpha*181245-d.beta*min (nu-131071+1) ((b.B+b.R-1)*181245) := by
  unfold cutoff
  apply Nat.sub_le_sub_left
  apply Nat.mul_le_mul_left
  by_cases hn : nu≤tail b
  · have hh : nu≤d.hi := by simpa only [min_eq_left hn] using hhi
    exact min_le_min (by omega) le_rfl
  · have hh : tail b≤d.hi := by simpa only [min_eq_right (by omega : tail b≤nu)] using hhi
    have hc : (b.B+b.R-1)*181245≤d.hi-131071+1 := by unfold tail at hh; omega
    rw [min_eq_right hc]
    exact min_le_right _ _

variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K

theorem regular_count_of_rectangle (b : Band) (d : Rectangle) (hvalid : Valid b d)
    {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T b.R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : b.R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤b.B)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hlo : d.lo≤nu) (hhi : min nu (tail b)≤d.hi)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤b.count := by
  classical
  rcases hvalid with ⟨hshape,hRpos,hBchar,hRchar,hTchar,hU,hgY,hgR,hgZ,hprice,hcheck⟩
  have hF := RCN167.positiveRFactors_spec H F.val F.property
  let Delta := RCN140.regularSeeds H selected Gamma F
  have hsub : Delta⊆Gamma := RCN140.regularSeeds_subset H selected Gamma F
  have hsol : ∀ gamma∈Delta, specialization K (selected gamma) gamma F.val=0 := by
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2.1
  have hreg : ∀ gamma∈Delta, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F.val)≠0 := by
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2.2
  have hrows := rectangle_rows b d T hshape hT0 hT1 hcheck
  have hlower := total_lower b d T hshape hT0 hT1
  have hupper := total_upper b d T hshape hT0 hT1
  have hshape' := hshape
  rcases hshape' with ⟨_,hRs,_,hweight,_,_,hD,_,_,_,_⟩
  have hTL : T≤total b d T := by
    have hh := (max_le_iff.mp hlower).1
    dsimp [lowerTotal] at hlower
    omega
  have hrowsNu := profile_rows_mono_weight (D:=cutoff b d) (w:=131071) (L:=total b d T)
    (s:=d.s) (T:=T) (R:=b.R) (B:=b.B) (N:=262144) (alpha:=d.alpha) (beta:=d.beta) hlo hrows
  obtain ⟨Q,hQ,hrel,hzero⟩ := exists_profile_helper K
    (D:=cutoff b d) (L:=total b d T) (s:=d.s) (nu:=nu) (B:=b.B)
    F.val hF.1 hF.2.2 hbox hTL hRs hcode htotal hslope hB nodes u0 u1 d.alpha d.beta 181245
    (by omega) hD (cutoff_of_clipped_weight b d nu hhi)
    (by simpa only [hcard] using hrowsNu)
    selected Delta (fun gamma hg => hdegree gamma (hsub hg)) hsol hreg
    (fun gamma hg => hagreement gamma (hsub hg))
  have hFY : F.val.degreeOf 1≤b.B := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights he).trans hB
    rw [RCN081.weight_fin4] at hw
    simp [RCN156.residualYSWeights] at hw
    omega
  have hFR : F.val.degreeOf 2≤b.R := MvPolynomial.degreeOf_le_iff.mpr (fun e he => (hbox he).2.1)
  have hFZ : F.val.degreeOf 3≤b.T1 := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hbox he).1; omega)
  have hQY : Q.degreeOf 1≤d.U := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hQ he).2.2; omega)
  have hQR : Q.degreeOf 2≤d.s := MvPolynomial.degreeOf_le_iff.mpr (fun e he => (hQ he).2.1)
  have hQZ : Q.degreeOf 3≤max d.L0 d.L1 := MvPolynomial.degreeOf_le_iff.mpr
    (fun e he => by have := (hQ he).1; omega)
  apply le_trans ?_ hprice
  exact AsymmetricHelper.regularSeeds_count_le_left_intersection
    (pair b d) H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
    hRpos hBchar hRchar hTchar hgY hgR hgZ
    selected Gamma (Finset.univ : Finset I) nodes u0 u1 nodes.injective.injOn
    (by simpa only [pair,Finset.card_univ] using hcard)
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    hdegree hagreement (by simpa only [pair,UnequalParameters.errors,Nat.reduceSub] using hno) hzero

end
end ProximityPrize.SubmissionLower.RelativeCertificate6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.RelativeCertificate6815
open RelativeCertificate6814
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def minimumWeight (b : Band) : ℕ := 131071*b.B-b.R
def checkList (b : Band) : List Rectangle → Bool
  | [] => true
  | d::ds => decide (Valid b d) && checkList b ds

theorem checkList_append (b : Band) (xs ys : List Rectangle) :
    checkList b (xs++ys)= (checkList b xs && checkList b ys) := by
  induction xs with
  | nil => simp [checkList]
  | cons x xs ih => simp only [List.cons_append,checkList,ih,Bool.and_assoc]

theorem checkList_spec (b : Band) (xs : List Rectangle) (hc : checkList b xs=true) :
    ∀ d∈xs, Valid b d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [checkList,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro d hd
    rcases List.mem_cons.mp hd with he | he
    · simpa only [he] using hc.1
    · exact ih hc.2 d he

def covers (start stop : ℕ) : List Rectangle → Bool
  | [] => decide (stop+1=start)
  | d::ds => decide (d.lo=start ∧ d.lo≤d.hi) && covers (d.hi+1) stop ds

theorem covers_spec (xs : List Rectangle) (start stop : ℕ) (hc : covers start stop xs=true)
    (nu : ℕ) (hlo : start≤nu) (hhi : nu≤stop) :
    ∃ d∈xs, d.lo≤nu ∧ nu≤d.hi := by
  induction xs generalizing start with
  | nil => simp only [covers,decide_eq_true_eq] at hc; omega
  | cons d ds ih =>
    simp only [covers,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases hn : nu≤d.hi
    · exact ⟨d,by simp,by omega,hn⟩
    · obtain ⟨e,he,hl,hh⟩ := ih (d.hi+1) hc.2 (by omega)
      exact ⟨e,List.mem_cons_of_mem _ he,hl,hh⟩

def VerifiedCover (b : Band) (xs : List Rectangle) : Prop :=
  checkList b xs=true ∧ covers (minimumWeight b) (tail b) xs=true ∧ minimumWeight b≤tail b

variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K

theorem regular_count_of_cover (b : Band) (xs : List Rectangle) (hc : VerifiedCover b xs)
    {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T b.R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : b.R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤b.B)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hnu : minimumWeight b≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤b.count := by
  obtain ⟨d,hd,hlo,hhi⟩ := covers_spec xs (minimumWeight b) (tail b) hc.2.1
    (min nu (tail b)) (le_min hnu hc.2.2) (min_le_right _ _)
  exact regular_count_of_rectangle K I b d (checkList_spec b xs hc.1 d hd) F hbox hcode
    htotal hslope hB hT0 hT1 (hlo.trans (min_le_left _ _)) hhi nodes u0 u1 hcard
    selected Gamma hdegree hagreement hno

end
end ProximityPrize.SubmissionLower.RelativeCertificate6815
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.RelativeCertificate6815
open RelativeCertificate6814
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000

structure Cubic where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ

def Cubic.eval (p : Cubic) (x : ℤ) : ℤ := ((p.c3*x+p.c2)*x+p.c1)*x+p.c0
def Cubic.deriv (p : Cubic) (x : ℤ) : ℤ := (3*p.c3*x+2*p.c2)*x+p.c1

theorem cubic_bernstein_identity (p : Cubic) (a b x : ℤ) :
    (b-a)^3*p.eval x=p.eval a*(b-x)^3+
      (3*p.eval a+(b-a)*p.deriv a)*(b-x)^2*(x-a)+
      (3*p.eval b-(b-a)*p.deriv b)*(b-x)*(x-a)^2+p.eval b*(x-a)^3 := by
  unfold Cubic.eval Cubic.deriv
  ring

theorem cubic_positive (p : Cubic) (a b x : ℤ)
    (ha : a≤x) (hb : x≤b) (h0 : 0<p.eval a) (h3 : 0<p.eval b)
    (h1 : 0≤3*p.eval a+(b-a)*p.deriv a)
    (h2 : 0≤3*p.eval b-(b-a)*p.deriv b) : 0<p.eval x := by
  by_cases he : a=b
  · have hx : x=a := by omega
    simpa only [hx] using h0
  have hw : 0<b-a := by omega
  have hu : 0≤b-x := by omega
  have hv : 0≤x-a := by omega
  have ht1 := mul_nonneg (mul_nonneg h1 (sq_nonneg (b-x))) hv
  have ht2 := mul_nonneg (mul_nonneg h2 hu) (sq_nonneg (x-a))
  have ht0 := mul_nonneg h0.le (pow_nonneg hu 3)
  have ht3 := mul_nonneg h3.le (pow_nonneg hv 3)
  have hid := cubic_bernstein_identity p a b x
  have hp : 0<(b-a)^3*p.eval x := by
    by_cases hx : x=b
    · have hs := mul_pos h3 (pow_pos (show 0<x-a by omega) 3)
      nlinarith only [hid,ht0,ht1,ht2,hs]
    · have hs := mul_pos h0 (pow_pos (show 0<b-x by omega) 3)
      nlinarith only [hid,hs,ht1,ht2,ht3]
  exact pos_of_mul_pos_right hp (pow_nonneg hw.le 3)

def Cubic.Check (p : Cubic) (a b : ℕ) : Prop :=
  b<a ∨ (0<p.eval a ∧ 0<p.eval b ∧
    0≤3*p.eval a+((b : ℤ)-a)*p.deriv a ∧
    0≤3*p.eval b-((b : ℤ)-a)*p.deriv b)

instance cubicCheckDecidable (p : Cubic) (a b : ℕ) : Decidable (p.Check a b) := by
  unfold Cubic.Check
  infer_instance

theorem Cubic.check_positive (p : Cubic) (a b x : ℕ) (hc : p.Check a b)
    (ha : a≤x) (hb : x≤b) : 0<p.eval x := by
  rcases hc with h | ⟨h0,h3,h1,h2⟩
  · omega
  · exact cubic_positive p a b x (by exact_mod_cast ha) (by exact_mod_cast hb) h0 h3 h1 h2

def rankPolynomial (base rate L s : ℤ) : Cubic :=
  let a0 := s*(s+1)*((4*s+2)*L-s*s+5*s+2)
  let a1 := -2*(s+1)*(3*L*s-3*L+6*s-4)
  let a2 := 6*(L+1)*(s+1)
  let a3 := -2*(s+1)
  ⟨a0+a1*base+a2*base^2+a3*base^3,
    -rate*(a1+2*a2*base+3*a3*base^2),
    rate^2*(a2+3*a3*base),-a3*rate^3⟩

theorem rankPolynomial_eval (base rate L s x : ℤ) :
    (rankPolynomial base rate L s).eval x=
      ClosedRank.sourceTwelve (base-rate*x) L s-
        ClosedRank.removedPartialTwelve (base-rate*x) L s s := by
  unfold rankPolynomial Cubic.eval ClosedRank.sourceTwelve ClosedRank.removedPartialTwelve
  ring

def marginPolynomial (b : Band) (d : Rectangle) (T L : ℕ) : Cubic :=
  let p := rankPolynomial ((d.alpha : ℤ)+d.beta) d.beta L d.s
  let q := rankPolynomial ((d.alpha : ℤ)+d.beta) ((d.beta : ℤ)+1) ((L : ℤ)-T) ((d.s : ℤ)-b.R)
  let c := 12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
    countSlope (cutoff b d-d.lo) (d.s-b.R)*T+
    countIntercept (cutoff b d) d.s-countIntercept (cutoff b d-d.lo) (d.s-b.R))
  ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩

theorem marginPolynomial_eval (b : Band) (d : Rectangle) (T L mu : ℕ)
    (hmu : 1≤mu) (hR : b.R≤d.s)
    (hmmu : mu≤d.alpha-d.beta*(mu-1))
    (hs : 2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu) :
    (marginPolynomial b d T L).eval mu=
      marginA (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*L+
      marginB (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      marginC (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu := by
  let m := d.alpha-d.beta*(mu-1)
  have hmcast : (m : ℤ)=(d.alpha : ℤ)+d.beta-(d.beta : ℤ)*mu := by
    have hle : d.beta*(mu-1)≤d.alpha := by omega
    have hh : (m : ℤ)+(d.beta : ℤ)*(mu-1 : ℕ)=d.alpha := by
      exact_mod_cast Nat.sub_add_cancel hle
    rw [Nat.cast_sub hmu,Nat.cast_one] at hh
    nlinarith only [hh]
  have hinner : (d.alpha : ℤ)+d.beta-((d.beta : ℤ)+1)*mu=(m-mu : ℕ) := by
    rw [Nat.cast_sub hmmu]
    nlinarith only [hmcast]
  have hk : min d.s (m/2)=d.s := min_eq_left (by omega)
  have hk' : min (d.s-b.R) ((m-mu)/2)=d.s-b.R := min_eq_left (by omega)
  have ho := rankAffine_eq m d.s L
  have hi := rankAffine_eq (m-mu) (d.s-b.R) ((L : ℤ)-T)
  simp only [rankAffine,hk,hk'] at ho hi
  have he : (marginPolynomial b d T L).eval mu=
      12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
        countSlope (cutoff b d-d.lo) (d.s-b.R)*T+countIntercept (cutoff b d) d.s-
        countIntercept (cutoff b d-d.lo) (d.s-b.R))-
      262144*((rankPolynomial ((d.alpha : ℤ)+d.beta) d.beta L d.s).eval mu-
        (rankPolynomial ((d.alpha : ℤ)+d.beta) ((d.beta : ℤ)+1) ((L : ℤ)-T) ((d.s : ℤ)-b.R)).eval mu) := by
    unfold marginPolynomial Cubic.eval
    ring
  rw [he,rankPolynomial_eval,rankPolynomial_eval,←hmcast,hinner,←Nat.cast_sub hR,ho,hi]
  unfold marginA marginB marginC
  dsimp only [m] at *
  ring

end ProximityPrize.SubmissionLower.RelativeCertificate6815
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.RelativeCertificate6815
open RelativeCertificate6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

structure FastWitness where
  normalEnd : ℕ
  firstExact : ℕ
  lastExact : ℕ

def checkRange (b : Band) (d : Rectangle) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => checkRange b d start n && decide (rowGood b d (start+n))

theorem checkRange_spec (b : Band) (d : Rectangle) (start n : ℕ)
    (hc : checkRange b d start n=true) (mu : ℕ) (h0 : start≤mu) (h1 : mu<start+n) : rowGood b d mu := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checkRange,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases hmu : mu<start+n
    · exact ih hc.1 hmu
    · have he : mu=start+n := by omega
      simpa only [he] using hc.2

def corners (b : Band) (d : Rectangle) (a z : ℕ) : Prop :=
  (marginPolynomial b d b.T0 d.L0).Check a z ∧
  (marginPolynomial b d b.T0 (d.L0+1)).Check a z ∧
  (marginPolynomial b d b.T1 d.L1).Check a z ∧
  (marginPolynomial b d b.T1 (d.L1+1)).Check a z

instance cornersDecidable (b : Band) (d : Rectangle) (a z : ℕ) : Decidable (corners b d a z) := by
  unfold corners
  infer_instance

theorem rowGood_of_corners (b : Band) (d : Rectangle) (a z mu : ℕ)
    (hR : b.R≤d.s) (hc : corners b d a z) (ha : a≤mu) (hz : mu≤z) (hmu : 1≤mu)
    (hm : mu≤d.alpha-d.beta*(mu-1))
    (hs : 2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu) : rowGood b d mu := by
  have h0 := Cubic.check_positive _ _ _ mu hc.1 ha hz
  have h0' := Cubic.check_positive _ _ _ mu hc.2.1 ha hz
  have h1 := Cubic.check_positive _ _ _ mu hc.2.2.1 ha hz
  have h1' := Cubic.check_positive _ _ _ mu hc.2.2.2 ha hz
  rw [marginPolynomial_eval b d b.T0 d.L0 mu hmu hR hm hs hs'] at h0
  rw [marginPolynomial_eval b d b.T0 (d.L0+1) mu hmu hR hm hs hs'] at h0'
  rw [marginPolynomial_eval b d b.T1 d.L1 mu hmu hR hm hs hs'] at h1
  rw [marginPolynomial_eval b d b.T1 (d.L1+1) mu hmu hR hm hs hs'] at h1'
  simp only [Nat.cast_add,Nat.cast_one] at h0' h1'
  unfold rowGood
  constructor
  · exact max_lt h0 (by nlinarith only [h0'])
  · exact max_lt h1 (by nlinarith only [h1'])

def FastRows (b : Band) (d : Rectangle) (w : FastWitness) : Prop :=
  1≤w.firstExact ∧ w.firstExact≤w.lastExact ∧ w.lastExact≤w.normalEnd ∧ w.normalEnd≤b.B+b.R ∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1) ∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1) ∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd ∧
  corners b d 1 (w.firstExact-1) ∧ corners b d (w.lastExact+1) w.normalEnd ∧
  rowGood b d 0 ∧ checkRange b d w.firstExact (w.lastExact+1-w.firstExact)=true ∧
  checkRange b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true

instance fastRowsDecidable (b : Band) (d : Rectangle) (w : FastWitness) : Decidable (FastRows b d w) := by
  unfold FastRows
  infer_instance

theorem checkRows_of_all (b : Band) (d : Rectangle) (n : ℕ)
    (h : ∀ mu<n, rowGood b d mu) : checkRows b d n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [checkRows,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨ih (fun mu hm => h mu (by omega)),h n (by omega)⟩

theorem fastRows_sound (b : Band) (d : Rectangle) (w : FastWitness)
    (hR : b.R≤d.s) (h : FastRows b d w) : checkRows b d (b.B+b.R+1)=true := by
  rcases h with ⟨hfirst,hlast,hend,hmax,hlevel,hs,hs',hleft,hright,hzero,hcenter,htail⟩
  apply checkRows_of_all
  intro mu hmu
  by_cases hz : mu=0
  · simpa only [hz] using hzero
  have hmu1 : 1≤mu := by omega
  by_cases hn : mu≤w.normalEnd
  · have hmono : d.alpha-d.beta*(w.normalEnd-1)≤d.alpha-d.beta*(mu-1) :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_left d.beta (Nat.sub_le_sub_right hn 1)) d.alpha
    have hm : mu≤d.alpha-d.beta*(mu-1) := by omega
    have hms : 2*d.s≤d.alpha-d.beta*(mu-1) := by omega
    have hms' : 2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu := by omega
    by_cases hbefore : mu<w.firstExact
    · exact rowGood_of_corners b d 1 (w.firstExact-1) mu hR hleft hmu1 (by omega) hmu1 hm hms hms'
    by_cases hwithin : mu≤w.lastExact
    · exact checkRange_spec _ _ _ _ hcenter mu (by omega) (by omega)
    · exact rowGood_of_corners b d (w.lastExact+1) w.normalEnd mu hR hright (by omega) hn hmu1 hm hms hms'
  · exact checkRange_spec _ _ _ _ htail mu (by omega) (by omega)

def Header (b : Band) (d : Rectangle) : Prop :=
  Shape b d ∧ 1≤b.R ∧ b.B<2130706433 ∧ b.R<2130706433 ∧ b.T1<2130706433 ∧
  cutoff b d≤131071*(d.U+1) ∧
  (pair b d).mixedCost.y<2130706433 ∧ (pair b d).mixedCost.r<2130706433 ∧
  (pair b d).mixedCost.z<2130706433 ∧ AsymmetricHelper.leftRegularCountCap (pair b d)≤b.count

def FastValid (b : Band) (dw : Rectangle × FastWitness) : Prop := Header b dw.1 ∧ FastRows b dw.1 dw.2

instance fastValidDecidable (b : Band) (dw : Rectangle × FastWitness) : Decidable (FastValid b dw) := by
  unfold FastValid Header
  infer_instance

theorem fastValid_sound (b : Band) (dw : Rectangle × FastWitness) (h : FastValid b dw) : Valid b dw.1 := by
  rcases h with ⟨⟨hs,hR,hB,hRc,hTc,hU,hgY,hgR,hgZ,hprice⟩,hf⟩
  exact ⟨hs,hR,hB,hRc,hTc,hU,hgY,hgR,hgZ,hprice,fastRows_sound b dw.1 dw.2 hs.2.1 hf⟩

def fastCheckList (b : Band) : List (Rectangle × FastWitness) → Bool
  | [] => true
  | d::ds => decide (FastValid b d) && fastCheckList b ds

theorem fastCheckList_append (b : Band) (xs ys : List (Rectangle × FastWitness)) :
    fastCheckList b (xs++ys)=(fastCheckList b xs && fastCheckList b ys) := by
  induction xs with
  | nil => simp [fastCheckList]
  | cons x xs ih => simp only [List.cons_append,fastCheckList,ih,Bool.and_assoc]

theorem fastCheckList_sound (b : Band) (xs : List (Rectangle × FastWitness))
    (hc : fastCheckList b xs=true) : checkList b (xs.map Prod.fst)=true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [fastCheckList,Bool.and_eq_true,decide_eq_true_eq] at hc
    simp only [List.map_cons,checkList,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨fastValid_sound b x hc.1,ih hc.2⟩

end
end ProximityPrize.SubmissionLower.RelativeCertificate6815
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.RelativeCompactBlocks6815
open RelativeCertificate6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 40000

structure Profile where
  alpha : ℕ
  beta : ℕ
  s : ℕ
structure Entry where
  hi : ℕ
  profile : ℕ
  L0 : ℕ
  deltaL : ℕ
  witness : ℕ

structure Layout where
  hiBase : ℕ
  profileBase : ℕ
  lengthBase : ℕ
  deltaBase : ℕ
def decode (l : Layout) (n : ℕ) : Entry :=
  ⟨n%l.hiBase,(n/l.hiBase)%l.profileBase,
    (n/l.hiBase/l.profileBase)%l.lengthBase,
    (n/l.hiBase/l.profileBase/l.lengthBase)%l.deltaBase,
    n/l.hiBase/l.profileBase/l.lengthBase/l.deltaBase⟩

def rectangle (b : Band) (profiles : ℕ → Profile) (lo : ℕ) (e : Entry) : Rectangle :=
  let p := profiles e.profile
  let L1 := if e.deltaL%2=0 then e.L0+e.deltaL/2 else e.L0-e.deltaL/2
  let d : Rectangle := ⟨lo,e.hi,p.alpha,p.beta,p.s,e.L0,L1,0⟩
  {d with U:=(cutoff b d-1)/131071}
def fastWitness (e : Entry) : FastWitness :=
  ⟨e.witness%256,(e.witness/256)%256,e.witness/65536⟩

def checkBlock (b : Band) (profiles : ℕ → Profile) (stop : ℕ) : ℕ → List Entry → Bool
  | start,[] => decide (stop+1=start)
  | start,e::es => decide (FastValid b (rectangle b profiles start e,fastWitness e)) &&
      checkBlock b profiles stop (e.hi+1) es

def Covered (b : Band) (lo hi : ℕ) : Prop :=
  ∀ nu, lo≤nu → nu≤hi → ∃ d : Rectangle, Valid b d ∧ d.lo≤nu ∧ nu≤d.hi

theorem block_sound (b : Band) (profiles : ℕ → Profile) (start stop : ℕ) (es : List Entry)
    (hc : checkBlock b profiles stop start es=true) : Covered b start stop := by
  intro nu hlo hhi
  induction es generalizing start with
  | nil => simp only [checkBlock,decide_eq_true_eq] at hc; omega
  | cons e es ih =>
    simp only [checkBlock,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases he : nu≤e.hi
    · exact ⟨rectangle b profiles start e,fastValid_sound b _ hc.1,hlo,he⟩
    · exact ih (e.hi+1) hc.2 (by omega)

theorem covered_join (b : Band) (lo mid hi : ℕ)
    (h0 : Covered b lo mid) (h1 : Covered b (mid+1) hi) : Covered b lo hi := by
  intro nu hlo hhi
  by_cases h : nu≤mid
  · exact h0 nu hlo h
  · exact h1 nu (by omega) hhi

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K

theorem regular_count (b : Band) (hc : Covered b (minimumWeight b) (tail b))
    (hrange : minimumWeight b≤tail b)
    {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T b.R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : b.R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤b.B)
    (hT0 : b.T0≤T) (hT1 : T≤b.T1) (hnu : minimumWeight b≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤b.count := by
  obtain ⟨d,hd,hlo,hhi⟩ := hc (min nu (tail b)) (le_min hnu hrange) (min_le_right _ _)
  exact regular_count_of_rectangle K I b d hd F hbox hcode htotal hslope hB hT0 hT1
    (hlo.trans (min_le_left _ _)) hhi nodes u0 u1 hcard selected Gamma hdegree hagreement hno

end
end ProximityPrize.SubmissionLower.RelativeCompactBlocks6815
end MergedPart8
