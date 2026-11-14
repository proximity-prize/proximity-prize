import ProximityPrize.SubmissionLower.RecoveryCore02
set_option autoImplicit false
set_option linter.all false
set_option Elab.async true
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace LD
open scoped BigOperators
open RCN100
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem EFE (D w:ℕ) {L L' s s' :ℕ}
    (hL:L≤L') (hs:s≤s'):AW D w L s≤AW D w L' s' :=by
  unfold AW
  calc
    _≤∑ i∈Finset.range (L+1),∑ j∈Finset.range (s+1),
        (L'+1-i-j)*(D-w*i-(w-1)*j):=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_right _ (by omega)
    _≤∑ i∈Finset.range (L+1),∑ j∈Finset.range (s'+1),
        (L'+1-i-j)*(D-w*i-(w-1)*j):=by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _=>Nat.zero_le _)
    _≤_:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _=>Nat.zero_le _)

theorem CXK (w L s:ℕ):
    StrictMono (fun D=>AW D w L s):=by
  intro D D' hD
  unfold AW
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
      simpa using Nat.mul_lt_mul_of_pos_left hD (by omega:0<L+1)

theorem DCH (D w L s nu T R:ℕ) (hD:0<D) (hnu:0<nu):
    AW (D-nu) w (L-T) (s-R)<AW D w L s:=
  (EFE (D-nu) w (Nat.sub_le _ _) (Nat.sub_le _ _)).trans_lt
    (CXK w L s (by omega))

theorem EWT (source multiple outer inner n:ℕ)
    (hbase:multiple<source) (h:multiple+n*outer<source+n*inner):
    multiple+n*(outer-inner)<source:=by
  by_cases hio:inner≤outer
  · have he:=congrArg (fun v:ℕ=>n*v) (Nat.sub_add_cancel hio)
    rw [Nat.mul_add] at he
    omega
  · rw [Nat.sub_eq_zero_of_le (by omega:outer≤ inner),mul_zero,add_zero]
    exact hbase

end LD
end MergedPart0
section MergedPart1
namespace LD
open scoped BigOperators
open RZ ClosedRank
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem FAQ (m L s r:ℕ) (hr:r<m) (hshape:m+s≤L+1):
    2*(rankRow m L s r:ℤ)=
      (r+1:ℤ)*(s+1)*(2*L+2-r-s)-
        if r<m-min s (m/2) then 0 else
          (2*r+1-m:ℤ)*(s+1-m+r)*(2*L+2-r-s):=by
  let h:=min (r+1) (m-r)
  have hl:r+s≤L:=by omega
  have hle:=CUI (r+1) (s+1) h L (by omega)
  have hsource:=BHS (r+1) (s+1) 0 L (by omega)
  have hsource' :2*(_Q9 (r+1) (s+1) 0 L:ℤ)=
      (r+1:ℤ)*(s+1)*(2*L+2-r-s):=by
    push_cast at hsource
    nlinarith only [hsource]
  unfold rankRow
  change 2*((_Q9 (r+1) (s+1) 0 L-
    _Q9 (r+1-h) (s+1-h) h L:ℕ):ℤ)=_
  rw [Nat.cast_sub hle,mul_sub,hsource']
  by_cases hearly:r<m-min s (m/2)
  · rw [if_pos hearly]
    have hzero:r+1-h=0∨s+1-h=0:=by dsimp [h];omega
    rcases hzero with hh | hh<;>simp [hh,_Q9]
  · rw [if_neg hearly]
    have heqh:h=m-r:=by dsimp [h];omega
    have hhr:h≤r+1:=by dsimp [h];omega
    have hhs:h≤s+1:=by omega
    have hkernel:=BHS (r+1-h) (s+1-h) h L (by omega)
    simp only [Nat.cast_sub hhr,Nat.cast_sub hhs,Nat.cast_add,Nat.cast_one] at hkernel
    have hhcast:(h:ℤ)=m-r:=by rw [heqh,Nat.cast_sub (by omega:r≤m)]
    rw [hhcast] at hkernel
    nlinarith only [hkernel]

theorem EPV (m L s k:ℕ) (hk:k≤m):
    (∑ r∈Finset.range m,if r<m-k then (0:ℤ) else removedTwice m L s ((m:ℤ)-r))=
      ∑ j∈Finset.range k,removedTwice m L s (j+1):=by
  let f:ℕ→ℤ:=fun r=>if r<m-k then 0 else removedTwice m L s ((m:ℤ)-r)
  change (∑ r∈Finset.range m,f r)=_
  have hsplit:=Finset.sum_range_add f (m-k) k
  rw [Nat.sub_add_cancel hk] at hsplit
  rw [hsplit]
  have hz:(∑ r∈Finset.range (m-k),f r)=0:=by
    apply Finset.sum_eq_zero
    intro r hr
    simp [f,Finset.mem_range.mp hr]
  rw [hz,zero_add]
  calc
    _=∑ j∈Finset.range k,f (m-k+(k-1-j)):=
      (Finset.sum_range_reflect (fun r=>f (m-k+r)) k).symm
    _=_:=by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' :=Finset.mem_range.mp hj
      have hlate: ¬m-k+(k-1-j)<m-k:=by omega
      have hindex:(m:ℤ)-(m-k+(k-1-j):ℕ)=(j:ℤ)+1:=by
        have he:m-k+(k-1-j)+j+1=m:=by omega
        have hi:((m-k+(k-1-j):ℕ):ℤ)+j+1=m:=by exact_mod_cast he
        omega
      simp only [f,if_neg hlate,hindex]

def rankTwelve (m L s:ℕ):ℤ:=
  sourceTwelve m L s-AAL m L s (min s (m/2):ℕ)

theorem FBK (m L s:ℕ) (hshape:m+s≤L+1):
    12*(RCN119.ES m L s:ℤ)=rankTwelve m L s:=by
  rw [AZU m L s hshape]
  have hfast:AFW m L s=∑ r∈Finset.range m,rankRow m L s r:=by
    unfold AFW
    rw [IL.VJ]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' :=Finset.mem_range.mp hr
    have he:min r L=r:=min_eq_left (by omega)
    simp only [he,rankRow]
  have hrow (r:ℕ) (hr:r∈Finset.range m):
      2*(rankRow m L s r:ℤ)=sourceTwice L s r-
        (if r<m-min s (m/2) then 0 else removedTwice m L s ((m:ℤ)-r)):=by
    rw [FAQ m L s r (Finset.mem_range.mp hr) hshape]
    split_ifs<;>simp only [sourceTwice,removedTwice]<;>ring
  have hsum:2*(AFW m L s:ℤ)=
      (∑ r∈Finset.range m,sourceTwice L s r)-
        ∑ j∈Finset.range (min s (m/2)),removedTwice m L s (j+1):=by
    rw [hfast,Nat.cast_sum,Finset.mul_sum]
    rw [Finset.sum_congr rfl hrow,Finset.sum_sub_distrib,
      EPV m L s (min s (m/2)) (by omega)]
  have hh:=congrArg (fun z:ℤ=>6*z) hsum
  rw [mul_sub,FEL,EYZ] at hh
  unfold rankTwelve
  nlinarith only [hh]

end LD
end MergedPart1
section MergedPart2
namespace LD
open RCN100 ClosedRank
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def rankAffine (m s:ℕ) (L:ℤ):ℤ:=
  sourceTwelve m L s-AAL m L s (min s (m/2):ℕ)
def rankSlope (m s:ℕ):ℤ:=rankAffine m s 1-rankAffine m s 0
def CPJ (m s:ℕ):ℤ:=rankAffine m s 0

theorem DSH (m s:ℕ) (L:ℤ):
    rankAffine m s L=rankSlope m s*L+CPJ m s:=by
  unfold rankSlope CPJ rankAffine sourceTwelve AAL
  ring

theorem rank_formula (m L s:ℕ) (hshape:m+s≤L+1):
    12*(RCN119.ES m L s:ℤ)=rankSlope m s*L+CPJ m s:=by
  rw [FBK m L s hshape]
  exact DSH m s L

def countSlope (D s:ℕ):ℤ:=ECJ (D/131071) (D%131071) 131071 s
def WY (D s:ℕ):ℤ:=CSW (D/131071) (D%131071) 131071 s

theorem BII (D L s:ℕ) (hs:s<131071) (hsq:s≤D/131071) (hL:D/131071+1≤L):
    (AW D 131071 L s:ℤ)=countSlope D s*L+WY D s:=by
  have he:(D/131071)*131071+D%131071=D:=by have:=Nat.div_add_mod D 131071;omega
  simpa only [he,countSlope,WY] using ERG (D/131071) (D%131071)
    131071 L s (by decide) (Nat.mod_lt _ (by decide)) hs hsq hL

def marginA (D nu s R m mu:ℕ):ℤ:=
  12*(countSlope D s-countSlope (D-nu) (s-R))-
    262144*(rankSlope m s-rankSlope (m-mu) (s-R))
def marginB (D nu s R m mu:ℕ):ℤ:=
  12*countSlope (D-nu) (s-R)-262144*rankSlope (m-mu) (s-R)
def marginC (D nu s R m mu:ℕ):ℤ:=
  12*(WY D s-WY (D-nu) (s-R))-
    262144*(CPJ m s-CPJ (m-mu) (s-R))

theorem GHD (D nu L s T R m mu:ℕ)
    (hs:s<131071) (hR:R≤s) (hT:T≤L)
    (hsq:s≤D/131071) (hsq' :s-R≤(D-nu)/131071)
    (hL:D/131071+1≤L) (hL' :(D-nu)/131071+1≤L-T)
    (hm:m+s≤L+1) (hm' :(m-mu)+(s-R)≤L-T+1):
    marginA D nu s R m mu*L+marginB D nu s R m mu*T+marginC D nu s R m mu=
      12*((AW D 131071 L s:ℤ)-AW (D-nu) 131071 (L-T) (s-R))-
        262144*(12*(RCN119.ES m L s:ℤ)-12*RCN119.ES (m-mu) (L-T) (s-R)):=by
  rw [BII D L s hs hsq hL,
    BII (D-nu) (L-T) (s-R) (by omega) hsq' hL',
    rank_formula m L s hm,rank_formula (m-mu) (L-T) (s-R) hm',Nat.cast_sub hT]
  unfold marginA marginB marginC
  ring

theorem FOG (D nu L s T R m mu:ℕ)
    (hD:0<D) (hnu:0<nu) (hs:s<131071) (hR:R≤s) (hT:T≤L)
    (hsq:s≤D/131071) (hsq' :s-R≤(D-nu)/131071)
    (hL:D/131071+1≤L) (hL' :(D-nu)/131071+1≤L-T)
    (hm:m+s≤L+1) (hm' :(m-mu)+(s-R)≤L-T+1)
    (hmargin:0<marginA D nu s R m mu*L+marginB D nu s R m mu*T+marginC D nu s R m mu):
    AW (D-nu) 131071 (L-T) (s-R)+
      262144*(RCN119.ES m L s-RCN119.ES (m-mu) (L-T) (s-R))<
      AW D 131071 L s:=by
  have hh:=GHD D nu L s T R m mu hs hR hT hsq hsq' hL hL' hm hm'
  have hi:(AW (D-nu) 131071 (L-T) (s-R):ℤ)+
      262144*RCN119.ES m L s<
      (AW D 131071 L s:ℤ)+262144*RCN119.ES (m-mu) (L-T) (s-R):=by
    nlinarith only [hh,hmargin]
  apply EWT _ _ _ _ 262144 (DCH _ _ _ _ _ _ _ hD hnu)
  exact_mod_cast hi

end LD
end MergedPart2
section MergedPart3
namespace AP
open LD
open RCN100 MA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 20000

structure Band where
  R:ℕ
  B:ℕ
  T0:ℕ
  T1:ℕ
  count:ℕ
  deriving DecidableEq

structure Rectangle where
  lo:ℕ
  hi:ℕ
  alpha:ℕ
  beta:ℕ
  s:ℕ
  L0:ℕ
  L1:ℕ
  U:ℕ
  deriving DecidableEq

def tail (b:Band):ℕ:=(b.B+b.R-1)*181235+131071-1
def cutoff (b:Band) (d:Rectangle):ℕ:=
  d.alpha*181235-d.beta*min (d.hi-131071+1) ((b.B+b.R-1)*181235)
def lowerTotal (b:Band) (d:Rectangle) (T:ℕ):ℕ:=
  max (T+d.alpha+d.s) (max (cutoff b d/131071+1) (T+(cutoff b d-d.lo)/131071+1))
def total (b:Band) (d:Rectangle) (T:ℕ):ℕ:=
  if b.T0=b.T1 then d.L0 else ceilBlend b.T0 b.T1 d.L0 d.L1 T

def Shape (b:Band) (d:Rectangle):Prop:=
  b.T0≤b.T1∧b.R≤d.s∧d.s<131071∧131071≤d.lo∧d.lo≤d.hi∧
  d.hi≤tail b∧0<cutoff b d∧d.s≤cutoff b d/131071∧
  d.s-b.R≤(cutoff b d-d.lo)/131071∧
  lowerTotal b d b.T0≤d.L0∧lowerTotal b d b.T1≤d.L1

def rowGood (b:Band) (d:Rectangle) (mu:ℕ):Prop:=
  let m:=d.alpha-d.beta*(mu-1)
  let a:=marginA (cutoff b d) d.lo d.s b.R m mu
  let v:=marginB (cutoff b d) d.lo d.s b.R m mu
  let c:=marginC (cutoff b d) d.lo d.s b.R m mu
  max 0 (-a)<a*d.L0+v*b.T0+c∧max 0 (-a)<a*d.L1+v*b.T1+c

instance shapeDecidable (b:Band) (d:Rectangle):Decidable (Shape b d):=by
  unfold Shape
  infer_instance
instance rowGoodDecidable (b:Band) (d:Rectangle) (mu:ℕ):Decidable (rowGood b d mu):=by
  unfold rowGood
  infer_instance

def checkRows (b:Band) (d:Rectangle):ℕ→Bool
  | 0=>true
  | n+1=>checkRows b d n && decide (rowGood b d n)

theorem GMS (b:Band) (d:Rectangle) (n:ℕ) (hc:checkRows b d n=true):
    ∀mu<n,rowGood b d mu:=by
  induction n with
  | zero=>omega
  | succ n ih=>
    simp only [checkRows,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro mu hmu
    rcases Nat.lt_or_eq_of_le (show mu≤n by omega) with h | h
    · exact ih hc.1 mu h
    · simpa only [h] using hc.2

theorem total_lower (b:Band) (d:Rectangle) (T:ℕ) (hshape:Shape b d)
    (hT0:b.T0≤T) (hT1:T≤b.T1):lowerTotal b d T≤total b d T:=by
  rcases hshape with ⟨h01,_,_,_,_,_,_,_,_,hL0,hL1⟩
  unfold total
  split_ifs with he
  · have ht:T=b.T0:=by omega
    simpa only [ht] using hL0
  · have hstrict:b.T0<b.T1:=by omega
    simp only [lowerTotal,max_le_iff] at hL0 hL1 ⊢
    refine ⟨?_,?_,?_⟩
    · simpa only [Nat.add_assoc] using CDI b.T0 b.T1 d.L0 d.L1 T (d.alpha+d.s)
        hstrict hT0 hT1 (by omega) (by omega)
    · exact DRS _ _ _ _ _ _ hstrict hT0 hT1 hL0.2.1 hL1.2.1
    · simpa only [Nat.add_assoc] using CDI b.T0 b.T1 d.L0 d.L1 T
        ((cutoff b d-d.lo)/131071+1) hstrict hT0 hT1 (by omega) (by omega)

theorem total_upper (b:Band) (d:Rectangle) (T:ℕ) (hshape:Shape b d)
    (hT0:b.T0≤T) (hT1:T≤b.T1):total b d T≤max d.L0 d.L1:=by
  unfold total
  split_ifs with he
  · exact le_max_left _ _
  · exact GGM _ _ _ _ _ (by have:=hshape.1;omega) hT0 hT1

theorem GGP (b:Band) (d:Rectangle) (T mu:ℕ) (hshape:Shape b d)
    (hT0:b.T0≤T) (hT1:T≤b.T1) (hgood:rowGood b d mu):
    0<marginA (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*total b d T+
      marginB (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      marginC (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu:=by
  unfold rowGood at hgood
  unfold total
  split_ifs with he
  · have ht:T=b.T0:=by omega
    rw [ht]
    exact lt_of_le_of_lt (le_max_left _ _) hgood.1
  · have hstrict:b.T0<b.T1:=by have:=hshape.1;omega
    let p:=b.T1-T
    let q:=T-b.T0
    have hsum:p+q=b.T1-b.T0:=by dsimp [p,q];omega
    have ht:(p+q)*T=p*b.T0+q*b.T1:=by
      rw [hsum]
      exact CUO _ _ _ hT0 hT1
    have hb:=CKO b.T0 b.T1 d.L0 d.L1 T hstrict hT0 hT1
    apply DIG (p:ℤ) (q:ℤ) d.L0 d.L1 b.T0 b.T1
      (ceilBlend b.T0 b.T1 d.L0 d.L1 T) T _ _ _
      (by exact_mod_cast Nat.zero_le p) (by exact_mod_cast Nat.zero_le q)
      (by exact_mod_cast (show 0<p+q by omega)) (by exact_mod_cast ht) ?_ ?_ hgood.1 hgood.2
    · exact_mod_cast (show p*d.L0+q*d.L1≤(p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T by simpa only [hsum] using hb.1)
    · exact_mod_cast (show (p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T≤p*d.L0+q*d.L1+(p+q) by simpa only [hsum] using hb.2.le)

theorem FLA (b:Band) (d:Rectangle) (T:ℕ) (hshape:Shape b d)
    (hT0:b.T0≤T) (hT1:T≤b.T1) (hcheck:checkRows b d (b.B+b.R+1)=true):
    ∀mu≤b.B+b.R,AW (cutoff b d-d.lo) 131071 (total b d T-T) (d.s-b.R)+
      262144*AHJ d.alpha d.beta (total b d T) d.s T b.R mu<
        AW (cutoff b d) 131071 (total b d T) d.s:=by
  intro mu hmu
  have hmargin:=GGP b d T mu hshape hT0 hT1 (GMS _ _ _ hcheck mu (by omega))
  have hl:=total_lower b d T hshape hT0 hT1
  rcases hshape with ⟨_,hR,hs,hlo,_,_,hD,hsq,hsq',_,_⟩
  simp only [lowerTotal,max_le_iff] at hl
  exact FOG _ _ _ _ _ _ _ _ hD (by omega) hs hR (by omega)
    hsq hsq' hl.2.1 (by omega) (by omega) (by omega) hmargin

end
end AP
end MergedPart3
section MergedPart4
namespace AP
open LD
open scoped BigOperators
open MvPolynomial RCN100 RCN119 RCN122 RCN260 MA BY
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

def pair (b:Band) (d:Rectangle):DG:=
  ⟨262144,131071,181235,b.B,b.R,b.T1,d.U,d.s,max d.L0 d.L1⟩

def Valid (b:Band) (d:Rectangle):Prop:=
  Shape b d∧1≤b.R∧b.B<2130706433∧b.R<2130706433∧b.T1<2130706433∧
  cutoff b d≤131071*(d.U+1)∧
  (pair b d).mixedCost.y<2130706433∧(pair b d).mixedCost.r<2130706433∧
  (pair b d).mixedCost.z<2130706433∧
  GB.FU (pair b d)≤b.count∧
  checkRows b d (b.B+b.R+1)=true

instance validDecidable (b:Band) (d:Rectangle):Decidable (Valid b d):=by
  unfold Valid
  infer_instance



variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K



end
end AP
end MergedPart4
section MergedPart5
namespace AP
open LD
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def AX (b:Band):ℕ:=131071*b.B-b.R












variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K



end
end AP
end MergedPart5
section MergedPart6
namespace AP
open LD
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000

structure Cubic where
  c0:ℤ
  c1:ℤ
  c2:ℤ
  c3:ℤ

def Cubic.eval (p:Cubic) (x:ℤ):ℤ:=((p.c3*x+p.c2)*x+p.c1)*x+p.c0
def Cubic.deriv (p:Cubic) (x:ℤ):ℤ:=(3*p.c3*x+2*p.c2)*x+p.c1

theorem EOO (p:Cubic) (a b x:ℤ):
    (b-a)^3*p.eval x=p.eval a*(b-x)^3+
      (3*p.eval a+(b-a)*p.deriv a)*(b-x)^2*(x-a)+
      (3*p.eval b-(b-a)*p.deriv b)*(b-x)*(x-a)^2+p.eval b*(x-a)^3:=by
  unfold Cubic.eval Cubic.deriv
  ring

theorem GKO (p:Cubic) (a b x:ℤ)
    (ha:a≤x) (hb:x≤b) (h0:0<p.eval a) (h3:0<p.eval b)
    (h1:0≤3*p.eval a+(b-a)*p.deriv a)
    (h2:0≤3*p.eval b-(b-a)*p.deriv b):0<p.eval x:=by
  by_cases he:a=b
  · have hx:x=a:=by omega
    simpa only [hx] using h0
  have hw:0<b-a:=by omega
  have hu:0≤b-x:=by omega
  have hv:0≤x-a:=by omega
  have ht1:=mul_nonneg (mul_nonneg h1 (sq_nonneg (b-x))) hv
  have ht2:=mul_nonneg (mul_nonneg h2 hu) (sq_nonneg (x-a))
  have ht0:=mul_nonneg h0.le (pow_nonneg hu 3)
  have ht3:=mul_nonneg h3.le (pow_nonneg hv 3)
  have hid:=EOO p a b x
  have hp:0<(b-a)^3*p.eval x:=by
    by_cases hx:x=b
    · have hs:=mul_pos h3 (pow_pos (show 0<x-a by omega) 3)
      nlinarith only [hid,ht0,ht1,ht2,hs]
    · have hs:=mul_pos h0 (pow_pos (show 0<b-x by omega) 3)
      nlinarith only [hid,hs,ht1,ht2,ht3]
  exact pos_of_mul_pos_right hp (pow_nonneg hw.le 3)

def Cubic.Check (p:Cubic) (a b:ℕ):Prop:=
  b<a∨(0<p.eval a∧0<p.eval b∧
    0≤3*p.eval a+((b:ℤ)-a)*p.deriv a∧
    0≤3*p.eval b-((b:ℤ)-a)*p.deriv b)

instance cubicCheckDecidable (p:Cubic) (a b:ℕ):Decidable (p.Check a b):=by
  unfold Cubic.Check
  infer_instance

theorem Cubic.check_positive (p:Cubic) (a b x:ℕ) (hc:p.Check a b)
    (ha:a≤x) (hb:x≤b):0<p.eval x:=by
  rcases hc with h | ⟨h0,h3,h1,h2⟩
  · omega
  · exact GKO p a b x (by exact_mod_cast ha) (by exact_mod_cast hb) h0 h3 h1 h2

def AVK (base rate L s:ℤ):Cubic:=
  let a0:=s*(s+1)*((4*s+2)*L-s*s+5*s+2)
  let a1:= -2*(s+1)*(3*L*s-3*L+6*s-4)
  let a2:=6*(L+1)*(s+1)
  let a3:= -2*(s+1)
  ⟨a0+a1*base+a2*base^2+a3*base^3,
    -rate*(a1+2*a2*base+3*a3*base^2),
    rate^2*(a2+3*a3*base),-a3*rate^3⟩

theorem BZV (base rate L s x:ℤ):
    (AVK base rate L s).eval x=
      ClosedRank.sourceTwelve (base-rate*x) L s-
        ClosedRank.AAL (base-rate*x) L s s:=by
  unfold AVK Cubic.eval ClosedRank.sourceTwelve ClosedRank.AAL
  ring

def BDN (b:Band) (d:Rectangle) (T L:ℕ):Cubic:=
  let p:=AVK ((d.alpha:ℤ)+d.beta) d.beta L d.s
  let q:=AVK ((d.alpha:ℤ)+d.beta) ((d.beta:ℤ)+1) ((L:ℤ)-T) ((d.s:ℤ)-b.R)
  let c:=12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
    countSlope (cutoff b d-d.lo) (d.s-b.R)*T+
    WY (cutoff b d) d.s-WY (cutoff b d-d.lo) (d.s-b.R))
  ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩

theorem BMR (b:Band) (d:Rectangle) (T L mu:ℕ)
    (hmu:1≤mu) (hR:b.R≤d.s)
    (hmmu:mu≤d.alpha-d.beta*(mu-1))
    (hs:2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' :2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu):
    (BDN b d T L).eval mu=
      marginA (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*L+
      marginB (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      marginC (cutoff b d) d.lo d.s b.R (d.alpha-d.beta*(mu-1)) mu:=by
  let m:=d.alpha-d.beta*(mu-1)
  have hmcast:(m:ℤ)=(d.alpha:ℤ)+d.beta-(d.beta:ℤ)*mu:=by
    have hle:d.beta*(mu-1)≤d.alpha:=by omega
    have hh:(m:ℤ)+(d.beta:ℤ)*(mu-1:ℕ)=d.alpha:=by
      exact_mod_cast Nat.sub_add_cancel hle
    rw [Nat.cast_sub hmu,Nat.cast_one] at hh
    nlinarith only [hh]
  have hinner:(d.alpha:ℤ)+d.beta-((d.beta:ℤ)+1)*mu=(m-mu:ℕ):=by
    rw [Nat.cast_sub hmmu]
    nlinarith only [hmcast]
  have hk:min d.s (m/2)=d.s:=min_eq_left (by omega)
  have hk' :min (d.s-b.R) ((m-mu)/2)=d.s-b.R:=min_eq_left (by omega)
  have ho:=DSH m d.s L
  have hi:=DSH (m-mu) (d.s-b.R) ((L:ℤ)-T)
  simp only [rankAffine,hk,hk'] at ho hi
  have he:(BDN b d T L).eval mu=
      12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
        countSlope (cutoff b d-d.lo) (d.s-b.R)*T+WY (cutoff b d) d.s-
        WY (cutoff b d-d.lo) (d.s-b.R))-
      262144*((AVK ((d.alpha:ℤ)+d.beta) d.beta L d.s).eval mu-
        (AVK ((d.alpha:ℤ)+d.beta) ((d.beta:ℤ)+1) ((L:ℤ)-T) ((d.s:ℤ)-b.R)).eval mu):=by
    unfold BDN Cubic.eval
    ring
  rw [he,BZV,BZV,←hmcast,hinner,←Nat.cast_sub hR,ho,hi]
  unfold marginA marginB marginC
  dsimp only [m] at*
  ring

end AP
end MergedPart6
section MergedPart7
namespace AP
open LD
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

structure FastWitness where
  normalEnd:ℕ
  firstExact:ℕ
  lastExact:ℕ

def checkRange (b:Band) (d:Rectangle) (start:ℕ):ℕ→Bool
  | 0=>true
  | n+1=>checkRange b d start n && decide (rowGood b d (start+n))

theorem FDY (b:Band) (d:Rectangle) (start n:ℕ)
    (hc:checkRange b d start n=true) (mu:ℕ) (h0:start≤mu) (h1:mu<start+n):rowGood b d mu:=by
  induction n with
  | zero=>omega
  | succ n ih=>
    simp only [checkRange,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases hmu:mu<start+n
    · exact ih hc.1 hmu
    · have he:mu=start+n:=by omega
      simpa only [he] using hc.2

def corners (b:Band) (d:Rectangle) (a z:ℕ):Prop:=
  (BDN b d b.T0 d.L0).Check a z∧
  (BDN b d b.T0 (d.L0+1)).Check a z∧
  (BDN b d b.T1 d.L1).Check a z∧
  (BDN b d b.T1 (d.L1+1)).Check a z

instance cornersDecidable (b:Band) (d:Rectangle) (a z:ℕ):Decidable (corners b d a z):=by
  unfold corners
  infer_instance

theorem EMJ (b:Band) (d:Rectangle) (a z mu:ℕ)
    (hR:b.R≤d.s) (hc:corners b d a z) (ha:a≤mu) (hz:mu≤z) (hmu:1≤mu)
    (hm:mu≤d.alpha-d.beta*(mu-1))
    (hs:2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' :2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu):rowGood b d mu:=by
  have h0:=Cubic.check_positive _ _ _ mu hc.1 ha hz
  have h0' :=Cubic.check_positive _ _ _ mu hc.2.1 ha hz
  have h1:=Cubic.check_positive _ _ _ mu hc.2.2.1 ha hz
  have h1' :=Cubic.check_positive _ _ _ mu hc.2.2.2 ha hz
  rw [BMR b d b.T0 d.L0 mu hmu hR hm hs hs'] at h0
  rw [BMR b d b.T0 (d.L0+1) mu hmu hR hm hs hs'] at h0'
  rw [BMR b d b.T1 d.L1 mu hmu hR hm hs hs'] at h1
  rw [BMR b d b.T1 (d.L1+1) mu hmu hR hm hs hs'] at h1'
  simp only [Nat.cast_add,Nat.cast_one] at h0' h1'
  unfold rowGood
  constructor
  · exact max_lt h0 (by nlinarith only [h0'])
  · exact max_lt h1 (by nlinarith only [h1'])

def FastRows (b:Band) (d:Rectangle) (w:FastWitness):Prop:=
  1≤w.firstExact∧w.firstExact≤w.lastExact∧w.lastExact≤w.normalEnd∧w.normalEnd≤b.B+b.R∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd∧
  corners b d 1 (w.firstExact-1)∧corners b d (w.lastExact+1) w.normalEnd∧
  rowGood b d 0∧checkRange b d w.firstExact (w.lastExact+1-w.firstExact)=true∧
  checkRange b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true

instance fastRowsDecidable (b:Band) (d:Rectangle) (w:FastWitness):Decidable (FastRows b d w):=by
  unfold FastRows
  infer_instance

theorem GDZ (b:Band) (d:Rectangle) (n:ℕ)
    (h: ∀mu<n,rowGood b d mu):checkRows b d n=true:=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [checkRows,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨ih (fun mu hm=>h mu (by omega)),h n (by omega)⟩

theorem FKM (b:Band) (d:Rectangle) (w:FastWitness)
    (hR:b.R≤d.s) (h:FastRows b d w):checkRows b d (b.B+b.R+1)=true:=by
  rcases h with ⟨hfirst,hlast,hend,hmax,hlevel,hs,hs',hleft,hright,hzero,hcenter,htail⟩
  apply GDZ
  intro mu hmu
  by_cases hz:mu=0
  · simpa only [hz] using hzero
  have hmu1:1≤mu:=by omega
  by_cases hn:mu≤w.normalEnd
  · have hmono:d.alpha-d.beta*(w.normalEnd-1)≤d.alpha-d.beta*(mu-1):=
      Nat.sub_le_sub_left (Nat.mul_le_mul_left d.beta (Nat.sub_le_sub_right hn 1)) d.alpha
    have hm:mu≤d.alpha-d.beta*(mu-1):=by omega
    have hms:2*d.s≤d.alpha-d.beta*(mu-1):=by omega
    have hms' :2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu:=by omega
    by_cases hbefore:mu<w.firstExact
    · exact EMJ b d 1 (w.firstExact-1) mu hR hleft hmu1 (by omega) hmu1 hm hms hms'
    by_cases hwithin:mu≤w.lastExact
    · exact FDY _ _ _ _ hcenter mu (by omega) (by omega)
    · exact EMJ b d (w.lastExact+1) w.normalEnd mu hR hright (by omega) hn hmu1 hm hms hms'
  · exact FDY _ _ _ _ htail mu (by omega) (by omega)

def Header (b:Band) (d:Rectangle):Prop:=
  Shape b d∧1≤b.R∧b.B<2130706433∧b.R<2130706433∧b.T1<2130706433∧
  cutoff b d≤131071*(d.U+1)∧
  (pair b d).mixedCost.y<2130706433∧(pair b d).mixedCost.r<2130706433∧
  (pair b d).mixedCost.z<2130706433∧GB.FU (pair b d)≤b.count

def FastValid (b:Band) (dw:Rectangle × FastWitness):Prop:=Header b dw.1∧FastRows b dw.1 dw.2

instance fastValidDecidable (b:Band) (dw:Rectangle × FastWitness):Decidable (FastValid b dw):=by
  unfold FastValid Header
  infer_instance









end
end AP
end MergedPart7
section MergedPart8
namespace AN
open AP
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 40000

structure Profile where
  alpha:ℕ
  beta:ℕ
  s:ℕ
structure Entry where
  hi:ℕ
  profile:ℕ
  L0:ℕ
  deltaL:ℕ
  witness:ℕ

structure Layout where
  hiBase:ℕ
  profileBase:ℕ
  lengthBase:ℕ
  deltaBase:ℕ













open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance:DecidableEq K:=Classical.decEq K



end
end AN
end MergedPart8

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace LD
open RCN100 ClosedRank MA
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem GGZ (D w L s:ℕ):
    countSlopeAt D w L s=AW (D+1) w L s-AW D w L s:=by
  rw [AAH,AAH,countSlopeAt]
  rw [← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_tsub_distrib]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Nat.mul_sub]
    · intro j _
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.le_succ D) _)
  · intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.le_succ D) _)

def tanMarginA (Dh k E s R m mu:ℕ):ℤ:=
  12*(countSlope Dh s+k*(countSlope (Dh+1) s-countSlope Dh s)-countSlope E (s-R))-
    262144*(rankSlope m s-rankSlope (m-mu) (s-R))
def tanMarginB (E s R m mu:ℕ):ℤ:=
  12*countSlope E (s-R)-262144*rankSlope (m-mu) (s-R)
def tanMarginC (Dh k E s R m mu:ℕ):ℤ:=
  12*(WY Dh s+k*(WY (Dh+1) s-WY Dh s)-
      WY E (s-R))-
    262144*(CPJ m s-CPJ (m-mu) (s-R))

theorem FIZ (Dh k E L s T R m mu:ℕ)
    (hs:s<131071) (hR:R≤s) (hT:T≤L)
    (hsq:s≤Dh/131071) (hsq1:s≤(Dh+1)/131071) (hsq' :s-R≤E/131071)
    (hL:(Dh+1)/131071+1≤L) (hL' :E/131071+1≤L-T)
    (hm:m+s≤L+1) (hm' :(m-mu)+(s-R)≤L-T+1):
    tanMarginA Dh k E s R m mu*L+tanMarginB E s R m mu*T+tanMarginC Dh k E s R m mu=
      12*((AW Dh 131071 L s:ℤ)+
          k*((AW (Dh+1) 131071 L s:ℤ)-AW Dh 131071 L s)-
          AW E 131071 (L-T) (s-R))-
        262144*(12*(RCN119.ES m L s:ℤ)-
          12*RCN119.ES (m-mu) (L-T) (s-R)):=by
  have hL0:Dh/131071+1≤L:=le_trans (Nat.add_le_add_right (Nat.div_le_div_right (Nat.le_succ Dh)) 1) hL
  rw [BII Dh L s hs hsq hL0,BII (Dh+1) L s hs hsq1 hL,
    BII E (L-T) (s-R) (by omega) hsq' hL',
    rank_formula m L s hm,rank_formula (m-mu) (L-T) (s-R) hm',Nat.cast_sub hT]
  unfold tanMarginA tanMarginB tanMarginC
  ring

theorem EUW (Dh k E L s T R m mu:ℕ)
    (hs:s<131071) (hR:R≤s) (hT:T≤L)
    (hsq:s≤Dh/131071) (hsq1:s≤(Dh+1)/131071) (hsq' :s-R≤E/131071)
    (hL:(Dh+1)/131071+1≤L) (hL' :E/131071+1≤L-T)
    (hm:m+s≤L+1) (hm' :(m-mu)+(s-R)≤L-T+1)
    (hmargin:0<tanMarginA Dh k E s R m mu*L+tanMarginB E s R m mu*T+tanMarginC Dh k E s R m mu)
    (hr:RCN119.ES (m-mu) (L-T) (s-R)≤RCN119.ES m L s):
    AW E 131071 (L-T) (s-R)+
      262144*(RCN119.ES m L s-RCN119.ES (m-mu) (L-T) (s-R))<
      AW Dh 131071 L s+countSlopeAt Dh 131071 L s*k:=by
  have hh:=FIZ Dh k E L s T R m mu hs hR hT hsq hsq1 hsq' hL hL' hm hm'
  have hmono:AW Dh 131071 L s≤AW (Dh+1) 131071 L s:=
    CBJ 131071 L s (Nat.le_succ Dh)
  rw [GGZ]
  have hslope:((AW (Dh+1) 131071 L s-AW Dh 131071 L s:ℕ):ℤ)=
      (AW (Dh+1) 131071 L s:ℤ)-AW Dh 131071 L s:=Nat.cast_sub hmono

  have hi:(AW E 131071 (L-T) (s-R):ℤ)+262144*RCN119.ES m L s<
      (AW Dh 131071 L s:ℤ)+
        ((AW (Dh+1) 131071 L s:ℤ)-AW Dh 131071 L s)*k+
        262144*RCN119.ES (m-mu) (L-T) (s-R):=by
    nlinarith only [hh,hmargin]
  have hle:262144*RCN119.ES (m-mu) (L-T) (s-R)≤262144*RCN119.ES m L s:=
    Nat.mul_le_mul_left _ hr
  have hfin:((AW E 131071 (L-T) (s-R)+
      262144*(RCN119.ES m L s-RCN119.ES (m-mu) (L-T) (s-R)):ℕ):ℤ)<
      ((AW Dh 131071 L s+
        (AW (Dh+1) 131071 L s-AW Dh 131071 L s)*k:ℕ):ℤ):=by
    rw [Nat.mul_sub]
    push_cast
    rw [hslope,Nat.cast_sub hle]
    push_cast
    linarith
  exact Nat.cast_lt.mp hfin

end LD
end MergedPart0
section MergedPart1
namespace AP
open LD
open scoped BigOperators
open MvPolynomial RCN100 RCN119 RCN122 RCN260 MA BY
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 20000

def hiRect (d:Rectangle):Rectangle:={d with lo:=d.hi}

def cutAt (b:Band) (d:Rectangle) (nu:ℕ):ℕ:=
  d.alpha*181235-d.beta*min (nu-131071+1) ((b.B+b.R-1)*181235)

def tanK (b:Band) (d:Rectangle):ℕ:=cutAt b d d.lo-cutoff b d
def tanE (b:Band) (d:Rectangle):ℕ:=cutAt b d d.lo-d.lo

def tanLower (b:Band) (d:Rectangle) (T:ℕ):ℕ:=
  max ((cutoff b d+1)/131071+1) (T+tanE b d/131071+1)

def tanRowGood (b:Band) (d:Rectangle) (mu:ℕ):Prop:=
  let m:=d.alpha-d.beta*(mu-1)
  let a:=tanMarginA (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
  let v:=tanMarginB (tanE b d) d.s b.R m mu
  let c:=tanMarginC (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
  max 0 (-a)<a*d.L0+v*b.T0+c∧max 0 (-a)<a*d.L1+v*b.T1+c

instance tanRowGoodDecidable (b:Band) (d:Rectangle) (mu:ℕ):Decidable (tanRowGood b d mu):=by
  unfold tanRowGood
  infer_instance

def checkTanRows (b:Band) (d:Rectangle):ℕ→Bool
  | 0=>true
  | n+1=>checkTanRows b d n && decide (tanRowGood b d n)

theorem FPN (b:Band) (d:Rectangle) (n:ℕ) (hc:checkTanRows b d n=true):
    ∀mu<n,tanRowGood b d mu:=by
  induction n with
  | zero=>omega
  | succ n ih=>
    simp only [checkTanRows,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro mu hmu
    rcases Nat.lt_or_eq_of_le (show mu≤n by omega) with h | h
    · exact ih hc.1 mu h
    · simpa only [h] using hc.2

def WideShape (b:Band) (d:Rectangle):Prop:=
  Shape b (hiRect d)∧131071≤d.lo∧d.lo≤d.hi∧d.hi<cutoff b d∧
  d.s≤(cutoff b d+1)/131071∧d.s-b.R≤tanE b d/131071∧
  tanLower b d b.T0≤d.L0∧tanLower b d b.T1≤d.L1

instance wideShapeDecidable (b:Band) (d:Rectangle):Decidable (WideShape b d):=by
  unfold WideShape Shape
  infer_instance




theorem GHL (b:Band) (d:Rectangle) (T:ℕ) (hshape:WideShape b d)
    (hT0:b.T0≤T) (hT1:T≤b.T1):tanLower b d T≤total b d T:=by
  rcases hshape with ⟨hs,_,_,_,_,_,hL0,hL1⟩
  have h01:=hs.1
  unfold total
  split_ifs with he
  · have ht:T=b.T0:=by omega
    simpa only [ht] using hL0
  · have hstrict:b.T0<b.T1:=by omega
    simp only [tanLower,max_le_iff] at hL0 hL1 ⊢
    refine ⟨?_,?_⟩
    · exact DRS _ _ _ _ _ _ hstrict hT0 hT1 hL0.1 hL1.1
    · simpa only [Nat.add_assoc] using CDI b.T0 b.T1 d.L0 d.L1 T
        (tanE b d/131071+1) hstrict hT0 hT1 (by omega) (by omega)

theorem FHT (b:Band) (d:Rectangle) (T mu:ℕ) (hshape:WideShape b d)
    (hT0:b.T0≤T) (hT1:T≤b.T1) (hgood:tanRowGood b d mu):
    0<tanMarginA (cutoff b d) (tanK b d) (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu*total b d T+
      tanMarginB (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      tanMarginC (cutoff b d) (tanK b d) (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu:=by
  unfold tanRowGood at hgood
  unfold total
  split_ifs with he
  · have ht:T=b.T0:=by omega
    rw [ht]
    exact lt_of_le_of_lt (le_max_left _ _) hgood.1
  · have hstrict:b.T0<b.T1:=by have:=hshape.1.1;omega
    let p:=b.T1-T
    let q:=T-b.T0
    have hsum:p+q=b.T1-b.T0:=by dsimp [p,q];omega
    have ht:(p+q)*T=p*b.T0+q*b.T1:=by
      rw [hsum]
      exact CUO _ _ _ hT0 hT1
    have hb:=CKO b.T0 b.T1 d.L0 d.L1 T hstrict hT0 hT1
    apply DIG (p:ℤ) (q:ℤ) d.L0 d.L1 b.T0 b.T1
      (ceilBlend b.T0 b.T1 d.L0 d.L1 T) T _ _ _
      (by exact_mod_cast Nat.zero_le p) (by exact_mod_cast Nat.zero_le q)
      (by exact_mod_cast (show 0<p+q by omega)) (by exact_mod_cast ht) ?_ ?_ hgood.1 hgood.2
    · exact_mod_cast (show p*d.L0+q*d.L1≤(p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T by simpa only [hsum] using hb.1)
    · exact_mod_cast (show (p+q)*ceilBlend b.T0 b.T1 d.L0 d.L1 T≤p*d.L0+q*d.L1+(p+q) by simpa only [hsum] using hb.2.le)

theorem cutAt_affine (b:Band) (d:Rectangle) (nu:ℕ) (hshape:WideShape b d)
    (hlo:d.lo≤nu) (hhi:nu≤d.hi):
    cutAt b d nu=cutoff b d+d.beta*(d.hi-nu):=by
  have htail:d.hi≤tail b:=hshape.1.2.2.2.2.2.1
  have hDh:d.hi<cutoff b d:=hshape.2.2.2.1
  have hw:131071≤d.lo:=hshape.2.1
  unfold cutAt
  unfold cutoff at hDh ⊢
  unfold tail at htail
  have hm1:min (nu-131071+1) ((b.B+b.R-1)*181235)=nu-131071+1:=min_eq_left (by omega)
  have hm2:min (d.hi-131071+1) ((b.B+b.R-1)*181235)=d.hi-131071+1:=min_eq_left (by omega)
  rw [hm1]
  rw [hm2] at hDh ⊢
  have hsplit:d.beta*(d.hi-131071+1)=d.beta*(nu-131071+1)+d.beta*(d.hi-nu):=by
    have hx:d.hi-131071+1=(nu-131071+1)+(d.hi-nu):=by omega
    rw [hx,Nat.mul_add]
  rw [hsplit] at hDh ⊢
  generalize d.beta*(nu-131071+1)=P at hDh ⊢
  generalize d.beta*(d.hi-nu)=Q at hDh ⊢
  omega

theorem tanK_eq (b:Band) (d:Rectangle) (hshape:WideShape b d):
    tanK b d=d.beta*(d.hi-d.lo):=by
  unfold tanK
  rw [cutAt_affine b d d.lo hshape le_rfl hshape.2.2.1]
  omega

theorem tanE_eq (b:Band) (d:Rectangle) (hshape:WideShape b d):
    tanE b d=(cutoff b d-d.hi)+(d.beta+1)*(d.hi-d.lo):=by
  have hDh:=hshape.2.2.2.1
  have hlh:=hshape.2.2.1
  unfold tanE
  rw [cutAt_affine b d d.lo hshape le_rfl hlh]
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem wide_rows (b:Band) (d:Rectangle) (T nu:ℕ) (hshape:WideShape b d)
    (hT0:b.T0≤T) (hT1:T≤b.T1)
    (hcheck:checkRows b (hiRect d) (b.B+b.R+1)=true)
    (htan:checkTanRows b d (b.B+b.R+1)=true)
    (hlo:d.lo≤nu) (hhi:nu≤d.hi):
    ∀mu≤b.B+b.R,AW (cutAt b d nu-nu) 131071 (total b d T-T) (d.s-b.R)+
      262144*AHJ d.alpha d.beta (total b d T) d.s T b.R mu<
        AW (cutAt b d nu) 131071 (total b d T) d.s:=by
  intro mu hmu
  have hcut:=cutAt_affine b d nu hshape hlo hhi
  have hDh:d.hi<cutoff b d:=hshape.2.2.2.1
  have hshape' :=hshape
  rcases hshape' with ⟨hS,hw,hlh,_,hsq1,hsqE,_,_⟩
  have hR:b.R≤d.s:=hS.2.1
  have hs:d.s<131071:=hS.2.2.1
  have hsq:d.s≤cutoff b d/131071:=hS.2.2.2.2.2.2.2.1
  have hl:=total_lower b (hiRect d) T hS hT0 hT1
  have hLa:T+d.alpha+d.s≤total b d T:=(le_max_left _ _).trans hl
  have htl:=GHL b d T hshape hT0 hT1
  have hLt1:(cutoff b d+1)/131071+1≤total b d T:=(le_max_left _ _).trans htl
  have hLt2:T+tanE b d/131071+1≤total b d T:=(le_max_right _ _).trans htl
  set m:=d.alpha-d.beta*(mu-1) with hmdef
  set L:=total b d T with hLdef
  have hTL:T≤L:=by omega
  have hmL:m≤d.alpha:=Nat.sub_le _ _
  by_cases hr:RCN119.ES (m-mu) (L-T) (d.s-b.R)≤RCN119.ES m L d.s
  · have hHi:AW (cutoff b d-d.hi) 131071 (L-T) (d.s-b.R)+
        262144*(RCN119.ES m L d.s-RCN119.ES (m-mu) (L-T) (d.s-b.R))<
        AW (cutoff b d) 131071 L d.s:=
      FLA b (hiRect d) T hS hT0 hT1 hcheck mu hmu
    have hLo:=EUW (cutoff b d) (tanK b d) (tanE b d) L d.s T b.R m mu
      hs hR hTL hsq hsq1 hsqE hLt1 (by omega) (by omega) (by omega)
      (FHT b d T mu hshape hT0 hT1 (FPN _ _ _ htan mu (by omega))) hr
    rw [tanK_eq b d hshape,tanE_eq b d hshape] at hLo
    have hE:cutAt b d nu-nu=(cutoff b d-d.hi)+(d.beta+1)*(d.hi-nu):=by
      rw [hcut,Nat.add_mul,Nat.one_mul];omega
    show AW (cutAt b d nu-nu) 131071 (L-T) (d.s-b.R)+
        262144*(RCN119.ES m L d.s-RCN119.ES (m-mu) (L-T) (d.s-b.R))<
        AW (cutAt b d nu) 131071 L d.s
    rw [hE,hcut]
    exact GOT 131071 L d.s T b.R _ d.beta (cutoff b d) (cutoff b d-d.hi) (d.hi-d.lo)
      (d.hi-nu) (by omega) hHi hLo
  · show AW (cutAt b d nu-nu) 131071 (L-T) (d.s-b.R)+
        262144*(RCN119.ES m L d.s-RCN119.ES (m-mu) (L-T) (d.s-b.R))<
        AW (cutAt b d nu) 131071 L d.s
    have hzero:RCN119.ES m L d.s-RCN119.ES (m-mu) (L-T) (d.s-b.R)=0:=by
      omega
    rw [hzero,Nat.mul_zero,Nat.add_zero]
    have hpos:0<cutAt b d nu:=by rw [hcut];omega
    exact DCH (cutAt b d nu) 131071 L d.s nu T b.R hpos (by omega)

def WideValid (b:Band) (d:Rectangle):Prop:=
  WideShape b d∧1≤b.R∧b.B<2130706433∧b.R<2130706433∧b.T1<2130706433∧
  cutAt b d d.lo≤131071*(d.U+1)∧
  (pair b d).mixedCost.y<2130706433∧(pair b d).mixedCost.r<2130706433∧
  (pair b d).mixedCost.z<2130706433∧
  GB.FU (pair b d)≤b.count∧
  checkRows b (hiRect d) (b.B+b.R+1)=true∧checkTanRows b d (b.B+b.R+1)=true

instance wideValidDecidable (b:Band) (d:Rectangle):Decidable (WideValid b d):=by
  unfold WideValid
  infer_instance

theorem GUA (b:Band) (d:Rectangle) (T nu:ℕ) (hshape:WideShape b d)
    (hT0:b.T0≤T) (hT1:T≤b.T1)
    (hcheck:checkRows b (hiRect d) (b.B+b.R+1)=true)
    (htan:checkTanRows b d (b.B+b.R+1)=true)
    (hlo:d.lo≤nu) (hhi:min nu (tail b)≤d.hi):
    ∀mu≤b.B+b.R,AW (cutAt b d nu-nu) 131071 (total b d T-T) (d.s-b.R)+
      262144*AHJ d.alpha d.beta (total b d T) d.s T b.R mu<
        AW (cutAt b d nu) 131071 (total b d T) d.s:=by
  by_cases hn:nu≤d.hi
  · exact wide_rows b d T nu hshape hT0 hT1 hcheck htan hlo hn
  · have htail:d.hi≤tail b:=hshape.1.2.2.2.2.2.1
    have hht:tail b≤d.hi:=by
      have:min nu (tail b)=tail b:=min_eq_right (by omega)
      omega
    have heq:cutAt b d nu=cutAt b d d.hi:=by
      unfold cutAt
      unfold tail at htail hht
      rw [min_eq_right (show (b.B+b.R-1)*181235≤nu-131071+1 by omega),
        min_eq_right (show (b.B+b.R-1)*181235≤d.hi-131071+1 by omega)]
    have hrows:=wide_rows b d T d.hi hshape hT0 hT1 hcheck htan hshape.2.2.1 le_rfl
    rw [heq]
    exact CYP (by omega) hrows

variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance wideRectDecEqK:DecidableEq K:=Classical.decEq K

set_option maxRecDepth 1000000 in
theorem BNW (b:Band) (d:Rectangle) (hvalid:WideValid b d)
    {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T b.R)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:b.R≤wt RCN156.BE F.val)
    (hB:wt RCN156.BC F.val≤b.B)
    (hT0:b.T0≤T) (hT1:T≤b.T1) (hlo:d.lo≤nu) (hhi:min nu (tail b)≤d.hi)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤b.count:=by
  classical
  rcases hvalid with ⟨hshape,hRpos,hBchar,hRchar,hTchar,hU,hgY,hgR,hgZ,hprice,hcheck,htan⟩
  have hF:=RCN167.KR H F.val F.property
  let Delta:=RCN140.regularSeeds H selected Gamma F
  have hsub:Delta⊆Gamma:=RCN140.ACS H selected Gamma F
  have hsol: ∀gamma∈Delta,BM K (selected gamma) gamma F.val=0:=by
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2.1
  have hreg: ∀gamma∈Delta,BM K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F.val)≠0:=by
    intro gamma hg
    exact (Finset.mem_filter.mp hg).2.2
  have hrows:=GUA b d T nu hshape hT0 hT1 hcheck htan hlo hhi
  have hS:=hshape.1
  have hRs:b.R≤d.s:=hS.2.1
  have hw:131071≤d.lo:=hshape.2.1
  have hl:=total_lower b (hiRect d) T hS hT0 hT1
  have hLa:T+d.alpha+d.s≤total b d T:=(le_max_left _ _).trans hl
  have hTL:T≤total b d T:=by omega
  have hupper:total b d T≤max d.L0 d.L1:=total_upper b (hiRect d) T hS hT0 hT1
  have hDle:cutAt b d nu≤cutAt b d d.lo:=
    EUG d.alpha d.beta 131071 b.B b.R 181235 hlo
  have hDpos:0<cutAt b d nu:=by
    by_cases hn:nu≤d.hi
    · rw [cutAt_affine b d nu hshape hlo hn];have:=hshape.2.2.2.1;omega
    · have htail:d.hi≤tail b:=hS.2.2.2.2.2.1
      have hht:tail b≤d.hi:=by
        have:min nu (tail b)=tail b:=min_eq_right (by omega)
        omega
      have heq:cutAt b d nu=cutAt b d d.hi:=by
        unfold cutAt
        unfold tail at htail hht
        rw [min_eq_right (show (b.B+b.R-1)*181235≤nu-131071+1 by omega),
          min_eq_right (show (b.B+b.R-1)*181235≤d.hi-131071+1 by omega)]
      rw [heq,cutAt_affine b d d.hi hshape hshape.2.2.1 le_rfl];have:=hshape.2.2.2.1;omega
  obtain ⟨Q,hQ,hrel,hzero⟩:=DTT K
    (D:=cutAt b d nu) (L:=total b d T) (s:=d.s) (nu:=nu) (B:=b.B)
    F.val hF.1 hF.2.2 hbox hTL hRs hcode htotal hslope hB nodes u0 u1 d.alpha d.beta 181235
    (by omega) hDpos le_rfl
    (by simpa only [hcard] using hrows)
    selected Delta (fun gamma hg=>hdegree gamma (hsub hg)) hsol hreg
    (fun gamma hg=>hagreement gamma (hsub hg))
  have hFY:F.val.degreeOf 1≤b.B:=by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw:=(MvPolynomial.le_weightedTotalDegree RCN156.BC he).trans hB
    rw [RCN081.weight_fin4] at hw
    simp [RCN156.BC] at hw
    omega
  have hFR:F.val.degreeOf 2≤b.R:=MvPolynomial.degreeOf_le_iff.mpr (fun e he=>(hbox he).2.1)
  have hFZ:F.val.degreeOf 3≤b.T1:=MvPolynomial.degreeOf_le_iff.mpr
    (fun e he=>by have:=(hbox he).1;omega)
  have hQY:Q.degreeOf 1≤d.U:=MvPolynomial.degreeOf_le_iff.mpr
    (fun e he=>by have:=(hQ he).2.2;omega)
  have hQR:Q.degreeOf 2≤d.s:=MvPolynomial.degreeOf_le_iff.mpr (fun e he=>(hQ he).2.1)
  have hQZ:Q.degreeOf 3≤max d.L0 d.L1:=MvPolynomial.degreeOf_le_iff.mpr
    (fun e he=>by have:=(hQ he).1;omega)
  apply le_trans ?_ hprice
  exact GB.ZF
    (pair b d) H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
    hRpos hBchar hRchar hTchar hgY hgR hgZ
    selected Gamma (Finset.univ:Finset I) nodes u0 u1 nodes.injective.injOn
    (by simpa only [pair,Finset.card_univ] using hcard)
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    hdegree hagreement (by simpa only [pair,DG.errors,Nat.reduceSub] using hno) hzero

end
end AP
end MergedPart1
section MergedPart2
namespace AP
open LD
open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000











variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance wideCoverDecEqK:DecidableEq K:=Classical.decEq K



end
end AP
end MergedPart2
section MergedPart3
namespace AP
open LD
open RCN100 ClosedRank MA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

def APE (b:Band) (d:Rectangle) (T L:ℕ):Cubic:=
  let p:=AVK ((d.alpha:ℤ)+d.beta) d.beta L d.s
  let q:=AVK ((d.alpha:ℤ)+d.beta) ((d.beta:ℤ)+1) ((L:ℤ)-T) ((d.s:ℤ)-b.R)
  let c:=12*((countSlope (cutoff b d) d.s+
        (tanK b d:ℤ)*(countSlope (cutoff b d+1) d.s-countSlope (cutoff b d) d.s)-
        countSlope (tanE b d) (d.s-b.R))*L+
      countSlope (tanE b d) (d.s-b.R)*T+
      WY (cutoff b d) d.s+
        (tanK b d:ℤ)*(WY (cutoff b d+1) d.s-WY (cutoff b d) d.s)-
      WY (tanE b d) (d.s-b.R))
  ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩

theorem AZB (b:Band) (d:Rectangle) (T L mu:ℕ)
    (hmu:1≤mu) (hR:b.R≤d.s)
    (hmmu:mu≤d.alpha-d.beta*(mu-1))
    (hs:2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' :2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu):
    (APE b d T L).eval mu=
      tanMarginA (cutoff b d) (tanK b d) (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu*L+
      tanMarginB (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu*T+
      tanMarginC (cutoff b d) (tanK b d) (tanE b d) d.s b.R (d.alpha-d.beta*(mu-1)) mu:=by
  let m:=d.alpha-d.beta*(mu-1)
  have hmcast:(m:ℤ)=(d.alpha:ℤ)+d.beta-(d.beta:ℤ)*mu:=by
    have hle:d.beta*(mu-1)≤d.alpha:=by omega
    have hh:(m:ℤ)+(d.beta:ℤ)*(mu-1:ℕ)=d.alpha:=by
      exact_mod_cast Nat.sub_add_cancel hle
    rw [Nat.cast_sub hmu,Nat.cast_one] at hh
    nlinarith only [hh]
  have hinner:(d.alpha:ℤ)+d.beta-((d.beta:ℤ)+1)*mu=(m-mu:ℕ):=by
    rw [Nat.cast_sub hmmu]
    nlinarith only [hmcast]
  have hk:min d.s (m/2)=d.s:=min_eq_left (by omega)
  have hk' :min (d.s-b.R) ((m-mu)/2)=d.s-b.R:=min_eq_left (by omega)
  have ho:=DSH m d.s L
  have hi:=DSH (m-mu) (d.s-b.R) ((L:ℤ)-T)
  simp only [rankAffine,hk,hk'] at ho hi
  have he:(APE b d T L).eval mu=
      12*((countSlope (cutoff b d) d.s+
          (tanK b d:ℤ)*(countSlope (cutoff b d+1) d.s-countSlope (cutoff b d) d.s)-
          countSlope (tanE b d) (d.s-b.R))*L+
        countSlope (tanE b d) (d.s-b.R)*T+
        WY (cutoff b d) d.s+
          (tanK b d:ℤ)*(WY (cutoff b d+1) d.s-WY (cutoff b d) d.s)-
        WY (tanE b d) (d.s-b.R))-
      262144*((AVK ((d.alpha:ℤ)+d.beta) d.beta L d.s).eval mu-
        (AVK ((d.alpha:ℤ)+d.beta) ((d.beta:ℤ)+1) ((L:ℤ)-T) ((d.s:ℤ)-b.R)).eval mu):=by
    unfold APE Cubic.eval
    ring
  rw [he,BZV,BZV,←hmcast,hinner,←Nat.cast_sub hR,ho,hi]
  unfold tanMarginA tanMarginB tanMarginC
  dsimp only [m] at*
  ring

def tanCorners (b:Band) (d:Rectangle) (a z:ℕ):Prop:=
  (APE b d b.T0 d.L0).Check a z∧
  (APE b d b.T0 (d.L0+1)).Check a z∧
  (APE b d b.T1 d.L1).Check a z∧
  (APE b d b.T1 (d.L1+1)).Check a z

instance tanCornersDecidable (b:Band) (d:Rectangle) (a z:ℕ):Decidable (tanCorners b d a z):=by
  unfold tanCorners
  infer_instance

theorem DSS (b:Band) (d:Rectangle) (a z mu:ℕ)
    (hR:b.R≤d.s) (hc:tanCorners b d a z) (ha:a≤mu) (hz:mu≤z) (hmu:1≤mu)
    (hm:mu≤d.alpha-d.beta*(mu-1))
    (hs:2*d.s≤d.alpha-d.beta*(mu-1))
    (hs' :2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu):tanRowGood b d mu:=by
  have h0:=Cubic.check_positive _ _ _ mu hc.1 ha hz
  have h0' :=Cubic.check_positive _ _ _ mu hc.2.1 ha hz
  have h1:=Cubic.check_positive _ _ _ mu hc.2.2.1 ha hz
  have h1' :=Cubic.check_positive _ _ _ mu hc.2.2.2 ha hz
  rw [AZB b d b.T0 d.L0 mu hmu hR hm hs hs'] at h0
  rw [AZB b d b.T0 (d.L0+1) mu hmu hR hm hs hs'] at h0'
  rw [AZB b d b.T1 d.L1 mu hmu hR hm hs hs'] at h1
  rw [AZB b d b.T1 (d.L1+1) mu hmu hR hm hs hs'] at h1'
  simp only [Nat.cast_add,Nat.cast_one] at h0' h1'
  unfold tanRowGood
  constructor
  · exact max_lt h0 (by nlinarith only [h0'])
  · exact max_lt h1 (by nlinarith only [h1'])

def DSU (b:Band) (d:Rectangle) (start:ℕ):ℕ→Bool
  | 0=>true
  | n+1=>DSU b d start n && decide (tanRowGood b d (start+n))

theorem EME (b:Band) (d:Rectangle) (start n:ℕ)
    (hc:DSU b d start n=true) (mu:ℕ) (h0:start≤mu) (h1:mu<start+n):
    tanRowGood b d mu:=by
  induction n with
  | zero=>omega
  | succ n ih=>
    simp only [DSU,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases hmu:mu<start+n
    · exact ih hc.1 hmu
    · have he:mu=start+n:=by omega
      simpa only [he] using hc.2

def TanFastRows (b:Band) (d:Rectangle) (w:FastWitness):Prop:=
  1≤w.firstExact∧w.firstExact≤w.lastExact∧w.lastExact≤w.normalEnd∧w.normalEnd≤b.B+b.R∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd∧
  tanCorners b d 1 (w.firstExact-1)∧tanCorners b d (w.lastExact+1) w.normalEnd∧
  tanRowGood b d 0∧DSU b d w.firstExact (w.lastExact+1-w.firstExact)=true∧
  DSU b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true

instance tanFastRowsDecidable (b:Band) (d:Rectangle) (w:FastWitness):
    Decidable (TanFastRows b d w):=by
  unfold TanFastRows
  infer_instance

theorem FHQ (b:Band) (d:Rectangle) (n:ℕ)
    (h: ∀mu<n,tanRowGood b d mu):checkTanRows b d n=true:=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [checkTanRows,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨ih (fun mu hm=>h mu (by omega)),h n (by omega)⟩

theorem FWG (b:Band) (d:Rectangle) (w:FastWitness)
    (hR:b.R≤d.s) (h:TanFastRows b d w):checkTanRows b d (b.B+b.R+1)=true:=by
  rcases h with ⟨hfirst,hlast,hend,hmax,hlevel,hs,hs',hleft,hright,hzero,hcenter,htail⟩
  apply FHQ
  intro mu hmu
  by_cases hz:mu=0
  · simpa only [hz] using hzero
  have hmu1:1≤mu:=by omega
  by_cases hn:mu≤w.normalEnd
  · have hmono:d.alpha-d.beta*(w.normalEnd-1)≤d.alpha-d.beta*(mu-1):=
      Nat.sub_le_sub_left (Nat.mul_le_mul_left d.beta (Nat.sub_le_sub_right hn 1)) d.alpha
    have hm:mu≤d.alpha-d.beta*(mu-1):=by omega
    have hms:2*d.s≤d.alpha-d.beta*(mu-1):=by omega
    have hms' :2*(d.s-b.R)≤d.alpha-d.beta*(mu-1)-mu:=by omega
    by_cases hbefore:mu<w.firstExact
    · exact DSS b d 1 (w.firstExact-1) mu hR hleft hmu1 (by omega) hmu1 hm hms hms'
    by_cases hwithin:mu≤w.lastExact
    · exact EME _ _ _ _ hcenter mu (by omega) (by omega)
    · exact DSS b d (w.lastExact+1) w.normalEnd mu hR hright (by omega) hn hmu1 hm hms hms'
  · exact EME _ _ _ _ htail mu (by omega) (by omega)

def WideHeader (b:Band) (d:Rectangle):Prop:=
  WideShape b d∧1≤b.R∧b.B<2130706433∧b.R<2130706433∧b.T1<2130706433∧
  cutAt b d d.lo≤131071*(d.U+1)∧
  (pair b d).mixedCost.y<2130706433∧(pair b d).mixedCost.r<2130706433∧
  (pair b d).mixedCost.z<2130706433∧GB.FU (pair b d)≤b.count

structure WideRow where
  rect:Rectangle
  hiW:FastWitness
  tanW:FastWitness

def DRX (b:Band) (x:WideRow):Prop:=
  WideHeader b x.rect∧FastRows b (hiRect x.rect) x.hiW∧TanFastRows b x.rect x.tanW

instance wideFastValidDecidable (b:Band) (x:WideRow):Decidable (DRX b x):=by
  unfold DRX WideHeader
  infer_instance

theorem EGR (b:Band) (x:WideRow) (h:DRX b x):WideValid b x.rect:=by
  rcases h with ⟨⟨hs,hR,hB,hRc,hTc,hU,hgY,hgR,hgZ,hprice⟩,hhi,htan⟩
  have hRs:b.R≤x.rect.s:=hs.1.2.1
  exact ⟨hs,hR,hB,hRc,hTc,hU,hgY,hgR,hgZ,hprice,
    FKM b (hiRect x.rect) x.hiW hRs hhi,FWG b x.rect x.tanW hRs htan⟩







end
end AP
end MergedPart3

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower
namespace AI
open AP LD AN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 40000

structure WideEntry where
  hi:ℕ
  profile:ℕ
  L0:ℕ
  deltaL:ℕ
  hiW:FastWitness
  tanW:FastWitness

def wideAux:ℕ→List ℕ→ℕ→List WideEntry
  | 0,_,_=>[]
  | n+1,previous,code=>
    let f:=DZG.ESH previous code
    let v:=f.1
    ⟨v.getD 0 0,v.getD 1 0,v.getD 2 0,v.getD 3 0,
      ⟨v.getD 4 0,v.getD 5 0,v.getD 6 0⟩,⟨v.getD 7 0,v.getD 8 0,v.getD 9 0⟩⟩::wideAux n v f.2
def wideData (n code:ℕ):List WideEntry:=wideAux n [0,0,0,0,0,0,0,0,0,0] code

def wideRect (b:Band) (profiles:ℕ→Profile) (lo:ℕ) (e:WideEntry):Rectangle:=
  let p:=profiles e.profile
  let L1:=if e.deltaL%2=0 then e.L0+e.deltaL/2 else e.L0-e.deltaL/2
  let d:Rectangle:=⟨lo,e.hi,p.alpha,p.beta,p.s,e.L0,L1,0⟩
  {d with U:=(cutAt b d lo-1)/131071}

def EAI (b:Band) (profiles:ℕ→Profile) (stop:ℕ):ℕ→List WideEntry→Bool
  | start,[]=>decide (stop+1=start)
  | start,e::es=>decide (DRX b ⟨wideRect b profiles start e,e.hiW,e.tanW⟩) &&
      EAI b profiles stop (e.hi+1) es

def WideCovered (b:Band) (lo hi:ℕ):Prop:=
  ∀nu,lo≤nu→nu≤hi→ ∃d:Rectangle,WideValid b d∧d.lo≤nu∧nu≤d.hi

theorem AD (b:Band) (profiles:ℕ→Profile) (start stop:ℕ) (es:List WideEntry)
    (hc:EAI b profiles stop start es=true):WideCovered b start stop:=by
  intro nu hlo hhi
  induction es generalizing start with
  | nil=>simp only [EAI,decide_eq_true_eq] at hc;omega
  | cons e es ih=>
    simp only [EAI,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases he:nu≤e.hi
    · exact ⟨wideRect b profiles start e,EGR b _ hc.1,hlo,he⟩
    · exact ih (e.hi+1) hc.2 (by omega)

theorem _Q1 (b:Band) (lo mid hi:ℕ)
    (h0:WideCovered b lo mid) (h1:WideCovered b (mid+1) hi):WideCovered b lo hi:=by
  intro nu hlo hhi
  by_cases h:nu≤mid
  · exact h0 nu hlo h
  · exact h1 nu (by omega) hhi

open MvPolynomial RCN100 RCN119 BY
open RCN234 (wt)
variable (K I:Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance wideBlocksDecEqK:DecidableEq K:=Classical.decEq K

theorem AS (b:Band) (hc:WideCovered b (AX b) (tail b))
    (hrange:AX b≤tail b)
    {DF T nu:ℕ} {H:Poly4 K} (F:RCN266.RegularIndex H)
    (hbox:F.val∈BA K DF 1 T b.R)
    (hcode:wt (RCN081.BV 131071) F.val=nu)
    (htotal:T≤wt RCN156.AT F.val)
    (hslope:b.R≤wt RCN156.BE F.val)
    (hB:wt RCN156.BC F.val≤b.B)
    (hT0:b.T0≤T) (hT1:T≤b.T1) (hnu:AX b≤nu)
    (nodes:I ↪ K) (u0 u1:I→K) (hcard:Fintype.card I=262144)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement: ∀gamma∈Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i=>(selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.BL selected Gamma 131071 80909):
    (RCN140.regularSeeds H selected Gamma F).card≤b.count:=by
  obtain ⟨d,hd,hlo,hhi⟩:=hc (min nu (tail b)) (le_min hnu hrange) (min_le_right _ _)
  exact BNW K I b d hd F hbox hcode htotal hslope hB hT0 hT1
    (hlo.trans (min_le_left _ _)) hhi nodes u0 u1 hcard selected Gamma hdegree hagreement hno

end
end AI

end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower.NatWideKernel80909
open LD AP AN AI
set_option autoImplicit false
set_option maxHeartbeats 10000000
structure Diff where
 pos : ℕ
 neg : ℕ
def value (d:Diff):ℤ:= (d.pos:ℤ)-d.neg
def ofInt:ℤ→Diff
 | .ofNat n => ⟨n,0⟩
 | .negSucc n => ⟨0,n+1⟩
def add (a b:Diff):Diff:=⟨a.pos+b.pos,a.neg+b.neg⟩
def sub (a b:Diff):Diff:=⟨a.pos+b.neg,a.neg+b.pos⟩
def scale (k:ℕ) (a:Diff):Diff:=⟨k*a.pos,k*a.neg⟩
lemma ofInt_eq (z:ℤ):value (ofInt z)=z:=by cases z <;> simp [value,ofInt] <;> omega
lemma add_eq (a b:Diff):value (add a b)=value a+value b:=by simp [value,add];ring
lemma sub_eq (a b:Diff):value (sub a b)=value a-value b:=by simp [value,sub];ring
lemma scale_eq (k:ℕ) (a:Diff):value (scale k a)= (k:ℤ)*value a:=by simp [value,scale];ring
lemma pos_iff (d:Diff): (0<value d)↔d.neg<d.pos:=by unfold value;omega
lemma nonneg_iff (d:Diff): (0≤value d)↔d.neg≤d.pos:=by unfold value;omega

def eval (p:Cubic) (x:ℕ):Diff:=add  (scale x  (add  (scale x  (add  (scale x  (ofInt p.c3))  (ofInt p.c2)))  (ofInt p.c1)))  (ofInt p.c0)
def deriv (p:Cubic) (x:ℕ):Diff:=add  (scale x  (add  (scale  (3*x)  (ofInt p.c3))  (scale 2  (ofInt p.c2))))  (ofInt p.c1)
lemma eval_eq (p:Cubic) (x:ℕ):value (eval p x)=p.eval x:=by
 simp only [eval,add_eq,scale_eq,ofInt_eq,Cubic.eval]
 ring
lemma deriv_eq (p:Cubic) (x:ℕ):value (deriv p x)=p.deriv x:=by
 simp only [deriv,add_eq,scale_eq,ofInt_eq,Cubic.deriv,Nat.cast_mul,Nat.cast_ofNat]
 ring

def mid1 (p:Cubic) (a b:ℕ):Diff:=add  (scale 3  (eval p a))  (scale  (b-a)  (deriv p a))
def mid2 (p:Cubic) (a b:ℕ):Diff:=sub  (scale 3  (eval p b))  (scale  (b-a)  (deriv p b))
def NatCheck (p:Cubic) (a b:ℕ):Prop:=b<a ∨
  (eval p a).neg< (eval p a).pos ∧  (eval p b).neg< (eval p b).pos ∧
  (mid1 p a b).neg≤ (mid1 p a b).pos ∧  (mid2 p a b).neg≤ (mid2 p a b).pos
instance (p:Cubic) (a b:ℕ):Decidable (NatCheck p a b):=by unfold NatCheck;infer_instance
lemma check_iff (p:Cubic) (a b:ℕ):NatCheck p a b↔p.Check a b:=by
 by_cases h:b<a
 · simp only [NatCheck,Cubic.Check,h,true_or]
 · have hab:a≤b:=by omega
   have hw: ( (b-a:ℕ):ℤ)= (b:ℤ)-a:=Int.ofNat_sub hab
   have h1:value (mid1 p a b)=3*p.eval a+ ( (b:ℤ)-a)*p.deriv a:=by
    simp only [mid1,add_eq,scale_eq,eval_eq,deriv_eq,hw,Nat.cast_ofNat]
   have h2:value (mid2 p a b)=3*p.eval b- ( (b:ℤ)-a)*p.deriv b:=by
    simp only [mid2,sub_eq,scale_eq,eval_eq,deriv_eq,hw,Nat.cast_ofNat]
   simp only [NatCheck,Cubic.Check,h,false_or]
   rw [←pos_iff,←pos_iff,←nonneg_iff,←nonneg_iff,eval_eq,eval_eq,h1,h2]
def checkDec (p:Cubic) (a b:ℕ):Decidable (p.Check a b):=decidable_of_iff  (NatCheck p a b)  (check_iff p a b)
attribute [local instance] checkDec

def cornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (corners b d a z):=by unfold corners;infer_instance
attribute [local instance] cornersDec
def rowsDec (b:Band) (d:Rectangle) (w:FastWitness):Decidable (FastRows b d w):=by unfold FastRows;infer_instance
attribute [local instance] rowsDec
def tanCornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (tanCorners b d a z):=by unfold tanCorners;infer_instance
attribute [local instance] tanCornersDec
def tanRowsDec (b:Band) (d:Rectangle) (w:FastWitness):Decidable (TanFastRows b d w):=by unfold TanFastRows;infer_instance
attribute [local instance] tanRowsDec
def wideDec (b:Band) (x:WideRow):Decidable (DRX b x):=by unfold DRX WideHeader;infer_instance
attribute [local instance] wideDec

def check (b:Band) (profiles:ℕ→Profile) (stop:ℕ):ℕ→List WideEntry→Bool
 | start,[] => decide (stop+1=start)
 | start,e::es => decide (DRX b ⟨wideRect b profiles start e,e.hiW,e.tanW⟩) && check b profiles stop  (e.hi+1) es

theorem block_sound (b:Band) (profiles:ℕ→Profile) (start stop:ℕ) (es:List WideEntry)
  (hc:check b profiles stop start es=true):WideCovered b start stop:=by
 intro nu hlo hhi
 induction es generalizing start with
 | nil => simp only [check,decide_eq_true_eq] at hc;omega
 | cons e es ih =>
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  by_cases he:nu≤e.hi
  · exact ⟨wideRect b profiles start e,EGR b _ hc.1,hlo,he⟩
  · exact ih  (e.hi+1) hc.2  (by omega)
end ProximityPrize.SubmissionLower.NatWideKernel80909
end
section
namespace ProximityPrize.SubmissionLower.NatRankWide80909
open LD AP AN AI
set_option autoImplicit false
set_option maxHeartbeats 10000000

def rank (base rate L s : ℕ) : Cubic :=
 let p0 : ℕ := s*(s+1)*((4*s+2)*L+5*s+2)+2*(s+1)*(3*L+4)*base+6*(L+1)*(s+1)*base^2
 let n0 : ℕ := s*(s+1)*s^2+2*(s+1)*(3*L*s+6*s)*base+2*(s+1)*base^3
 let p1 : ℕ := rate*(2*(s+1)*(3*L*s+6*s)+6*(s+1)*base^2)
 let n1 : ℕ := rate*(2*(s+1)*(3*L+4)+12*(L+1)*(s+1)*base)
 let p2 : ℕ := rate^2*6*(L+1)*(s+1)
 let n2 : ℕ := rate^2*6*(s+1)*base
 let p3 : ℕ := 2*(s+1)*rate^3
 ⟨(p0:ℤ)-n0,(p1:ℤ)-n1,(p2:ℤ)-n2,p3⟩
lemma rank_eq (base rate L s : ℕ) : rank base rate L s=AVK base rate L s := by
 simp only [rank,AVK,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 congr 1 <;> ring

def hiConstant (b : Band) (d : Rectangle) (T L : ℕ) : ℤ :=
 12*((countSlope (cutoff b d) d.s-countSlope (cutoff b d-d.lo) (d.s-b.R))*L+
    countSlope (cutoff b d-d.lo) (d.s-b.R)*T+
    WY (cutoff b d) d.s-WY (cutoff b d-d.lo) (d.s-b.R))
def tanConstant (b : Band) (d : Rectangle) (T L : ℕ) : ℤ :=
 12*((countSlope (cutoff b d) d.s+
        (tanK b d : ℤ)*(countSlope (cutoff b d+1) d.s-countSlope (cutoff b d) d.s)-
        countSlope (tanE b d) (d.s-b.R))*L+
      countSlope (tanE b d) (d.s-b.R)*T+
      WY (cutoff b d) d.s+
        (tanK b d : ℤ)*(WY (cutoff b d+1) d.s-WY (cutoff b d) d.s)-
      WY (tanE b d) (d.s-b.R))
def margin (c : ℤ) (b : Band) (d : Rectangle) (T L : ℕ) : Cubic :=
 let p := rank (d.alpha+d.beta) d.beta L d.s
 let q := rank (d.alpha+d.beta) (d.beta+1) (L-T) (d.s-b.R)
 ⟨c-262144*(p.c0-q.c0),-262144*(p.c1-q.c1),-262144*(p.c2-q.c2),-262144*(p.c3-q.c3)⟩
lemma hi_eq (b : Band) (d : Rectangle) (T L : ℕ) (hL : T≤L) (hR : b.R≤d.s) :
 margin (hiConstant b d T L) b d T L=BDN b d T L := by
 simp only [margin,hiConstant,BDN,rank_eq,Nat.cast_add,Nat.cast_one,Nat.cast_sub hL,Nat.cast_sub hR]
lemma tan_eq (b : Band) (d : Rectangle) (T L : ℕ) (hL : T≤L) (hR : b.R≤d.s) :
 margin (tanConstant b d T L) b d T L=APE b d T L := by
 simp only [margin,tanConstant,APE,rank_eq,Nat.cast_add,Nat.cast_one,Nat.cast_sub hL,Nat.cast_sub hR]

attribute [local instance] NatWideKernel80909.checkDec
def hiDec (b : Band) (d : Rectangle) (T L a z : ℕ) : Decidable ((BDN b d T L).Check a z) :=
 if h:T≤L ∧ b.R≤d.s then
  decidable_of_iff ((margin (hiConstant b d T L) b d T L).Check a z) (by rw [hi_eq b d T L h.1 h.2])
 else NatWideKernel80909.checkDec _ _ _
attribute [local instance] hiDec
def tanDec (b : Band) (d : Rectangle) (T L a z : ℕ) : Decidable ((APE b d T L).Check a z) :=
 if h:T≤L ∧ b.R≤d.s then
  decidable_of_iff ((margin (tanConstant b d T L) b d T L).Check a z) (by rw [tan_eq b d T L h.1 h.2])
 else NatWideKernel80909.checkDec _ _ _
attribute [local instance] tanDec
def cornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (corners b d a z):=by unfold corners;infer_instance
attribute [local instance] cornersDec
def rowsDec (b:Band) (d:Rectangle) (w:FastWitness):Decidable (FastRows b d w):=by unfold FastRows;infer_instance
attribute [local instance] rowsDec
def tanCornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (tanCorners b d a z):=by unfold tanCorners;infer_instance
attribute [local instance] tanCornersDec
def tanRowsDec (b:Band) (d:Rectangle) (w:FastWitness):Decidable (TanFastRows b d w):=by unfold TanFastRows;infer_instance
attribute [local instance] tanRowsDec
def wideDec (b:Band) (x:WideRow):Decidable (DRX b x):=by unfold DRX WideHeader;infer_instance
attribute [local instance] wideDec

def check (b:Band) (profiles:ℕ→Profile) (stop:ℕ):ℕ→List WideEntry→Bool
 | start,[] => decide (stop+1=start)
 | start,e::es => decide (DRX b ⟨wideRect b profiles start e,e.hiW,e.tanW⟩) && check b profiles stop  (e.hi+1) es

theorem block_sound (b:Band) (profiles:ℕ→Profile) (start stop:ℕ) (es:List WideEntry)
  (hc:check b profiles stop start es=true):WideCovered b start stop:=by
 intro nu hlo hhi
 induction es generalizing start with
 | nil => simp only [check,decide_eq_true_eq] at hc;omega
 | cons e es ih =>
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  by_cases he:nu≤e.hi
  · exact ⟨wideRect b profiles start e,EGR b _ hc.1,hlo,he⟩
  · exact ih  (e.hi+1) hc.2  (by omega)
end ProximityPrize.SubmissionLower.NatRankWide80909
namespace ProximityPrize.SubmissionLower
abbrev NWB := NatRankWide80909.block_sound
end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower.NatPoly80909
open LD AP AN AI NatWideKernel80909
set_option autoImplicit false
set_option maxHeartbeats 10000000
structure Poly where
 c0:Diff
 c1:Diff
 c2:Diff
 c3:Diff
def polyValue (p:Poly):Cubic:=⟨value p.c0,value p.c1,value p.c2,value p.c3⟩
def rank (base rate L s : ℕ) : Poly :=
 let p0 : ℕ := s*(s+1)*((4*s+2)*L+5*s+2)+2*(s+1)*(3*L+4)*base+6*(L+1)*(s+1)*base^2
 let n0 : ℕ := s*(s+1)*s^2+2*(s+1)*(3*L*s+6*s)*base+2*(s+1)*base^3
 let p1 : ℕ := rate*(2*(s+1)*(3*L*s+6*s)+6*(s+1)*base^2)
 let n1 : ℕ := rate*(2*(s+1)*(3*L+4)+12*(L+1)*(s+1)*base)
 let p2 : ℕ := rate^2*6*(L+1)*(s+1)
 let n2 : ℕ := rate^2*6*(s+1)*base
 let p3 : ℕ := 2*(s+1)*rate^3
 ⟨⟨p0,n0⟩,⟨p1,n1⟩,⟨p2,n2⟩,⟨p3,0⟩⟩
lemma rank_eq (base rate L s:ℕ):polyValue (rank base rate L s)=NatRankWide80909.rank base rate L s:=by
 simp only [polyValue,rank,NatRankWide80909.rank,value]
 rfl

def counts (D s:ℕ):Diff:=⟨ECJ (D/131071) (D%131071) 131071 s,0⟩
lemma counts_eq (D s:ℕ):value (counts D s)=countSlope D s:=by simp [counts,value,countSlope]
def intercept (q r w s:ℕ):Diff:=⟨RZ.OM q r w q s,oneSlope q r w s*q⟩
lemma intercept_eq (q r w s:ℕ):value (intercept q r w s)=oneIntercept q r w s:=by
 simp only [intercept,value,oneIntercept,Nat.cast_mul]
def base (D s:ℕ):Diff:=
 let q:=D/131071
 let r:=D%131071
 if r+s≤131071 then intercept q r 131071 s else
 sub (add (intercept q r 131071 (131071-r-1)) (intercept (q+1-(131071-r)) 0 131071 (s-(131071-r))))
  ⟨oneSlope (q+1-(131071-r)) 0 131071 (s-(131071-r))*(131071-r),0⟩
lemma base_eq (D s:ℕ):value (base D s)=WY D s:=by
 dsimp only [base,WY,CSW]
 split_ifs with h <;> simp only [h,ite_true,ite_false,intercept,sub,add,value,oneIntercept,Nat.cast_mul,Nat.cast_add,Nat.cast_zero,sub_zero,Nat.cast_sub (show D%131071≤131071 from Nat.le_of_lt (Nat.mod_lt _ (by decide)))] <;> ring
def hiConstant (b:Band)(d:Rectangle)(T L:ℕ):Diff:=
 let D:=cutoff b d
 let E:=D-d.lo
 scale 12 (add (add (scale L (sub (counts D d.s) (counts E (d.s-b.R))))
  (scale T (counts E (d.s-b.R)))) (sub (base D d.s) (base E (d.s-b.R))))
lemma hi_eq (b:Band)(d:Rectangle)(T L:ℕ):value (hiConstant b d T L)=NatRankWide80909.hiConstant b d T L:=by
 simp only [hiConstant,scale_eq,add_eq,sub_eq,counts_eq,base_eq,NatRankWide80909.hiConstant]
 ring

def tanConstant (b:Band)(d:Rectangle)(T L:ℕ):Diff:=
 let D:=cutoff b d
 let E:=tanE b d
 let K:=tanK b d
 scale 12 (add (add (scale L (sub (add (counts D d.s) (scale K (sub (counts (D+1) d.s) (counts D d.s)))) (counts E (d.s-b.R))))
  (scale T (counts E (d.s-b.R)))) (sub (add (base D d.s) (scale K (sub (base (D+1) d.s) (base D d.s)))) (base E (d.s-b.R))))
lemma tan_eq (b:Band)(d:Rectangle)(T L:ℕ):value (tanConstant b d T L)=NatRankWide80909.tanConstant b d T L:=by
 simp only [tanConstant,scale_eq,add_eq,sub_eq,counts_eq,base_eq,NatRankWide80909.tanConstant]
 ring

def margin (c:Diff)(b:Band)(d:Rectangle)(T L:ℕ):Poly:=
 let p:=rank (d.alpha+d.beta) d.beta L d.s
 let q:=rank (d.alpha+d.beta) (d.beta+1) (L-T) (d.s-b.R)
 ⟨sub c (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),
  scale 262144 (sub q.c2 p.c2),scale 262144 (sub q.c3 p.c3)⟩
lemma margin_eq (c:Diff)(b:Band)(d:Rectangle)(T L:ℕ):
 polyValue (margin c b d T L)=NatRankWide80909.margin (value c) b d T L:=by
 have hp:=rank_eq (d.alpha+d.beta) d.beta L d.s
 have hq:=rank_eq (d.alpha+d.beta) (d.beta+1) (L-T) (d.s-b.R)
 simp only [NatRankWide80909.margin,←hp,←hq,margin,polyValue,sub_eq,scale_eq]
 congr 1 <;> ring
def eval (p:Poly) (x:ℕ):Diff:=add  (scale x  (add  (scale x  (add  (scale x  (p.c3))  (p.c2)))  (p.c1)))  (p.c0)
def deriv (p:Poly) (x:ℕ):Diff:=add  (scale x  (add  (scale  (3*x)  (p.c3))  (scale 2  (p.c2))))  (p.c1)
lemma eval_eq (p:Poly) (x:ℕ):value (eval p x)=(polyValue p).eval x:=by
 simp only [eval,add_eq,scale_eq,ofInt_eq,Cubic.eval,polyValue]
 ring
lemma deriv_eq (p:Poly) (x:ℕ):value (deriv p x)=(polyValue p).deriv x:=by
 simp only [deriv,add_eq,scale_eq,ofInt_eq,Cubic.deriv,polyValue,Nat.cast_mul,Nat.cast_ofNat]
 ring

def mid1 (p:Poly) (a b:ℕ):Diff:=add  (scale 3  (eval p a))  (scale  (b-a)  (deriv p a))
def mid2 (p:Poly) (a b:ℕ):Diff:=sub  (scale 3  (eval p b))  (scale  (b-a)  (deriv p b))
def NatCheck (p:Poly) (a b:ℕ):Prop:=b<a ∨
  (eval p a).neg< (eval p a).pos ∧  (eval p b).neg< (eval p b).pos ∧
  (mid1 p a b).neg≤ (mid1 p a b).pos ∧  (mid2 p a b).neg≤ (mid2 p a b).pos
instance (p:Poly) (a b:ℕ):Decidable (NatCheck p a b):=by unfold NatCheck;infer_instance
lemma check_iff (p:Poly) (a b:ℕ):NatCheck p a b↔(polyValue p).Check a b:=by
 by_cases h:b<a
 · simp only [NatCheck,Cubic.Check,h,true_or]
 · have hab:a≤b:=by omega
   have hw: ( (b-a:ℕ):ℤ)= (b:ℤ)-a:=Int.ofNat_sub hab
   have h1:value (mid1 p a b)=3*(polyValue p).eval a+ ( (b:ℤ)-a)*(polyValue p).deriv a:=by
    simp only [mid1,add_eq,scale_eq,eval_eq,deriv_eq,hw,Nat.cast_ofNat]
   have h2:value (mid2 p a b)=3*(polyValue p).eval b- ( (b:ℤ)-a)*(polyValue p).deriv b:=by
    simp only [mid2,sub_eq,scale_eq,eval_eq,deriv_eq,hw,Nat.cast_ofNat]
   simp only [NatCheck,Cubic.Check,h,false_or]
   rw [←pos_iff,←pos_iff,←nonneg_iff,←nonneg_iff,eval_eq,eval_eq,h1,h2]
def hiDec (b:Band)(d:Rectangle)(T L a z:ℕ):Decidable ((BDN b d T L).Check a z):=
 if h:T≤L ∧ b.R≤d.s then decidable_of_iff (NatCheck (margin (hiConstant b d T L) b d T L) a z)
  (by rw [check_iff,margin_eq,hi_eq,NatRankWide80909.hi_eq b d T L h.1 h.2])
 else NatWideKernel80909.checkDec _ _ _
attribute [local instance] hiDec
def tanDec (b:Band)(d:Rectangle)(T L a z:ℕ):Decidable ((APE b d T L).Check a z):=
 if h:T≤L ∧ b.R≤d.s then decidable_of_iff (NatCheck (margin (tanConstant b d T L) b d T L) a z)
  (by rw [check_iff,margin_eq,tan_eq,NatRankWide80909.tan_eq b d T L h.1 h.2])
 else NatWideKernel80909.checkDec _ _ _
attribute [local instance] tanDec
def cornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (corners b d a z):=by unfold corners;infer_instance
attribute [local instance] cornersDec
def rowsDec (b:Band) (d:Rectangle) (w:FastWitness):Decidable (FastRows b d w):=by unfold FastRows;infer_instance
attribute [local instance] rowsDec
def tanCornersDec (b:Band) (d:Rectangle) (a z:ℕ):Decidable (tanCorners b d a z):=by unfold tanCorners;infer_instance
attribute [local instance] tanCornersDec
def tanRowsDec (b:Band) (d:Rectangle) (w:FastWitness):Decidable (TanFastRows b d w):=by unfold TanFastRows;infer_instance
attribute [local instance] tanRowsDec
def wideDec (b:Band) (x:WideRow):Decidable (DRX b x):=by unfold DRX WideHeader;infer_instance
attribute [local instance] wideDec

def check (b:Band) (profiles:ℕ→Profile) (stop:ℕ):ℕ→List WideEntry→Bool
 | start,[] => decide (stop+1=start)
 | start,e::es => decide (DRX b ⟨wideRect b profiles start e,e.hiW,e.tanW⟩) && check b profiles stop  (e.hi+1) es

theorem block_sound (b:Band) (profiles:ℕ→Profile) (start stop:ℕ) (es:List WideEntry)
  (hc:check b profiles stop start es=true):WideCovered b start stop:=by
 intro nu hlo hhi
 induction es generalizing start with
 | nil => simp only [check,decide_eq_true_eq] at hc;omega
 | cons e es ih =>
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  by_cases he:nu≤e.hi
  · exact ⟨wideRect b profiles start e,EGR b _ hc.1,hlo,he⟩
  · exact ih  (e.hi+1) hc.2  (by omega)
#print axioms block_sound
end ProximityPrize.SubmissionLower.NatPoly80909
namespace ProximityPrize.SubmissionLower
abbrev NFB:=NatPoly80909.block_sound
end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower.NatRows80909
open LD AP AN AI NatWideKernel80909
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def rankSlopeN (m s:ℕ):Diff:=
 let u:=min s (m/2)
 let K:=(s+1)*m*(m+1)
 let p0:=(m+1)*(s+1)
 let P:=m+2*s+3
 ⟨6*K+6*P*u*(u+1),12*p0*u+4*u*(u+1)*(2*u+1)⟩
def rankBaseN (m s:ℕ):Diff:=
 let u:=min s (m/2)
 let K:=(s+1)*m*(m+1)
 let p0:=(m+1)*(s+1)
 let P:=m+2*s+3
 let C:Diff:=⟨2,m+s⟩
 sub ⟨8*K,K*(2*m+3*s)⟩
  (add (add (scale (6*p0*u) C) (scale (3*u*(u+1)) (sub ⟨p0,0⟩ (scale P C))))
   (add (scale (u*(u+1)*(2*u+1)) (sub (scale 2 C) ⟨P,0⟩)) ⟨3*u*u*(u+1)*(u+1),0⟩))
def rankAffineN (m s L:ℕ):Diff:=add (scale L (rankSlopeN m s)) (rankBaseN m s)
lemma rankAffine_eq (m s L:ℕ):value (rankAffineN m s L)=rankAffine m s L:=by
 simp only [rankAffineN,rankSlopeN,rankBaseN,add,sub,scale,value,rankAffine,ClosedRank.sourceTwelve,ClosedRank.AAL,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,sub_zero]
 ring
lemma rankSlope_eq (m s:ℕ):value (rankSlopeN m s)=rankSlope m s:=by
 have h1:=rankAffine_eq m s 1
 have h0:=rankAffine_eq m s 0
 simp only [Nat.cast_one,Nat.cast_zero] at h1 h0
 unfold rankSlope
 rw [←h1,←h0]
 simp only [rankAffineN,add_eq,scale_eq,Nat.cast_one,Nat.cast_zero,one_mul,zero_mul,zero_add]
 ring
lemma rankBase_eq (m s:ℕ):value (rankBaseN m s)=CPJ m s:=by
 have h0:=rankAffine_eq m s 0
 simp only [Nat.cast_zero] at h0
 unfold CPJ
 rw [←h0]
 simp only [rankAffineN,add_eq,scale_eq,Nat.cast_zero,zero_mul,zero_add]

def rowA (D nu s R m mu:ℕ):Diff:=
 sub (scale 12 (sub (NatPoly80909.counts D s) (NatPoly80909.counts (D-nu) (s-R))))
  (scale 262144 (sub (rankSlopeN m s) (rankSlopeN (m-mu) (s-R))))
def rowB (D nu s R m mu:ℕ):Diff:=
 sub (scale 12 (NatPoly80909.counts (D-nu) (s-R))) (scale 262144 (rankSlopeN (m-mu) (s-R)))
def rowC (D nu s R m mu:ℕ):Diff:=
 sub (scale 12 (sub (NatPoly80909.base D s) (NatPoly80909.base (D-nu) (s-R))))
  (scale 262144 (sub (rankBaseN m s) (rankBaseN (m-mu) (s-R))))
lemma rowA_eq (D nu s R m mu:ℕ):value (rowA D nu s R m mu)=marginA D nu s R m mu:=by
 simp only [rowA,sub_eq,scale_eq,NatPoly80909.counts_eq,rankSlope_eq,marginA];ring
lemma rowB_eq (D nu s R m mu:ℕ):value (rowB D nu s R m mu)=marginB D nu s R m mu:=by
 simp only [rowB,sub_eq,scale_eq,NatPoly80909.counts_eq,rankSlope_eq,marginB];ring
lemma rowC_eq (D nu s R m mu:ℕ):value (rowC D nu s R m mu)=marginC D nu s R m mu:=by
 simp only [rowC,sub_eq,scale_eq,NatPoly80909.base_eq,rankBase_eq,marginC];ring

def tanA (D k E s R m mu:ℕ):Diff:=
 sub (scale 12 (sub (add (NatPoly80909.counts D s) (scale k (sub (NatPoly80909.counts (D+1) s) (NatPoly80909.counts D s)))) (NatPoly80909.counts E (s-R))))
  (scale 262144 (sub (rankSlopeN m s) (rankSlopeN (m-mu) (s-R))))
def tanB (E s R m mu:ℕ):Diff:=
 sub (scale 12 (NatPoly80909.counts E (s-R))) (scale 262144 (rankSlopeN (m-mu) (s-R)))
def tanC (D k E s R m mu:ℕ):Diff:=
 sub (scale 12 (sub (add (NatPoly80909.base D s) (scale k (sub (NatPoly80909.base (D+1) s) (NatPoly80909.base D s)))) (NatPoly80909.base E (s-R))))
  (scale 262144 (sub (rankBaseN m s) (rankBaseN (m-mu) (s-R))))
lemma tanA_eq (D k E s R m mu:ℕ):value (tanA D k E s R m mu)=tanMarginA D k E s R m mu:=by
 simp only [tanA,sub_eq,add_eq,scale_eq,NatPoly80909.counts_eq,rankSlope_eq,tanMarginA];ring
lemma tanB_eq (E s R m mu:ℕ):value (tanB E s R m mu)=tanMarginB E s R m mu:=by
 simp only [tanB,sub_eq,scale_eq,NatPoly80909.counts_eq,rankSlope_eq,tanMarginB];ring
lemma tanC_eq (D k E s R m mu:ℕ):value (tanC D k E s R m mu)=tanMarginC D k E s R m mu:=by
 simp only [tanC,sub_eq,add_eq,scale_eq,NatPoly80909.base_eq,rankBase_eq,tanMarginC];ring

def testAt (a b c:Diff)(T L:ℕ):Prop:=
 let f:=add (add (scale L a) (scale T b)) c
 let g:=add a f
 f.neg<f.pos ∧ g.neg<g.pos
instance (a b c:Diff)(T L:ℕ):Decidable (testAt a b c T L):=by unfold testAt;infer_instance
lemma testAt_iff (a b c:Diff)(T L:ℕ):testAt a b c T L ↔ max 0 (-value a)<value a*L+value b*T+value c:=by
 dsimp only [testAt]
 rw [←pos_iff,←pos_iff]
 simp only [add_eq,scale_eq,mul_comm]
 omega

def RowN (b:Band)(d:Rectangle)(mu:ℕ):Prop:=
 let m:=d.alpha-d.beta*(mu-1)
 let a:=rowA (cutoff b d) d.lo d.s b.R m mu
 let v:=rowB (cutoff b d) d.lo d.s b.R m mu
 let c:=rowC (cutoff b d) d.lo d.s b.R m mu
 testAt a v c b.T0 d.L0 ∧ testAt a v c b.T1 d.L1
instance (b:Band)(d:Rectangle)(mu:ℕ):Decidable (RowN b d mu):=by unfold RowN;infer_instance
lemma row_iff (b:Band)(d:Rectangle)(mu:ℕ):RowN b d mu ↔ rowGood b d mu:=by
 simp only [RowN,testAt_iff,rowA_eq,rowB_eq,rowC_eq,rowGood]
def rowDec (b:Band)(d:Rectangle)(mu:ℕ):Decidable (rowGood b d mu):=decidable_of_iff (RowN b d mu) (row_iff b d mu)
attribute [local instance] rowDec

def TanRowN (b:Band)(d:Rectangle)(mu:ℕ):Prop:=
 let m:=d.alpha-d.beta*(mu-1)
 let a:=tanA (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
 let v:=tanB (tanE b d) d.s b.R m mu
 let c:=tanC (cutoff b d) (tanK b d) (tanE b d) d.s b.R m mu
 testAt a v c b.T0 d.L0 ∧ testAt a v c b.T1 d.L1
instance (b:Band)(d:Rectangle)(mu:ℕ):Decidable (TanRowN b d mu):=by unfold TanRowN;infer_instance
lemma tanRow_iff (b:Band)(d:Rectangle)(mu:ℕ):TanRowN b d mu ↔ tanRowGood b d mu:=by
 simp only [TanRowN,testAt_iff,tanA_eq,tanB_eq,tanC_eq,tanRowGood]
def tanRowDec (b:Band)(d:Rectangle)(mu:ℕ):Decidable (tanRowGood b d mu):=decidable_of_iff (TanRowN b d mu) (tanRow_iff b d mu)
attribute [local instance] tanRowDec

lemma decide_irrel (p:Prop)(a b:Decidable p):@decide p a=@decide p b:=congrArg (fun d=>@decide p d) (Subsingleton.elim a b)
def range (b:Band)(d:Rectangle)(start:ℕ):ℕ→Bool
 | 0=>true
 | n+1=>range b d start n && decide (rowGood b d (start+n))
lemma range_eq (b:Band)(d:Rectangle)(start n:ℕ):range b d start n=checkRange b d start n:=by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [range,checkRange,ih];congr 1;exact decide_irrel _ _ _
def tanRange (b:Band)(d:Rectangle)(start:ℕ):ℕ→Bool
 | 0=>true
 | n+1=>tanRange b d start n && decide (tanRowGood b d (start+n))
lemma tanRange_eq (b:Band)(d:Rectangle)(start n:ℕ):tanRange b d start n=DSU b d start n:=by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [tanRange,DSU,ih];congr 1;exact decide_irrel _ _ _
attribute [local instance] NatPoly80909.cornersDec NatPoly80909.tanCornersDec
def FastRowsN (b:Band) (d:Rectangle) (w:FastWitness):Prop:=
  1≤w.firstExact∧w.firstExact≤w.lastExact∧w.lastExact≤w.normalEnd∧w.normalEnd≤b.B+b.R∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd∧
  corners b d 1 (w.firstExact-1)∧corners b d (w.lastExact+1) w.normalEnd∧
  rowGood b d 0∧range b d w.firstExact (w.lastExact+1-w.firstExact)=true∧
  range b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true

instance (b:Band)(d:Rectangle)(w:FastWitness):Decidable (FastRowsN b d w):=by unfold FastRowsN;infer_instance
lemma FastRows_iff (b:Band)(d:Rectangle)(w:FastWitness):FastRowsN b d w ↔ FastRows b d w:=by
 simp only [FastRowsN,FastRows,range_eq,tanRange_eq]
def rowsDec (b:Band)(d:Rectangle)(w:FastWitness):Decidable (FastRows b d w):=decidable_of_iff (FastRowsN b d w) (FastRows_iff b d w)
attribute [local instance] rowsDec
def TanFastRowsN (b:Band) (d:Rectangle) (w:FastWitness):Prop:=
  1≤w.firstExact∧w.firstExact≤w.lastExact∧w.lastExact≤w.normalEnd∧w.normalEnd≤b.B+b.R∧
  w.normalEnd≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*d.s≤d.alpha-d.beta*(w.normalEnd-1)∧
  2*(d.s-b.R)≤d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd∧
  tanCorners b d 1 (w.firstExact-1)∧tanCorners b d (w.lastExact+1) w.normalEnd∧
  tanRowGood b d 0∧tanRange b d w.firstExact (w.lastExact+1-w.firstExact)=true∧
  tanRange b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)=true

instance (b:Band)(d:Rectangle)(w:FastWitness):Decidable (TanFastRowsN b d w):=by unfold TanFastRowsN;infer_instance
lemma TanFastRows_iff (b:Band)(d:Rectangle)(w:FastWitness):TanFastRowsN b d w ↔ TanFastRows b d w:=by
 simp only [TanFastRowsN,TanFastRows,range_eq,tanRange_eq]
def tanRowsDec (b:Band)(d:Rectangle)(w:FastWitness):Decidable (TanFastRows b d w):=decidable_of_iff (TanFastRowsN b d w) (TanFastRows_iff b d w)
attribute [local instance] tanRowsDec
def wideDec (b:Band) (x:WideRow):Decidable (DRX b x):=by unfold DRX WideHeader;infer_instance
attribute [local instance] wideDec

def check (b:Band) (profiles:ℕ→Profile) (stop:ℕ):ℕ→List WideEntry→Bool
 | start,[] => decide (stop+1=start)
 | start,e::es => decide (DRX b ⟨wideRect b profiles start e,e.hiW,e.tanW⟩) && check b profiles stop  (e.hi+1) es

theorem block_sound (b:Band) (profiles:ℕ→Profile) (start stop:ℕ) (es:List WideEntry)
  (hc:check b profiles stop start es=true):WideCovered b start stop:=by
 intro nu hlo hhi
 induction es generalizing start with
 | nil => simp only [check,decide_eq_true_eq] at hc;omega
 | cons e es ih =>
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  by_cases he:nu≤e.hi
  · exact ⟨wideRect b profiles start e,EGR b _ hc.1,hlo,he⟩
  · exact ih  (e.hi+1) hc.2  (by omega)
#print axioms block_sound
end ProximityPrize.SubmissionLower.NatRows80909
namespace ProximityPrize.SubmissionLower
abbrev NRB:=NatRows80909.block_sound
end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower.MonotoneCheck80909
open AP NatWideKernel80909 NatPoly80909
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def curv(p:Poly)(x:ℕ):Diff:=add p.c2 (scale (3*x) p.c3)
lemma curv_eq(p:Poly)(x:ℕ):value (curv p x)=value p.c2+3*value p.c3*x:=by
 simp only [curv,add_eq,scale_eq,Nat.cast_mul,Nat.cast_ofNat];ring
def positive(p:Poly)(a b:ℕ):Bool:=
 if a=1 then
  let c:=curv p b
  let d:=NatPoly80909.deriv p b
  Nat.ble c.neg c.pos && Nat.ble d.pos d.neg
 else
  let c:=curv p a
  let d:=NatPoly80909.deriv p a
  Nat.ble c.neg c.pos && Nat.ble d.neg d.pos
lemma middle_of_positive(p:Poly)(a b:ℕ)(hab:a≤b)
 (ha:0<value (NatPoly80909.eval p a))(hb:0<value (NatPoly80909.eval p b))
 (hc:positive p a b=true):0≤value (NatPoly80909.mid1 p a b) ∧ 0≤value (NatPoly80909.mid2 p a b):=by
 have hsub:((b-a:ℕ):ℤ)=(b:ℤ)-a:=Int.ofNat_sub hab
 have hab':(a:ℤ)≤b:=by exact_mod_cast hab
 have hh:0≤(b:ℤ)-a:=by omega
 unfold positive at hc
 by_cases h:a=1
 · simp only [h,ite_true,Bool.and_eq_true,Nat.ble_eq] at hc
   have cv:0≤value (curv p b):=by unfold value;omega
   have dv:value (NatPoly80909.deriv p b)≤0:=by unfold value;omega
   have hm:=mul_nonpos_of_nonneg_of_nonpos hh dv
   have hs:=mul_nonneg (sq_nonneg ((b:ℤ)-a)) cv
   have he:value (NatPoly80909.mid1 p a b)=3*value (NatPoly80909.eval p b)-2*((b:ℤ)-a)*value (NatPoly80909.deriv p b)+((b:ℤ)-a)^2*value (curv p b):=by
    simp only [NatPoly80909.mid1,add_eq,scale_eq,NatPoly80909.eval_eq,NatPoly80909.deriv_eq,hsub,Nat.cast_ofNat,curv_eq,Cubic.eval,Cubic.deriv,polyValue]
    ring
   rw [he]
   simp only [NatPoly80909.mid2,sub_eq,scale_eq,hsub,Nat.cast_ofNat]
   constructor <;> nlinarith
 · simp only [h,ite_false,Bool.and_eq_true,Nat.ble_eq] at hc
   have cv:0≤value (curv p a):=by unfold value;omega
   have dv:0≤value (NatPoly80909.deriv p a):=by unfold value;omega
   have hm:=mul_nonneg hh dv
   have hs:=mul_nonneg (sq_nonneg ((b:ℤ)-a)) cv
   have he:value (NatPoly80909.mid2 p a b)=3*value (NatPoly80909.eval p a)+2*((b:ℤ)-a)*value (NatPoly80909.deriv p a)+((b:ℤ)-a)^2*value (curv p a):=by
    simp only [NatPoly80909.mid2,sub_eq,scale_eq,NatPoly80909.eval_eq,NatPoly80909.deriv_eq,hsub,Nat.cast_ofNat,curv_eq,Cubic.eval,Cubic.deriv,polyValue]
    ring
   rw [he]
   simp only [NatPoly80909.mid1,add_eq,scale_eq,hsub,Nat.cast_ofNat]
   constructor <;> nlinarith
def Check(p:Poly)(a b:ℕ):Prop:=b<a ∨
 (eval p a).neg<(eval p a).pos ∧ (eval p b).neg<(eval p b).pos ∧
 (positive p a b=true ∨ (mid1 p a b).neg≤(mid1 p a b).pos ∧ (mid2 p a b).neg≤(mid2 p a b).pos)
instance(p:Poly)(a b:ℕ):Decidable (Check p a b):=by unfold Check;infer_instance
lemma check_iff(p:Poly)(a b:ℕ):Check p a b↔NatPoly80909.NatCheck p a b:=by
 by_cases h:b<a
 · simp only [Check,NatPoly80909.NatCheck,h,true_or]
 · have hab:a≤b:=by omega
   simp only [Check,NatPoly80909.NatCheck,h,false_or]
   constructor
   · rintro ⟨ha,hb,hc⟩
     refine ⟨ha,hb,?_⟩
     rcases hc with hc|hc
     · have hh:=middle_of_positive p a b hab ((pos_iff _).mpr ha) ((pos_iff _).mpr hb) hc
       exact ⟨(nonneg_iff _).mp hh.1,(nonneg_iff _).mp hh.2⟩
     · exact hc
   · rintro ⟨ha,hb,hc⟩
     exact ⟨ha,hb,Or.inr hc⟩
def checkDec(p:Poly)(a b:ℕ):Decidable (NatPoly80909.NatCheck p a b):=
 decidable_of_iff (Check p a b) (check_iff p a b)
#print axioms check_iff
end ProximityPrize.SubmissionLower.MonotoneCheck80909
end
section
namespace ProximityPrize.SubmissionLower.MonotoneBoolCheck80909
open NatPoly80909
set_option autoImplicit false
def check(p:Poly)(a b:ℕ):Bool:=
 Nat.blt b a || (Nat.blt (eval p a).neg (eval p a).pos &&
 (Nat.blt (eval p b).neg (eval p b).pos &&
 (MonotoneCheck80909.positive p a b ||
 (Nat.ble (mid1 p a b).neg (mid1 p a b).pos && Nat.ble (mid2 p a b).neg (mid2 p a b).pos))))
lemma check_iff(p:Poly)(a b:ℕ):check p a b=true ↔ NatCheck p a b:=by
 rw [←MonotoneCheck80909.check_iff]
 simp only [check,MonotoneCheck80909.Check,Bool.or_eq_true,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq]
def checkDec(p:Poly)(a b:ℕ):Decidable (NatCheck p a b):=
 decidable_of_iff (check p a b=true) (check_iff p a b)
#print axioms check_iff
end ProximityPrize.SubmissionLower.MonotoneBoolCheck80909
end
section
namespace ProximityPrize.SubmissionLower.PairedBool80909
open AI AP AN LD NatWideKernel80909 NatPoly80909
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local instance] MonotoneBoolCheck80909.checkDec

def addP(p q:Poly):Poly:=⟨add p.c0 q.c0,add p.c1 q.c1,add p.c2 q.c2,add p.c3 q.c3⟩
def rankSlopeP(base rate s:ℕ):Poly:=
 ⟨⟨s*(s+1)*(4*s+2)+6*(s+1)*base+6*(s+1)*base^2,6*s*(s+1)*base⟩,
 ⟨rate*6*s*(s+1),rate*(6*(s+1)+12*(s+1)*base)⟩,
 ⟨rate^2*6*(s+1),0⟩,⟨0,0⟩⟩
def delta(c:Diff)(b:Band)(d:Rectangle):Poly:=
 let p:=rankSlopeP (d.alpha+d.beta) d.beta d.s
 let q:=rankSlopeP (d.alpha+d.beta) (d.beta+1) (d.s-b.R)
 ⟨sub c (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),
  scale 262144 (sub q.c2 p.c2),⟨0,0⟩⟩
def hiDelta(b:Band)(d:Rectangle):Poly:=delta (scale 12 (sub (counts (cutoff b d) d.s) (counts (cutoff b d-d.lo) (d.s-b.R)))) b d
def tanDelta(b:Band)(d:Rectangle):Poly:=
 let D:=cutoff b d
 delta (scale 12 (sub (add (counts D d.s) (scale (tanK b d) (sub (counts (D+1) d.s) (counts D d.s)))) (counts (tanE b d) (d.s-b.R)))) b d

lemma hi_step(b:Band)(d:Rectangle)(T L:ℕ)(h:T≤L):
 polyValue (addP (margin (hiConstant b d T L) b d T L) (hiDelta b d))=
 polyValue (margin (hiConstant b d T (L+1)) b d T (L+1)):=by
 have hh:L+1-T=(L-T)+1:=by omega
 simp only [polyValue,addP,margin,hiDelta,delta,rankSlopeP,NatPoly80909.rank,hiConstant,hh,
  NatWideKernel80909.add,NatWideKernel80909.sub,NatWideKernel80909.scale,value,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero,sub_zero]
 congr 1 <;> ring
lemma tan_step(b:Band)(d:Rectangle)(T L:ℕ)(h:T≤L):
 polyValue (addP (margin (tanConstant b d T L) b d T L) (tanDelta b d))=
 polyValue (margin (tanConstant b d T (L+1)) b d T (L+1)):=by
 have hh:L+1-T=(L-T)+1:=by omega
 simp only [polyValue,addP,margin,tanDelta,delta,rankSlopeP,NatPoly80909.rank,tanConstant,hh,
  NatWideKernel80909.add,NatWideKernel80909.sub,NatWideKernel80909.scale,value,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero,sub_zero]
 congr 1 <;> ring
def hiFast(b:Band)(d:Rectangle)(a z:ℕ):Prop:=
 let p:=margin (hiConstant b d b.T0 d.L0) b d b.T0 d.L0
 let q:=margin (hiConstant b d b.T1 d.L1) b d b.T1 d.L1
 let r:=hiDelta b d
 NatCheck p a z ∧ NatCheck (addP p r) a z ∧ NatCheck q a z ∧ NatCheck (addP q r) a z
instance(b:Band)(d:Rectangle)(a z:ℕ):Decidable (hiFast b d a z):=by unfold hiFast;infer_instance
lemma hiFast_iff(b:Band)(d:Rectangle)(a z:ℕ)(h:b.T0≤d.L0 ∧ b.T1≤d.L1 ∧ b.R≤d.s):
 hiFast b d a z ↔ corners b d a z:=by
 simp only [hiFast,NatPoly80909.check_iff,hi_step b d b.T0 d.L0 h.1,hi_step b d b.T1 d.L1 h.2.1,
  NatPoly80909.margin_eq,NatPoly80909.hi_eq]
 rw [NatRankWide80909.hi_eq b d b.T0 d.L0 h.1 h.2.2,
  NatRankWide80909.hi_eq b d b.T0 (d.L0+1) (by omega) h.2.2,
  NatRankWide80909.hi_eq b d b.T1 d.L1 h.2.1 h.2.2,
  NatRankWide80909.hi_eq b d b.T1 (d.L1+1) (by omega) h.2.2]
 rfl
def hiDec(b:Band)(d:Rectangle)(a z:ℕ):Decidable (corners b d a z):=
 if h:b.T0≤d.L0 ∧ b.T1≤d.L1 ∧ b.R≤d.s then decidable_of_iff (hiFast b d a z) (hiFast_iff b d a z h)
 else NatPoly80909.cornersDec b d a z
attribute [local instance] hiDec
def tanFast(b:Band)(d:Rectangle)(a z:ℕ):Prop:=
 let p:=margin (tanConstant b d b.T0 d.L0) b d b.T0 d.L0
 let q:=margin (tanConstant b d b.T1 d.L1) b d b.T1 d.L1
 let r:=tanDelta b d
 NatCheck p a z ∧ NatCheck (addP p r) a z ∧ NatCheck q a z ∧ NatCheck (addP q r) a z
instance(b:Band)(d:Rectangle)(a z:ℕ):Decidable (tanFast b d a z):=by unfold tanFast;infer_instance
lemma tanFast_iff(b:Band)(d:Rectangle)(a z:ℕ)(h:b.T0≤d.L0 ∧ b.T1≤d.L1 ∧ b.R≤d.s):
 tanFast b d a z ↔ tanCorners b d a z:=by
 simp only [tanFast,NatPoly80909.check_iff,tan_step b d b.T0 d.L0 h.1,tan_step b d b.T1 d.L1 h.2.1,
  NatPoly80909.margin_eq,NatPoly80909.tan_eq]
 rw [NatRankWide80909.tan_eq b d b.T0 d.L0 h.1 h.2.2,
  NatRankWide80909.tan_eq b d b.T0 (d.L0+1) (by omega) h.2.2,
  NatRankWide80909.tan_eq b d b.T1 d.L1 h.2.1 h.2.2,
  NatRankWide80909.tan_eq b d b.T1 (d.L1+1) (by omega) h.2.2]
 rfl
def tanDec(b:Band)(d:Rectangle)(a z:ℕ):Decidable (tanCorners b d a z):=
 if h:b.T0≤d.L0 ∧ b.T1≤d.L1 ∧ b.R≤d.s then decidable_of_iff (tanFast b d a z) (tanFast_iff b d a z h)
 else NatPoly80909.tanCornersDec b d a z
attribute [local instance] tanDec
attribute [local instance] NatRows80909.rowDec NatRows80909.tanRowDec
def rowsNatDec(b:Band)(d:Rectangle)(w:FastWitness):Decidable (NatRows80909.FastRowsN b d w):=by
 unfold NatRows80909.FastRowsN;infer_instance
attribute [local instance] rowsNatDec
def rowsDec(b:Band)(d:Rectangle)(w:FastWitness):Decidable (FastRows b d w):=
 decidable_of_iff (NatRows80909.FastRowsN b d w) (NatRows80909.FastRows_iff b d w)
attribute [local instance] rowsDec
def tanRowsNatDec(b:Band)(d:Rectangle)(w:FastWitness):Decidable (NatRows80909.TanFastRowsN b d w):=by
 unfold NatRows80909.TanFastRowsN;infer_instance
attribute [local instance] tanRowsNatDec
def tanRowsDec(b:Band)(d:Rectangle)(w:FastWitness):Decidable (TanFastRows b d w):=
 decidable_of_iff (NatRows80909.TanFastRowsN b d w) (NatRows80909.TanFastRows_iff b d w)
attribute [local instance] tanRowsDec
def wideDec(b:Band)(x:WideRow):Decidable (DRX b x):=by unfold DRX WideHeader;infer_instance
attribute [local instance] wideDec
def check(b:Band)(profiles:ℕ→Profile)(stop:ℕ):ℕ→List WideEntry→Bool
 | start,[]=>decide (stop+1=start)
 | start,e::es=>decide (DRX b ⟨wideRect b profiles start e,e.hiW,e.tanW⟩) && check b profiles stop (e.hi+1) es
theorem block_sound(b:Band)(profiles:ℕ→Profile)(start stop:ℕ)(es:List WideEntry)
 (hc:check b profiles stop start es=true):WideCovered b start stop:=by
 intro nu hlo hhi
 induction es generalizing start with
 | nil=>simp only [check,decide_eq_true_eq] at hc;omega
 | cons e es ih=>
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  by_cases he:nu≤e.hi
  · exact ⟨wideRect b profiles start e,EGR b _ hc.1,hlo,he⟩
  · exact ih (e.hi+1) hc.2 (by omega)
#print axioms block_sound
end ProximityPrize.SubmissionLower.PairedBool80909
namespace ProximityPrize.SubmissionLower
abbrev PBCB:=PairedBool80909.block_sound
end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower.AffineRank80909
open AI AP AN NatWideKernel80909 NatPoly80909 PairedBool80909
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def scaleP (k:ℕ)(p:Poly):Poly:=⟨scale k p.c0,scale k p.c1,scale k p.c2,scale k p.c3⟩
def rankFast(base rate L s:ℕ):Poly:=addP (NatPoly80909.rank base rate 0 s) (scaleP L (rankSlopeP base rate s))
lemma rankFast_eq(base rate L s:ℕ):rankFast base rate L s=NatPoly80909.rank base rate L s:=by
 simp only [rankFast,NatPoly80909.rank,scaleP,addP,rankSlopeP,add,scale]
 congr 1 <;> congr 1 <;> ring
def margin(c:Diff)(b:Band)(d:Rectangle)(T L:ℕ):Poly:=
 let p:=rankFast (d.alpha+d.beta) d.beta L d.s
 let q:=rankFast (d.alpha+d.beta) (d.beta+1) (L-T) (d.s-b.R)
 ⟨sub c (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),
  scale 262144 (sub q.c2 p.c2),scale 262144 (sub q.c3 p.c3)⟩
lemma margin_eq(c:Diff)(b:Band)(d:Rectangle)(T L:ℕ):margin c b d T L=NatPoly80909.margin c b d T L:=by simp only [margin,rankFast_eq];rfl
end ProximityPrize.SubmissionLower.AffineRank80909
end
section
namespace ProximityPrize.SubmissionLower.ProfileCached6816
open AI AP AN LD NatWideKernel80909 NatPoly80909 PairedBool80909
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local instance] MonotoneBoolCheck80909.checkDec
structure Parts(base rate s:ℕ) where
 zero:Poly
 slope:Poly
 hz:zero=NatPoly80909.rank base rate 0 s
 hs:slope=rankSlopeP base rate s
def parts(base rate s:ℕ):Parts base rate s:=⟨NatPoly80909.rank base rate 0 s,rankSlopeP base rate s,rfl,rfl⟩
structure CachedProfile where
 p:Profile
 high:Parts (p.alpha+p.beta) p.beta p.s
 low:(R:ℕ)→Parts (p.alpha+p.beta) (p.beta+1) (p.s-R)
def build(a r s:ℕ):CachedProfile:=⟨⟨a,r,s⟩,parts (a+r) r s,fun R=>parts (a+r) (r+1) (s-R)⟩
def fromParts{base rate s:ℕ}(p:Parts base rate s)(L:ℕ):Poly:=addP p.zero (AffineRank80909.scaleP L p.slope)
lemma fromParts_eq{base rate s:ℕ}(p:Parts base rate s)(L:ℕ):fromParts p L=NatPoly80909.rank base rate L s:=by
 rw [fromParts,p.hz,p.hs]
 exact AffineRank80909.rankFast_eq base rate L s

def compatible(c:CachedProfile)(d:Rectangle):Prop:=d.alpha=c.p.alpha ∧ d.beta=c.p.beta ∧ d.s=c.p.s

def margin(c:CachedProfile)(v:Diff)(b:Band)(T L:ℕ):Poly:=
 let p:=fromParts c.high L
 let q:=fromParts (c.low b.R) (L-T)
 ⟨sub v (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),scale 262144 (sub q.c2 p.c2),scale 262144 (sub q.c3 p.c3)⟩
lemma margin_eq(c:CachedProfile)(v:Diff)(b:Band)(d:Rectangle)(T L:ℕ)(hm:compatible c d):margin c v b T L=NatPoly80909.margin v b d T L:=by
 rcases hm with ⟨ha,hb,hs⟩
 simp only [margin,fromParts_eq,NatPoly80909.margin,ha,hb,hs]
def delta(c:CachedProfile)(v:Diff)(b:Band):Poly:=
 let p:=c.high.slope
 let q:=(c.low b.R).slope
 ⟨sub v (scale 262144 (sub p.c0 q.c0)),scale 262144 (sub q.c1 p.c1),scale 262144 (sub q.c2 p.c2),⟨0,0⟩⟩
lemma delta_eq(c:CachedProfile)(v:Diff)(b:Band)(d:Rectangle)(hm:compatible c d):delta c v b=PairedBool80909.delta v b d:=by
 rcases hm with ⟨ha,hb,hs⟩
 simp only [delta,Parts.hs,PairedBool80909.delta,ha,hb,hs]
def hiFast(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Prop:=
 let p:=margin c (hiConstant b d b.T0 d.L0) b b.T0 d.L0
 let q:=margin c (hiConstant b d b.T1 d.L1) b b.T1 d.L1
 let r:=delta c (scale 12 (sub (counts (cutoff b d) d.s) (counts (cutoff b d-d.lo) (d.s-b.R)))) b
 NatCheck p a z ∧ NatCheck (addP p r) a z ∧ NatCheck q a z ∧ NatCheck (addP q r) a z
instance(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Decidable (hiFast c b d a z):=by unfold hiFast;infer_instance
lemma hiFast_iff(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ)(hm:compatible c d):hiFast c b d a z ↔ PairedBool80909.hiFast b d a z:=by
 simp only [hiFast,margin_eq c _ b d _ _ hm,delta_eq c _ b d hm,PairedBool80909.hiFast,PairedBool80909.hiDelta]
def hiCorner(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Bool:=
 if b.T0≤d.L0 ∧ b.T1≤d.L1 ∧ b.R≤d.s then decide (hiFast c b d a z)
 else @decide (corners b d a z) (PairedBool80909.hiDec b d a z)
lemma hiCorner_iff(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ)(hm:compatible c d):hiCorner c b d a z=true ↔ corners b d a z:=by
 unfold hiCorner
 split_ifs with h
 · simp only [decide_eq_true_eq,hiFast_iff c b d a z hm,PairedBool80909.hiFast_iff b d a z h]
 · simp only [decide_eq_true_eq]
def tanFast(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Prop:=
 let p:=margin c (tanConstant b d b.T0 d.L0) b b.T0 d.L0
 let q:=margin c (tanConstant b d b.T1 d.L1) b b.T1 d.L1
 let r:=delta c (scale 12 (sub (add (counts (cutoff b d) d.s) (scale (tanK b d) (sub (counts (cutoff b d+1) d.s) (counts (cutoff b d) d.s)))) (counts (tanE b d) (d.s-b.R)))) b
 NatCheck p a z ∧ NatCheck (addP p r) a z ∧ NatCheck q a z ∧ NatCheck (addP q r) a z
instance(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Decidable (tanFast c b d a z):=by unfold tanFast;infer_instance
lemma tanFast_iff(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ)(hm:compatible c d):tanFast c b d a z ↔ PairedBool80909.tanFast b d a z:=by
 simp only [tanFast,margin_eq c _ b d _ _ hm,delta_eq c _ b d hm,PairedBool80909.tanFast,PairedBool80909.tanDelta]
def tanCorner(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ):Bool:=
 if b.T0≤d.L0 ∧ b.T1≤d.L1 ∧ b.R≤d.s then decide (tanFast c b d a z)
 else @decide (tanCorners b d a z) (PairedBool80909.tanDec b d a z)
lemma tanCorner_iff(c:CachedProfile)(b:Band)(d:Rectangle)(a z:ℕ)(hm:compatible c d):tanCorner c b d a z=true ↔ tanCorners b d a z:=by
 unfold tanCorner
 split_ifs with h
 · simp only [decide_eq_true_eq,tanFast_iff c b d a z hm,PairedBool80909.tanFast_iff b d a z h]
 · simp only [decide_eq_true_eq]
def hiRows(c:CachedProfile)(b:Band)(d:Rectangle)(w:FastWitness):Bool:=
 Nat.ble 1 w.firstExact && Nat.ble w.firstExact w.lastExact && Nat.ble w.lastExact w.normalEnd && Nat.ble w.normalEnd (b.B+b.R) &&
 Nat.ble w.normalEnd (d.alpha-d.beta*(w.normalEnd-1)) && Nat.ble (2*d.s) (d.alpha-d.beta*(w.normalEnd-1)) &&
 Nat.ble (2*(d.s-b.R)) (d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd) &&
 hiCorner c b d 1 (w.firstExact-1) && hiCorner c b d (w.lastExact+1) w.normalEnd &&
 @decide (rowGood b d 0) (NatRows80909.rowDec b d 0) &&
 NatRows80909.range b d w.firstExact (w.lastExact+1-w.firstExact) && NatRows80909.range b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)
lemma hiRows_iff(c:CachedProfile)(b:Band)(d:Rectangle)(w:FastWitness)(hm:compatible c d):hiRows c b d w=true ↔ FastRows b d w:=by
 rw [←NatRows80909.FastRows_iff]
 simp only [hiRows,NatRows80909.FastRowsN,Bool.and_eq_true,Nat.ble_eq,decide_eq_true_eq,hiCorner_iff c b d _ _ hm,and_assoc]
def tanRows(c:CachedProfile)(b:Band)(d:Rectangle)(w:FastWitness):Bool:=
 Nat.ble 1 w.firstExact && Nat.ble w.firstExact w.lastExact && Nat.ble w.lastExact w.normalEnd && Nat.ble w.normalEnd (b.B+b.R) &&
 Nat.ble w.normalEnd (d.alpha-d.beta*(w.normalEnd-1)) && Nat.ble (2*d.s) (d.alpha-d.beta*(w.normalEnd-1)) &&
 Nat.ble (2*(d.s-b.R)) (d.alpha-d.beta*(w.normalEnd-1)-w.normalEnd) &&
 tanCorner c b d 1 (w.firstExact-1) && tanCorner c b d (w.lastExact+1) w.normalEnd &&
 @decide (tanRowGood b d 0) (NatRows80909.tanRowDec b d 0) &&
 NatRows80909.tanRange b d w.firstExact (w.lastExact+1-w.firstExact) && NatRows80909.tanRange b d (w.normalEnd+1) (b.B+b.R-w.normalEnd)
lemma tanRows_iff(c:CachedProfile)(b:Band)(d:Rectangle)(w:FastWitness)(hm:compatible c d):tanRows c b d w=true ↔ TanFastRows b d w:=by
 rw [←NatRows80909.TanFastRows_iff]
 simp only [tanRows,NatRows80909.TanFastRowsN,Bool.and_eq_true,Nat.ble_eq,decide_eq_true_eq,tanCorner_iff c b d _ _ hm,and_assoc]
instance headerDec(b:Band)(d:Rectangle):Decidable (WideHeader b d):=by unfold WideHeader;infer_instance
def valid(b:Band)(profiles:ℕ→CachedProfile)(start:ℕ)(e:WideEntry):Bool:=
 let c:=profiles e.profile
 let d:=wideRect b (fun i=>(profiles i).p) start e
 decide (WideHeader b d) && hiRows c b (hiRect d) e.hiW && tanRows c b d e.tanW
lemma valid_iff(b:Band)(profiles:ℕ→CachedProfile)(start:ℕ)(e:WideEntry):valid b profiles start e=true ↔ DRX b ⟨wideRect b (fun i=>(profiles i).p) start e,e.hiW,e.tanW⟩:=by
 have hm:compatible (profiles e.profile) (wideRect b (fun i=>(profiles i).p) start e):=⟨rfl,rfl,rfl⟩
 have hh:compatible (profiles e.profile) (hiRect (wideRect b (fun i=>(profiles i).p) start e)):=⟨rfl,rfl,rfl⟩
 simp only [valid,DRX,Bool.and_eq_true,decide_eq_true_eq,hiRows_iff _ _ _ _ hh,tanRows_iff _ _ _ _ hm,and_assoc]
def check(b:Band)(profiles:ℕ→CachedProfile)(stop:ℕ):ℕ→List WideEntry→Bool
 | start,[]=>Nat.beq (stop+1) start
 | start,e::es=>valid b profiles start e && check b profiles stop (e.hi+1) es
theorem block_sound(b:Band)(profiles:ℕ→CachedProfile)(start stop:ℕ)(es:List WideEntry)
 (hc:check b profiles stop start es=true):WideCovered b start stop:=by
 intro nu hlo hhi
 induction es generalizing start with
 | nil=>simp only [check,Nat.beq_eq] at hc;omega
 | cons e es ih=>
  simp only [check,Bool.and_eq_true,valid_iff] at hc
  by_cases he:nu≤e.hi
  · exact ⟨wideRect b (fun i=>(profiles i).p) start e,EGR b _ hc.1,hlo,he⟩
  · exact ih (e.hi+1) hc.2 (by omega)
#print axioms block_sound
end ProximityPrize.SubmissionLower.ProfileCached6816
namespace ProximityPrize.SubmissionLower
abbrev PRB:=ProfileCached6816.block_sound
end ProximityPrize.SubmissionLower
end
section
namespace ProximityPrize.SubmissionLower.Z0
open ProfileCached6816
def p0:CachedProfile:=build 0 0 0
def p1:CachedProfile:=⟨⟨156780,926,36454⟩,⟨⟨⟨5682346560459160,287745945755569099720⟩,⟨5037523044970029120,63885071878400⟩,⟨187555725480,29578663242548880⟩,⟨57892200598160,0⟩⟩,⟨⟨5633890227115920,1257481946834520⟩,⟨7383538246920,63885004363740⟩,⟨187555725480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨5679470959732554,287609292108208334862⟩,⟨5040611451082908360,63924238644480⟩,⟨187873380612,29628759362796072⟩,⟨58052874609108,0⟩⟩,⟨⟨5631082374989676,1256309405247816⟩,⟨7384619600172,63924171088428⟩,⟨187873380612,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 157706 927 (36454-R)⟩
def p2:CachedProfile:=⟨⟨82392,332,18149⟩,⟨⟨⟨775135501240650,20658325572403858350⟩,⟨247418015358175200,5981787556800⟩,⟨12003393600,992968732166400⟩,⟨1328375558400,0⟩⟩,⟨⟨769154138811300,163497872696400⟩,⟨656173465200,5981775505200⟩,⟨12003393600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨774353558304856,20638671545021789056⟩,⟨247930809704346960,5994185337144⟩,⟨12064501422,998023815633528⟩,⟨1339159657842,0⟩⟩,⟨⟨768388982270880,163191730695264⟩,⟨656917536888,5994173260566⟩,⟨12064501422,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 82724 333 (18149-R)⟩
def p3:CachedProfile:=⟨⟨89136,27,27841⟩,⟨⟨⟨1435996220768810,40073237690422291862⟩,⟨35858145930895404,804328317576⟩,⟨121780908,10858351100004⟩,⟨1096028172,0⟩⟩,⟨⟨1414410329110716,414687726989316⟩,⟨125574157764,804326814108⟩,⟨121780908,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1435402980868920,40058197341053367672⟩,⟨37172869154600256,833818665344⟩,⟨130921728,11673374033664⟩,⟨1221936128,0⟩⟩,⟨⟨1413840336837936,414389888687376⟩,⟨130131521856,833817106752⟩,⟨130921728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨1435343661471618,40056693357261446394⟩,⟨37171533529082232,833788706352⟩,⟨130917024,11672954610912⟩,⟨1221892224,0⟩⟩,⟨⟨1413783341284812,414360110741940⟩,⟨130122170640,833787147816⟩,⟨130917024,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 12=>⟨⟨⟨1435284342909230,40055189382765938810⟩,⟨37170197903564880,833758747360⟩,⟨130912320,11672535188160⟩,⟨1221848320,0⟩⟩,⟨⟨1413726346399620,414330333866460⟩,⟨130112819760,833757188880⟩,⟨130912320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨1435225025181726,40053685417566177006⟩,⟨37168862278048200,833728788368⟩,⟨130907616,11672115765408⟩,⟨1221804416,0⟩⟩,⟨⟨1413669352182336,414300558060936⟩,⟨130103469216,833727229944⟩,⟨130907616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨1435165708289076,40052181461661493092⟩,⟨37167526652532192,833698829376⟩,⟨130902912,11671696342656⟩,⟨1221760512,0⟩⟩,⟨⟨1413612358632936,414270783325368⟩,⟨130094119008,833697271008⟩,⟨130902912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨1435106392231250,40050677515051219202⟩,⟨37166191027016856,833668870384⟩,⟨130898208,11671276919904⟩,⟨1221716608,0⟩⟩,⟨⟨1413555365751396,414241009659756⟩,⟨130084769136,833667312072⟩,⟨130898208,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨1435047077008218,40049173577734687494⟩,⟨37164855401502192,833638911392⟩,⟨130893504,11670857497152⟩,⟨1221672704,0⟩⟩,⟨⟨1413498373537692,414211237064100⟩,⟨130075419600,833637353136⟩,⟨130893504,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 17=>⟨⟨⟨1434987762619950,40047669649711230150⟩,⟨37163519775988200,833608952400⟩,⟨130888800,11670438074400⟩,⟨1221628800,0⟩⟩,⟨⟨1413441381991800,414181465538400⟩,⟨130066070400,833607394200⟩,⟨130888800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 18=>⟨⟨⟨1434928449066416,40046165730980179376⟩,⟨37162184150474880,833578993408⟩,⟨130884096,11670018651648⟩,⟨1221584896,0⟩⟩,⟨⟨1413384391113696,414151695082656⟩,⟨130056721536,833577435264⟩,⟨130884096,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 89163 28 (27841-R)⟩
def p4:CachedProfile:=⟨⟨202981,1222,47391⟩,⟨⟨⟨12389427727048480,812138630878663112992⟩,⟨14489477224402936704,141912622182656⟩,⟨424618291968,86708329074741504⟩,⟨172961184261632,0⟩⟩,⟨⟨12282970352966976,2751783601231296⟩,⟨16467336722304,141912506356608⟩,⟨424618291968,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨12385737353984466,811911704521193269506⟩,⟨14497356567445571430,141989794015548⟩,⟨425196865746,86826475575930438⟩,⟨173338588935786,0⟩⟩,⟨⟨12279367552787556,2750274120403116⟩,⟨16471771958556,141989678126514⟩,⟨425196865746,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 204203 1223 (47391-R)⟩
def p5:CachedProfile:=⟨⟨59638,321,10550⟩,⟨⟨⟨233467287930258,4561163929366393458⟩,⟨73056896105929506,2436907874436⟩,⟨6523113546,391119365104614⟩,⟨697973149422,0⟩⟩,⟨⟨232291669997940,40045314989700⟩,⟨214388934300,2436901100694⟩,⟨6523113546,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨233072242507646,4553755055099707706⟩,⟨73166409434886936,2440560857168⟩,⟨6553243536,392925929175024⟩,⟨703381472864,0⟩⟩,⟨⟨231902294257908,39916369082988⟩,⟨214364329704,2440554073272⟩,⟨6553243536,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 59959 322 (10550-R)⟩
def p6:CachedProfile:=⟨⟨1998,10,539⟩,⟨⟨⟨13857550740,8835667696980⟩,⟨130673800800,130161600⟩,⟨324000,650592000⟩,⟨1080000,0⟩⟩,⟨⟨13698500760,3506690880⟩,⟨17463600,130150800⟩,⟨324000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨13572616830,8667382399410⟩,⟨141078607560,140526320⟩,⟨384780,772638240⟩,⟨1410860,0⟩⟩,⟨⟨13422172620,3377897760⟩,⟨18504420,140514660⟩,⟨384780,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨13544211296,8650572832256⟩,⟨140812351680,140261176⟩,⟨384054,771180432⟩,⟨1408198,0⟩⟩,⟨⟨13394610096,3365150976⟩,⟨18434592,140249538⟩,⟨384054,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 12=>⟨⟨⟨13515821616,8633766661872⟩,⟨140546096064,139996032⟩,⟨383328,769722624⟩,⟨1405536,0⟩⟩,⟨⟨13367060256,3352428288⟩,⟨18364896,139984416⟩,⟨383328,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨13487447760,8616963875592⟩,⟨140279840712,139730888⟩,⟨382602,768264816⟩,⟨1402874,0⟩⟩,⟨⟨13339523076,3339729696⟩,⟨18295332,139719294⟩,⟨382602,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨13459089698,8600164460774⟩,⟨140013585624,139465744⟩,⟨381876,766807008⟩,⟨1400212,0⟩⟩,⟨⟨13311998532,3327055200⟩,⟨18225900,139454172⟩,⟨381876,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨13430747400,8583368404800⟩,⟨139747330800,139200600⟩,⟨381150,765349200⟩,⟨1397550,0⟩⟩,⟨⟨13284486600,3314404800⟩,⟨18156600,139189050⟩,⟨381150,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨13402420836,8566575695076⟩,⟨139481076240,138935456⟩,⟨380424,763891392⟩,⟨1394888,0⟩⟩,⟨⟨13256987256,3301778496⟩,⟨18087432,138923928⟩,⟨380424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2008 11 (539-R)⟩
def p7:CachedProfile:=⟨⟨9247,59,1751⟩,⟨⟨⟨937351134792,2833673858155560⟩,⟨53713199428704,11544138240⟩,⟨36592272,340527683232⟩,⟨719648016,0⟩⟩,⟨⟨931946892816,171291000672⟩,⟨1085984208,11543931504⟩,⟨36592272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨928871547192,2809172435394960⟩,⟨54155906134560,11639289600⟩,⟨37519200,349153675200⟩,⟨750384000,0⟩⟩,⟨⟨923604428196,168369661152⟩,⟨1085555520,11639081160⟩,⟨37519200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨928306659224,2807539299954872⟩,⟨54124727045760,11632588800⟩,⟨37497600,348952665600⟩,⟨749952000,0⟩⟩,⟨⟨923048598192,168175798560⟩,⟨1084305600,11632380480⟩,⟨37497600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 17=>⟨⟨⟨927741823320,2805906200871240⟩,⟨54093547958400,11625888000⟩,⟨37476000,348751656000⟩,⟨749520000,0⟩⟩,⟨⟨922492809840,167982047640⟩,⟨1083056400,11625679800⟩,⟨37476000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9306 60 (1751-R)⟩
def p8:CachedProfile:=⟨⟨289409,1486,73598⟩,⟨⟨⟨39361128542305074,3652712841533134062738⟩,⟨55528410483118951164,381776525209272⟩,⟨975126104424,283659308146419480⟩,⟨483012463724688,0⟩⟩,⟨⟨38962424551354068,9454214100994740⟩,⟨48295646725032,381776306473044⟩,⟨975126104424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨39354061028296194,3652102932229387553802⟩,⟨55556718412093285158,381971151864012⟩,⟨976279759218,283994900557720110⟩,⟨483909333985722,0⟩⟩,⟨⟨38955552014262012,9451131393593340⟩,⟨48312388945404,381970933016274⟩,⟨976279759218,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 290895 1487 (73598-R)⟩
def p9:CachedProfile:=⟨⟨46558,207,11789⟩,⟨⟨⟨162903510588870,2431002673220526810⟩,⟨32024470700313540,1369596149640⟩,⟨3031138260,141751180728900⟩,⟨209148539940,0⟩⟩,⟨⟨161263827527580,38999852262900⟩,⟨172628449020,1369591268580⟩,⟨3031138260,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨162705848965854,2428258328608701162⟩,⟨32143696199757792,1374695103808⟩,⟨3057120768,142966252715520⟩,⟨211960373248,0⟩⟩,⟨⟨161071581692292,38913891271680⟩,⟨173080068096,1374690204576⟩,⟨3057120768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 46765 208 (11789-R)⟩
def p10:CachedProfile:=⟨⟨25504,152,6348⟩,⟨⟨⟨26355241712520,216074725841459520⟩,⟨3811416729273216,297118978240⟩,⟨880123776,22580455597056⟩,⟨44592937984,0⟩⟩,⟨⟨26099069619336,6204152187072⟩,⟨36756748224,297117048144⟩,⟨880123776,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨26309709903240,215726726336953560⟩,⟨3830449051916424,298602651960⟩,⟨890337906,22842509316336⟩,⟨45407233206,0⟩⟩,⟨⟨26054745459756,6184622326752⟩,⟨36882102276,298600712226⟩,⟨890337906,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25656 153 (6348-R)⟩
def p11:CachedProfile:=⟨⟨297156,1397,76896⟩,⟨⟨⟨43398427493997550,4127626716682406470162⟩,⟨57451408674891681054,384865922208196⟩,⟨900437263638,268828246370915814⟩,⟨419303619100762,0⟩⟩,⟨⟨42943690015971516,10592191792996416⟩,⟨49563367089984,384865707357978⟩,⟨900437263638,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨43390322166168276,4126911180654624116436⟩,⟨57482813970187844400,385076305811808⟩,⟨901574382816,269167736712865248⟩,⟨420133662392256,0⟩⟩,⟨⟨42935815265717496,10588610697529896⟩,⟨49582076733936,385076090844144⟩,⟨901574382816,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 298553 1398 (76896-R)⟩
def p12:CachedProfile:=⟨⟨4134,1,1270⟩,⟨⟨⟨140686316370,182405939581650⟩,⟨130410433890,63077188⟩,⟨7626,31533510⟩,⟨2542,0⟩⟩,⟨⟨138625809300,40047557700⟩,⟨9685020,63074646⟩,⟨7626,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨139419879950,180909639834950⟩,⟨258768473340,125161816⟩,⟨30264,125141640⟩,⟨20176,0⟩⟩,⟨⟨137407487880,39419616600⟩,⟨19066320,125156772⟩,⟨30264,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨139293444780,180760115729340⟩,⟨258563234160,125062560⟩,⟨30240,125042400⟩,⟨20160,0⟩⟩,⟨⟨137285822520,39357095400⟩,⟨19036080,125057520⟩,⟨30240,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 12=>⟨⟨⟨139167047394,180610610751498⟩,⟨258357995028,124963304⟩,⟨30216,124943160⟩,⟨20144,0⟩⟩,⟨⟨137164187388,39294623820⟩,⟨19005864,124958268⟩,⟨30216,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨138788081640,180162210282600⟩,⟨257742277920,124665536⟩,⟨30144,124645440⟩,⟨20096,0⟩⟩,⟨⟨136799463120,39107506800⟩,⟨18915360,124660512⟩,⟨30144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨138661835090,180012781513970⟩,⟨257537038980,124566280⟩,⟨30120,124546200⟩,⟨20080,0⟩⟩,⟨⟨136677948660,39045233700⟩,⟨18885240,124561260⟩,⟨30120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4135 2 (1270-R)⟩
def p13:CachedProfile:=⟨⟨105285,794,25796⟩,⟨⟨⟨1827577984968750,62030439396514806534⟩,⟨1382935043200064364,26073726070008⟩,⟨97580144952,10351204196363208⟩,⟨25826211697296,0⟩⟩,⟨⟨1810406320936872,423547613793288⟩,⟨3170248638768,26073685104372⟩,⟨97580144952,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨1826725540148578,62003422871957651038⟩,⟨1384086337564467420,26095432515720⟩,⟨97784379900,10372869235412100⟩,⟨25912860673500,0⟩⟩,⟨⟨1809575828964540,423186477172740⟩,⟨3171534887700,26095391515980⟩,⟨97784379900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 106079 795 (25796-R)⟩
def p14:CachedProfile:=⟨⟨43768,250,10158⟩,⟨⟨⟨123348578952616,1743596200333826536⟩,⟨29526188306640000,1341556904000⟩,⟨3809625000,167692073250000⟩,⟨317468750000,0⟩⟩,⟨⟨122299428545616,27254657281176⟩,⟨154792683000,1341551824500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 8=>⟨⟨⟨123243198504088,1742197993361214664⟩,⟨29620948554565344,1345862457824⟩,⟨3837138906,168903180364308⟩,⟨321040621802,0⟩⟩,⟨⟨122196523453152,27211747126200⟩,⟨155167170900,1345857362022⟩,⟨3837138906,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨123216856437696,1741848453996808176⟩,⟨29615112428300280,1345597289376⟩,⟨3836382894,168869902228092⟩,⟨320977368798,0⟩⟩,⟨⟨122170799616636,27201024869616⟩,⟨155106030312,1345592194578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨123203685861196,1741673686170076972⟩,⟨29612194365176784,1345464705152⟩,⟨3836004888,168853263159984⟩,⟨320945742296,0⟩⟩,⟨⟨122157938063736,27195664533648⟩,⟨155075464536,1345459610856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44018 251 (10158-R)⟩
def p15:CachedProfile:=⟨⟨36748,194,8831⟩,⟨⟨⟨75765437299584,896650681642979712⟩,⟨14030025785883648,759574327296⟩,⟨1994406912,73677380143104⟩,⟨128971646976,0⟩⟩,⟨⟨75076007449344,17287834627584⟩,⟨90786636288,759570900480⟩,⟨1994406912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨75643799361344,895304049178589720⟩,⟨14081587709670000,762365862960⟩,⟨2012054850,74329330268700⟩,⟨130783565250,0⟩⟩,⟨⟨74957407701792,17236976576184⟩,⟨90986152140,762362423550⟩,⟨2012054850,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 36942 195 (8831-R)⟩
def p16:CachedProfile:=⟨⟨36533,140,9785⟩,⟨⟨⟨83655598032258,974537569739182134⟩,⟨11055635044619760,602932683360⟩,⟨1150833600,42204520612800⟩,⟨53705568000,0⟩⟩,⟨⟨82717907710452,21069960928380⟩,⟨80435048400,602929943280⟩,⟨1150833600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨83532043822206,973206465551476842⟩,⟨11119812127768134,606432671412⟩,⟨1165782078,42752726146494⟩,⟨54791757666,0⟩⟩,⟨⟨82598083852116,21014015386728⟩,⟨80794485576,606429915426⟩,⟨1165782078,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 36673 141 (9785-R)⟩
def p17:CachedProfile:=⟨⟨44518,250,10158⟩,⟨⟨⟨127407536289616,1833692565569246536⟩,⟨30540912402390000,1364414654000⟩,⟨3809625000,170549292000000⟩,⟨317468750000,0⟩⟩,⟨⟨126358370644116,27719035330176⟩,⟨154792683000,1364409574500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 8=>⟨⟨⟨127298959497088,1832223408862722664⟩,⟨30638929276402344,1368793566824⟩,⟨3837138906,171781034543808⟩,⟨321040621802,0⟩⟩,⟨⟨126252269219652,27675394051200⟩,⟨155167170900,1368788471022⟩,⟨3837138906,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 9=>⟨⟨⟨127285388768650,1832039769845289550⟩,⟨30635910929479800,1368658723600⟩,⟨3836760900,171764111971200⟩,⟨321008995300,0⟩⟩,⟨⟨126239007638100,27669941308800⟩,⟨155136599100,1368653628300⟩,⟨3836760900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨127271818344696,1831856132065018176⟩,⟨30632892582563280,1368523880376⟩,⟨3836382894,171747189398592⟩,⟨320977368798,0⟩⟩,⟨⟨126225746300136,27664489103616⟩,⟨155106030312,1368518785578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨127258248225196,1831672495521664972⟩,⟨30629874235652784,1368389037152⟩,⟨3836004888,171730266825984⟩,⟨320945742296,0⟩⟩,⟨⟨126212485205736,27659037435648⟩,⟨155075464536,1368383942856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44768 251 (10158-R)⟩
def p18:CachedProfile:=⟨⟨25214,139,5555⟩,⟨⟨⟨22285958917428,182045871859242804⟩,⟨2978478757273176,234962773296⟩,⟨644084856,16329483354168⟩,⟨29842598328,0⟩⟩,⟨⟨22114230007992,4694906062440⟩,⟨25740225720,234961228728⟩,⟨644084856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨22242769259378,181713073708139654⟩,⟨2994507168789360,236227211360⟩,⟨652209600,16535469988800⟩,⟨30436448000,0⟩⟩,⟨⟨22071965043252,4678019443260⟩,⟨25832158800,236225658480⟩,⟨652209600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25353 140 (5555-R)⟩
def p19:CachedProfile:=⟨⟨25336,139,5555⟩,⟨⟨⟨22492681409460,184672675888510500⟩,⟨3007212429916440,236093397072⟩,⟨644084856,16408061706600⟩,⟨29842598328,0⟩⟩,⟨⟨22320951144360,4717498203000⟩,⟨25740225720,236091852504⟩,⟨644084856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨22449119680690,184335149787190750⟩,⟨3023395469967600,237363919520⟩,⟨652209600,16615039560000⟩,⟨30436448000,0⟩⟩,⟨⟨22278314111340,4700530324500⟩,⟨25832158800,237362366640⟩,⟨652209600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25475 140 (5555-R)⟩
def p20:CachedProfile:=⟨⟨108097,661,25021⟩,⟨⟨⟨1854154914104290,64770501011772375622⟩,⟨1173813208306478712,21585822422368⟩,⟨65595823572,7134070580043576⟩,⟨14452946460364,0⟩⟩,⟨⟨1838484437284236,408544290577176⟩,⟨2483015282292,21585789343284⟩,⟨65595823572,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨1853110274222056,64736239238135970736⟩,⟨1174978251142029840,21607247009632⟩,⟨65760265176,7151954920011408⟩,⟨14511098515504,0⟩⟩,⟨⟨1837464204163836,408119879883456⟩,⟨2484188385984,21607213897716⟩,⟨65760265176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 108758 662 (25021-R)⟩
def p21:CachedProfile:=⟨⟨2984,24,635⟩,⟨⟨⟨35825780148,34796909502324⟩,⟨828774205056,551091456⟩,⟨2198016,6611632128⟩,⟨17584128,0⟩⟩,⟨⟨35565502872,7288865280⟩,⟨58155840,551060928⟩,⟨2198016,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 8=>⟨⟨⟨35343429916,34353030018172⟩,⟨852445755600,566832800⟩,⟨2355000,7083840000⟩,⟨19625000,0⟩⟩,⟨⟨35092766856,7106508288⟩,⟨59063400,566801400⟩,⟨2355000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 9=>⟨⟨⟨35283221160,34297566811992⟩,⟨851088169800,565930200⟩,⟨2351250,7072560000⟩,⟨19593750,0⟩⟩,⟨⟨35033742876,7083876096⟩,⟨58875300,565898850⟩,⟨2351250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨35223031198,34242108384274⟩,⟨849730584600,565027600⟩,⟨2347500,7061280000⟩,⟨19562500,0⟩⟩,⟨⟨34974733932,7061280000⟩,⟨58687500,564996300⟩,⟨2347500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (635-R)⟩
def p22:CachedProfile:=⟨⟨43018,250,10158⟩,⟨⟨⟨119358194865616,1656518292416906536⟩,⟨28528607523390000,1318699154000⟩,⟨3809625000,164834854500000⟩,⟨317468750000,0⟩⟩,⟨⟨118309059697116,26790279232176⟩,⟨154792683000,1318694074500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨119243178368650,1655022459500589550⟩,⟨28617346690879800,1322801023600⟩,⟨3836760900,166008970621200⟩,⟨321008995300,0⟩⟩,⟨⟨118196827688100,26742830158800⟩,⟨155136599100,1322795928300⟩,⟨3836760900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨119230400280696,1654856262032098176⟩,⟨28614527217287280,1322670698376⟩,⟨3836382894,165992615057592⟩,⟨320977368798,0⟩⟩,⟨⟨118184358683136,26737560635616⟩,⟨155106030312,1322665603578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨119217622497196,1654690065800488972⟩,⟨28611707743700784,1322540373152⟩,⟨3836004888,165976259493984⟩,⟨320945742296,0⟩⟩,⟨⟨118171889921736,26732291631648⟩,⟨155075464536,1322535278856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43268 251 (10158-R)⟩
def p23:CachedProfile:=⟨⟨24400,167,5079⟩,⟨⟨⟨19052097191640,151316575202571480⟩,⟨3072154090853520,250106708320⟩,⟨850056720,20883343440240⟩,⟨47319824080,0⟩⟩,⟨⟨18920802686640,3803166170640⟩,⟨25852922640,250105011600⟩,⟨850056720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19012020443910,151014777093820770⟩,⟨3084466360641120,251109069120⟩,⟨858574080,21092589423360⟩,⟨48080148480,0⟩⟩,⟨⟨18881498896260,3788206341660⟩,⟨25905428640,251107365600⟩,⟨858574080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨18995994004850,150894066507938126⟩,⟨3082032815756832,250910955456⟩,⟨857896704,21075948327168⟩,⟨48042215424,0⟩⟩,⟨⟨18865780788156,3782230664580⟩,⟨25864564320,250909253280⟩,⟨857896704,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24567 168 (5079-R)⟩
def p24:CachedProfile:=⟨⟨4130,1,1270⟩,⟨⟨⟨140434129634,181884802219562⟩,⟨130158287826,63016180⟩,⟨7626,31503006⟩,⟨2542,0⟩⟩,⟨⟨138373632732,40008817620⟩,⟨9685020,63013638⟩,⟨7626,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨139169677374,180392603293422⟩,⟨258268148892,125040760⟩,⟨30264,125020584⟩,⟨20176,0⟩⟩,⟨⟨137157295392,39381483960⟩,⟨19066320,125035716⟩,⟨30264,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4131 2 (1270-R)⟩
def p25:CachedProfile:=⟨⟨25215,139,5555⟩,⟨⟨⟨22287649330428,182067300609150108⟩,⟨2978713718501904,234972040704⟩,⟨644084856,16330127439024⟩,⟨29842598328,0⟩⟩,⟨⟨22115920409880,4695091243920⟩,⟨25740225720,234970496136⟩,⟨644084856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨22244456629878,181734463888717098⟩,⟨2994743394447840,236236528640⟩,⟨652209600,16536122198400⟩,⟨30436448000,0⟩⟩,⟨⟨22073652402660,4678203958680⟩,⟨25832158800,236234975760⟩,⟨652209600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25354 140 (5555-R)⟩
def p26:CachedProfile:=⟨⟨57480,425,12354⟩,⟨⟨⟨257991286816690,4820967047376009670⟩,⟨105637535911598250,3648665009500⟩,⟨13389731250,775332388031250⟩,⟨1896878593750,0⟩⟩,⟨⟨256104219624960,53029515968100⟩,⟨389215858500,3648654507750⟩,⟨13389731250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨257700015553134,4815820902274925202⟩,⟨105774680059105464,3653401924656⟩,⟨13438660752,778165650844560⟩,⟨1908289826784,0⟩⟩,⟨⟨255818896158012,52917974261460⟩,⟨389311061832,3653391409272⟩,⟨13438660752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 57905 426 (12354-R)⟩
def p27:CachedProfile:=⟨⟨19941,112,3471⟩,⟨⟨⟨8586753971600,56142902045893712⟩,⟨938242700957184,93577788416⟩,⟨261316608,5240181940224⟩,⟨9755820032,0⟩⟩,⟨⟨8544784619616,1449989757216⟩,⟨8098481664,93577010688⟩,⟨261316608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨8542676716530,55865882161084710⟩,⟨941984840775330,93951027260⟩,⟨264701370,5308056572610⟩,⟨9970418270,0⟩⟩,⟨⟨8501319599520,1435823275260⟩,⟨8090960460,93950246430⟩,⟨264701370,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 20053 113 (3471-R)⟩
def p28:CachedProfile:=⟨⟨16536,4,5080⟩,⟨⟨⟨8996439330480,46652996710790400⟩,⟨33361654141440,4034070112⟩,⟨487776,8067815040⟩,⟨650368,0⟩⟩,⟨⟨8865148932600,2561531275200⟩,⟨619475520,4034029464⟩,⟨487776,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨8976159655760,46557249908186600⟩,⟨41619990106200,5032663240⟩,⟨760650,12581151000⟩,⟨1267750,0⟩⟩,⟨⟨8845642359180,2551457422800⟩,⟨771299100,5032612530⟩,⟨760650,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16540 5 (5080-R)⟩
def p29:CachedProfile:=⟨⟨24592,152,5079⟩,⟨⟨⟨19318135257480,154596206178668520⟩,⟨2836648799274240,229282101760⟩,⟨704209920,17424970260480⟩,⟨35679969280,0⟩⟩,⟨⟨19186838954160,3830567172480⟩,⟨23530803840,229280557440⟩,⟨704209920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19277534812770,154287951995742630⟩,⟨2849690178471240,230336224560⟩,⟨712101780,17620246444320⟩,⟨36317190780,0⟩⟩,⟨⟨19147011470340,3815499561120⟩,⟨23592443940,230334673140⟩,⟨712101780,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19257240295440,154133836497941760⟩,⟨2846879786630880,230109068520⟩,⟨711399510,17602869475440⟩,⟨36281375010,0⟩⟩,⟨⟨19127102292480,3807976890240⟩,⟨23545928880,230107518630⟩,⟨711399510,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24744 153 (5079-R)⟩
def p30:CachedProfile:=⟨⟨42518,250,10158⟩,⟨⟨⟨116736035057616,1600117877038126536⟩,⟨27873077730390000,1303460654000⟩,⟨3809625000,162930042000000⟩,⟨317468750000,0⟩⟩,⟨⟨115686910048116,26480693866176⟩,⟨154792683000,1303455574500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨116623341568650,1598672010585689550⟩,⟨27959777844679800,1307515123600⟩,⟨3836760900,164090590171200⟩,⟨321008995300,0⟩⟩,⟨⟨115577001038100,26433793108800⟩,⟨155136599100,1307510028300⟩,⟨3836760900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨116610821592696,1598511364946458176⟩,⟨27957023156195280,1307386304376⟩,⟨3836382894,164074423610592⟩,⟨320977368798,0⟩⟩,⟨⟨115564790144136,26428584479616⟩,⟨155106030312,1307381209578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨116598301921196,1598350720544096972⟩,⟨27954268467716784,1307257485152⟩,⟨3836004888,164058257049984⟩,⟨320945742296,0⟩⟩,⟨⟨115552579493736,26423376363648⟩,⟨155075464536,1307252390856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42768 251 (10158-R)⟩
def p31:CachedProfile:=⟨⟨24334,159,5079⟩,⟨⟨⟨18941438373080,149959357737362360⟩,⟨2907390758628240,237408293280⟩,⟨770564880,18873445605840⟩,⟨40839938640,0⟩⟩,⟨⟨18810144619920,3791710384560⟩,⟨24614459280,237406677840⟩,⟨770564880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18901579457670,149660231361556890⟩,⟨2919916932566400,238431148800⟩,⟨778752000,19073972736000⟩,⟨41533440000,0⟩⟩,⟨⟨18771058660380,3776795617140⟩,⟨24671836800,238429526400⟩,⟨778752000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨18881655704990,149510679767090330⟩,⟨2917037281444800,238196009600⟩,⟨777984000,19055162112000⟩,⟨41492480000,0⟩⟩,⟨⟨18751520244660,3769349255280⟩,⟨24623193600,238194388800⟩,⟨777984000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24493 160 (5079-R)⟩
def p32:CachedProfile:=⟨⟨24794,145,5396⟩,⟨⟨⟨20926957683870,168281357569974894⟩,⟨2920365954695070,234202922940⟩,⟨680831550,16979258025450⟩,⟨32906858250,0⟩⟩,⟨⟨20769545036352,4357673070408⟩,⟨25336324440,234201357810⟩,⟨680831550,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20885278277330,167964839226009554⟩,⟨2935057906040916,235381172552⟩,⟨688975752,17182366279128⟩,⟨33530153264,0⟩⟩,⟨⟨20728738123092,4341538036188⟩,⟨25416598632,235379599548⟩,⟨688975752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨20864444635710,167806593139817034⟩,⟨2932333654415256,235162701072⟩,⟨688336272,17166418287408⟩,⟨33499031904,0⟩⟩,⟨⟨20708339515812,4333481741628⟩,⟨25369434792,235161129528⟩,⟨688336272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24939 146 (5396-R)⟩
def p33:CachedProfile:=⟨⟨20215,107,4960⟩,⟨⟨⟨12903970778600,83883278617876496⟩,⟨1315368934983048,129453842144⟩,⟨340790934,6925553360748⟩,⟨12154876646,0⟩⟩,⟨⟨12781720606116,3000327073920⟩,⟨15797411520,129452780490⟩,⟨340790934,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨12866970286812,83658716892975996⟩,⟨1324182961115712,130321294848⟩,⟨346280832,7037119067904⟩,⟨12466109952,0⟩⟩,⟨⟨12745677721368,2984621744592⟩,⟨15861585888,130320226080⟩,⟨346280832,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 20322 108 (4960-R)⟩
def p34:CachedProfile:=⟨⟨9247,70,1751⟩,⟨⟨⟨939504703704,2843700024921912⟩,⟨63878263777440,13712623680⟩,⟨51508800,479907489600⟩,⟨1201872000,0⟩⟩,⟨⟨934100423184,171493472304⟩,⟨1288455840,13712378400⟩,⟨51508800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨931572847282,2820751653016726⟩,⟨64273054885644,13797377176⟩,⟨52567548,489771844716⟩,⟨1244098636,0⟩⟩,⟨⟨926296621668,168762883212⟩,⟨1286053956,13797130380⟩,⟨52567548,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨931006678014,2819112758253162⟩,⟨64236072361482,13789438524⟩,⟨52537302,489490042734⟩,⟨1243382814,0⟩⟩,⟨⟨925739520804,168568679664⟩,⟨1284574032,13789191870⟩,⟨52537302,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨930440560840,2817473899887976⟩,⟨64199089839024,13781499872⟩,⟨52507056,489208240752⟩,⟨1242666992,0⟩⟩,⟨⟨925182461616,168374587920⟩,⟨1283094960,13781253360⟩,⟨52507056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 17=>⟨⟨⟨929874495730,2815835077879510⟩,⟨64162107318270,13773561220⟩,⟨52476810,488926438770⟩,⟨1241951170,0⟩⟩,⟨⟨924625444080,168180607980⟩,⟨1281616740,13773314850⟩,⟨52476810,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9317 71 (1751-R)⟩
def p35:CachedProfile:=⟨⟨8268,2,2540⟩,⟨⟨⟨1124866752240,2916706414683600⟩,⟨2085591206160,504378336⟩,⟨60984,504337680⟩,⟨40656,0⟩⟩,⟨⟨1108431208500,320254426800⟩,⟨77449680,504368172⟩,⟨60984,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1119798226720,2904737382026200⟩,⟨3116074261680,753590064⟩,⟨136674,1130293980⟩,⟨136674,0⟩⟩,⟨⟨1103555686080,317738196600⟩,⟨115261740,753574878⟩,⟨136674,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8270 3 (2540-R)⟩
def p36:CachedProfile:=⟨⟨21238,125,4267⟩,⟨⟨⟨12076231297196,83558822615680412⟩,⟨1460892555903000,136770194000⟩,⟨400125000,8547870375000⟩,⟨16671875000,0⟩⟩,⟨⟨11998340233176,2334320824968⟩,⟨13658667000,136769127000⟩,⟨400125000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨12025052460018,83222046760945794⟩,⟨1466714110316364,137315223864⟩,⟨404933256,8650589147928⟩,⟨17007196752,0⟩⟩,⟨⟨11948087144292,2315759881500⟩,⟨13658463000,137314152612⟩,⟨404933256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 21363 126 (4267-R)⟩
def p37:CachedProfile:=⟨⟨61004,422,11962⟩,⟨⟨⟨279394470209904,5565904232705520312⟩,⟨114290735770058400,3721266288320⟩,⟨12782513352,785178665159952⟩,⟨1798073544848,0⟩⟩,⟨⟨277681221512856,52740881789736⟩,⟨362332759992,3721256191548⟩,⟨12782513352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨279047502466320,5559318744169832880⟩,⟨114427497508955064,3725719230240⟩,⟨12828135726,787981065105276⟩,⟨1808767137366,0⟩⟩,⟨⟨277340258549676,52617506194512⟩,⟨362341762776,3725709121386⟩,⟨12828135726,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 61426 423 (11962-R)⟩
def p38:CachedProfile:=⟨⟨18758,120,3962⟩,⟨⟨⟨8785651867536,53573942129992632⟩,⟨1016899862474880,107735264640⟩,⟨342403200,6463887609600⟩,⟨13696128000,0⟩⟩,⟨⟨8723293269936,1778466854808⟩,⟨11305012320,107734313520⟩,⟨342403200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨8745312015478,53340966377823754⟩,⟨1020975404608104,108167057504⟩,⟨346640316,6543875885448⟩,⟨13981159412,0⟩⟩,⟨⟨8683751333652,1763239557960⟩,⟨11301620220,108166102572⟩,⟨346640316,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18878 121 (3962-R)⟩
def p39:CachedProfile:=⟨⟨16529,93,2357⟩,⟨⟨⟨3974786843562,21690248050268046⟩,⟨363539801206872,43743012768⟩,⟨122366052,2033968516344⟩,⟨3793347612,0⟩⟩,⟨⟨3961608705468,554291107992⟩,⟨3101255748,43742574180⟩,⟨122366052,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 18=>⟨⟨⟨3943455897420,21523968597013740⟩,⟨364643830905120,43875861120⟩,⟨124057440,2062082767680⟩,⟨3887133120,0⟩⟩,⟨⟨3930576151320,545859166320⟩,⟨3086918640,43875421200⟩,⟨124057440,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 20=>⟨⟨⟨3939976088062,21505494429488146⟩,⟨364332164236656,43838360384⟩,⟨123951408,2060320303776⟩,⟨3883810784,0⟩⟩,⟨⟨3927129215268,544926273192⟩,⟨3081642984,43837920840⟩,⟨123951408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16622 94 (2357-R)⟩
def p40:CachedProfile:=⟨⟨24672,148,5079⟩,⟨⟨⟨19432952360840,156018891280866920⟩,⟨2778992620840320,223934040320⟩,⟨667633920,16570673894400⟩,⟨32936606720,0⟩⟩,⟨⟨19301655285360,3842332574400⟩,⟨22911572160,223932536640⟩,⟨667633920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19392125898210,155707836490477830⟩,⟨2792262086888040,225003314640⟩,⟨675354420,16762296704400⟩,⟨33542602860,0⟩⟩,⟨⟨19261601785140,3827218683600⟩,⟨22975648020,225001803780⟩,⟨675354420,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19371718371920,155552320689013760⟩,⟨2789508331462080,224781417880⟩,⟨674688390,16745765839800⟩,⟨33509523370,0⟩⟩,⟨⟨19241579599080,3819672907200⟩,⟨22930349040,224779908510⟩,⟨674688390,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24820 149 (5079-R)⟩
def p41:CachedProfile:=⟨⟨24880,144,5396⟩,⟨⟨⟨21064483012440,169999137589130304⟩,⟨2920028618674944,233380441728⟩,⟨671473152,16802944155648⟩,⟨32230711296,0⟩⟩,⟨⟨20907069447432,4372525398528⟩,⟨25161591168,233378887392⟩,⟨671473152,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21022548787800,169679436347862264⟩,⟨2934858462558120,234565710040⟩,⟨679570050,17005560931200⟩,⟨32845885750,0⟩⟩,⟨⟨20866007717772,4356335371008⟩,⟨25242512340,234564147810⟩,⟨679570050,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨21001587737130,169519598813094894⟩,⟨2932134396370920,234347995440⟩,⟨678939300,16989777043200⟩,⟨32815399500,0⟩⟩,⟨⟨20845481702292,4348251618048⟩,⟨25195671540,234346434660⟩,⟨678939300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25024 145 (5396-R)⟩
def p42:CachedProfile:=⟨⟨16536,4,5144⟩,⟨⟨⟨9126591443760,47266515788110080⟩,⟨33781891530240,4084883040⟩,⟨493920,8169436800⟩,⟨658560,0⟩⟩,⟨⟨8990280760440,2626473931200⟩,⟨635181120,4084841880⟩,⟨493920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨9106213705680,47170568403627240⟩,⟨42145286765400,5096179400⟩,⟨770250,12739935000⟩,⟨1283750,0⟩⟩,⟨⟨8970695735820,2616273051600⟩,⟨790892700,5096128050⟩,⟨770250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨9104176779554,47160975409190918⟩,⟨42137079001320,5095186960⟩,⟨770100,12737454000⟩,⟨1283500,0⟩⟩,⟨⟨8968737911508,2615254055280⟩,⟨790584660,5095135620⟩,⟨770100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨9096030614790,47122606596214170⟩,⟨42104247946200,5091217200⟩,⟨769500,12727530000⟩,⟨1282500,0⟩⟩,⟨⟨8960907846060,2611180054800⟩,⟨789353100,5091165900⟩,⟨769500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16540 5 (5144-R)⟩
def p43:CachedProfile:=⟨⟨43268,250,10158⟩,⟨⟨⟨120680703644616,1685212052263546536⟩,⟨28859229638640000,1326318404000⟩,⟨3809625000,165787260750000⟩,⟨317468750000,0⟩⟩,⟨⟨119631563396616,26945071915176⟩,⟨154792683000,1326313324500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨120564515518650,1683690798870539550⟩,⟨28948997220229800,1330443973600⟩,⟨3836760900,166968160846200⟩,⟨321008995300,0⟩⟩,⟨⟨119518159763100,26897348683800⟩,⟨155136599100,1330438878300⟩,⟨3836760900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨120551607249696,1683521776904668176⟩,⟨28946145071708280,1330312895376⟩,⟨3836382894,166951710781092⟩,⟨320977368798,0⟩⟩,⟨⟨119505560577636,26892048713616⟩,⟨155106030312,1330307800578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨120538699285196,1683352756175684972⟩,⟨28943292923192784,1330181817152⟩,⟨3836004888,166935260715984⟩,⟨320945742296,0⟩⟩,⟨⟨119492961635736,26886749265648⟩,⟨155075464536,1330176722856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43518 251 (10158-R)⟩
def p44:CachedProfile:=⟨⟨43518,250,10158⟩,⟨⟨⟨122010831673616,1714237386631686536⟩,⟨29191756566390000,1333937654000⟩,⟨3809625000,166739667000000⟩,⟨317468750000,0⟩⟩,⟨⟨120961686346116,27099864598176⟩,⟨154792683000,1333932574500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 8=>⟨⟨⟨121906504673088,1712862299354378664⟩,⟨29285443498786344,1338218754824⟩,⟨3837138906,167943895637808⟩,⟨321040621802,0⟩⟩,⟨⟨120859834697652,27057198151200⟩,⟨155167170900,1338213659022⟩,⟨3837138906,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 9=>⟨⟨⟨121893465168650,1712690419015489550⟩,⟨29282558487079800,1338086923600⟩,⟨3836760900,167927351071200⟩,⟨321008995300,0⟩⟩,⟨⟨120847104338100,27051867208800⟩,⟨155136599100,1338081828300⟩,⟨3836760900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨121880425968696,1712518539913738176⟩,⟨29279673475379280,1337955092376⟩,⟨3836382894,167910806504592⟩,⟨320977368798,0⟩⟩,⟨⟨120834374222136,27046536791616⟩,⟨155106030312,1337949997578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨121867387073196,1712346662048880972⟩,⟨29276788463684784,1337823261152⟩,⟨3836004888,167894261937984⟩,⟨320945742296,0⟩⟩,⟨⟨120821644349736,27041206899648⟩,⟨155075464536,1337818166856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43768 251 (10158-R)⟩
def p45:CachedProfile:=⟨⟨7858,48,1633⟩,⟨⟨⟨634692945150,1622294180774130⟩,⟨29415812736384,7441628160⟩,⟨22588416,178584016896⟩,⟨361414656,0⟩⟩,⟨⟨630309738516,126574522392⟩,⟨768476736,7441471296⟩,⟨22588416,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨628057349774,1606201264035842⟩,⟨29734588834440,7522276160⟩,⟨23308908,184280226648⟩,⟨380712164,0⟩⟩,⟨⟨623801199156,124107091416⟩,⟨769193964,7522117596⟩,⟨23308908,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7906 49 (1633-R)⟩
def p46:CachedProfile:=⟨⟨45018,250,10158⟩,⟨⟨⟨130151604097616,1895459127292026536⟩,⟨31226919195390000,1379653154000⟩,⟨3809625000,172454104500000⟩,⟨317468750000,0⟩⟩,⟨⟨129102428293116,28028620696176⟩,⟨154792683000,1379648074500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 7=>⟨⟨⟨130054707554040,1894131050523017112⟩,⟨31330223863746912,1384217322048⟩,⟨3837516912,173716715572416⟩,⟨321072248304,0⟩⟩,⟨⟨129007697916816,27990006186816⟩,⟨155197745712,1384212225744⟩,⟨3837516912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 8=>⟨⟨⟨130040866409088,1893941330222894664⟩,⟨31327137719710344,1384080972824⟩,⟨3837138906,173699603996808⟩,⟨321040621802,0⟩⟩,⟨⟨128994165980652,27984492001200⟩,⟨155167170900,1384075877022⟩,⟨3837138906,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨130013185032696,1893561893334658176⟩,⟨31320965431655280,1383808274376⟩,⟨3836382894,173665380845592⟩,⟨320977368798,0⟩⟩,⟨⟨128967102839136,27973465259616⟩,⟨155106030312,1383803179578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45268 251 (10158-R)⟩
def p47:CachedProfile:=⟨⟨24880,144,5237⟩,⟨⟨⟨20399626537146,164919948406928766⟩,⟨2834000766633600,226504864512⟩,⟨651691008,16307915784192⟩,⟨31281168384,0⟩⟩,⟨⟨20255706112500,4118661022464⟩,⟨23700734784,226503355968⟩,⟨651691008,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20357945693316,164600786497179396⟩,⟨2848233200410800,227642385760⟩,⟨659512200,16503633292800⟩,⟨31876423000,0⟩⟩,⟨⟨20214847088760,4102948452864⟩,⟨23774277720,227640869640⟩,⟨659512200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨20337111154176,164441217868536936⟩,⟨2845509136990200,227424671160⟩,⟨658881450,16487849404800⟩,⟨31845936750,0⟩⟩,⟨⟨20194422283140,4095103428864⟩,⟨23728820220,227423156490⟩,⟨658881450,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25024 145 (5237-R)⟩
def p48:CachedProfile:=⟨⟨44268,250,10158⟩,⟨⟨⟨126046931260616,1803321884990106536⟩,⟨30200766224640000,1356795404000⟩,⟨3809625000,169596885750000⟩,⟨317468750000,0⟩⟩,⟨⟨124997770694616,27564242647176⟩,⟨154792683000,1356790324500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨125925989118650,1801695995350339550⟩,⟨30294706712629800,1361015773600⟩,⟨3836760900,170804921746200⟩,⟨321008995300,0⟩⟩,⟨⟨124879613063100,27515422783800⟩,⟨155136599100,1361010678300⟩,⟨3836760900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨125912552625696,1801515347134948176⟩,⟨30291721981892280,1360881683376⟩,⟨3836382894,170788093675092⟩,⟨320977368798,0⟩⟩,⟨⟨124866485655636,27510001025616⟩,⟨155106030312,1360876588578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨125899116437196,1801334700156468972⟩,⟨30288737251160784,1360747593152⟩,⟨3836004888,170771265603984⟩,⟨320945742296,0⟩⟩,⟨⟨124853358491736,27504579801648⟩,⟨155075464536,1360742498856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44518 251 (10158-R)⟩
def p49:CachedProfile:=⟨⟨33072,8,10160⟩,⟨⟨⟨71961536748960,746333512078809600⟩,⟨533724027932160,32268734784⟩,⟨3901824,129072337920⟩,⟨10404864,0⟩⟩,⟨⟨70911989175600,20490233644800⟩,⟨4955316480,32268572208⟩,⟨3901824,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨71880406891840,745567559487193000⟩,⟨599848594831800,36266599512⟩,⟨4933386,163196408880⟩,⟨14800158,0⟩⟩,⟨⟨70833953904180,20449920372000⟩,⟨5563763100,36266416794⟩,⟨4933386,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨71856073874092,745337797844729164⟩,⟨599671313858448,36255881376⟩,⟨4931928,163148178240⟩,⟨14795784,0⟩⟩,⟨⟨70810548074280,20437834130880⟩,⟨5560474824,36255698712⟩,⟨4931928,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 33080 9 (10160-R)⟩
def p50:CachedProfile:=⟨⟨24327,169,5079⟩,⟨⟨⟨18945918049160,150014220885964520⟩,⟨3091002567974880,252370539200⟩,⟨870539280,21324730202880⟩,⟨49040379440,0⟩⟩,⟨⟨18814624265520,3792174808320⟩,⟨26162538480,252368822160⟩,⟨870539280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18906050315490,149714986510009830⟩,⟨3103171765995600,253364124000⟩,⟨879138000,21535364448000⟩,⟨49817820000,0⟩⟩,⟨⟨18775529487780,3777258214080⟩,⟨26213826600,253362400200⟩,⟨879138000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨18890107482054,149595301417197882⟩,⟨3100723462908720,253164231200⟩,⟨878444400,21518374022400⟩,⟨49778516000,0⟩⟩,⟨⟨18759894984732,3771299807040⟩,⟨26172475800,253162508760⟩,⟨878444400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24496 170 (5079-R)⟩
def p51:CachedProfile:=⟨⟨24496,156,5079⟩,⟨⟨⟨19179617231240,152885662781535080⟩,⟨2889689223058560,234440943360⟩,⟨741761280,18285899074560⟩,⟨38571586560,0⟩⟩,⟨⟨19048321862640,3816324843840⟩,⟨24150035520,234439358400⟩,⟨741761280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19139289459810,152580775865993670⟩,⟨2902487947917480,235479313680⟩,⟨749822580,18484626242160⟩,⟨39240715020,0⟩⟩,⟨⟨19008767050260,3801313254960⟩,⟨24209239860,235477721700⟩,⟨749822580,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19119131279120,152428344001802240⟩,⟨2899625486055360,235247085560⟩,⟨749083110,18466396827720⟩,⟨39202016090,0⟩⟩,⟨⟨18988994208120,3793818553920⟩,⟨24161508720,235245495150⟩,⟨749083110,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24652 157 (5079-R)⟩
def p52:CachedProfile:=⟨⟨24854,154,5237⟩,⟨⟨⟨20374467375546,164605260722242302⟩,⟨3026931967792656,242079491808⟩,⟨745346448,18639623971584⟩,⟨38261117664,0⟩⟩,⟨⟨20230547118516,4116027607488⟩,⟨25346619144,242077878504⟩,⟨745346448,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20332834563716,164286699600851972⟩,⟨3040770954936720,243186275360⟩,⟨753616200,18846433929600⟩,⟨38936837000,0⟩⟩,⟨⟨20189736126456,4100325084288⟩,⟨25413883080,243184654680⟩,⟨753616200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨20316185831736,164159284357042776⟩,⟨3038444388943200,243000210880⟩,⟨753039600,18832014316800⟩,⟨38907046000,0⟩⟩,⟨⟨20173415243856,4094052477696⟩,⟨25375005360,242998591440⟩,⟨753039600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25008 155 (5237-R)⟩
def p53:CachedProfile:=⟨⟨2984,24,639⟩,⟨⟨⟨36067411840,35018966711680⟩,⟨833987358720,554557440⟩,⟨2211840,6653214720⟩,⟨17694720,0⟩⟩,⟨⟨35802236160,7380910080⟩,⟨58890240,554526720⟩,⟨2211840,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨35463903930,34463970826110⟩,⟨855160929000,568638000⟩,⟨2362500,7106400000⟩,⟨19687500,0⟩⟩,⟨⟨35210860020,7151880960⟩,⟨59440500,568606500⟩,⟨2362500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨35403657496,34408498017856⟩,⟨853803342000,567735400⟩,⟨2358750,7095120000⟩,⟨19656250,0⟩⟩,⟨⟨35151805896,7129176576⟩,⟨59251800,567703950⟩,⟨2358750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (639-R)⟩
def p54:CachedProfile:=⟨⟨24896,152,5237⟩,⟨⟨⟨20437395450426,165392735010515262⟩,⟨2997185975621568,239317766784⟩,⟨726112512,18187666200576⟩,⟨36789700608,0⟩⟩,⟨⟨20293474774356,4122611144928⟩,⟨25017442272,239316174432⟩,⟨726112512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20395642500996,165072670476691332⟩,⟨3011144559120432,240432332256⟩,⟨734293512,18392583888576⟩,⟨37448969112,0⟩⟩,⟨⟨20252543645496,4106883505728⟩,⟨25085962008,240430732488⟩,⟨734293512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨20378945713976,164944653867935576⟩,⟨3008840661108000,240248374848⟩,⟨733731696,18378511521408⟩,⟨37420316496,0⟩⟩,⟨⟨20236174708176,4100600866176⟩,⟨25047585936,240246776304⟩,⟨733731696,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25048 153 (5237-R)⟩
def p55:CachedProfile:=⟨⟨46156,259,9049⟩,⟨⟨⟨120690119195650,1816647488385941950⟩,⟨30298417911575100,1305552022600⟩,⟨3642498300,169066558594500⟩,⟨314469019900,0⟩⟩,⟨⟨119948225255100,22806506890500⟩,⟨127262421300,1305547334700⟩,⟨3642498300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨120449525485182,1813197263933140974⟩,⟨30358265840037720,1308130877040⟩,⟨3663784800,170054571492000⟩,⟨317528016000,0⟩⟩,⟨⟨119711801694000,22720900735440⟩,⟨127274247360,1308126179880⟩,⟨3663784800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 18=>⟨⟨⟨120435375354184,1812994318384806472⟩,⟨30354904994207040,1307986060160⟩,⟨3663379200,170035745568000⟩,⟨317492864000,0⟩⟩,⟨⟨119697896377872,22715870092080⟩,⟨127246067520,1307981363520⟩,⟨3663379200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 46415 260 (9049-R)⟩
def p56:CachedProfile:=⟨⟨11528,71,3037⟩,⟨⟨⟨2592740138646,9567934299838866⟩,⟨174123774310500,30024298808⟩,⟨91887348,1065801349452⟩,⟨2174667236,0⟩⟩,⟨⟨2564649068100,642102499164⟩,⟨3930448956,30023867412⟩,⟨91887348,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨2582342871810,9532368060025674⟩,⟨175936845325392,30336933024⟩,⟨94151808,1092066820992⟩,⟨2259643392,0⟩⟩,⟨⟨2554555393212,637460300988⟩,⟨3956991264,30336497136⟩,⟨94151808,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 12=>⟨⟨⟨2581398211098,9529135428010998⟩,⟨175878720198432,30326910912⟩,⟨94120704,1091706045696⟩,⟨2258896896,0⟩⟩,⟨⟨2553638222700,637039118100⟩,⟨3954376800,30326475168⟩,⟨94120704,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨2580453641150,9525902906100350⟩,⟨175820595073200,30316888800⟩,⟨94089600,1091345270400⟩,⟨2258150400,0⟩⟩,⟨⟨2552721124800,636618074400⟩,⟨3951763200,30316453200⟩,⟨94089600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨2579509161936,9522670494221136⟩,⟨175762469949696,30306866688⟩,⟨94058496,1090984495104⟩,⟨2257403904,0⟩⟩,⟨⟨2551804099488,636197169888⟩,⟨3949150464,30306431232⟩,⟨94058496,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨2578564773426,9519438192300786⟩,⟨175704344827920,30296844576⟩,⟨94027392,1090623719808⟩,⟨2256657408,0⟩⟩,⟨⟨2550887146740,635776404564⟩,⟨3946538592,30296409264⟩,⟨94027392,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11599 72 (3037-R)⟩
def p57:CachedProfile:=⟨⟨24896,152,5143⟩,⟨⟨⟨20045533945416,162385413107152296⟩,⟨2943398251019520,235023022592⟩,⟨713081856,17861274329088⟩,⟨36129480704,0⟩⟩,⟨⟨19909215141936,3975958010496⟩,⟨24127499904,235021458816⟩,⟨713081856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20003927226146,162065652430112486⟩,⟨2957002971360840,236109333168⟩,⟨721090836,18061883260128⟩,⟨36775632636,0⟩⟩,⟨⟨19868400997956,3960512912736⟩,⟨24191890596,236107762164⟩,⟨721090836,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25048 153 (5143-R)⟩
def p58:CachedProfile:=⟨⟨24794,145,5237⟩,⟨⟨⟨20266152816366,163252776430721466⟩,⟨2834328154466700,227303114760⟩,⟨660773700,16479035304300⟩,⟨31937395500,0⟩⟩,⟨⟨20122233282180,4104671005404⟩,⟨23865323220,227301595740⟩,⟨660773700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20224726790636,162936797415031196⟩,⟨2848426747244400,228433779488⟩,⟨668640288,16675220142432⟩,⟨32540494016,0⟩⟩,⟨⟨20081629074840,4089011807304⟩,⟨23938238256,228432252912⟩,⟨668640288,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24939 146 (5237-R)⟩
def p59:CachedProfile:=⟨⟨2984,24,643⟩,⟨⟨⟨36309350476,35241103535596⟩,⟨839200521600,558023424⟩,⟨2225664,6694797312⟩,⟨17805312,0⟩⟩,⟨⟨36039215016,7473532416⟩,⟨59629248,557992512⟩,⟨2225664,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨35705078806,34685910446986⟩,⟨860591283000,572248400⟩,⟨2377500,7151520000⟩,⟨19812500,0⟩⟩,⟨⟨35447227836,7243059456⟩,⟨60198300,572216700⟩,⟨2377500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨35644756656,34630418253312⟩,⟨859233693600,571345800⟩,⟨2373750,7140240000⟩,⟨19781250,0⟩⟩,⟨⟨35388113136,7220210688⟩,⟨60008400,571314150⟩,⟨2373750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (643-R)⟩
def p60:CachedProfile:=⟨⟨17315,118,3521⟩,⟨⟨⟨6641050251690,37475827659900222⟩,⟨757838967704856,86944345584⟩,⟨294241968,5129520228144⟩,⟨11573517408,0⟩⟩,⟨⟨6597263666436,1297115823276⟩,⟨8779881096,86943514392⟩,⟨294241968,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨6612926088756,37325031102681012⟩,⟨761223312062136,87332628208⟩,⟨298060728,5196092671224⟩,⟨11823075544,0⟩⟩,⟨⟨6569658714936,1286822752488⟩,⟨8784024984,87331793304⟩,⟨298060728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 17433 119 (3521-R)⟩
def p61:CachedProfile:=⟨⟨6586,43,1392⟩,⟨⟨⟨380854532926,815479962814426⟩,⟨15794081466450,4765324844⟩,⟨15453942,102444181518⟩,⟨221506502,0⟩⟩,⟨⟨378136898580,77124013344⟩,⟨500276448,4765205046⟩,⟨15453942,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨376759422466,807171547838446⟩,⟨15998949506232,4827139856⟩,⟨16018464,106186397856⟩,⟨234937472,0⟩⟩,⟨⟨374122578648,75581020788⟩,⟨501669168,4827018504⟩,⟨16018464,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨376467225706,806578262858446⟩,⟨15987346929840,4823639392⟩,⟨16006848,106109395392⟩,⟨234767104,0⟩⟩,⟨⟨373836090420,75471403644⟩,⟨500941584,4823518128⟩,⟨16006848,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨376175070270,805985000799354⟩,⟨15975744354504,4820138928⟩,⟨15995232,106032392928⟩,⟨234596736,0⟩⟩,⟨⟨373549635252,75361866048⟩,⟨500214528,4820017752⟩,⟨15995232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6629 44 (1392-R)⟩
def p62:CachedProfile:=⟨⟨2984,24,637⟩,⟨⟨⟨35946557746,34907928216502⟩,⟨831380780736,552824448⟩,⟨2204928,6632423424⟩,⟨17639424,0⟩⟩,⟨⟨35683838916,7334815488⟩,⟨58522464,552793824⟩,⟨2204928,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨35343429916,34353030018172⟩,⟨852445755600,566832800⟩,⟨2355000,7083840000⟩,⟨19625000,0⟩⟩,⟨⟨35092766856,7106508288⟩,⟨59063400,566801400⟩,⟨2355000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (637-R)⟩
def p63:CachedProfile:=⟨⟨43767,250,10158⟩,⟨⟨⟨123343212785954,1743478098263652830⟩,⟨29524846785292500,1341526427000⟩,⟨3809625000,167688263625000⟩,⟨317468750000,0⟩⟩,⟨⟨122294062399272,27254038110444⟩,⟨154792683000,1341521347500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨123211495553214,1741730468181489690⟩,⟨29613766866674490,1345566720588⟩,⟨3836382894,168866065845198⟩,⟨320977368798,0⟩⟩,⟨⟨122165438752452,27200406917304⟩,⟨155106030312,1345561625790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44017 251 (10158-R)⟩
def p64:CachedProfile:=⟨⟨24296,172,5079⟩,⟨⟨⟨18904129075080,149502687258528360⟩,⟨3138684928225920,256556906240⟩,⟨901720320,22063292789760⟩,⟨51698631680,0⟩⟩,⟨⟨18772835575920,3787840186560⟩,⟨26626962240,256555158720⟩,⟨901720320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18864343603170,149204459855568390⟩,⟨3150718555930920,257540546640⟩,⟨910440180,22276650324240⟩,⟨52502050380,0⟩⟩,⟨⟨18733823059380,3772940642640⟩,⟨26676423540,257538792420⟩,⟨910440180,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨18848433674438,149085177551935514⟩,⟨3148232739854232,257337358832⟩,⟨909721884,22259075057712⟩,⟨52460628644,0⟩⟩,⟨⟨18718221460812,3766989046320⟩,⟨26634343020,257335605996⟩,⟨909721884,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24468 173 (5079-R)⟩
def p65:CachedProfile:=⟨⟨30771,228,6637⟩,⟨⟨⟨39735984820646,397424105488280066⟩,⟨8726190962799600,563002554144⟩,⟨2070418752,64180910893248⟩,⟨157351825152,0⟩⟩,⟨⟨39443170911300,8194227177564⟩,⟨60269163408,562999527216⟩,⟨2070418752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨39646030304736,396573646966400736⟩,⟨8745978616615872,564279244416⟩,⟨2084215104,64608584008896⟩,⟨159095086272,0⟩⟩,⟨⟨39355063639488,8159696647488⟩,⟨60278413248,564276210624⟩,⟨2084215104,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 30999 229 (6637-R)⟩
def p66:CachedProfile:=⟨⟨24705,157,5237⟩,⟨⟨⟨20145633361002,161752292711373006⟩,⟨3049972195197528,245354540832⟩,⟨774668772,19259815009464⟩,⟨40540999068,0⟩⟩,⟨⟨20001714633468,4091997695832⟩,⟨25840384452,245352896100⟩,⟨774668772,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20104437422052,161439178355901156⟩,⟨3063538802735712,246445912448⟩,⟨783070752,19468705036224⟩,⟨41241726272,0⟩⟩,⟨⟨19961340511368,4076386846032⟩,⟨25905764688,246444260400⟩,⟨783070752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24862 158 (5237-R)⟩
def p67:CachedProfile:=⟨⟨24644,140,5079⟩,⟨⟨⟨19378521420680,155343900070425320⟩,⟨2621156676700800,211522259200⟩,⟨597408000,14806159872000⟩,⟨27879040000,0⟩⟩,⟨⟨19247224710960,3836759489280⟩,⟨21673108800,211520836800⟩,⟨597408000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19337802105570,155034174024793830⟩,⟨2634682525960680,212613775920⟩,⟨604780020,14988868015680⟩,⟨28424660940,0⟩⟩,⟨⟨19207278357540,3821667520320⟩,⟨21742056180,212612346180⟩,⟨604780020,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨19313377818456,154848353235401976⟩,⟨2631564507064608,212362161984⟩,⟨604064304,14971129710336⟩,⟨28391022288,0⟩⟩,⟨⟨19183316387088,3812626614528⟩,⟨21690621072,212360733936⟩,⟨604064304,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24784 141 (5079-R)⟩
def p68:CachedProfile:=⟨⟨11580,79,1920⟩,⟨⟨⟨1602349894958,6103046659698278⟩,⟨123777178721034,21233512244⟩,⟨71933766,838675777794⟩,⟨1894255838,0⟩⟩,⟨⟨1595223526680,258012737280⟩,⟨1748263680,21233208726⟩,⟨71933766,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨1589291212058,6055073709348038⟩,⟨124365210934080,21334391680⟩,⟨73190400,853326873600⟩,⟨1951744000,0⟩⟩,⟨⟨1582329846300,253998077220⟩,⟨1742846400,21334086720⟩,⟨73190400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨1588421091630,6051875865084870⟩,⟨124299959781600,21323198400⟩,⟨73152000,852879168000⟩,⟨1950720000,0⟩⟩,⟨⟨1581470634360,253731552480⟩,⟨1741017600,21322893600⟩,⟨73152000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11659 80 (1920-R)⟩
def p69:CachedProfile:=⟨⟨44768,250,10158⟩,⟨⟨⟨128775760568616,1864404344732386536⟩,⟨30882963392640000,1372033904000⟩,⟨3809625000,171501698250000⟩,⟨317468750000,0⟩⟩,⟨⟨127726589843616,27873828013176⟩,⟨154792683000,1372028824500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 7=>⟨⟨⟨128679812042040,1863097666294289112⟩,⟨30985130186538912,1376572866048⟩,⟨3837516912,172757336344416⟩,⟨321072248304,0⟩⟩,⟨⟨127632807480816,27835426758816⟩,⟨155197745712,1376567769744⟩,⟨3837516912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 8=>⟨⟨⟨128666106328088,1862911002898558664⟩,⟨30982078035181344,1376437269824⟩,⟨3837138906,172740319270308⟩,⟨321040621802,0⟩⟩,⟨⟨127619410975152,27829943026200⟩,⟨155167170900,1376432174022⟩,⟨3837138906,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨128638695813696,1862537679819088176⟩,⟨30975973732484280,1376166077376⟩,⟨3836382894,172706285122092⟩,⟨320977368798,0⟩⟩,⟨⟨127592618694636,27818977181616⟩,⟨155106030312,1376160982578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45018 251 (10158-R)⟩
def p70:CachedProfile:=⟨⟨44018,250,10158⟩,⟨⟨⟨124693945481616,1773290398182466536⟩,⟨29862524859390000,1349176154000⟩,⟨3809625000,168644479500000⟩,⟨317468750000,0⟩⟩,⟨⟨123644789995116,27409449964176⟩,⟨154792683000,1349171074500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨124560898656696,1771513422091378176⟩,⟨29952461930471280,1353239486376⟩,⟨3836382894,169828997951592⟩,⟨320977368798,0⟩⟩,⟨⟨123514836761136,27355512947616⟩,⟨155106030312,1353234391578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨124547595649196,1771335731289272972⟩,⟨29949510627668784,1353106149152⟩,⟨3836004888,169812264381984⟩,⟨320945742296,0⟩⟩,⟨⟨123501842777736,27350122167648⟩,⟨155075464536,1353101054856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44268 251 (10158-R)⟩
def p71:CachedProfile:=⟨⟨24652,159,5237⟩,⟨⟨⟨20066013948654,160763568347640762⟩,⟨3076166197417140,247970377080⟩,⟨794531268,19713115290348⟩,⟨42110157204,0⟩⟩,⟨⟨19922095755396,4083603685596⟩,⟨26169561324,247968711396⟩,⟨794531268,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20024970013164,160452341623178652⟩,⟨3089603330784000,249053555200⟩,⟨803020800,19923749068800⟩,⟨42827776000,0⟩⟩,⟨⟨19881873635736,4068024858696⟩,⟨26233685760,249051882240⟩,⟨803020800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24811 160 (5237-R)⟩
def p72:CachedProfile:=⟨⟨24444,155,5079⟩,⟨⟨⟨19100053041880,151906018541884120⟩,⟨2858833458699600,232437330400⟩,⟨732282000,18013404918000⟩,⟨37834570000,0⟩⟩,⟨⟨18968758211760,3808120024080⟩,⟨23995227600,232435755600⟩,⟨732282000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19059881892870,151603060092130530⟩,⟨2871613518443280,233476420320⟩,⟨740301120,18210667250880⟩,⟨38495658240,0⟩⟩,⟨⟨18929360020740,3793140709020⟩,⟨24055040880,233474838480⟩,⟨740301120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19039802023390,151451592460785310⟩,⟨2868781505040360,233246167440⟩,⟨739571040,18192708012960⟩,⟨38457694080,0⟩⟩,⟨⟨18909665489280,3785662121040⟩,⟨24007613760,233244587160⟩,⟨739571040,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24599 156 (5079-R)⟩
def p73:CachedProfile:=⟨⟨24763,147,5237⟩,⟨⟨⟨20220718624362,162686569705741134⟩,⟨2866743688319784,230170375008⟩,⟨679127652,16917069811320⟩,⟨33277254948,0⟩⟩,⟨⟨20076799393980,4099897940760⟩,⟨24194500092,230168835036⟩,⟨679127652,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20179379338212,162371671668009444⟩,⟨2880735048277056,231293746432⟩,⟨687084672,17115279179520⟩,⟨33896177152,0⟩⟩,⟨⟨20036281925640,4084256951760⟩,⟨24266159328,231292198944⟩,⟨687084672,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨20158715577912,162214234975273224⟩,⟨2877979899517056,231072539712⟩,⟨686427552,17098910320320⟩,⟨33863759232,0⟩⟩,⟨⟨20016027897720,4076447666760⟩,⟨24219761328,231070993704⟩,⟨686427552,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24910 148 (5237-R)⟩
def p74:CachedProfile:=⟨⟨9800,59,2313⟩,⟨⟨⟨1411615503506,4464250665291326⟩,⟨79625655136092,16153210216⟩,⟨48330204,476487481236⟩,⟨950494012,0⟩⟩,⟨⟨1399190047788,316608889428⟩,⟨1894707828,16152937164⟩,⟨48330204,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1402332450300,4436723875262700⟩,⟨80485308612000,16327608000⟩,⟨49680000,489795120000⟩,⟨993600000,0⟩⟩,⟨⟨1390130676600,312788605800⟩,⟨1903572000,16327332000⟩,⟨49680000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9859 60 (2313-R)⟩
def p75:CachedProfile:=⟨⟨10600,85,2602⟩,⟨⟨⟨1871447814562,6397514290208494⟩,⟨151569979730370,28371086140⟩,⟨112840050,1205695934250⟩,⟨3197134750,0⟩⟩,⟨⟨1853768826840,434217414660⟩,⟨3454233060,28370643630⟩,⟨112840050,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨1862798904864,6369898753747872⟩,⟨152705072479104,28583559936⟩,⟨115022592,1229016395520⟩,⟨3297314304,0⟩⟩,⟨⟨1845342689472,430554553920⟩,⟨3465389952,28583114112⟩,⟨115022592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10685 86 (2602-R)⟩
def p76:CachedProfile:=⟨⟨187069,1144,45079⟩,⟨⟨⟨10039630535827480,605256360199214717560⟩,⟨10961286312642906240,116477578497280⟩,⟨353986913280,66624938909168640⟩,⟨134987009597440,0⟩⟩,⟨⟨9948005766399120,2294875071126960⟩,⟨13948755300480,116477475354240⟩,⟨353986913280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨10036714289022796,605091947583494243212⟩,⟨10967947476204111480,116548361893040⟩,⟨354511648200,66723700842666600⟩,⟨135305279063000,0⟩⟩,⟨⟨9945162661905576,2293653458840568⟩,⟨13953516549720,116548258687320⟩,⟨354511648200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 188213 1145 (45079-R)⟩
def p77:CachedProfile:=⟨⟨159360,420,45622⟩,⟨⟨⟨7463288380431392,376540216318498947464⟩,⟨2935153145681094240,36739953710880⟩,⟨48287383200,7715358087696000⟩,⟨6760233648000,0⟩⟩,⟨⟨7368315599796780,1995408541252080⟩,⟨5245159515120,36739915387560⟩,⟨48287383200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨7460891292035430,376429221047440044090⟩,⟨2941303256965851480,36816936036080⟩,⟨48503772060,7749932699746800⟩,⟨6806696012420,0⟩⟩,⟨⟨7365999666921420,1994271531433200⟩,⟨5254652113740,36816897632460⟩,⟨48503772060,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 159780 421 (45622-R)⟩
def p78:CachedProfile:=⟨⟨25470,154,6031⟩,⟨⟨⟨24861600469680,204304516363135344⟩,⟨3659612763590784,285641644288⟩,⟨858329472,21993834390528⟩,⟨44060912896,0⟩⟩,⟨⟨24641889640992,5593051746048⟩,⟨33614188608,285639786432⟩,⟨858329472,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨24816755310890,203959236475364654⟩,⟨3677269977452280,287019841360⟩,⟨868071300,22243458991200⟩,⟨44850350500,0⟩⟩,⟨⟨24598134495732,5574520981728⟩,⟨33720369660,287017974540⟩,⟨868071300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25624 155 (6031-R)⟩
def p79:CachedProfile:=⟨⟨24634,150,5079⟩,⟨⟨⟨19378521420680,155343900070425320⟩,⟨2808382153608000,226630992000⟩,⟨685800000,16996867200000⟩,⟨34290000000,0⟩⟩,⟨⟨19247224710960,3836759489280⟩,⟨23221188000,226629468000⟩,⟨685800000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19337802105570,155034174024793830⟩,⟨2821539442695480,227692767120⟩,⟨693606420,17190341513280⟩,⟨34911523140,0⟩⟩,⟨⟨19207278357540,3821667520320⟩,⟨23284045980,227691235980⟩,⟨693606420,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19317448153040,154879322595676160⟩,⟨2818756813529760,227468218040⟩,⟨692922390,17173388513760⟩,⟨34877093630,0⟩⟩,⟨⟨19187309744880,3814132688640⟩,⟨23238138960,227466688410⟩,⟨692922390,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24784 151 (5079-R)⟩
def p80:CachedProfile:=⟨⟨8983,66,1976⟩,⟨⟨⟨1010060430510,2945480702992674⟩,⟨64109736456876,14169823272⟩,⟨51670872,467569720728⟩,⟨1136759184,0⟩⟩,⟨⟨1002305304012,212102334288⟩,⟨1546994592,14169562308⟩,⟨51670872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1002366576146,2924299842884966⟩,⟨64620206353950,14282654516⟩,⟨52871442,478433678658⟩,⟨1180795538,0⟩⟩,⟨⟨994774591200,209108237364⟩,⟨1548265212,14282391474⟩,⟨52871442,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9049 67 (1976-R)⟩
def p81:CachedProfile:=⟨⟨2984,24,699⟩,⟨⟨⟨39729795700,38359941358900⟩,⟨912185769600,606547200⟩,⟨2419200,7276953600⟩,⟨19353600,0⟩⟩,⟨⟨39383563800,8830886400⟩,⟨70459200,606513600⟩,⟨2419200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨39114327390,37801723096530⟩,⟨936617247000,622794000⟩,⟨2587500,7783200000⟩,⟨21562500,0⟩⟩,⟨⟨38782618860,8580199680⟩,⟨71311500,622759500⟩,⟨2587500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨39052894816,37745933295616⟩,⟨935259624000,621891400⟩,⟨2583750,7771920000⟩,⟨21531250,0⟩⟩,⟨⟨38722615776,8555329536⟩,⟨71104800,621856950⟩,⟨2583750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (699-R)⟩
def p82:CachedProfile:=⟨⟨44518,250,10222⟩,⟨⟨⟨128276854073296,1845448685197312072⟩,⟨30733317002646000,1373010238000⟩,⟨3833625000,171623724000000⟩,⟨319468750000,0⟩⟩,⟨⟨127207744796436,28069403307648⟩,⟨156749259000,1373005126500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨128154530538826,1843795171735511566⟩,⟨30829085144667000,1377288689936⟩,⟨3860953284,172847156618112⟩,⟨323033091428,0⟩⟩,⟨⟨127088240979156,28019999849856⟩,⟨157099266492,1377283562508⟩,⟨3860953284,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨128140940567416,1843611454284803392⟩,⟨30826066797364944,1377153846712⟩,⟨3860575278,172830234045504⟩,⟨323001464926,0⟩⟩,⟨⟨127074964003176,28014513262848⟩,⟨157068504936,1377148719786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44768 251 (10222-R)⟩
def p83:CachedProfile:=⟨⟨24754,155,5237⟩,⟨⟨⟨20219152870926,162667068830858466⟩,⟨3022514264981700,242686911240⟩,⟨755057700,18807732249300⟩,⟨39011314500,0⟩⟩,⟨⟨20075233651020,4099733352324⟩,⟨25511207580,242685287460⟩,⟨755057700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20177816573996,162352208023373996⟩,⟨3036206671598880,243786324288⟩,⟨763371648,19014824380032⟩,⟨39695325696,0⟩⟩,⟨⟨20034719171880,4084092991224⟩,⟨25577843616,243784693152⟩,⟨763371648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24909 156 (5237-R)⟩
def p84:CachedProfile:=⟨⟨41768,250,10158⟩,⟨⟨⟨112859939720616,1517956442568706536⟩,⟨26904069134640000,1280602904000⟩,⟨3809625000,160072823250000⟩,⟨317468750000,0⟩⟩,⟨⟨111810829949616,26016315817176⟩,⟨154792683000,1280597824500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨112738541685696,1516430806904248176⟩,⟨26985096183932280,1284459713376⟩,⟨3836382894,161197136440092⟩,⟨320977368798,0⟩⟩,⟨⟨111692525460636,25965120245616⟩,⟨155106030312,1284454618578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨112726403557196,1516278250144508972⟩,⟨26982437261240784,1284333153152⟩,⟨3836004888,161181253383984⟩,⟨320945742296,0⟩⟩,⟨⟨111680696351736,25960003461648⟩,⟨155075464536,1284328058856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42018 251 (10158-R)⟩
def p85:CachedProfile:=⟨⟨86280,547,19101⟩,⟨⟨⟨898912257765494,25141170992845368482⟩,⟨472638624454776084,10886932830008⟩,⟨34292941908,2977553267045916⟩,⟨6252746407892,0⟩⟩,⟨⟨891939610291284,190081999384524⟩,⟨1197494485164,10886911932420⟩,⟨34292941908,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨898202412373392,25122452277388899216⟩,⟨473155644994722432,10898842112768⟩,⟨34393216512,2986259810087424⟩,⟨6282494216192,0⟩⟩,⟨⟨891245080260768,189803469135072⟩,⟨1197925772928,10898821192320⟩,⟨34393216512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 86827 548 (19101-R)⟩
def p86:CachedProfile:=⟨⟨324516,1571,72182⟩,⟨⟨⟨47933146276469202,5032873846124023615506⟩,⟨72348565320204611814,443738112882636⟩,⟨1068903621018,348555575066896566⟩,⟨559749196206426,0⟩⟩,⟨⟨47557008365539668,10194092610081732⟩,⟨49112413222356,443737886083650⟩,⟨1068903621018,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨47921688095621074,5031740216272190961202⟩,⟨72378570947350908744,443922147631248⟩,⟨1070027614368,348922094686418016⟩,⟨560694469928832,0⟩⟩,⟨⟨47545800233578164,10189573858174884⟩,⟨49121891105904,443921920738200⟩,⟨1070027614368,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 17=>⟨⟨⟨47920971977721790,5031669364937804254906⟩,⟨72377568014304071088,443915996313504⟩,⟨1070012787264,348917259760555968⟩,⟨560686700526336,0⟩⟩,⟨⟨47545099740053556,10189291469441580⟩,⟨49120529766480,443915769423600⟩,⟨1070012787264,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 326087 1572 (72182-R)⟩
def p87:CachedProfile:=⟨⟨42768,250,10158⟩,⟨⟨⟨118043305336616,1628154202279266536⟩,⟨28199890220640000,1311079904000⟩,⟨3809625000,163882448250000⟩,⟨317468750000,0⟩⟩,⟨⟨116994175247616,26635486549176⟩,⟨154792683000,1311074824500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨117916805061696,1626520092358528176⟩,⟨28284819912116280,1315028501376⟩,⟨3836382894,165033519334092⟩,⟨320977368798,0⟩⟩,⟨⟨116870768538636,26583072557616⟩,⟨155106030312,1315023406578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨117904156709196,1626356688173292972⟩,⟨28282032925208784,1314898929152⟩,⟨3836004888,165017258271984⟩,⟨320945742296,0⟩⟩,⟨⟨116858429207736,26577833997648⟩,⟨155075464536,1314893834856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43018 251 (10158-R)⟩
def p88:CachedProfile:=⟨⟨24652,159,5396⟩,⟨⟨⟨20720743581342,165716588015092590⟩,⟨3169545159150594,255497542020⟩,⟨818649342,20311508824362⟩,⟨43388415126,0⟩⟩,⟨⟨20563332315456,4335307211592⟩,⟨27782590248,255495825774⟩,⟨818649342,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20679446265042,165404821967239890⟩,⟨3183569575479360,256628060800⟩,⟨827443200,20529693235200⟩,⟨44130304000,0⟩⟩,⟨⟨20522907489876,4319254990812⟩,⟨27853806720,256626336960⟩,⟨827443200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24811 160 (5396-R)⟩
def p89:CachedProfile:=⟨⟨24808,156,5237⟩,⟨⟨⟨20305362651066,163741943726727966⟩,⟨3055462723179360,244791937728⟩,⟨764831808,19093261254912⟩,⟨39771254016,0⟩⟩,⟨⟨20161442854980,4108785716304⟩,⟨25675796016,244790303472⟩,⟨764831808,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20263861768836,163425030813536196⟩,⟨3069178269318000,245890782496⟩,⟨773189832,19301910966048⟩,⟨40463601208,0⟩⟩,⟨⟨20120763791640,4093110820704⟩,⟨25741804152,245889140904⟩,⟨773189832,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨20247265808696,163298274852976856⟩,⟨3066829968075936,245702648768⟩,⟨772598256,19287142862784⟩,⟨40432642064,0⟩⟩,⟨⟨20104495680528,4086849250368⟩,⟨25702424784,245701008432⟩,⟨772598256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24964 157 (5237-R)⟩
def p90:CachedProfile:=⟨⟨24880,144,5143⟩,⟨⟨⟨20008442824776,161921111167592616⟩,⟨2783141574446592,222440057856⟩,⟨639995904,16015257501696⟩,⟨30719803392,0⟩⟩,⟨⟨19872124268208,3972148405248⟩,⟨22857631488,222438576384⟩,⟨639995904,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19966908211106,161602253114085926⟩,⟨2797020822660360,223549351280⟩,⟨647654100,16206896198400⟩,⟨31303281500,0⟩⟩,⟨⟨19831382229348,3956718106368⟩,⟨22926955140,223547862420⟩,⟨647654100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19946146681296,161442835975174656⟩,⟨2794296760875360,223331636680⟩,⟨647023350,16191112310400⟩,⟨31272795250,0⟩⟩,⟨⟨19811015831568,3949014217728⟩,⟨22882315440,223330149270⟩,⟨647023350,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25024 145 (5143-R)⟩
def p91:CachedProfile:=⟨⟨42268,250,10158⟩,⟨⟨⟨115436384028616,1572407411880986536⟩,⟨27548170052640000,1295841404000⟩,⟨3809625000,161977635750000⟩,⟨317468750000,0⟩⟩,⟨⟨114387264098616,26325901183176⟩,⟨154792683000,1295836324500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨115312449873696,1570828176858388176⟩,⟨27631136949524280,1299744107376⟩,⟨3836382894,163115327887092⟩,⟨320977368798,0⟩⟩,⟨⟨114266423499636,26274096401616⟩,⟨155106030312,1299739012578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨115300058133196,1570670260162900972⟩,⟨27628414371224784,1299616041152⟩,⟨3836004888,163099255827984⟩,⟨320945742296,0⟩⟩,⟨⟨114254340779736,26268918729648⟩,⟨155075464536,1299610946856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42518 251 (10158-R)⟩
def p92:CachedProfile:=⟨⟨2984,24,651⟩,⟨⟨⟨36794156260,35685619973092⟩,⟨849626875008,564955392⟩,⟨2253312,6777962496⟩,⟨18026496,0⟩⟩,⟨⟨36513915576,7660509696⟩,⟨61121088,564924096⟩,⟨2253312,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨36188342670,35130025110402⟩,⟨871452019800,579469200⟩,⟨2407500,7241760000⟩,⟨20062500,0⟩⟩,⟨⟨35920694796,7427149056⟩,⟨61728300,579437100⟩,⟨2407500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨36127867648,35074493415424⟩,⟨870094425600,578566600⟩,⟨2403750,7230480000⟩,⟨20031250,0⟩⟩,⟨⟨35861457792,7404011520⟩,⟨61536000,578534550⟩,⟨2403750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (651-R)⟩
def p93:CachedProfile:=⟨⟨24620,142,5079⟩,⟨⟨⟨19345296960840,154932369534544680⟩,⟨2653884025744320,214353566720⟩,⟨614598720,15218693504640⟩,⟨29091006080,0⟩⟩,⟨⟨19214000474640,3833353715040⟩,⟨21982724640,214352124000⟩,⟨614598720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19304643048210,154623453601778070⟩,⟨2667312291706920,215438171520⟩,⟨622058580,15403414557960⟩,⟨29651458980,0⟩⟩,⟨⟨19174119523260,3818275142760⟩,⟨22050454140,215436721500⟩,⟨622058580,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨19280258002584,154438118880079800⟩,⟨2664155656974240,215183215104⟩,⟨621322416,15385185664992⟩,⟨29616368496,0⟩⟩,⟨⟨19150196794032,3809242262304⟩,⟨21998289456,215181766800⟩,⟨621322416,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24762 143 (5079-R)⟩
def p94:CachedProfile:=⟨⟨77780,460,19571⟩,⟨⟨⟨756355455408924,18894935680870166652⟩,⟨330677579235810240,8452921330560⟩,⟨24848611200,1944155340288000⟩,⟨3810120384000,0⟩⟩,⟨⟨748855846251912,179815993217280⟩,⟨1057200369120,8452903324320⟩,⟨24848611200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨755633461042440,18878141798469492120⟩,⟨331108594798784040,8463939181240⟩,⟨24935088930,1950921357883200⟩,⟨3831691998910,0⟩⟩,⟨⟨748153372473660,179503748956800⟩,⟨1057658848020,8463921151530⟩,⟨24935088930,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 78240 461 (19571-R)⟩
def p95:CachedProfile:=⟨⟨2984,24,667⟩,⟨⟨⟨37767535636,36575651972692⟩,⟨870479692416,578819328⟩,⟨2308608,6944292864⟩,⟨18468864,0⟩⟩,⟨⟨37466331096,8041394688⟩,⟨64160064,578787264⟩,⟨2308608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨37158580606,36019223659762⟩,⟨893173608600,593910800⟩,⟨2467500,7422240000⟩,⟨20562500,0⟩⟩,⟨⟨36870597036,7802258688⟩,⟨64845900,593877900⟩,⟨2467500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨37097794080,35963609997312⟩,⟨891816004800,593008200⟩,⟨2463750,7410960000⟩,⟨20531250,0⟩⟩,⟨⟨36811110816,7778543616⟩,⟨64648800,592975350⟩,⟨2463750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (667-R)⟩
def p96:CachedProfile:=⟨⟨108826,507,28156⟩,⟨⟨⟨2131117788752430,74228236144672792962⟩,⟨1023882608683406394,18729642990396⟩,⟨43426372158,4747935547150614⟩,⟨7339056894702,0⟩⟩,⟨⟨2108789878993116,520067665175016⟩,⟨2411662592664,18729614439198⟩,⟨43426372158,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨2130030866376176,74193094972377698096⟩,⟨1025428442944041600,18757920612608⟩,⟨43577719296,4764482783789568⟩,⟨7379160467456,0⟩⟩,⟨⟨2107733863571616,519587540238816⟩,⟨2414188492416,18757892018304⟩,⟨43577719296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 109333 508 (28156-R)⟩
def p97:CachedProfile:=⟨⟨43017,250,10158⟩,⟨⟨⟨119352920129954,1656404180624150330⟩,⟨28527288859792500,1318668677000⟩,⟨3809625000,164831044875000⟩,⟨317468750000,0⟩⟩,⟨⟨118303784981772,26789660061444⟩,⟨154792683000,1318663597500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨119225130737214,1654742262566372190⟩,⟨28613204582252490,1322640129588⟩,⟨3836382894,165988778674698⟩,⟨320977368798,0⟩⟩,⟨⟨118179089159952,26736942683304⟩,⟨155106030312,1322635034790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43267 251 (10158-R)⟩
def p98:CachedProfile:=⟨⟨44517,250,10158⟩,⟨⟨⟨127402078691954,1833570404648405330⟩,⟨30539548023292500,1364384177000⟩,⟨3809625000,170545482375000⟩,⟨317468750000,0⟩⟩,⟨⟨126352913066772,27718416159444⟩,⟨154792683000,1364379097500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨127266366119214,1831734091394357190⟩,⟨30631524094346490,1368493311588⟩,⟨3836382894,171743353015698⟩,⟨320977368798,0⟩⟩,⟨⟨126220294094952,27663871151304⟩,⟨155106030312,1368488216790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44767 251 (10158-R)⟩
def p99:CachedProfile:=⟨⟨24854,154,5143⟩,⟨⟨⟨19983735163976,161612070891965096⟩,⟨2972610416529600,237735186304⟩,⟨731970624,18305121364992⟩,⟨37574492032,0⟩⟩,⟨⟨19847416772016,3969608668416⟩,⟨24444967008,237733601952⟩,⟨731970624,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19942248582306,161293813626456486⟩,⟨2986096669824600,238813760080⟩,⟨740066100,18507573028800⟩,⟨38236748500,0⟩⟩,⟨⟨19806722764836,3954188235456⟩,⟨24508124460,238812168540⟩,⟨740066100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25008 155 (5143-R)⟩
def p100:CachedProfile:=⟨⟨24327,169,5015⟩,⟨⟨⟨18691026594504,148099651680027432⟩,⟨3052060152302304,249191067840⟩,⟨859571856,21056072184576⟩,⟨48422547888,0⟩⟩,⟨⟨18564627322032,3697216554240⟩,⟨25507413360,249189372432⟩,⟨859571856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18651255676194,147800612941525542⟩,⟨3063998924439120,250165839200⟩,⟨868040400,21263517638400⟩,⟨49188956000,0⟩⟩,⟨⟨18525609997092,3682488089280⟩,⟨25556130600,250164137160⟩,⟨868040400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24496 170 (5015-R)⟩
def p101:CachedProfile:=⟨⟨8127,53,1627⟩,⟨⟨⟨675259787092,1789421815302484⟩,⟨34642501738416,8470327712⟩,⟨27438312,224445392160⟩,⟨484743512,0⟩⟩,⟨⟨670923627000,130000944480⟩,⟨842304408,8470155144⟩,⟨27438312,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨668646219592,1772741762717824⟩,⟨34970908089888,8550629136⟩,⟨28221048,230848172640⟩,⟨507978864,0⟩⟩,⟨⟨664428379440,127615656480⟩,⟨842450544,8550454932⟩,⟨28221048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨668205703204,1771630011768292⟩,⟨34949226383136,8545328064⟩,⟨28203552,230705055360⟩,⟨507663936,0⟩⟩,⟨⟨663995673432,127457422560⟩,⟨841405968,8545153968⟩,⟨28203552,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8180 54 (1627-R)⟩
def p102:CachedProfile:=⟨⟨2984,24,636⟩,⟨⟨⟨35886159400,34852416394432⟩,⟨830077492608,551957952⟩,⟨2201472,6622027776⟩,⟨17611776,0⟩⟩,⟨⟨35624663256,7311822336⟩,⟨58339008,551927376⟩,⟨2201472,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨35283221160,34297566811992⟩,⟨851088169800,565930200⟩,⟨2351250,7072560000⟩,⟨19593750,0⟩⟩,⟨⟨35033742876,7083876096⟩,⟨58875300,565898850⟩,⟨2351250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (636-R)⟩
def p103:CachedProfile:=⟨⟨43768,250,10222⟩,⟨⟨⟨124192325984296,1754784722049124072⟩,⟨29712200314896000,1350008488000⟩,⟨3833625000,168748505250000⟩,⟨319468750000,0⟩⟩,⟨⟨123123232041936,27599155530648⟩,⟨156749259000,1350003376500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨124060407908416,1753036178315345392⟩,⟨29801868480733944,1354082679712⟩,⟨3860575278,169934802587004⟩,⟨323001464926,0⟩⟩,⟨⟨122994446663676,27545185060848⟩,⟨157068504936,1354077552786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44018 251 (10222-R)⟩
def p104:CachedProfile:=⟨⟨3037,24,699⟩,⟨⟨⟨41081051900,40410047810300⟩,⟨944608795200,617232000⟩,⟨2419200,7405171200⟩,⟨19353600,0⟩⟩,⟨⟨40734745800,8986483800⟩,⟨70459200,617198400⟩,⟨2419200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨40446279930,39822537924510⟩,⟨969908746500,633765000⟩,⟨2587500,7920337500⟩,⟨21562500,0⟩⟩,⟨⟨40114498260,8731380060⟩,⟨71311500,633730500⟩,⟨2587500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3061 25 (699-R)⟩
def p105:CachedProfile:=⟨⟨8260,2,2540⟩,⟨⟨⟨1122850214640,2908372116659856⟩,⟨2081558456208,503890464⟩,⟨60984,503849808⟩,⟨40656,0⟩⟩,⟨⟨1106414711556,319944628080⟩,⟨77449680,503880300⟩,⟨60984,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1117789625120,2896435885716056⟩,⟨3110048942832,752861136⟩,⟨136674,1129200588⟩,⟨136674,0⟩⟩,⟨⟨1101547124976,317430831960⟩,⟨115261740,752845950⟩,⟨136674,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8262 3 (2540-R)⟩
def p106:CachedProfile:=⟨⟨8268,2,2556⟩,⟨⟨⟨1132992258064,2935873040026192⟩,⟨2098724600208,507554272⟩,⟨61368,507513360⟩,⟨40912,0⟩⟩,⟨⟨1116244736532,324301037040⟩,⟨78428304,507544044⟩,⟨61368,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1127911523904,2923891556763672⟩,⟨3135774341232,758353968⟩,⟨137538,1137439260⟩,⟨137538,0⟩⟩,⟨⟨1111359447072,321768928440⟩,⟨116723916,758338686⟩,⟨137538,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8270 3 (2556-R)⟩
def p107:CachedProfile:=⟨⟨16529,4,5112⟩,⟨⟨⟨9054334278846,46900869728511402⟩,⟨33543363608856,4057758608⟩,⟨490848,8115189984⟩,⟨654464,0⟩⟩,⟨⟨8920549514916,2592803199888⟩,⟨627303744,4057717704⟩,⟨490848,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨9034019617266,46805138122578822⟩,⟨41847196355370,5062278060⟩,⟨765450,12655184850⟩,⟨1275750,0⟩⟩,⟨⟨8901017729856,2582670124188⟩,⟨781065180,5062227030⟩,⟨765450,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16533 5 (5112-R)⟩
def p108:CachedProfile:=⟨⟨16472,4,5138⟩,⟨⟨⟨9049207337640,46671149884286520⟩,⟨33481882330272,4064332320⟩,⟨493344,8128335744⟩,⟨657792,0⟩⟩,⟨⟨8913373310196,2610211815792⟩,⟨633700368,4064291208⟩,⟨493344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨9028965631760,46576268052162560⟩,⟨41770909179840,5070529400⟩,⟨769350,12675810600⟩,⟨1282250,0⟩⟩,⟨⟨8893922467416,2600062270272⟩,⟨789045360,5070478110⟩,⟨769350,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16476 5 (5138-R)⟩
def p109:CachedProfile:=⟨⟨25178,148,5555⟩,⟨⟨⟨22240342968444,181467934340039772⟩,⟨3164578916995008,249909768960⟩,⟨730191744,18492836108544⟩,⟨36022792704,0⟩⟩,⟨⟨22068614359032,4689906162480⟩,⟨27406859040,249908124384⟩,⟨730191744,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨22197235412534,181136176411223882⟩,⟨3180226836381384,251145507680⟩,⟨738760476,18709847815176⟩,⟨36691770308,0⟩⟩,⟨⟨22026431495892,4673037526920⟩,⟨27492797580,251143854972⟩,⟨738760476,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25326 149 (5555-R)⟩
def p110:CachedProfile:=⟨⟨10754,48,2248⟩,⟨⟨⟨1631554268344,5695537649049040⟩,⟨75580023542400,13994033664⟩,⟨31090176,335836081152⟩,⟨497442816,0⟩⟩,⟨⟨1620140350452,327673398624⟩,⟨1456056576,13993817760⟩,⟨31090176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨1618371656424,5651909733980232⟩,⟨76571379930528,14177592576⟩,⟨32154192,347329581984⟩,⟨525185136,0⟩⟩,⟨⟨1607213966544,322737316704⟩,⟨1464000048,14177373840⟩,⟨32154192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10802 49 (2248-R)⟩
def p111:CachedProfile:=⟨⟨16536,4,5112⟩,⟨⟨⟨9061436859632,46959595471103744⟩,⟨33571772786688,4059476576⟩,⟨490848,8118625920⟩,⟨654464,0⟩⟩,⟨⟨8927652024120,2593900981440⟩,⟨627303744,4059435672⟩,⟨490848,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨9041108306832,46863749005139304⟩,⟨41882638374360,5064421320⟩,⟨765450,12660543000⟩,⟨1275750,0⟩⟩,⟨⟨8908106347980,2583763615440⟩,⟨781065180,5064370290⟩,⟨765450,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16540 5 (5112-R)⟩
def p112:CachedProfile:=⟨⟨24469,165,5079⟩,⟨⟨⟨19152576228680,152552480494017320⟩,⟨3051940418128800,247785331200⟩,⟨829818000,20441736612000⟩,⟨45639990000,0⟩⟩,⟨⟨19021281042960,3813538301280⟩,⟨25543306800,247783654800⟩,⟨829818000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19112301687570,152248249460071830⟩,⟨3064392758353680,248796337920⟩,⟨838253520,20649537211680⟩,⟨46383361440,0⟩⟩,⟨⟨18981779460540,3798537673320⟩,⟨25597030680,248794654680⟩,⟨838253520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24634 166 (5079-R)⟩
def p113:CachedProfile:=⟨⟨8266,2,2572⟩,⟨⟨⟨1140626729096,2952948442671872⟩,⟨2110836751968,510606704⟩,⟨61752,510565536⟩,⟨41168,0⟩⟩,⟨⟨1123563313536,328293639648⟩,⟨79413072,510596412⟩,⟨61752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1135535694216,2940962558451192⟩,⟨3153948511032,762933336⟩,⟨138402,1144307736⟩,⟨138402,0⟩⟩,⟨⟨1118670180276,325746268848⟩,⟨118195308,762917958⟩,⟨138402,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8268 3 (2572-R)⟩
def p114:CachedProfile:=⟨⟨43768,250,10190⟩,⟨⟨⟨123770295942888,1749189822649231464⟩,⟨29619194307696000,1345782696000⟩,⟨3821625000,168220289250000⟩,⟨318468750000,0⟩⟩,⟨⟨122711205072912,27426635959320⟩,⟨155769435000,1345777600500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨123638475801088,1747441678865396464⟩,⟨29708490451432824,1349839984544⟩,⟨3848479086,169402352407548⟩,⟨321989416862,0⟩⟩,⟨⟨122582498042172,27372834518640⟩,⟨156085725480,1349834873682⟩,⟨3848479086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44018 251 (10190-R)⟩
def p115:CachedProfile:=⟨⟨36117,213,8914⟩,⟨⟨⟨74144440029920,861312575070878360⟩,⟨15037957850193360,827857455360⟩,⟨2426787810,88165201137300⟩,⟨172301934510,0⟩⟩,⟨⟨73435411750680,17322502213800⟩,⟨101560500180,827853657570⟩,⟨2426787810,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨74026012859994,860028998077704222⟩,⟨15086526744825936,830531247104⟩,⟨2446055952,88865212736160⟩,⟨174485324576,0⟩⟩,⟨⟨73320080156172,17272016301960⟩,⟨101739925368,830527437048⟩,⟨2446055952,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 36330 214 (8914-R)⟩
def p116:CachedProfile:=⟨⟨24595,161,5237⟩,⟨⟨⟨19980333101754,159701842732117662⟩,⟨3101065866559080,250532911440⟩,⟨814645188,20167356274128⟩,⟨43719291756,0⟩⟩,⟨⟨19836415484676,4074551321616⟩,⟨26498738196,250531224804⟩,⟨814645188,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19939452741764,159392643009734852⟩,⟨3114369947103840,251607746880⟩,⟨823221792,20379678682752⟩,⟨44453976768,0⟩⟩,⟨⟨19796356939416,4059007029216⟩,⟨26561606832,251606053008⟩,⟨823221792,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24756 162 (5237-R)⟩
def p117:CachedProfile:=⟨⟨24493,153,5079⟩,⟨⟨⟨19170601369160,152774547936292520⟩,⟨2832738886870560,229876502400⟩,⟨713506320,17585076762720⟩,⟨36388822320,0⟩⟩,⟨⟨19039306061520,3815395996320⟩,⟨23685611760,229874947920⟩,⟨713506320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19130291345490,152469879754411830⟩,⟨2845640722644720,230923492800⟩,⟨721440720,17780627985120⟩,⟨37033956960,0⟩⟩,⟨⟨18999768996780,3800388061080⟩,⟨23746642920,230921931240⟩,⟨721440720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19110142038680,152317557257045360⟩,⟨2842834324046640,230695757600⟩,⟨720729240,17763092849040⟩,⟨36997434320,0⟩⟩,⟨⟨18980005028460,3792895184160⟩,⟨23699823840,230694197580⟩,⟨720729240,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24646 154 (5079-R)⟩
def p118:CachedProfile:=⟨⟨24763,147,5079⟩,⟨⟨⟨19569375354440,157714954392772520⟩,⟨2780269286064480,223227473280⟩,⟨658642320,16406780191200⟩,⟨32273473680,0⟩⟩,⟨⟨19438077364560,3856265287200⟩,⟨22756764240,223225979760⟩,⟨658642320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19528280342610,157400560840714230⟩,⟨2793672390394080,224303614080⟩,⟨666319680,16598023228800⟩,⟨32871770880,0⟩⟩,⟨⟨19397755316940,3841096591800⟩,⟨22821449040,224302113360⟩,⟨666319680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19507738541720,157243375658496560⟩,⟨2790917244440160,224082407360⟩,⟨665662560,16581654369600⟩,⟨32839352960,0⟩⟩,⟨⟨19377598857180,3833523453600⟩,⟨22776454080,224080908120⟩,⟨665662560,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24910 148 (5079-R)⟩
def p119:CachedProfile:=⟨⟨24934,150,5237⟩,⟨⟨⟨20494116704826,166103615557887966⟩,⟨2966257279926000,236508271200⟩,⟨707130000,17737648920000⟩,⟨35356500000,0⟩⟩,⟨⟨20350195651620,4128536328624⟩,⟨24688265400,236506699800⟩,⟨707130000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20452255467396,165782193841212996⟩,⟨2980331522905680,237630458848⟩,⟨715221768,17940622828512⟩,⟨35999495656,0⟩⟩,⟨⟨20309156235480,4112786085024⟩,⟨24758040936,237628879992⟩,⟨715221768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25084 151 (5237-R)⟩
def p120:CachedProfile:=⟨⟨42517,250,10158⟩,⟨⟨⟨116730821275954,1600006387334065330⟩,⟨27871774305292500,1303430177000⟩,⟨3809625000,162926232375000⟩,⟨317468750000,0⟩⟩,⟨⟨115681696286772,26480074695444⟩,⟨154792683000,1303425097500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨116605612943214,1598399984988377190⟩,⟨27955715805554490,1307355735588⟩,⟨3836382894,164070587227698⟩,⟨320977368798,0⟩⟩,⟨⟨115559581514952,26427966527304⟩,⟨155106030312,1307350640790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42767 251 (10158-R)⟩
def p121:CachedProfile:=⟨⟨7418,54,1452⟩,⟨⟨⟨502140677512,1216926274223296⟩,⟨26284936967136,7035844464⟩,⟨25421688,189950852736⟩,⟨457590384,0⟩⟩,⟨⟨499055598168,94584580992⟩,⟨683560944,7035687540⟩,⟨25421688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨497011282864,1205072897211400⟩,⟨26513730124200,7097090440⟩,⟨26117850,195152575200⟩,⟨478827250,0⟩⟩,⟨⟨494014150932,92770050624⟩,⟨682863060,7096932150⟩,⟨26117850,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7472 55 (1452-R)⟩
def p122:CachedProfile:=⟨⟨37001,255,8250⟩,⟨⟨⟨71525313862264,858009695322829432⟩,⟨17522482319245080,940658555400⟩,⟨3219127650,119931819728400⟩,⟨273625850250,0⟩⟩,⟨⟨70963115376252,15216263172000⟩,⟨104148247500,940654347390⟩,⟨3219127650,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨71413138775440,856741630015338760⟩,⟨17565613536565248,942973982720⟩,⟨3239706624,120698509983744⟩,⟨276454965248,0⟩⟩,⟨⟨70853388069156,15172032550752⟩,⟨104252746752,942969764352⟩,⟨3239706624,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 37256 256 (8250-R)⟩
def p123:CachedProfile:=⟨⟨310356,1424,77701⟩,⟨⟨⟨47664775704525994,4746322452660301860622⟩,⟨64534304928039106176,413973569502464⟩,⟨945373504512,294748551236751360⟩,⟨448737290141696,0⟩⟩,⟨⟨47195605670118372,11294273716449360⟩,⟨51584597383488,413973348207168⟩,⟨945373504512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨47656016425133104,4745510071697467702528⟩,⟨64568819395547827200,414194972436600⟩,⟨946543353750,295113286832175000⟩,⟨449608093031250,0⟩⟩,⟨⟨47187081821830248,11290494811901760⟩,⟨51603550923600,414194751022950⟩,⟨946543353750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 311780 1425 (77701-R)⟩
def p124:CachedProfile:=⟨⟨4384,31,1056⟩,⟨⟨⟨129552750334,183230820249022⟩,⟨3832625642874,1736257796⟩,⟨6094662,26907932730⟩,⟨62978174,0⟩⟩,⟨⟨128364718272,29567926080⟩,⟨207611712,1736192262⟩,⟨6094662,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨128217025074,181462070996802⟩,⟨3918825580608,1775309952⟩,⟨6432768,28400670720⟩,⟨68616192,0⟩⟩,⟨⟨127062240612,29010841380⟩,⟨210271104,1775242944⟩,⟨6432768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨128083625710,181285269315850⟩,⟨3915082270080,1773614336⟩,⟨6426624,28373544960⟩,⟨68550656,0⟩⟩,⟨⟨126932131380,28955424300⟩,⟨209869440,1773547392⟩,⟨6426624,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 12=>⟨⟨⟨127950257710,181108480851430⟩,⟨3911338960320,1771918720⟩,⟨6420480,28346419200⟩,⟨68485120,0⟩⟩,⟨⟨126802047240,28900060200⟩,⟨209468160,1771851840⟩,⟨6420480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4415 32 (1056-R)⟩
def p125:CachedProfile:=⟨⟨43517,250,10158⟩,⟨⟨⟨122005495983954,1714120622273235330⟩,⟨29190422664292500,1333907177000⟩,⟨3809625000,166735857375000⟩,⟨317468750000,0⟩⟩,⟨⟨120956350676772,27099245427444⟩,⟨154792683000,1333902097500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨121875095531214,1712401890493367190⟩,⟨29278335555950490,1337924523588⟩,⟨3836382894,167906970121698⟩,⟨320977368798,0⟩⟩,⟨⟨120829043804952,27045918839304⟩,⟨155106030312,1337919428790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43767 251 (10158-R)⟩
def p126:CachedProfile:=⟨⟨43768,250,10475⟩,⟨⟨⟨127540137039588,1799065296606688164⟩,⟨30447529275636000,1383418656000⟩,⟨3928500000,172924713000000⟩,⟨327375000000,0⟩⟩,⟨⟨126389729126952,28982181898800⟩,⟨164604150000,1383413418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨127407433856638,1797313501725481714⟩,⟨30540138742076184,1387626488384⟩,⟨3956210796,174144486818328⟩,⟨331002969932,0⟩⟩,⟨⟨126260315661012,28926875042520⟩,⟨164947195140,1387621234452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44018 251 (10475-R)⟩
def p127:CachedProfile:=⟨⟨24296,172,4920⟩,⟨⟨⟨18273325117488,144764464995166464⟩,⟨3040444946423808,248526877088⟩,⟨873497184,21372729098112⟩,⟨50080505216,0⟩⟩,⟨⟨18153964609032,3554415466560⟩,⟨24986082240,248525184264⟩,⟨873497184,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18233777905488,144466714565085864⟩,⟨3051907418045592,249463831272⟩,⟨881887914,21578033479752⟩,⟨50855536374,0⟩⟩,⟨⟨18115142701692,3539982772080⟩,⟨25029304380,249462132066⟩,⟨881887914,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24468 173 (4920-R)⟩
def p128:CachedProfile:=⟨⟨24538,151,5079⟩,⟨⟨⟨19235263541080,153572066961164920⟩,⟨2805473344459920,227267394080⟩,⟨694974480,17158224936720⟩,⟨34980382160,0⟩⟩,⟨⟨19103967796560,3822052736880⟩,⟨23375995920,227265859920⟩,⟨694974480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19194826229670,153265828833782730⟩,⟨2818493386918560,228322136640⟩,⟨702823680,17352013835520⟩,⟨35609733120,0⟩⟩,⟨⟨19064303444940,3807018617220⟩,⟨23438244960,228320595360⟩,⟨702823680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19174613278990,153112721363704210⟩,⟨2815713761448720,228096966880⟩,⟨702130560,17334901395840⟩,⟨35574615040,0⟩⟩,⟨⟨19044475833180,3799512667440⟩,⟨23392033920,228095427120⟩,⟨702130560,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24689 152 (5079-R)⟩
def p129:CachedProfile:=⟨⟨24794,145,5079⟩,⟨⟨⟨19613439061080,158264081674144920⟩,⟨2748831559628400,220446701600⟩,⟨640842000,15981958638000⟩,⟨30974030000,0⟩⟩,⟨⟨19482140776560,3860754716880⟩,⟨22447148400,220445228400⟩,⟨640842000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19572257309670,157948607145227730⟩,⟨2762340526253880,221530080720⟩,⟨648432720,16171263604080⟩,⟨31557059040,0⟩⟩,⟨⟨19441731989940,3845568362220⟩,⟨22513051080,221528600280⟩,⟨648432720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19551672138990,157790881474606710⟩,⟨2759616280182060,221311609240⟩,⟨647793240,16155315612360⟩,⟨31525937680,0⟩⟩,⟨⟨19421532160680,3837986407440⟩,⟨22468664160,221310130260⟩,⟨647793240,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24939 146 (5079-R)⟩
def p130:CachedProfile:=⟨⟨12772,95,2571⟩,⟨⟨⟨2640200224524,11002770180639612⟩,⟨242724664839240,37729028080⟩,⟨139273800,1792035984600⟩,⟨4410337000,0⟩⟩,⟨⟨2623133011224,510506871624⟩,⟨3769188840,37728539400⟩,⟨139273800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2624910703382,10942167692843426⟩,⟨243944505258624,37918646016⟩,⟨141447168,1820000710656⟩,⟨4526309376,0⟩⟩,⟨⟨2608120034868,504963304812⟩,⟨3767504256,37918154880⟩,⟨141447168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12867 96 (2571-R)⟩
def p131:CachedProfile:=⟨⟨42018,250,10158⟩,⟨⟨⟨114144352249616,1545020901995346536⟩,⟨27225167187390000,1288222154000⟩,⟨3809625000,161025229500000⟩,⟨317468750000,0⟩⟩,⟨⟨113095237399116,26171108500176⟩,⟨154792683000,1288217074500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨114021689904696,1543468625156818176⟩,⟨27307161292103280,1292101910376⟩,⟨3836382894,162156232163592⟩,⟨320977368798,0⟩⟩,⟨⟨112975668605136,26119608323616⟩,⟨155106030312,1292096815578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨114009425345196,1543313404279704972⟩,⟨27304470635732784,1291974597152⟩,⟨3836004888,162140254605984⟩,⟨320945742296,0⟩⟩,⟨⟨112963713065736,26114461095648⟩,⟨155075464536,1291969502856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42268 251 (10158-R)⟩
def p132:CachedProfile:=⟨⟨41018,250,10158⟩,⟨⟨⟨109052417633616,1438676318917786536⟩,⟨25952203851390000,1257745154000⟩,⟨3809625000,157215604500000⟩,⟨317468750000,0⟩⟩,⟨⟨108003323101116,25551937768176⟩,⟨154792683000,1257740074500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨108934767528696,1437228723465538176⟩,⟨26030364154919280,1261533122376⟩,⟨3836382894,158319849269592⟩,⟨320977368798,0⟩⟩,⟨⟨107888766527136,25501656011616⟩,⟨155106030312,1261528027578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨108923004193196,1437083970726920972⟩,⟨26027799303764784,1261408821152⟩,⟨3836004888,158304249717984⟩,⟨320945742296,0⟩⟩,⟨⟨107877312209736,25496630559648⟩,⟨155075464536,1261403726856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41268 251 (10158-R)⟩
def p133:CachedProfile:=⟨⟨15227,106,3037⟩,⟨⟨⟨4425913085846,21989572701861002⟩,⟨454266150485784,59254440112⟩,⟨204809808,3140348786064⟩,⟨7236613216,0⟩⟩,⟨⟨4397799327516,848810899188⟩,⟨5867994216,59253796056⟩,⟨204809808,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4404234307536,21887064425970576⟩,⟨456438484464480,59537806272⟩,⟨207730656,3185134148448⟩,⟨7409060064,0⟩⟩,⟨⟨4376506661856,841004500896⟩,⟨5868876384,59537159136⟩,⟨207730656,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 15333 107 (3037-R)⟩
def p134:CachedProfile:=⟨⟨33072,8,10477⟩,⟨⟨⟨74549310693442,770679758545500934⟩,⟨550375317850176,33275445632⟩,⟨4023552,133099100160⟩,⟨10729472,0⟩⟩,⟨⟨73398473300100,21788738630880⟩,⟨5269344288,33275277984⟩,⟨4023552,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨74467199978092,769909756672671244⟩,⟨618581295304848,37399149216⟩,⟨5087448,168292779840⟩,⟨15262344,0⟩⟩,⟨⟨73319653339560,21747166994880⟩,⟨5916702024,37398960792⟩,⟨5087448,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 33080 9 (10477-R)⟩
def p135:CachedProfile:=⟨⟨43018,250,10222⟩,⟨⟨⟨120176803145296,1667158231995436072⟩,⟨28708334939646000,1327006738000⟩,⟨3833625000,165873286500000⟩,⟨319468750000,0⟩⟩,⟨⟨119107724537436,27128907753648⟩,⟨156749259000,1327001626500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨120048812999416,1665495404225387392⟩,⟨28794973539352944,1331011512712⟩,⟨3860575278,167039371128504⟩,⟨323001464926,0⟩⟩,⟨⟨118982867074176,27075856858848⟩,⟨157068504936,1331006385786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨120036015670380,1665329128341282252⟩,⟨28792154065380912,1330881187488⟩,⟨3860197272,167023015564896⟩,⟨322969838424,0⟩⟩,⟨⟨118970382676296,27070554625056⟩,⟨157037746392,1330876061064⟩,⟨3860197272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43268 251 (10222-R)⟩
def p136:CachedProfile:=⟨⟨40768,250,10158⟩,⟨⟨⟨107798482104616,1412881013202146536⟩,⟨25638725048640000,1250125904000⟩,⟨3809625000,156263198250000⟩,⟨317468750000,0⟩⟩,⟨⟨106749392651616,25397145085176⟩,⟨154792683000,1250120824500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨107682066309696,1411458809633968176⟩,⟨25715941243748280,1253890925376⟩,⟨3836382894,157360753546092⟩,⟨320977368798,0⟩⟩,⟨⟨106636070382636,25347167933616⟩,⟨155106030312,1253885830578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨107670426405196,1411316596083724972⟩,⟨25713407373272784,1253767377152⟩,⟨3836004888,157345248495984⟩,⟨320945742296,0⟩⟩,⟨⟨106624739495736,25342172925648⟩,⟨155075464536,1253762282856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 12=>⟨⟨⟨107658786805120,1411174383770066392⟩,⟨25710873502803312,1253643828928⟩,⟨3835626882,157329743445876⟩,⟨320914115794,0⟩⟩,⟨⟨106613408852376,25337178409896⟩,⟨155044901772,1253638735134⟩,⟨3835626882,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨107647147509438,1411032172692748914⟩,⟨25708339632339864,1253520280704⟩,⟨3835248876,157314238395768⟩,⟨320882489292,0⟩⟩,⟨⟨106602078452532,25332184386360⟩,⟨155014342020,1253515187412⟩,⟨3835248876,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41018 251 (10158-R)⟩
def p137:CachedProfile:=⟨⟨24391,157,5079⟩,⟨⟨⟨19023652940680,150967318937133160⟩,⟨2883727141876320,234948415040⟩,⟨751301520,18442949712960⟩,⟨39318112880,0⟩⟩,⟨⟨18892358628720,3800224820160⟩,⟨24304843440,234946819920⟩,⟨751301520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18983632185570,150666208352275590⟩,⟨2896381949451120,235979459040⟩,⟨759404880,18641870994240⟩,⟨39995323680,0⟩⟩,⟨⟨18853110830580,3785276561040⟩,⟨24363438840,235977856920⟩,⟨759404880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨18963627513040,150515664653332480⟩,⟨2893525508979840,235746737680⟩,⟨758655960,18623486506080⟩,⟨39955880560,0⟩⟩,⟨⟨18833491495560,3777813478080⟩,⟨24315403680,235745137140⟩,⟨758655960,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24548 158 (5079-R)⟩
def p138:CachedProfile:=⟨⟨24904,142,5237⟩,⟨⟨⟨20434246658154,165353301501691662⟩,⟨2799555571149840,223555325760⟩,⟨633714192,15872005652832⟩,⟨29995805088,0⟩⟩,⟨⟨20290326003036,4122281968056⟩,⟨23371557912,223553838168⟩,⟨633714192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20392499720164,165033312252644452⟩,⟨2813888319493680,224699858240⟩,⟨641444232,16065612234672⟩,⟨30575508392,0⟩⟩,⟨⟨20249400885576,4106555584656⟩,⟨23446356648,224698363032⟩,⟨641444232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25046 143 (5237-R)⟩
def p139:CachedProfile:=⟨⟨24327,169,4920⟩,⟨⟨⟨18313806129584,145259987759946752⟩,⟨2994255034671264,244471540040⟩,⟨843292086,20657282938656⟩,⟨47505454178,0⟩⟩,⟨⟨18194445345552,3558482968320⟩,⟨24550278480,244469876742⟩,⟨843292086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18274176655824,144961230357939912⟩,⟨3005851768567920,245418385200⟩,⟨851567400,20859995030400⟩,⟨48255486000,0⟩⟩,⟨⟨18155541177012,3544033757760⟩,⟨24595270200,245416715460⟩,⟨851567400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24496 170 (4920-R)⟩
def p140:CachedProfile:=⟨⟨24327,169,5047⟩,⟨⟨⟨18818394792744,149056779464184072⟩,⟨3071531358061920,250780803520⟩,⟨865055568,21190401193728⟩,⟨48731463664,0⟩⟩,⟨⟨18689563770096,3744545177856⟩,⟨25833937584,250779097296⟩,⟨865055568,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18778575620354,148757643526547462⟩,⟨3083585343128400,251764981600⟩,⟨873589200,21399441043200⟩,⟨49503388000,0⟩⟩,⟨⟨18650507841636,3729722648256⟩,⟨25883934120,251763268680⟩,⟨873589200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24496 170 (5047-R)⟩
def p141:CachedProfile:=⟨⟨24259,175,4761⟩,⟨⟨⟨17598745944070,139452812254641274⟩,⟨2985209092987800,244351553600⟩,⟨875017500,21380177595000⟩,⟨51042687500,0⟩⟩,⟨⟨17490572404452,3323788588728⟩,⟨23805476100,244349886900⟩,⟨875017500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨17559529170480,139156728630323184⟩,⟨2995962694788096,245231788032⟩,⟨883187712,21579808555008⟩,⟨51813679104,0⟩⟩,⟨⟨17452034800992,3309842150208⟩,⟨23841050112,245230115328⟩,⟨883187712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨17543846453956,139038302788396036⟩,⟨2993440800556800,245025363968⟩,⟨882444288,21561643732992⟩,⟨51770064896,0⟩⟩,⟨⟨17436622953960,3304271784624⟩,⟨23800926336,245023692672⟩,⟨882444288,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24434 176 (4761-R)⟩
def p142:CachedProfile:=⟨⟨41268,250,10158⟩,⟨⟨⟨110313972412616,1464786055842426536⟩,⟨26267587466640000,1265364404000⟩,⟨3809625000,158168010750000⟩,⟨317468750000,0⟩⟩,⟨⟨109264872800616,25706730451176⟩,⟨154792683000,1265359324500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨110195080497696,1463312758996108176⟩,⟨26346697615340280,1269175319376⟩,⟨3836382894,159278944993092⟩,⟨320977368798,0⟩⟩,⟨⟨109149074421636,25656144089616⟩,⟨155106030312,1269170224578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨110183192981196,1463165436118116972⟩,⟨26344101595256784,1269050265152⟩,⟨3836004888,159263250939984⟩,⟨320945742296,0⟩⟩,⟨⟨109137495923736,25651088193648⟩,⟨155075464536,1269045170856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41518 251 (10158-R)⟩
def p143:CachedProfile:=⟨⟨24724,139,5079⟩,⟨⟨⟨19498070635480,156827700900521560⟩,⟨2619051023599440,210680787680⟩,⟨588904080,14641922141040⟩,⟨27285889040,0⟩⟩,⟨⟨19366773123120,3848989314960⟩,⟨21518300880,210679375440⟩,⟨588904080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19457115987270,156515053939050690⟩,⟨2632700329131600,211778767200⟩,⟨596232000,14824116216000⟩,⟨27824160000,0⟩⟩,⟨⟨19326591438180,3833849239740⟩,⟨21587857200,211777347600⟩,⟨596232000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨19432550500296,156327480600246216⟩,⟨2629584656395200,211528141440⟩,⟨595526400,14806572883200⟩,⟨27791232000,0⟩⟩,⟨⟨19302488268816,3824779515696⟩,⟨21536786880,211526723520⟩,⟨595526400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24863 140 (5079-R)⟩
def p144:CachedProfile:=⟨⟨24769,195,5143⟩,⟨⟨⟨19915870577736,160764247049348136⟩,⟨3750786442035360,300498694080⟩,⟨1173603600,29297840270400⟩,⟨76284234000,0⟩⟩,⟨⟨19779552638448,3962624392128⟩,⟨30953042640,300496687920⟩,⟨1173603600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19874515925666,160447637991045446⟩,⟨3762692155346208,301452544064⟩,⟨1183366464,29541560407296⟩,⟨77313275648,0⟩⟩,⟨⟨19738990559988,3947231090448⟩,⟨30990918672,301450531536⟩,⟨1183366464,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨19870381307976,160415978829661056⟩,⟨3761959246476480,301393827168⟩,⟨1183135968,29535806305152⟩,⟨77298216576,0⟩⟩,⟨⟨19734935030160,3945693407904⟩,⟨30978845856,301391815032⟩,⟨1183135968,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24964 196 (5143-R)⟩
def p145:CachedProfile:=⟨⟨24916,139,6114⟩,⟨⟨⟨24176482904770,193766553683870410⟩,⟨3201546291427230,255563289980⟩,⟨708887490,17761176061950⟩,⟨32845120370,0⟩⟩,⟨⟨23947591691580,5620404246300⟩,⟨31180849740,255561590010⟩,⟨708887490,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨24120240645294,193345720714152522⟩,⟨3217723668729360,256854659040⟩,⟨717595200,17979347736000⟩,⟨33487776000,0⟩⟩,⟨⟨23892805003572,5596530639660⟩,⟨31271773680,256852950480⟩,⟨717595200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25055 140 (6114-R)⟩
def p146:CachedProfile:=⟨⟨51706,309,8934⟩,⟨⟨⟨148614757049330,2521261198011266690⟩,⟨44819226843810570,1723330012020⟩,⟨5118736410,266251074366150⟩,⟨527229850230,0⟩⟩,⟨⟨147900668400420,24912674756100⟩,⟨147996087660,1723324490190⟩,⟨5118736410,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨148318466241582,2516427843038223114⟩,⟨44878721942101320,1725617661040⟩,⟨5142118800,267467309382000⟩,⟨531352276000,0⟩⟩,⟨⟨147608442557940,24817960434540⟩,⟨147910559160,1725612131880⟩,⟨5142118800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 18=>⟨⟨⟨148301039779694,2516143536649195142⟩,⟨44873689533740340,1725424162760⟩,⟨5141542200,267437317533000⟩,⟨531292694000,0⟩⟩,⟨⟨147591254729832,24812394621480⟩,⟨147877387920,1725418634220⟩,⟨5141542200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 52015 310 (8934-R)⟩
def p147:CachedProfile:=⟨⟨8673,61,1752⟩,⟨⟨⟨829374858296,2345634214485296⟩,⟨48945111843480,11208289328⟩,⟨39137478,341826732852⟩,⟨795795386,0⟩⟩,⟨⟨823963396380,160946099424⟩,⟨1124079696,11208075462⟩,⟨39137478,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨821823253526,2325322437079466⟩,⟨49321793999280,11294552896⟩,⟨40085232,350104416288⟩,⟨828428128,0⟩⟩,⟨⟨816549054420,158202750024⟩,⟨1123033032,11294337384⟩,⟨40085232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8734 62 (1752-R)⟩
def p148:CachedProfile:=⟨⟨43267,250,10158⟩,⟨⟨⟨120675398431954,1685096617997567830⟩,⟨28857903355792500,1326287927000⟩,⟨3809625000,165783451125000⟩,⟨317468750000,0⟩⟩,⟨⟨119626258204272,26944452744444⟩,⟨154792683000,1326282847500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨120546307259214,1683406456267494690⟩,⟨28944814794476490,1330282326588⟩,⟨3836382894,166947874398198⟩,⟨320977368798,0⟩⟩,⟨⟨119500260607452,26891430761304⟩,⟨155106030312,1330277231790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43517 251 (10158-R)⟩
def p149:CachedProfile:=⟨⟨45017,250,10158⟩,⟨⟨⟨130146085545954,1895334222374490330⟩,⟨31225539577792500,1379622677000⟩,⟨3809625000,172450294875000⟩,⟨317468750000,0⟩⟩,⟨⟨129096909761772,28028001525444⟩,⟨154792683000,1379617597500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨130007671913214,1893437111368352190⟩,⟨31319581659044490,1383777705588⟩,⟨3836382894,173661544462698⟩,⟨320977368798,0⟩⟩,⟨⟨128961589739952,27972847307304⟩,⟨155106030312,1383772610790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45267 251 (10158-R)⟩
def p150:CachedProfile:=⟨⟨44017,250,10158⟩,⟨⟨⟨124688548837954,1773170950781320330⟩,⟨29861175718792500,1349145677000⟩,⟨3809625000,168640669875000⟩,⟨317468750000,0⟩⟩,⟨⟨123639393371772,27408830793444⟩,⟨154792683000,1349140597500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨124555507325214,1771394092269362190⟩,⟨29951108726648490,1353208917588⟩,⟨3836382894,169825161568698⟩,⟨320977368798,0⟩⟩,⟨⟨123509445449952,27354894995304⟩,⟨155106030312,1353203822790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44267 251 (10158-R)⟩
def p151:CachedProfile:=⟨⟨44268,250,10222⟩,⟨⟨⟨126907677460296,1814886672449916072⟩,⟨30391027960896000,1365342988000⟩,⟨3833625000,170665317750000⟩,⟨319468750000,0⟩⟩,⟨⟨125838573294936,27912654048648⟩,⟨156749259000,1365337876500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨126773103264416,1813079337190317392⟩,⟨30482744761237944,1369463457712⟩,⟨3860575278,171865090226004⟩,⟨323001464926,0⟩⟩,⟨⟨125707131806676,27858070528848⟩,⟨157068504936,1369458330786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44518 251 (10222-R)⟩
def p152:CachedProfile:=⟨⟨44518,250,10190⟩,⟨⟨⟨127842038655888,1839569986831819464⟩,⟨30637114699446000,1368712446000⟩,⟨3821625000,171086508000000⟩,⟨318468750000,0⟩⟩,⟨⟨126782932499412,27893944264320⟩,⟨155769435000,1368707350500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨127706223084088,1837733155875014464⟩,⟨30729479686879824,1372838863544⟩,⟨3848479086,172288711722048⟩,⟨321989416862,0⟩⟩,⟨⟨126650230053672,27839226128640⟩,⟨156085725480,1372833752682⟩,⟨3848479086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44768 251 (10190-R)⟩
def p153:CachedProfile:=⟨⟨24296,172,5015⟩,⟨⟨⟨18649764095688,147594562678596264⟩,⟨3099141778347648,253324693248⟩,⟨890360064,21785330045952⟩,⟨51047310336,0⟩⟩,⟨⟨18523365104112,3692990473920⟩,⟨25960207680,253322967744⟩,⟨890360064,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18610075439138,147296530912659014⟩,⟨3110945506675752,254289541712⟩,⟨898947444,21995446059792⟩,⟨51839302604,0⟩⟩,⟨⟨18484430040372,3678278844240⟩,⟨26007121140,254287809636⟩,⟨898947444,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24468 173 (5015-R)⟩
def p154:CachedProfile:=⟨⟨24374,170,5079⟩,⟨⟨⟨19017667481480,150893860152844520⟩,⟨3121489595870400,254361289600⟩,⟨880872000,21620122368000⟩,⟨49916080000,0⟩⟩,⟨⟨18886373210160,3799605588480⟩,⟨26317346400,254359562400⟩,⟨880872000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18977658508770,150592894174326630⟩,⟨3133670385694680,255353875920⟩,⟨889511220,21832163383680⟩,⟨50702139540,0⟩⟩,⟨⟨18847137194340,3784659765120⟩,⟨26368025580,255352141980⟩,⟨889511220,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24544 171 (5079-R)⟩
def p155:CachedProfile:=⟨⟨42518,250,10222⟩,⟨⟨⟨117538124169296,1610402499512144072⟩,⟨28048675418646000,1311672238000⟩,⟨3833625000,163956474000000⟩,⟨319468750000,0⟩⟩,⟨⟨116469055784436,26815409235648⟩,⟨156749259000,1311667126500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨117412715143416,1608795190042915392⟩,⟨28133323231348944,1315630734712⟩,⟨3860575278,165109083489504⟩,⟨323001464926,0⟩⟩,⟨⟨116346779431176,26762971390848⟩,⟨157068504936,1315625607786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨117400175926380,1608634465988826252⟩,⟨28130568542484912,1315501915488⟩,⟨3860197272,165092916928896⟩,⟨322969838424,0⟩⟩,⟨⟨116334553144296,26757730429056⟩,⟨157037746392,1315496789064⟩,⟨3860197272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42768 251 (10222-R)⟩
def p156:CachedProfile:=⟨⟨25216,192,5143⟩,⟨⟨⟨20606167394376,169457290846845096⟩,⟨3825615515904000,301137825792⟩,⟨1137770496,28908472762368⟩,⟨72817311744,0⟩⟩,⟨⟨20469844887216,4033102089216⟩,⟨30476841984,301135850496⟩,⟨1137770496,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20563470796706,169123782129704486⟩,⟨3838064699047560,302117787248⟩,⟨1147418196,29153601523968⟩,⟨73817237276,0⟩⟩,⟨⟨20427940872036,4017435008256⟩,⟨30516567876,302115805524⟩,⟨1147418196,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25408 193 (5143-R)⟩
def p157:CachedProfile:=⟨⟨16983,137,3952⟩,⟨⟨⟨7260881405152,39917740647614464⟩,⟨952396661139264,111262624328⟩,⟨445163142,7621192991040⟩,⟨20329116818,0⟩⟩,⟨⟨7199006898720,1604718136320⟩,⟨12841494432,111261541206⟩,⟨445163142,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨7240956996352,39814908851890024⟩,⟨956921509212336,111791242032⟩,⟨450542952,7713295338240⟩,⟨20724975792,0⟩⟩,⟨⟨7179550275780,1596608392320⟩,⟨12869857368,111790153764⟩,⟨450542952,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 17120 138 (3952-R)⟩
def p158:CachedProfile:=⟨⟨305649,839,85266⟩,⟨⟨⟨51157082730568360,4962544335295172610712⟩,⟨40320130878073228728,263110760508232⟩,⟨360127391442,110374723948275696⟩,⟨100715627139946,0⟩⟩,⟨⟨50537114582051916,13369698037384416⟩,⟨36599072894748,263110617430206⟩,⟨360127391442,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨51148338270874026,4961763561118526149806⟩,⟨40362033608422344000,263384198663040⟩,⟨360931334400,110621122817587200⟩,⟨101060773632000,0⟩⟩,⟨⟨50528653630654836,13365621575351136⟩,⟨36631522680480,263384055436320⟩,⟨360931334400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 306488 840 (85266-R)⟩
def p159:CachedProfile:=⟨⟨45018,250,10222⟩,⟨⟨⟨131038209049296,1907604369848604072⟩,⟨31423645523646000,1388344738000⟩,⟨3833625000,173540536500000⟩,⟨319468750000,0⟩⟩,⟨⟨129969089549436,28382901825648⟩,⟨156749259000,1388339626500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨130899594423416,1905706338475275392⟩,⟨31518478661368944,1392534624712⟩,⟨3860575278,174760521684504⟩,⟨323001464926,0⟩⟩,⟨⟨129833607646176,28327398730848⟩,⟨157068504936,1392529497786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45268 251 (10222-R)⟩
def p160:CachedProfile:=⟨⟨4133,1,1278⟩,⟨⟨⟨141638741736,183473179503336⟩,⟨131167937088,63458864⟩,⟨7674,31724316⟩,⟨2558,0⟩⟩,⟨⟨139539196728,40543675848⟩,⟨9807372,63456306⟩,⟨7674,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨140369754816,181976351199696⟩,⟨260284468176,125925408⟩,⟨30456,125905104⟩,⟨20304,0⟩⟩,⟨⟨138318934068,39911917968⟩,⟨19309104,125920332⟩,⟨30456,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4134 2 (1278-R)⟩
def p161:CachedProfile:=⟨⟨4133,1,1286⟩,⟨⟨⟨142656691320,184672059538824⟩,⟨131988501216,63855792⟩,⟨7722,31922748⟩,⟨2574,0⟩⟩,⟨⟨140517614952,41052653928⟩,⟨9930492,63853218⟩,⟨7722,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨141384638480,183173657171984⟩,⟨261925592592,126719264⟩,⟨30648,126698832⟩,⟨20432,0⟩⟩,⟨⟨139294899492,40416927408⟩,⟨19553424,126714156⟩,⟨30648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4134 2 (1286-R)⟩
def p162:CachedProfile:=⟨⟨24758,158,5237⟩,⟨⟨⟨20230114464954,162803607837839262⟩,⟨3082746426588720,247453596000⟩,⟨784568592,19548311038272⟩,⟨41320612512,0⟩⟩,⟨⟨20086195171716,4100885471376⟩,⟨26004972888,247451940792⟩,⟨784568592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20188757240964,162488486355846852⟩,⟨3096334780935120,248544348000⟩,⟨793014408,19758746989728⟩,⟨42029763624,0⟩⟩,⟨⟨20045659765656,4085240714976⟩,⟨26069725224,248542685496⟩,⟨793014408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24916 159 (5237-R)⟩
def p163:CachedProfile:=⟨⟨24546,154,5079⟩,⟨⟨⟨19251823132040,153776530260086120⟩,⟨2863761333639360,231885906560⟩,⟨722863680,17854732896000⟩,⟨37107002240,0⟩⟩,⟨⟨19120527275760,3823755624000⟩,⟨23840419680,231884341920⟩,⟨722863680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19211353223010,153469889639202630⟩,⟨2876683160683800,232932226800⟩,⟨730840500,18051760350000⟩,⟨37760092500,0⟩⟩,⟨⟨19080830326740,3808714806000⟩,⟨23900841900,232930655100⟩,⟨730840500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19191123973520,153316580922383360⟩,⟨2873846147937600,232702510600⟩,⟨730119750,18033957825000⟩,⟨37722853750,0⟩⟩,⟨⟨19060986416280,3801205512000⟩,⟨23853718800,232700940450⟩,⟨730119750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24700 155 (5079-R)⟩
def p164:CachedProfile:=⟨⟨24672,148,5396⟩,⟨⟨⟨20735208329304,165896061317331072⟩,⟨2952409175214912,237907877088⟩,⟨709295328,17604710040960⟩,⟨34991902848,0⟩⟩,⟨⟨20577796966272,4336879811040⟩,⟨25860524256,237906279576⟩,⟨709295328,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20693884211544,165583962720947352⟩,⟨2966850363402216,239071569224⟩,⟨717580722,17810353520040⟩,⟨35639842526,0⟩⟩,⟨⟨20537345339412,4320821767440⟩,⟨25938857508,239069963898⟩,⟨717580722,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨20673228214314,165427926508438542⟩,⟨2964096602308296,238849672464⟩,⟨716914692,17793822655440⟩,⟨35606763036,0⟩⟩,⟨⟨20517124375332,4312803914640⟩,⟨25890724548,238848068628⟩,⟨716914692,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24820 149 (5396-R)⟩
def p165:CachedProfile:=⟨⟨24672,148,5143⟩,⟨⟨⟨19694603845704,158010381660866088⟩,⟨2814004136184192,226755256576⟩,⟨676045056,16779438289920⟩,⟨33351556096,0⟩⟩,⟨⟨19558287387888,3939766760640⟩,⟨23492565696,226753733952⟩,⟨676045056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19653679338914,157699126239856838⟩,⟨2827510164236136,227843593168⟩,⟨683879604,16973891771280⟩,⟨33966020332,0⟩⟩,⟨⟨19518155451828,3924462252240⟩,⟨23559422868,227842063236⟩,⟨683879604,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19633222862544,157543510417010688⟩,⟨2824756407665856,227621696408⟩,⟨683213574,16957360906680⟩,⟨33932940842,0⟩⟩,⟨⟨19498094105448,3916821167040⟩,⟨23513551728,227620167966⟩,⟨683213574,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24820 149 (5143-R)⟩
def p166:CachedProfile:=⟨⟨24535,143,5079⟩,⟨⟨⟨19218711326280,153367785772257960⟩,⟨2654472092294880,215130847360⟩,⟨623285520,15381440062560⟩,⟨29709943120,0⟩⟩,⟨⟨19087415693520,3820349849760⟩,⟨22137532560,215129394480⟩,⟨623285520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19178306597970,153061949779892790⟩,⟨2667772866994560,216208811520⟩,⟨630789120,15566613903360⟩,⟨30277877760,0⟩⟩,⟨⟨19047783924780,3805322428440⟩,⟨22204653120,216207351360⟩,⟨630789120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨19154071062936,152878463022338616⟩,⟨2664615686837760,215952943104⟩,⟨630042624,15548191875072⟩,⟨30242045952,0⟩⟩,⟨⟨19024010705136,3796320190176⟩,⟨22152123648,215951484672⟩,⟨630042624,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24678 144 (5079-R)⟩
def p167:CachedProfile:=⟨⟨43268,250,10222⟩,⟨⟨⟨121507643508296,1696032759690332072⟩,⟨29041039918896000,1334673988000⟩,⟨3833625000,166831692750000⟩,⟨319468750000,0⟩⟩,⟨⟨120438559788936,27285657012648⟩,⟨156749259000,1334668876500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨121378351552416,1694341686942373392⟩,⟨29128682589229944,1338701901712⟩,⟨3860575278,168004514948004⟩,⟨323001464926,0⟩⟩,⟨⟨120312400520676,27232299592848⟩,⟨157068504936,1338696774786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨121365424042380,1694172586560510252⟩,⟨29125830440328912,1338570823488⟩,⟨3860197272,167988064882896⟩,⟨322969838424,0⟩⟩,⟨⟨120299785942296,27226966723056⟩,⟨157037746392,1338565697064⟩,⟨3860197272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43518 251 (10222-R)⟩
def p168:CachedProfile:=⟨⟨5691,37,1208⟩,⟨⟨⟨246883196976,456659853851136⟩,⟨8806782535200,3075125352⟩,⟨9930726,56883198528⟩,⟨122478954,0⟩⟩,⟨⟨245105096496,50193501696⟩,⟨324224784,3075035886⟩,⟨9930726,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨243823373720,451298270962040⟩,⟨8940058875120,3121665040⟩,⟨10353480,59304733440⟩,⟨131144080,0⟩⟩,⟨⟨242106048780,49037293440⟩,⟨325317240,3121574220⟩,⟨10353480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5728 38 (1208-R)⟩
def p169:CachedProfile:=⟨⟨256165,998,69587⟩,⟨⟨⟨29297299601686356,2390417547462618666372⟩,⟨27557132690428825392,214316570706336⟩,⟨415859558112,106943691542756256⟩,⟨138342612998592,0⟩⟩,⟨⟨28960294319373096,7471747767464568⟩,⟨28996411894128,214316431808688⟩,⟨415859558112,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨29291666530288968,2389993206140268420744⟩,⟨27579988227159881136,214494322232736⟩,⟨416621505456,107139636207581328⟩,⟨138734961316848,0⟩⟩,⟨⟨28954835550378192,7469171062095600⟩,⟨29015456698800,214494183219888⟩,⟨416621505456,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 257163 999 (69587-R)⟩
def p170:CachedProfile:=⟨⟨149030,860,34564⟩,⟨⟨⟨4865946335752320,234230262893069666160⟩,⟨4007125259252431200,53467619619200⟩,⟨153385644000,22990974179160000⟩,⟨43970551280000,0⟩⟩,⟨⟨4824642201988380,1074445688924400⟩,⟨6164676045600,53467560167400⟩,⟨153385644000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4863808304059320,234133657870299957000⟩,⟨4010159793047839200,53508109884768⟩,⟨153680291226,23035138851865140⟩,⟨44106243581862,0⟩⟩,⟨⟨4822554331283040,1073575478547000⟩,⟨6166845600300,53508050387946⟩,⟨153680291226,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 149890 861 (34564-R)⟩
def p171:CachedProfile:=⟨⟨778,5,174⟩,⟨⟨⟨671392050,169225052850⟩,⟨3220544250,8228500⟩,⟨26250,20553750⟩,⟨43750,0⟩⟩,⟨⟨665819700,143054100⟩,⟨913500,8226750⟩,⟨26250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨626146916,158417385716⟩,⟨3621602160,9253536⟩,⟨35424,27736992⟩,⟨70848,0⟩⟩,⟨⟨621532776,125586936⟩,⟨962352,9251568⟩,⟨35424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨613911998,155477174174⟩,⟨3555318564,9084264⟩,⟨34776,27229608⟩,⟨69552,0⟩⟩,⟨⟨609538272,121020480⟩,⟨927360,9082332⟩,⟨34776,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 783 6 (174-R)⟩
def p172:CachedProfile:=⟨⟨52251,356,10569⟩,⟨⟨⟨181422840441010,3090315389828053870⟩,⟨62483683670844240,2375501292640⟩,⟨8037597120,422833871691840⟩,⟨953794858240,0⟩⟩,⟨⟨180241019575260,35261734549860⟩,⟨238621808880,2375493766800⟩,⟨8037597120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨181148659537090,3085876809043536730⟩,⟨62570278617877170,2378793480420⟩,⟨8071345170,424609255358190⟩,⟨960490075230,0⟩⟩,⟨⟨179971860104940,35161720225740⟩,⟨238613380740,2378785944150⟩,⟨8071345170,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 52607 357 (10569-R)⟩
def p173:CachedProfile:=⟨⟨16536,4,5096⟩,⟨⟨⟨9028918524624,46806256147441152⟩,⟨33466713451776,4046773344⟩,⟨489312,8093220480⟩,⟨652416,0⟩⟩,⟨⟨8896384821912,2577690722880⟩,⟨623383488,4046732568⟩,⟨489312,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨9008614449264,46710459669560232⟩,⟨41751314224920,5048542280⟩,⟨763050,12620847000⟩,⟨1271750,0⟩⟩,⟨⟨8876858727852,2567585113680⟩,⟨776174460,5048491410⟩,⟨763050,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16540 5 (5096-R)⟩
def p174:CachedProfile:=⟨⟨44518,250,10475⟩,⟨⟨⟨131725749507588,1891973045975596164⟩,⟨31493916678636000,1406989656000⟩,⟨3928500000,175871088000000⟩,⟨327375000000,0⟩⟩,⟨⟨130575325880952,29475994348800⟩,⟨164604150000,1406984418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨131589050894638,1890132563870119714⟩,⟨31589708856818184,1411269182384⟩,⟨3956210796,177111644915328⟩,⟨331002969932,0⟩⟩,⟨⟨130441917000012,29419745147520⟩,⟨164947195140,1411263928452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44768 251 (10475-R)⟩
def p175:CachedProfile:=⟨⟨40518,250,10158⟩,⟨⟨⟨106552165825616,1387398233883006536⟩,⟨25327151058390000,1242506654000⟩,⟨3809625000,155310792000000⟩,⟨317468750000,0⟩⟩,⟨⟨105503081452116,25242352402176⟩,⟨154792683000,1242501574500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨106436976840696,1386001114563898176⟩,⟨25403428881827280,1246248728376⟩,⟨3836382894,156401657822592⟩,⟨320977368798,0⟩⟩,⟨⟨105390985988136,25192679855616⟩,⟨155106030312,1246243633578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 12=>⟨⟨⟨106413942698120,1385721705549738392⟩,⟨25398422725740312,1246003137928⟩,⟨3835626882,156370836725376⟩,⟨320914115794,0⟩⟩,⟨⟨105368569818876,25182751216896⟩,⟨155044901772,1245998044134⟩,⟨3835626882,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨106402426083438,1385582002897282914⟩,⟨25395919647705864,1245880342704⟩,⟨3835248876,156355426176768⟩,⟨320882489292,0⟩⟩,⟨⟨105357362099532,25177787631360⟩,⟨155014342020,1245875249412⟩,⟨3835248876,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40768 251 (10158-R)⟩
def p176:CachedProfile:=⟨⟨25026,149,5143⟩,⟨⟨⟨20242399671064,164857189908554008⟩,⟨2914637078888496,231552489248⟩,⟨685211664,17250203641200⟩,⟨34032179312,0⟩⟩,⟨⟨20106079561008,3996117171600⟩,⟨23651299248,231550956336⟩,⟨685211664,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20200410242374,164532623988417058⟩,⟨2928494190954600,232653370800⟩,⟨693090000,17448540750000⟩,⟨34654500000,0⟩⟩,⟨⟨20064882710148,3980593763100⟩,⟨23717539800,232651830600⟩,⟨693090000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25175 150 (5143-R)⟩
def p177:CachedProfile:=⟨⟨25057,147,5143⟩,⟨⟨⟨20287492890696,165425121975113256⟩,⟨2882142961389216,228707548608⟩,⟨666940176,16809560195904⟩,⟨32680068624,0⟩⟩,⟨⟨20151172482288,4000720444608⟩,⟨23333832144,228706036272⟩,⟨666940176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20245415800226,165099451970106566⟩,⟨2896108248022944,229815747392⟩,⟨674730816,17005915486464⟩,⟨33286720256,0⟩⟩,⟨⟨20109887970228,3985179154128⟩,⟨23401305936,229814227728⟩,⟨674730816,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25204 148 (5143-R)⟩
def p178:CachedProfile:=⟨⟨24904,142,5143⟩,⟨⟨⟨20042441660680,162346687275040360⟩,⟨2749314536496576,219543450880⟩,⟨622341696,15587170118016⟩,⟨29457506944,0⟩⟩,⟨⟨19906122877776,3975640543392⟩,⟨22540164384,219541989984⟩,⟨622341696,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20000840952850,162027001882732150⟩,⟨2763293477963304,220659730720⟩,⟨629910996,15776750805816⟩,⟨30025757476,0⟩⟩,⟨⟨19865314745196,3960196678872⟩,⟨22610721276,220658262396⟩,⟨629910996,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25046 143 (5143-R)⟩
def p179:CachedProfile:=⟨⟨24763,147,5396⟩,⟨⟨⟨20880144332544,167697963286102032⟩,⟨2953765485829368,237157219152⟩,⟨699742638,17430589112580⟩,⟨34287389262,0⟩⟩,⟨⟨20722731998052,4352605805520⟩,⟨25685790984,237155632434⟩,⟨699742638,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20838551665584,167382525921201912⟩,⟨2968348825156032,238328120128⟩,⟨707981088,17635808902080⟩,⟨34927067008,0⟩⟩,⟨⟨20682011823792,4336489533720⟩,⟨25764771216,238326525576⟩,⟨707981088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24910 148 (5396-R)⟩
def p180:CachedProfile:=⟨⟨40517,250,10158⟩,⟨⟨⟨106547195859954,1387296927763725330⟩,⟨25325908587292500,1242476177000⟩,⟨3809625000,155306982375000⟩,⟨317468750000,0⟩⟩,⟨⟨105498111506772,25241733231444⟩,⟨154792683000,1242471097500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨106432011767214,1385899908166397190⟩,⟨25402182668762490,1246218159588⟩,⟨3836382894,156397821439698⟩,⟨320977368798,0⟩⟩,⟨⟨105386020934952,25192061903304⟩,⟨155106030312,1246213064790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40767 251 (10158-R)⟩
def p181:CachedProfile:=⟨⟨24705,157,5396⟩,⟨⟨⟨20802779848704,166735325728324752⟩,⟨3142556014848264,252802301808⟩,⟨798183918,19844448569316⟩,⟨41771625042,0⟩⟩,⟨⟨20645368032324,4344218608464⟩,⟨27433123704,252800607150⟩,⟨798183918,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20761330528944,166421672047516152⟩,⟨3156712322214816,253941111392⟩,⟨806886408,20060809875696⟩,⟨42496017488,0⟩⟩,⟨⟨20604791204304,4328133391704⟩,⟨27505634136,253939409100⟩,⟨806886408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24862 158 (5396-R)⟩
def p182:CachedProfile:=⟨⟨24534,163,5079⟩,⟨⟨⟨19247306148440,153720749477068280⟩,⟨3030387760528080,245407870880⟩,⟨809823120,20000201594640⟩,⟨44000389520,0⟩⟩,⟨⟨19116010322640,3823291200240⟩,⟨25233690960,245406214800⟩,⟨809823120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19206845131110,153414218662700970⟩,⟨3042977069349360,246427390560⟩,⟨818176320,20206500575040⟩,⟨44726972160,0⟩⟩,⟨⟨19076322265260,3808252209060⟩,⟨25288632720,246425727600⟩,⟨818176320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24697 164 (5079-R)⟩
def p183:CachedProfile:=⟨⟨24327,169,5063⟩,⟨⟨⟨18882136977240,149535460722092280⟩,⟨3081266962499232,251575671360⟩,⟨867797424,21257565698304⟩,⟨48885921552,0⟩⟩,⟨⟨18752078462736,3768322367232⟩,⟨25997978448,251573959728⟩,⟨867797424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18842293562610,149236275720686070⟩,⟨3093378554039760,252564552800⟩,⟨876363600,21467402745600⟩,⟨49660604000,0⟩⟩,⟨⟨18713003140356,3753452805312⟩,⟨26048619240,252562834440⟩,⟨876363600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24496 170 (5063-R)⟩
def p184:CachedProfile:=⟨⟨24374,170,5015⟩,⟨⟨⟨18761872096968,148968208692493608⟩,⟨3082163087805120,251156737920⟩,⟨869774400,21347742873600⟩,⟨49287216000,0⟩⟩,⟨⟨18635472342960,3704461263360⟩,⟨25658344800,251155032480⟩,⟨869774400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18721959939618,148667438352165798⟩,⟨3094112547855576,252130473936⟩,⟨878282676,21556569999744⟩,⟨50062112532,0⟩⟩,⟨⟨18596313779940,3689703937920⟩,⟨25706460780,252128761884⟩,⟨878282676,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24544 171 (5015-R)⟩
def p185:CachedProfile:=⟨⟨41767,250,10158⟩,⟨⟨⟨112854817369954,1517848828853312830⟩,⟨26902788567292500,1280572427000⟩,⟨3809625000,160069013625000⟩,⟨317468750000,0⟩⟩,⟨⟨111805707619272,26015696646444⟩,⟨154792683000,1280567347500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨112733424377214,1516323299119509690⟩,⟨26983811759882490,1284429144588⟩,⟨3836382894,161193300057198⟩,⟨320977368798,0⟩⟩,⟨⟨111687408172452,25964502293304⟩,⟨155106030312,1284424049790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42017 251 (10158-R)⟩
def p186:CachedProfile:=⟨⟨41017,250,10158⟩,⟨⟨⟨109047386713954,1438572512617810330⟩,⟨25950946141792500,1257714677000⟩,⟨3809625000,157211794875000⟩,⟨317468750000,0⟩⟩,⟨⟨107998292201772,25551318597444⟩,⟨154792683000,1257709597500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨108929741561214,1437125019348392190⟩,⟨26029102657460490,1261502553588⟩,⟨3836382894,158316012886698⟩,⟨320977368798,0⟩⟩,⟨⟨107883740579952,25501038059304⟩,⟨155106030312,1261497458790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41267 251 (10158-R)⟩
def p187:CachedProfile:=⟨⟨41518,250,10158⟩,⟨⟨⟨111583146441616,1491212128788566536⟩,⟨26584875894390000,1272983654000⟩,⟨3809625000,159120417000000⟩,⟨317468750000,0⟩⟩,⟨⟨110534041750116,25861523134176⟩,⟨154792683000,1272978574500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨111463005216696,1489712819163178176⟩,⟨26664941625011280,1276817516376⟩,⟨3836382894,160238040716592⟩,⟨320977368798,0⟩⟩,⟨⟨110416994066136,25810632167616⟩,⟨155106030312,1276812421578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨111450992769196,1489562895007312972⟩,⟨26662314247748784,1276691709152⟩,⟨3836004888,160222252161984⟩,⟨320945742296,0⟩⟩,⟨⟨110405290637736,25805545827648⟩,⟨155075464536,1276686614856⟩,⟨3836004888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41768 251 (10158-R)⟩
def p188:CachedProfile:=⟨⟨24986,187,5143⟩,⟨⟨⟨20239291707416,164818070371122296⟩,⟨3657386166807120,290583057952⟩,⟨1079283216,27168796396368⟩,⟨67275320464,0⟩⟩,⟨⟨20102971617936,3995799704496⟩,⟨29683174224,290581134096⟩,⟨1079283216,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20197308320646,164493580501084986⟩,⟨3669796240154640,291569060128⟩,⟨1088736576,27406765827648⟩,⟨68227492096,0⟩⟩,⟨⟨20061780808956,3980277529236⟩,⟨29725983216,291567129744⟩,⟨1088736576,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨20193110829486,164461133258554722⟩,⟨3669081426034632,291512268336⟩,⟨1088524512,27401427540576⟩,⟨68214202752,0⟩⟩,⟨⟨20057662406076,3978726973128⟩,⟨29714403168,291510338328⟩,⟨1088524512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25173 188 (5143-R)⟩
def p189:CachedProfile:=⟨⟨25032,184,5143⟩,⟨⟨⟨20306167339080,165660510986391720⟩,⟨3611016313051392,286409689600⟩,⟨1044931584,26348994822144⟩,⟨64089137152,0⟩⟩,⟨⟨20169846807216,4002625247232⟩,⟨29206973568,286407796608⟩,⟨1044931584,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20264053945250,165334383374825510⟩,⟨3623583275678280,287406454000⟩,⟨1054266900,26584394150400⟩,⟨65013125500,0⟩⟩,⟨⟨20128525992036,3987076557312⟩,⟨29251632420,287404554420⟩,⟨1054266900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨20259843453384,165301772358148032⟩,⟨3622877463099600,287350473000⟩,⟨1054061550,26579216044800⟩,⟨65000462250,0⟩⟩,⟨⟨20124394588536,3985523352576⟩,⟨29240237160,287348573790⟩,⟨1054061550,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25216 185 (5143-R)⟩
def p190:CachedProfile:=⟨⟨166518,657,44471⟩,⟨⟨⟨7897100248256184,419472281257632017592⟩,⟨4899449964935045808,58614672179232⟩,⟨115177765968,19254843025700400⟩,⟨25223930746992,0⟩⟩,⟨⟨7809134445874032,1983746340651600⟩,⟨7796149817904,58614613743024⟩,⟨115177765968,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨7894534786392674,419346232398663178058⟩,⟨4905472885193663412,58686727566376⟩,⟨115494878856,19307856372751800⟩,⟨25331876762416,0⟩⟩,⟨⟨7806646096092348,1982586724577100⟩,⟨7803451860456,58686669058332⟩,⟨115494878856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 167175 658 (44471-R)⟩
def p191:CachedProfile:=⟨⟨35662,253,7211⟩,⟨⟨⟨57693242830764,670937181246960732⟩,⟨14121605889452952,786396220368⟩,⟨2769797448,99477275344920⟩,⟨233586251448,0⟩⟩,⟨⟨57317711459352,11206715188680⟩,⟨78944701176,786392571096⟩,⟨2769797448,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨57573988366582,669619018972579234⟩,⟨14149900864828488,787971912496⟩,⟨2786317008,100070575342320⟩,⟨235908173344,0⟩⟩,⟨⟨57200637903060,11163245252940⟩,⟨78949305144,787968255912⟩,⟨2786317008,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨57565471810974,669524869198527102⟩,⟨14147935032824676,787862441544⟩,⟨2785929912,100056672789480⟩,⟨235875399216,0⟩⟩,⟨⟨57192276802512,11160143489880⟩,⟨78927368688,787858785468⟩,⟨2785929912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 35915 254 (7211-R)⟩
def p192:CachedProfile:=⟨⟨31928,208,6532⟩,⟨⟨⟨41876139640184,435466001264368832⟩,⟨8420083044023040,524032312960⟩,⟨1695862272,54498229972992⟩,⟨117579784192,0⟩⟩,⟨⟨41596976083416,8228144373696⟩,⟨53256597888,524029595232⟩,⟨1695862272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨41773611337274,434453632209655742⟩,⟨8441138211413160,525342717680⟩,⟨1708276548,54897175146528⟩,⟨119009932844,0⟩⟩,⟨⟨41496364550676,8190400641696⟩,⟨53267168724,525339993156⟩,⟨1708276548,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 32136 209 (6532-R)⟩
def p193:CachedProfile:=⟨⟨4133,1,1270⟩,⟨⟨⟨140623246808,182275560678728⟩,⟨130347374496,63061936⟩,⟨7626,31525884⟩,⟨2542,0⟩⟩,⟨⟨138562742280,40037872680⟩,⟨9685020,63059394⟩,⟨7626,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨139357306608,180780286881168⟩,⟨258643346832,125131552⟩,⟨30264,125111376⟩,⟨20176,0⟩⟩,⟨⟨137344917060,39410083440⟩,⟨19066320,125126508⟩,⟨30264,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4134 2 (1270-R)⟩
def p194:CachedProfile:=⟨⟨44518,250,10174⟩,⟨⟨⟨127624748402800,1836631117063342600⟩,⟨30589013550150000,1366563550000⟩,⟨3815625000,170817900000000⟩,⟨317968750000,0⟩⟩,⟨⟨126570620315700,27806421033600⟩,⟨155280675000,1366558462500⟩,⟨3815625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨127488981682840,1834794485145225280⟩,⟨30681186133950480,1370681371960⟩,⟨3842430990,172017950560320⟩,⟨321483392830,0⟩⟩,⟨⟨126437956951560,27751788852480⟩,⟨155595492360,1370676269130⟩,⟨3842430990,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44768 251 (10174-R)⟩
def p195:CachedProfile:=⟨⟨4134,1,1274⟩,⟨⟨⟨141193956450,183005002703850⟩,⟨130820913450,63275700⟩,⟨7650,31632750⟩,⟨2550,0⟩⟩,⟨⟨139113990300,40300123500⟩,⟨9746100,63273150⟩,⟨7650,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨139925999070,181507928140110⟩,⟨259589430540,125558840⟩,⟨30360,125538600⟩,⟨20240,0⟩⟩,⟨⟨137894452080,39670197600⟩,⟨19187520,125553780⟩,⟨30360,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4135 2 (1274-R)⟩
def p196:CachedProfile:=⟨⟨5245,24,1327⟩,⟨⟨⟨232962563376,391733993187696⟩,⟨5309559348480,2015457792⟩,⟨4589568,24182433792⟩,⟨36716544,0⟩⟩,⟨⟨230610055200,55711961184⟩,⟨253764864,2015394048⟩,⟨4589568,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨229686463218,386601681346278⟩,⟨5459983513650,2072559900⟩,⟨4916250,25903721250⟩,⟨40968750,0⟩⟩,⟨⟨227422840800,54294199740⟩,⟨257611500,2072494350⟩,⟨4916250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5269 25 (1327-R)⟩
def p197:CachedProfile:=⟨⟨24991,151,5237⟩,⟨⟨⟨20585672293482,167253222392384526⟩,⟨2999856855350664,238635485856⟩,⟨716589828,18016501455576⟩,⟨36068354676,0⟩⟩,⟨⟨20441750632668,4138082457912⟩,⟨24852853836,238633903980⟩,⟨716589828,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20543636264932,166929605895461476⟩,⟨3013958330264448,239757251072⟩,⟨724726272,18221067930624⟩,⟨36719464448,0⟩⟩,⟨⟨20400536426568,4122295796112⟩,⟨24922001472,239755661760⟩,⟨724726272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨20526826246264,166800168501529240⟩,⟨3011652279655680,239573810176⟩,⟨724171776,18207126792192⟩,⟨36691369984,0⟩⟩,⟨⟨20384054258352,4115989579104⟩,⟨24883876224,239572222080⟩,⟨724171776,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25142 152 (5237-R)⟩
def p198:CachedProfile:=⟨⟨24296,172,5047⟩,⟨⟨⟨18776869056296,148548468150094472⟩,⟨3118913351173248,254940799744⟩,⟨896040192,21924311417856⟩,⟨51372971008,0⟩⟩,⟨⟨18648038316336,3740264998848⟩,⟨26292528192,254939063232⟩,⟨896040192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18737132145666,148250339185237542⟩,⟨3130832029177512,255915044176⟩,⟨904693812,22136048192016⟩,⟨52170676492,0⟩⟩,⟨⟨18609064649076,3725459412048⟩,⟨26340709428,255913301028⟩,⟨904693812,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24468 173 (5047-R)⟩
def p199:CachedProfile:=⟨⟨8268,2,2572⟩,⟨⟨⟨1141137397552,2955059790030544⟩,⟨2111858006544,510730208⟩,⟨61752,510689040⟩,⟨41168,0⟩⟩,⟨⟨1124073971700,328373052720⟩,⟨79413072,510719916⟩,⟨61752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 8270 3 (2572-R)⟩
def p200:CachedProfile:=⟨⟨24964,143,5237⟩,⟨⟨⟨20530397931822,166558858833439386⟩,⟨2833020017834292,225677951928⟩,⟨642671172,16135545115404⟩,⟨30633992532,0⟩⟩,⟨⟨20386476637668,4132321862652⟩,⟨23536146348,225676453860⟩,⟨642671172,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20488467428972,166236567985734236⟩,⟨2847384842875776,226822258944⟩,⟨650446848,16330769012736⟩,⟨31221448704,0⟩⟩,⟨⟨20345367956568,4116557177352⟩,⟨23610317184,226820753280⟩,⟨650446848,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25107 144 (5237-R)⟩
def p201:CachedProfile:=⟨⟨24985,141,5143⟩,⟨⟨⟨20166325641480,163900549466884200⟩,⟨2747420343619488,218693662080⟩,⟨613607184,15417494105184⟩,⟨28839537648,0⟩⟩,⟨⟨20030006035536,3988339227552⟩,⟨22381430832,218692211472⟩,⟨613607184,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20124484101650,163577843297855990⟩,⟨2761526607899856,219816522560⟩,⟨621131856,15606559013856⟩,⟨29400241184,0⟩⟩,⟨⟨19988957072556,3972846033432⟩,⟨22452604344,219815064504⟩,⟨621131856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25126 142 (5143-R)⟩
def p202:CachedProfile:=⟨⟨24504,145,5079⟩,⟨⟨⟨19175109025880,152830098597200120⟩,⟨2685275413436400,217883333600⟩,⟨640842000,15796114458000⟩,⟨30974030000,0⟩⟩,⟨⟨19043813687760,3815860420080⟩,⟨22447148400,217881860400⟩,⟨640842000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19134790128870,152525321061799530⟩,⟨2698472035167480,218954115120⟩,⟨648432720,15983218115280⟩,⟨31557059040,0⟩⟩,⟨⟨19004267749740,3800850658020⟩,⟨22513051080,218952634680⟩,⟨648432720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨19110606092616,152342469378390696⟩,⟨2695278523904928,218694997824⟩,⟨647665344,15964303064256⟩,⟨31519713408,0⟩⟩,⟨⟨18980546028528,3791858998608⟩,⟨22459792032,218693519136⟩,⟨647665344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24649 146 (5079-R)⟩
def p203:CachedProfile:=⟨⟨24934,150,5143⟩,⟨⟨⟨20101237292616,163083536139136296⟩,⟨2913024606523200,232263945600⟩,⟨694440000,17419332960000⟩,⟨34722000000,0⟩⟩,⟨⟨19964918118768,3981672418368⟩,⟨23810032800,232262402400⟩,⟨694440000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20059522285346,162762418280057606⟩,⟨2926743968420088,233357837744⟩,⟨702362004,17618048508336⟩,⟨35352220868,0⟩⟩,⟨⟨19923995687508,3966205122288⟩,⟨23875656732,233356287276⟩,⟨702362004,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25084 151 (5143-R)⟩
def p204:CachedProfile:=⟨⟨77147,212,20724⟩,⟨⟨⟨788680973322350,19374073410700286150⟩,⟨157763434636363800,4078742009200⟩,⟨5588786400,432342927117600⟩,⟨394940905600,0⟩⟩,⟨⟨779776707244200,199356417354600⟩,⟨546330232800,4078733221800⟩,⟨5588786400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨787961118902436,19357727992513954356⟩,⟨158377582582867080,4094619926064⟩,⟨5637007512,436073264120808⟩,⟨400227533352,0⟩⟩,⟨⟨779078741889000,199029493269624⟩,⟨548007110568,4094611104456⟩,⟨5637007512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 77359 213 (20724-R)⟩
def p205:CachedProfile:=⟨⟨9726,54,2096⟩,⟨⟨⟨1249683898464,3943066419107712⟩,⟨64989049277376,13290517584⟩,⟨36689112,358819515360⟩,⟨660404016,0⟩⟩,⟨⟨1240430307192,257916908160⟩,⟨1424081088,13290291108⟩,⟨36689112,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨1238814726240,3910634279716320⟩,⟨65655915811200,13426899200⟩,⟨37752000,369214560000⟩,⟨692120000,0⟩⟩,⟨⟨1229783780160,253751097600⟩,⟨1427025600,13426670400⟩,⟨37752000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9780 55 (2096-R)⟩
def p206:CachedProfile:=⟨⟨9515,86,3087⟩,⟨⟨⟨1855289029904,5557777633823312⟩,⟨146888914008000,30598744960⟩,⟨137033088,1315654677888⟩,⟨3928281856,0⟩⟩,⟨⟨1825802425056,549138181536⟩,⟨4918850496,30598213824⟩,⟨137033088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1848332268414,5538898990088802⟩,⟨148115684844180,30854302920⟩,⟨139784292,1342068987492⟩,⟨4053744468,0⟩⟩,⟨⟨1819130879196,545586771636⟩,⟨4943865132,30853767348⟩,⟨139784292,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9601 87 (3087-R)⟩
def p207:CachedProfile:=⟨⟨11438,69,2529⟩,⟨⟨⟨2091152810890,7751495410367830⟩,⟨138695278793940,24106720440⟩,⟨72271980,831633673860⟩,⟨1662255540,0⟩⟩,⟨⟨2074913107740,441756261540⟩,⟨2648925180,24106371300⟩,⟨72271980,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨2080471889422,7714148228324986⟩,⟨140037952737480,24340095920⟩,⟨74029200,851854004400⟩,⟨1727348000,0⟩⟩,⟨⟨2064461682468,437574801852⟩,⟨2661878520,24339743400⟩,⟨74029200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11507 70 (2529-R)⟩
def p208:CachedProfile:=⟨⟨67917,417,15337⟩,⟨⟨⟨447776168987126,9843871430187110666⟩,⟨179197760703021480,5244778055136⟩,⟨16002656892,1093525556057928⟩,⟨2224369307988,0⟩⟩,⟨⟨444166213672020,96448892415624⟩,⟨588567742812,5244765263244⟩,⟨16002656892,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨447334565469876,9834734852647340916⟩,⟨179463532658455584,5252556726912⟩,⟨16064823456,1097773646042304⟩,⟨2238365401536,0⟩⟩,⟨⟨443734482871848,96272896558608⟩,⟨588902607216,5252543916048⟩,⟨16064823456,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 68334 418 (15337-R)⟩
def p209:CachedProfile:=⟨⟨92918,587,18258⟩,⟨⟨⟨988298822357234,29966121308655452678⟩,⟨562260822016493118,12026361852244⟩,⟨37748912226,3529712037692130⟩,⟨7386203825554,0⟩⟩,⟨⟨982208686757568,187032154326660⟩,⟨1174139079084,12026340416178⟩,⟨37748912226,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨987379525533042,29939570611788302694⟩,⟨562725137480087736,12036293276112⟩,⟨37844446752,3538644993545760⟩,⟨7417511563392,0⟩⟩,⟨⟨981305380510560,186704503830180⟩,⟨1174078907568,12036271822344⟩,⟨37844446752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 93505 588 (18258-R)⟩
def p210:CachedProfile:=⟨⟨44767,250,10158⟩,⟨⟨⟨128770272493954,1864280815622822830⟩,⟨30881591394292500,1372003427000⟩,⟨3809625000,171497888625000⟩,⟨317468750000,0⟩⟩,⟨⟨127721101789272,27873208842444⟩,⟨154792683000,1371998347500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨128633213141214,1862414272306479690⟩,⟨30974597602070490,1376135508588⟩,⟨3836382894,172702448739198⟩,⟨320977368798,0⟩⟩,⟨⟨127587136042452,27818359229304⟩,⟨155106030312,1376130413790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45017 251 (10158-R)⟩
def p211:CachedProfile:=⟨⟨45018,250,10190⟩,⟨⟨⟨130594750047888,1901531110012711464⟩,⟨31325282356446000,1383998946000⟩,⟨3821625000,172997320500000⟩,⟨318468750000,0⟩⟩,⟨⟨129535633700412,28205483134320⟩,⟨155769435000,1383993850500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨130456233356088,1899633478598926464⟩,⟨31419722043427824,1388171449544⟩,⟨3848479086,174212951265048⟩,⟨321989416862,0⟩⟩,⟨⟨129400230144672,28150153868640⟩,⟨156085725480,1388166338682⟩,⟨3848479086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45268 251 (10190-R)⟩
def p212:CachedProfile:=⟨⟨44018,250,10222⟩,⟨⟨⟨125546168097296,1784665990338020072⟩,⟨30050655731646000,1357675738000⟩,⟨3833625000,169706911500000⟩,⟨319468750000,0⟩⟩,⟨⟨124477069043436,27755904789648⟩,⟨156749259000,1357670626500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨125412925711416,1782888216846331392⟩,⟨30141345322360944,1361773068712⟩,⟨3860575278,170899946406504⟩,⟨323001464926,0⟩⟩,⟨⟨124346959360176,27701627794848⟩,⟨157068504936,1361767941786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44268 251 (10222-R)⟩
def p213:CachedProfile:=⟨⟨44267,250,10158⟩,⟨⟨⟨126041504139954,1803201084638737830⟩,⟨30199409464792500,1356764927000⟩,⟨3809625000,169593076125000⟩,⟨317468750000,0⟩⟩,⟨⟨124992343594272,27563623476444⟩,⟨154792683000,1356759847500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨125907130847214,1801394665694484690⟩,⟨30290361135872490,1360851114588⟩,⟨3836382894,170784257292198⟩,⟨320977368798,0⟩⟩,⟨⟨124861063897452,27509383073304⟩,⟨155106030312,1360846019790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44517 251 (10158-R)⟩
def p214:CachedProfile:=⟨⟨16530,4,5096⟩,⟨⟨⟨9022849465560,46756074284807664⟩,⟨33442438194144,4045305408⟩,⟨489312,8090284608⟩,⟨652416,0⟩⟩,⟨⟨8890315824012,2576755647648⟩,⟨623383488,4045264632⟩,⟨489312,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨9002557297320,46660376264312424⟩,⟨41721029686080,5046710960⟩,⟨763050,12616268700⟩,⟨1271750,0⟩⟩,⟨⟨8870801636952,2566653704328⟩,⟨776174460,5046660090⟩,⟨763050,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16534 5 (5096-R)⟩
def p215:CachedProfile:=⟨⟨8671,38,2155⟩,⟨⟨⟨1031374760108,2870348726756588⟩,⟨37285919943888,8562786848⟩,⟨18679584,162680497056⟩,⟨236608064,0⟩⟩,⟨⟨1021324689000,242781489720⟩,⟨1059329040,8562622992⟩,⟨18679584,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨1022461794306,2847209680624926⟩,⟨37965376103382,8718829236⟩,⟨19520514,170004156426⟩,⟨253766682,0⟩⟩,⟨⟨1012647074088,238967052228⟩,⟨1070124588,8718662394⟩,⟨19520514,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8709 39 (2155-R)⟩
def p216:CachedProfile:=⟨⟨24860,163,5237⟩,⟨⟨⟨20398053618126,164900268632493162⟩,⟨3207675044372292,256380677496⟩,⟨835010532,20894468542236⟩,⟨45368905572,0⟩⟩,⟨⟨20254133203956,4118496434028⟩,⟨26827915068,256378969908⟩,⟨835010532,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20356375777196,164581144294532732⟩,⟨3221192505218016,257461099328⟩,⟨843673728,21111247695744⟩,⟨46120830464,0⟩⟩,⟨⟨20213277183096,4102784492328⟩,⟨26889527904,257459384544⟩,⟨843673728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20343875484350,164485413404415950⟩,⟨3219344047147800,257313359600⟩,⟨843189600,21099133360800⟩,⟨46094364800,0⟩⟩,⟨⟨20201022824400,4098076765200⟩,⟨26858673600,257311645800⟩,⟨843189600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25023 164 (5237-R)⟩
def p217:CachedProfile:=⟨⟨25168,144,5143⟩,⟨⟨⟨20455882924104,167551701104919720⟩,⟨2847571242094080,225000041472⟩,⟨639995904,16199576322048⟩,⟨30719803392,0⟩⟩,⟨⟨20319561404592,4017863668224⟩,⟨22857631488,224998560000⟩,⟨639995904,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20413478481314,167221896937089830⟩,⟨2861771796673800,226122101360⟩,⟨647654100,16393420579200⟩,⟨31303281500,0⟩⟩,⟨⟨20277949542372,4002255782784⟩,⟨22926955140,226120612500⟩,⟨647654100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25312 145 (5143-R)⟩
def p218:CachedProfile:=⟨⟨24534,163,5396⟩,⟨⟨⟨20537977500894,163454509320641322⟩,⟨3219492075469866,260721708492⟩,⟨860357358,21248245670526⟩,⟨46746083118,0⟩⟩,⟨⟨20380567465524,4315387618584⟩,⟨28481523336,260719949070⟩,⟨860357358,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20497018828434,163146934709637222⟩,⟨3233241520985448,261835178096⟩,⟨869332512,21469905048864⟩,⟨47523510656,0⟩⟩,⟨⟨20340481281504,4299409153524⟩,⟨28550151888,261833411160⟩,⟨869332512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24697 164 (5396-R)⟩
def p219:CachedProfile:=⟨⟨43268,250,10475⟩,⟨⟨⟨124789013727588,1738859317907416164⟩,⟨29759758923636000,1367704656000⟩,⟨3928500000,170960463000000⟩,⟨327375000000,0⟩⟩,⟨⟨123638616290952,28652973598800⟩,⟨164604150000,1367699418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨124658936664638,1737164994042389714⟩,⟨29850276454748184,1371864692384⟩,⟨3956210796,172166381420328⟩,⟨331002969932,0⟩⟩,⟨⟨123511828935012,28598294972520⟩,⟨164947195140,1371859438452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43518 251 (10475-R)⟩
def p220:CachedProfile:=⟨⟨41517,250,10158⟩,⟨⟨⟨111578054567954,1491105791830895330⟩,⟨26583602946292500,1272953177000⟩,⟨3809625000,159116607375000⟩,⟨317468750000,0⟩⟩,⟨⟨110528949896772,25860903963444⟩,⟨154792683000,1272948097500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨111457918355214,1489606586879387190⟩,⟨26663664843158490,1276786947588⟩,⟨3836382894,160234204333698⟩,⟨320977368798,0⟩⟩,⟨⟨110411907224952,25810014215304⟩,⟨155106030312,1276781852790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41767 251 (10158-R)⟩
def p221:CachedProfile:=⟨⟨25032,184,5111⟩,⟨⟨⟨20171458645992,164617013972677320⟩,⟨3588552397810944,284627980800⟩,⟨1038431232,26185081946112⟩,⟨63690448896,0⟩⟩,⟨⟨20037663532656,3952975951872⟩,⟨28844684928,284626099584⟩,⟨1038431232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20129394427842,164290987306918470⟩,⟨3600997275362760,285615062000⟩,⟨1047695700,26418694771200⟩,⟨64607901500,0⟩⟩,⟨⟨19996382058276,3937524091392⟩,⟨28888085220,285613174260⟩,⟨1047695700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨20125188848264,164258386363193792⟩,⟨3600291462926160,285559081000⟩,⟨1047490350,26413516665600⟩,⟨64595238250,0⟩⟩,⟨⟨19992254584632,3935980569600⟩,⟨28876761000,285557193630⟩,⟨1047490350,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25216 185 (5111-R)⟩
def p222:CachedProfile:=⟨⟨25032,184,5095⟩,⟨⟨⟨20104163244984,164095386333459672⟩,⟨3577320441886464,283737126400⟩,⟨1035181056,26103125508096⟩,⟨63491104768,0⟩⟩,⟨⟨19971619052112,3928267499520⟩,⟨28664388480,283735251072⟩,⟨1035181056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨20057920364520,163736813715215040⟩,⟨3588998464544400,284663385000⟩,⟨1044204750,26330666976000⟩,⟨64392626250,0⟩⟩,⟨⟨19926231638040,3911325373440⟩,⟨28695875400,284661503550⟩,⟨1044204750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25216 185 (5095-R)⟩
def p223:CachedProfile:=⟨⟨24664,184,5237⟩,⟨⟨⟨20123760772026,161480473786878462⟩,⟨3570465258046656,287387353728⟩,⟨1064026368,26438927192064⟩,⟨65260283904,0⟩⟩,⟨⟨19979842191156,4089693457728⟩,⟨30284272224,287385426144⟩,⟨1064026368,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20082606590596,161167878376662532⟩,⟨3583016331758640,288397601120⟩,⟨1073569800,26676062390400⟩,⟨66203471000,0⟩⟩,⟨⟨19939509826296,4074091398528⟩,⟨30332699160,288395666760⟩,⟨1073569800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24848 185 (5237-R)⟩
def p224:CachedProfile:=⟨⟨6351,44,1265⟩,⟨⟨⟨320843601690,664879804921350⟩,⟨13669278646320,4275170592⟩,⟨14705856,94043949120⟩,⟨215685888,0⟩⟩,⟨⟨318801524700,61449171300⟩,⟨422793360,4275059184⟩,⟨14705856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨317075030884,657442700131732⟩,⟨13825338067080,4323982320⟩,⟨15211800,97279461000⟩,⟨228177000,0⟩⟩,⟨⟨315099636552,60097089240⟩,⟨422888040,4323869640⟩,⟨15211800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨316806129810,656911621397250⟩,⟨13814294789250,4320528660⟩,⟨15199650,97201761750⟩,⟨227994750,0⟩⟩,⟨⟨314835442020,60001087500⟩,⟨422212500,4320416070⟩,⟨15199650,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6395 45 (1265-R)⟩
def p225:CachedProfile:=⟨⟨24610,179,5035⟩,⟨⟨⟨19206959703788,154074156476095148⟩,⟨3323648859176424,268157955344⟩,⟨968150856,23999491569384⟩,⟨57766334408,0⟩⟩,⟨⟨19079041259880,3771337974840⟩,⟨27232623240,268156152456⟩,⟨968150856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨19150029434070,153640479526745994⟩,⟨3332925268616880,268906404960⟩,⟨976276800,24200925595200⟩,⟨58576608000,0⟩⟩,⟨⟨19023173618652,3750396525108⟩,⟨27232698960,268904597040⟩,⟨976276800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24789 180 (5035-R)⟩
def p226:CachedProfile:=⟨⟨5145,30,1040⟩,⟨⟨⟨172946774430,289782042336750⟩,⟨5018543262900,1939632840⟩,⟨5621400,29090745000⟩,⟨56214000,0⟩⟩,⟨⟨171810054480,33615972000⟩,⟨194875200,1939570380⟩,⟨5621400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨170119329950,285274720998350⟩,⟨5106116607450,1973481700⟩,⟨5910150,30585026250⟩,⟨61071550,0⟩⟩,⟨⟨169033930800,32590080000⟩,⟨195225600,1973418150⟩,⟨5910150,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5175 31 (1040-R)⟩
def p227:CachedProfile:=⟨⟨252183,1329,62111⟩,⟨⟨⟨25149213321138144,2038850446456269593952⟩,⟨31830951983595182208,251120058736896⟩,⟨658228565952,166868840211623424⟩,⟨291595254716736,0⟩⟩,⟨⟨24909567626013504,5868050019439104⟩,⟨30762403656768,251119893643200⟩,⟨658228565952,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨25142117886868400,2038313741682280467056⟩,⟨31846697225890350720,251244275887360⟩,⟨659049686400,167077004098636800⟩,⟨292178694304000,0⟩⟩,⟨⟨24902657327409696,5865027174800640⟩,⟨30769691937600,251244110712000⟩,⟨659049686400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 253512 1330 (62111-R)⟩
def p228:CachedProfile:=⟨⟨44768,250,10222⟩,⟨⟨⟨129653697936296,1876353945392708072⟩,⟨31077522856896000,1380677488000⟩,⟨3833625000,172582130250000⟩,⟨319468750000,0⟩⟩,⟨⟨128584583547936,28226152566648⟩,⟨156749259000,1380672376500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨129516437620416,1874486483067289392⟩,⟨31171311430741944,1384844235712⟩,⟨3860575278,173795377865004⟩,⟨323001464926,0⟩⟩,⟨⟨128450455949676,28170955996848⟩,⟨157068504936,1384839108786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45018 251 (10222-R)⟩
def p229:CachedProfile:=⟨⟨43268,250,10190⟩,⟨⟨⟨121094017050888,1690621767440839464⟩,⟨28950134775696000,1330496196000⟩,⟨3821625000,166309476750000⟩,⟨318468750000,0⟩⟩,⟨⟨120034936371912,27115097089320⟩,⟨155769435000,1330491100500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨120964823029088,1688931094638984464⟩,⟨29037413827384824,1334507398544⟩,⟨3848479086,167478112864548⟩,⟨321989416862,0⟩⟩,⟨⟨119908855451172,27061906778640⟩,⟨156085725480,1334502287682⟩,⟨3848479086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43518 251 (10190-R)⟩
def p230:CachedProfile:=⟨⟨44018,250,10475⟩,⟨⟨⟨128927484195588,1829686077970324164⟩,⟨30794360826636000,1391275656000⟩,⟨3928500000,173906838000000⟩,⟨327375000000,0⟩⟩,⟨⟨127777071044952,29146786048800⟩,⟨164604150000,1391270418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨128793456702638,1827905053316027714⟩,⟨30888025222490184,1395507386384⟩,⟨3956210796,175133539517328⟩,⟨331002969932,0⟩⟩,⟨⟨127646333274012,29091165077520⟩,⟨164947195140,1395502132452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44268 251 (10475-R)⟩
def p231:CachedProfile:=⟨⟨44268,250,10190⟩,⟨⟨⟨126477147834888,1809103640171623464⟩,⟨30295897089696000,1361069196000⟩,⟨3821625000,170131101750000⟩,⟨318468750000,0⟩⟩,⟨⟨125418046773912,27738174829320⟩,⟨155769435000,1361064100500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨126342671573088,1807296704865808464⟩,⟨30387233368480824,1365172570544⟩,⟨3848479086,171326591950548⟩,⟨321989416862,0⟩⟩,⟨⟨125286683633172,27683762258640⟩,⟨156085725480,1365167459682⟩,⟨3848479086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44518 251 (10190-R)⟩
def p232:CachedProfile:=⟨⟨24917,161,5237⟩,⟨⟨⟨20484657505386,165984993644666382⟩,⟨3182259923156664,253791492192⟩,⟨814645188,20429672024664⟩,⟨43719291756,0⟩⟩,⟨⟨20340736515036,4127548798008⟩,⟨26498738196,253789805556⟩,⟨814645188,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20442814326756,165663798395889252⟩,⟨3195912342165408,254880307584⟩,⟨823221792,20644756099776⟩,⟨44453976768,0⟩⟩,⟨⟨20299715157576,4111802321808⟩,⟨26561606832,254878613712⟩,⟨823221792,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20430264432600,165567446232553200⟩,⟨3194078391068400,254734048800⟩,⟨822749400,20632909453200⟩,⟨44428467600,0⟩⟩,⟨⟨20287411197900,4107084247200⟩,⟨26531128800,254732355900⟩,⟨822749400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25078 162 (5237-R)⟩
def p233:CachedProfile:=⟨⟨24917,161,5143⟩,⟨⟨⟨20091947845896,162967043023585896⟩,⟨3125150849832480,249237005696⟩,⟨800025744,20063045608032⟩,⟨42934714928,0⟩⟩,⟨⟨19955628733776,3980720017056⟩,⟨25556101872,249235349328⟩,⟨800025744,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20050250897426,162646151632269686⟩,⟨3138448557754800,250297532352⟩,⟨808420176,20273561173728⟩,⟨43654689504,0⟩⟩,⟨⟨19914724361196,3965256420696⟩,⟨25614942984,250295868936⟩,⟨808420176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20037744817328,162549890398179704⟩,⟨3136614607754208,250151273568⟩,⟨807947784,20261714527152⟩,⟨43629180336,0⟩⟩,⟨⟨19902455452992,3960623210040⟩,⟨25585013160,250149611124⟩,⟨807947784,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25078 162 (5143-R)⟩
def p234:CachedProfile:=⟨⟨24296,172,5063⟩,⟨⟨⟨18840479621976,149025538251415416⟩,⟨3128799139171200,255748852992⟩,⟨898880256,21993802103808⟩,⟨51535801344,0⟩⟩,⟨⟨18710421391056,3764015009856⟩,⟨26459481024,255747110976⟩,⟨898880256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18800718469106,148727360222896406⟩,⟨3140775292022760,256727795408⟩,⟨907566996,22206349258128⟩,⟨52336363436,0⟩⟩,⟨⟨18671428329876,3749162444496⟩,⟨26508300756,256726046724⟩,⟨907566996,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24468 173 (5063-R)⟩
def p235:CachedProfile:=⟨⟨24448,168,5079⟩,⟨⟨⟨19125554977160,152219784753618920⟩,⟨3102890796552960,252106176000⟩,⟨860267520,21176345272320⟩,⟨48174981120,0⟩⟩,⟨⟨18994259974320,3810751758720⟩,⟨26007730560,252104469120⟩,⟨860267520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19085333627490,151916208643499430⟩,⟨3115215871602120,253107582000⟩,⟨868825620,21387011461920⟩,⟨48943843260,0⟩⟩,⟨⟨18954811582980,3795762091680⟩,⟨26059627620,253105868340⟩,⟨868825620,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24616 169 (5079-R)⟩
def p236:CachedProfile:=⟨⟨25168,144,5111⟩,⟨⟨⟨20320242874344,166496439111972552⟩,⟨2829856674866688,223600352256⟩,⟨636014592,16098801352704⟩,⟨30528700416,0⟩⟩,⟨⟨20186446779504,3968025352704⟩,⟨22574101248,223598880000⟩,⟨636014592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20277887607234,166166735890687302⟩,⟨2843934212732040,224712692080⟩,⟨643617300,16291241097600⟩,⟨31108169500,0⟩⟩,⟨⟨20144874258084,3952514665344⟩,⟨22642012740,224711212500⟩,⟨643617300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25312 145 (5111-R)⟩
def p237:CachedProfile:=⟨⟨24672,148,5237⟩,⟨⟨⟨20080052553402,160937754130794654⟩,⟨2865427325722656,230898917952⟩,⟨688398912,17086060995840⟩,⟨33961012992,0⟩⟩,⟨⟨19936134265860,4085084981520⟩,⟨24359088528,230897367504⟩,⟨688398912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20038981816452,160626194858144964⟩,⟨2879280804396528,232015252256⟩,⟨696400968,17284672025760⟩,⟨34587914744,0⟩⟩,⟨⟨19895885344920,4069500503520⟩,⟨24430119864,232013694312⟩,⟨696400968,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24820 149 (5237-R)⟩
def p238:CachedProfile:=⟨⟨24794,145,5143⟩,⟨⟨⟨19877364394136,160283858387486936⟩,⟨2783463081246960,223223982880⟩,⟨648915600,16183306148400⟩,⟨31364254000,0⟩⟩,⟨⟨19741046712048,3958656053328⟩,⟨23016365040,223222491120⟩,⟨648915600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19836084598566,159968183226121746⟩,⟨2797210883710008,224326515664⟩,⟨656618064,16375397898096⟩,⟨31955412448,0⟩⟩,⟨⟨19700559489588,3943278167148⟩,⟨23085072072,224325016536⟩,⟨656618064,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19815450477806,159810357533204726⟩,⟨2794486636516908,224108044184⟩,⟨655978584,16359449906376⟩,⟨31924291088,0⟩⟩,⟨⟨19680320500008,3935600446608⟩,⟨23040124512,224106546516⟩,⟨655978584,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24939 146 (5143-R)⟩
def p239:CachedProfile:=⟨⟨24852,146,5396⟩,⟨⟨⟨21022366767360,169472457791097552⟩,⟨2954435763826512,236375992608⟩,⟨690254712,17254987290576⟩,⟨33592395984,0⟩⟩,⟨⟨20864953482996,4367982333456⟩,⟨25511057712,236374416684⟩,⟨690254712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20980510579120,169153732441749112⟩,⟨2969159816975184,237554029776⟩,⟨698446098,17459755557804⟩,⟨34223858802,0⟩⟩,⟨⟨20823969789216,4351809127416⟩,⟨25590684924,237552445998⟩,⟨698446098,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24998 147 (5396-R)⟩
def p240:CachedProfile:=⟨⟨24414,146,5079⟩,⟨⟨⟨19041615170440,151187838964428520⟩,⟨2684304979400640,218593863040⟩,⟨649711680,15956918860800⟩,⟨31619301760,0⟩⟩,⟨⟨18910320736560,3802082515200⟩,⟨22601956320,218592379680⟩,⟨649711680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19001559056610,150886294277728230⟩,⟨2697370283364120,219657831120⟩,⟨657345780,16144412356800⟩,⟨32209943220,0⟩⟩,⟨⟨18871037579940,3787126948800⟩,⟨22667250060,219656340540⟩,⟨657345780,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨18977532690264,150705382303437048⟩,⟨2694178075585248,219397881024⟩,⟨656567856,16125306543360⟩,⟨32171824944,0⟩⟩,⟨⟨18847473527568,3778167755520⟩,⟨22613626224,219396392208⟩,⟨656567856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24560 147 (5079-R)⟩
def p241:CachedProfile:=⟨⟨43518,250,10475⟩,⟨⟨⟨126160646883588,1768790364669052164⟩,⟨30102661974636000,1375561656000⟩,⟨3928500000,171942588000000⟩,⟨327375000000,0⟩⟩,⟨⟨125010244208952,28817577748800⟩,⟨164604150000,1375556418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨126029260510638,1767067469425935714⟩,⟨30194222486162184,1379745590384⟩,⟨3956210796,173155434119328⟩,⟨331002969932,0⟩⟩,⟨⟨124882147548012,28762585007520⟩,⟨164947195140,1379740336452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43768 251 (10475-R)⟩
def p242:CachedProfile:=⟨⟨24799,153,5237⟩,⟨⟨⟨20286537027642,163507021092411966⟩,⟨2993823581208552,239968996848⟩,⟨735698052,18357137793504⟩,⟨37520600652,0⟩⟩,⟨⟨20142617357268,4106810655072⟩,⟨25182030708,239967394020⟩,⟨735698052,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20245072085892,163190556683568516⟩,⟨3007638016913376,241076296384⟩,⟨743923488,18562378872576⟩,⟨38188072384,0⟩⟩,⟨⟨20101974234168,4091143294272⟩,⟨25249922544,241074686160⟩,⟨743923488,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24952 154 (5237-R)⟩
def p243:CachedProfile:=⟨⟨43018,250,10190⟩,⟨⟨⟨119767342479888,1661837623673143464⟩,⟨28618471228446000,1322852946000⟩,⟨3821625000,165354070500000⟩,⟨318468750000,0⟩⟩,⟨⟨118708266896412,26959327654320⟩,⟨155769435000,1322847850500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨119626662727180,1660008959914510060⟩,⟨28701930901456560,1326710780320⟩,⟨3848101080,166499637529440⟩,⟨321957790360,0⟩⟩,⟨⟨118571011213320,26901157289760⟩,⟨156055063320,1326705669960⟩,⟨3848101080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43268 251 (10190-R)⟩
def p244:CachedProfile:=⟨⟨25314,190,5111⟩,⟨⟨⟨20619507369960,170298273800748744⟩,⟨3790697430507840,297266071680⟩,⟨1107259200,28239538636800⟩,⟨70126416000,0⟩⟩,⟨⟨20485709312112,3998124154368⟩,⟨29785272480,297264129120⟩,⟨1107259200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20576566687170,169961133383101254⟩,⟨3803194032510456,298246062992⟩,⟨1116756372,28481754511488⟩,⟨71100155684,0⟩⟩,⟨⟨20443551378852,3982495813248⟩,⟨29824996092,298244114028⟩,⟨1116756372,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25504 191 (5111-R)⟩
def p245:CachedProfile:=⟨⟨3384,27,965⟩,⟨⟨⟨71962043454,77580969439722⟩,⟨1821074086692,1067797080⟩,⟨4225284,14412443724⟩,⟨38027556,0⟩⟩,⟨⟨71055890052,19078200540⟩,⟨151014780,1067744916⟩,⟨4225284,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨71125299644,76751030777132⟩,⟨1868968153248,1095881920⟩,⟨4497024,15339348864⟩,⟨41972224,0⟩⟩,⟨⟨70246881912,18685048680⟩,⟨153380640,1095828384⟩,⟨4497024,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨71041783410,76668097965570⟩,⟨1867012844760,1094735600⟩,⟨4492320,15323303520⟩,⟨41928320,0⟩⟩,⟨⟨70166107620,18645958620⟩,⟨153059760,1094682120⟩,⟨4492320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 12=>⟨⟨⟨70958295810,76585176162990⟩,⟨1865057536944,1093589280⟩,⟨4487616,15307258176⟩,⟨41884416,0⟩⟩,⟨⟨70085356236,18606909492⟩,⟨152739216,1093535856⟩,⟨4487616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3411 28 (965-R)⟩
def p246:CachedProfile:=⟨⟨2045,13,841⟩,⟨⟨⟨24389990870,15196711441802⟩,⟨278272233096,270409984⟩,⟨853788,1757095704⟩,⟨3699748,0⟩⟩,⟨⟨23790994596,8743890456⟩,⟨55233516,270388092⟩,⟨853788,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨24030751680,14998577810112⟩,⟨296117273088,287752192⟩,⟨978432,2013613056⟩,⟨4566016,0⟩⟩,⟨⟨23452780416,8537308416⟩,⟨58076928,287728896⟩,⟨978432,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2058 14 (841-R)⟩
def p247:CachedProfile:=⟨⟨25648,193,5111⟩,⟨⟨⟨21150246895992,177111005617687320⟩,⟨3952980616439088,305949621600⟩,⟨1142501328,29523376816848⟩,⟨73500918768,0⟩⟩,⟨⟨21016445392656,4050953821872⟩,⟨30255566256,305947648368⟩,⟨1142501328,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨21110665191714,176795583399915102⟩,⟨3966466742011620,306993418200⟩,⟨1152339048,29777593339368⟩,⟨74517925104,0⟩⟩,⟨⟨20977568306856,4036701063276⟩,⟨30305328984,306991438236⟩,⟨1152339048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨21106267990342,176760538053540970⟩,⟨3965689448781624,306933258800⟩,⟨1152113232,29771758028112⟩,⟨74503322336,0⟩⟩,⟨⟨20973249243276,4035118973892⟩,⟨30293451528,306931279224⟩,⟨1152113232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25841 194 (5111-R)⟩
def p248:CachedProfile:=⟨⟨127080,934,21884⟩,⟨⟨⟨2204281718553360,92052566163484841040⟩,⟨2009836705707952560,31400343783840⟩,⟨114549066360,14663884181009040⟩,⟨35662942660080,0⟩⟩,⟨⟨2193795181936020,367859499352560⟩,⟨2683931229360,31400302902660⟩,⟨114549066360,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 18=>⟨⟨⟨2202382636287600,91976289018330492024⟩,⟨2010333738047841360,31408109153520⟩,⟨114700068450,14683214562558300⟩,⟨35748188000250,0⟩⟩,⟨⟨2191921944911472,367254619377048⟩,⟨2682386841420,31408068262230⟩,⟨114700068450,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 19=>⟨⟨⟨2202277137950838,91972051453719843978⟩,⟨2010241803209828760,31406672828960⟩,⟨114694823100,14682543084323400⟩,⟨35746553199500,0⟩⟩,⟨⟨2191817881174740,367221029527560⟩,⟨2682141504900,31406631939540⟩,⟨114694823100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 128014 935 (21884-R)⟩
def p249:CachedProfile:=⟨⟨40675,226,8555⟩,⟨⟨⟨89013503190444,1176246517408596972⟩,⟨19408982119251696,949077037920⟩,⟨2622037536,107243957259936⟩,⟨197526827712,0⟩⟩,⟨⟨88386606550632,17962879911480⟩,⟨99254562480,949073170608⟩,⟨2622037536,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨88846497775854,1174156231105656162⟩,⟨19460684693069802,951605251740⟩,⟨2640655134,108005435635734⟩,⟨199809571806,0⟩⟩,⟨⟨88222890309372,17899947996840⟩,⟨99344470680,951601374126⟩,⟨2640655134,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨88835366132380,1174016885702812060⟩,⟨19458406167910920,951493835600⟩,⟨2640345960,107992790109960⟩,⟨199786177640,0⟩⟩,⟨⟨88211977533960,17895756462360⟩,⟨99321207720,951489958440⟩,⟨2640345960,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40901 227 (8555-R)⟩
def p250:CachedProfile:=⟨⟨12268,84,1940⟩,⟨⟨⟨1813577464920,7330623719908416⟩,⟨149259396758976,24168338208⟩,⟨82174176,1015015421952⟩,⟨2300876928,0⟩⟩,⟨⟨1806224366856,279071700480⟩,⟨1897832160,24168012120⟩,⟨82174176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨1799003826090,7273644883277166⟩,⟨149869060124040,24267060720⟩,⟨83492100,1031294419200⟩,⟨2365609500,0⟩⟩,⟨⟨1791819212436,274773945600⟩,⟨1890850500,24266733300⟩,⟨83492100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨1798032713400,7269846654100800⟩,⟨149791244526000,24254461000⟩,⟨83448750,1030758960000⟩,⟨2364381250,0⟩⟩,⟨⟨1790859239400,274488614400⟩,⟨1888887000,24254133750⟩,⟨83448750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12352 85 (1940-R)⟩
def p251:CachedProfile:=⟨⟨178590,1070,37481⟩,⟨⟨⟨7522335019474854,436693930055417404602⟩,⟨7767148056324155280,86465087826720⟩,⟨257478850800,46258650334728000⟩,⟨91834123452000,0⟩⟩,⟨⟨7469665887261612,1514385949162320⟩,⟨9019219445640,86465007615240⟩,⟨257478850800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨7519114036417464,436516799777403253272⟩,⟨7771295809744065144,86511261336696⟩,⟨257857110882,46326608541060120⟩,⟨92054988584874,0⟩⟩,⟨⟨7466508102563172,1513174084971120⟩,⟨9020424384972,86511181082382⟩,⟨257857110882,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 179660 1071 (37481-R)⟩
def p252:CachedProfile:=⟨⟨45018,250,10475⟩,⟨⟨⟨134555442819588,1955666982684868164⟩,⟨32201329530636000,1422703656000⟩,⟨3928500000,177835338000000⟩,⟨327375000000,0⟩⟩,⟨⟨133405008716952,29805202648800⟩,⟨164604150000,1422698418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨134416043086638,1953765700088211714⟩,⟨32299273389146184,1427030978384⟩,⟨3956210796,179089750313328⟩,⟨331002969932,0⟩⟩,⟨⟨133268898726012,29748325217520⟩,⟨164947195140,1427025724452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45268 251 (10475-R)⟩
def p253:CachedProfile:=⟨⟨44018,250,10190⟩,⟨⟨⟨125119900263888,1778977555714927464⟩,⟨29956590292446000,1353425946000⟩,⟨3821625000,169175695500000⟩,⟨318468750000,0⟩⟩,⟨⟨124060804298412,27582405394320⟩,⟨155769435000,1353420850500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨124986755812088,1777200182175102464⟩,⟨30046903623331824,1357506277544⟩,⟨3848479086,170364472179048⟩,⟨321989416862,0⟩⟩,⟨⟨123930772962672,27528298388640⟩,⟨156085725480,1357501166682⟩,⟨3848479086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44268 251 (10190-R)⟩
def p254:CachedProfile:=⟨⟨68420,244,18731⟩,⟨⟨⟨562771244613060,12251733888438937284⟩,⟨129296531782401984,3766071297408⟩,⟨6691370112,459456237370368⟩,⟨544231435776,0⟩⟩,⟨⟨556196543222712,144552451998528⟩,⟨513672350688,3766062156192⟩,⟨6691370112,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨562335115613936,12242975032420302536⟩,⟨129736335394880760,3778881652280⟩,⟨6741647850,462908507972400⟩,⟨550567907750,0⟩⟩,⟨⟨555774090165348,144351877588128⟩,⟨515061895740,3778872479970⟩,⟨6741647850,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 68664 245 (18731-R)⟩
def p255:CachedProfile:=⟨⟨24799,165,5237⟩,⟨⟨⟨20305362651066,163741943726727966⟩,⟨3231739418747400,258914549520⟩,⟨855627300,21359879917200⟩,⟨47059501500,0⟩⟩,⟨⟨20161442854980,4108785716304⟩,⟨27157091940,258912820980⟩,⟨855627300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20263861768836,163425030813536196⟩,⟨3245118424884000,259986432448⟩,⟨864376608,21578297642112⟩,⟨47828838976,0⟩⟩,⟨⟨20120763791640,4093110820704⟩,⟨27217448976,259984696752⟩,⟨864376608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20251414563600,163329963350822400⟩,⟨3243256236950400,259837243600⟩,⟨863880600,21565915298400⟩,⟨47801393200,0⟩⟩,⟨⟨20108562520200,4088414193600⟩,⟨27186218400,259835508900⟩,⟨863880600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24964 166 (5237-R)⟩
def p256:CachedProfile:=⟨⟨66144,16,20577⟩,⟨⟨⟨584014107596462,12098069806729058594⟩,⟨8647079906285952,261399206144⟩,⟨31607808,2091172577280⟩,⟨168574976,0⟩⟩,⟨⟨575298393462540,168086164541760⟩,⟨40649616576,261398547648⟩,⟨31607808,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨583687989608712,12091929379568396904⟩,⟨9183057627981024,277601688768⟩,⟨35664912,2359590577920⟩,⟨202101168,0⟩⟩,⟨⟨574984973425200,167922835349760⟩,⟨43148249712,277600989456⟩,⟨35664912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 66160 17 (20577-R)⟩
def p257:CachedProfile:=⟨⟨24758,158,5396⟩,⟨⟨⟨20889825384792,167818554183880320⟩,⟨3176325121521888,254965074000⟩,⟨808384248,20141701923168⟩,⟨42574903728,0⟩⟩,⟨⟨20732412985536,4353654205152⟩,⟨27607856976,254963368548⟩,⟨808384248,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20848214779992,167502893374490520⟩,⟨3190505740021944,256103367000⟩,⟨817132482,20359672921512⟩,⟨43308021546,0⟩⟩,⟨⟨20691674873556,4337534051472⟩,⟨27679720428,256101653934⟩,⟨817132482,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨20831575064384,167376638822649032⟩,⟨3188136658107240,255913203000⟩,⟨816525738,20344555288008⟩,⟨43275864114,0⟩⟩,⟨⟨20675383249836,4331094361776⟩,⟨27638625924,255911491206⟩,⟨816525738,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24916 159 (5396-R)⟩
def p258:CachedProfile:=⟨⟨24952,153,5237⟩,⟨⟨⟨20527241722542,166519239332014674⟩,⟨3030650418597516,241440392952⟩,⟨735698052,18469699595460⟩,⟨37520600652,0⟩⟩,⟨⟨20383320449340,4131992685780⟩,⟨25182030708,241438790124⟩,⟨735698052,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20485317245292,166197024124169484⟩,⟨3044634786003888,242554482016⟩,⟨743923488,18676199166240⟩,⟨38188072384,0⟩⟩,⟨⟨20342217793800,4116229256280⟩,⟨25249922544,242552871792⟩,⟨743923488,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25105 154 (5237-R)⟩
def p259:CachedProfile:=⟨⟨25144,146,5143⟩,⟨⟨⟨20421522855944,167117033504052968⟩,⟨2882104404907584,227926771712⟩,⟨657897024,16638215736960⟩,⟨32017655168,0⟩⟩,⟨⟨20285201562768,4014371530080⟩,⟨23175098592,227925269664⟩,⟨657897024,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20379185209554,166788074349000918⟩,⟨2896203532988808,229041786624⟩,⟨665643636,16834127554440⟩,⟨32616538164,0⟩⟩,⟨⟨20243656496508,3998777210280⟩,⟨23243189004,229040277228⟩,⟨665643636,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25290 147 (5143-R)⟩
def p260:CachedProfile:=⟨⟨25267,141,5111⟩,⟨⟨⟨20469592449000,168390174296914632⟩,⟨2791959063931872,219772363968⟩,⟨609790032,15493545133056⟩,⟨28660131504,0⟩⟩,⟨⟨20335795372656,3983074753536⟩,⟨22103807472,219770922384⟩,⟨609790032,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20426945027010,168056766527055942⟩,⟨2806259791742064,220898069536⟩,⟨617260368,15683351430144⟩,⟨29216990752,0⟩⟩,⟨⟨20293930698276,3967505239296⟩,⟨22173557304,220896620568⟩,⟨617260368,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25408 142 (5111-R)⟩
def p261:CachedProfile:=⟨⟨24672,148,5111⟩,⟨⟨⟨19563699591144,157014475653588552⟩,⟨2796498376693632,225344648448⟩,⟨671839488,16675056092160⟩,⟨33144081408,0⟩⟩,⟨⟨19429908526512,3890897173440⟩,⟨23201159616,225343135296⟩,⟨671839488,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19522824260034,156703321175345382⟩,⟨2809886123731176,226423453904⟩,⟨679617012,16868094237840⟩,⟨33754311596,0⟩⟩,⟨⟨19389815931252,3875687973840⟩,⟨23266619988,226421933508⟩,⟨679617012,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19502392335504,156547755676457472⟩,⟨2807132367733056,226201557144⟩,⟨678950982,16851563373240⟩,⟨33721232106,0⟩⟩,⟨⟨19369774226472,3868094543040⟩,⟨23221034928,226200038238⟩,⟨678950982,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24820 149 (5111-R)⟩
def p262:CachedProfile:=⟨⟨24384,160,5079⟩,⟨⟨⟨19017667481480,150893860152844520⟩,⟨2937872560819200,239398860800⟩,⟨780288000,19151388672000⟩,⟨41615360000,0⟩⟩,⟨⟨18886373210160,3799605588480⟩,⟨24769267200,239397235200⟩,⟨780288000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨18957659727440,150442422778549760⟩,⟨2947505079358560,240183799240⟩,⟨787739190,19334270679360⟩,⟨42275336530,0⟩⟩,⟨⟨18827523750480,3777197898240⟩,⟨24777088560,240182168310⟩,⟨787739190,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24544 161 (5079-R)⟩
def p263:CachedProfile:=⟨⟨2984,24,631⟩,⟨⟨⟨35584453480,34574930928712⟩,⟨823561060608,547625472⟩,⟨2184192,6570049536⟩,⟨17473536,0⟩⟩,⟨⟨35329013616,7197398016⟩,⟨57426048,547595136⟩,⟨2184192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨34982458690,34020322158022⟩,⟨844300249800,561417200⟩,⟨2332500,7016160000⟩,⟨19437500,0⟩⟩,⟨⟨34738848036,6971256576⟩,⟨57939300,561386100⟩,⟨2332500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨34682162320,33743195095552⟩,⟨837512344800,556904200⟩,⟨2313750,6959760000⟩,⟨19281250,0⟩⟩,⟨⟨34444326096,6859539456⟩,⟨57010800,556873350⟩,⟨2313750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (631-R)⟩
def p264:CachedProfile:=⟨⟨2984,24,627⟩,⟨⟨⟨35343429916,34353030018172⟩,⟨818347925376,544159488⟩,⟨2170368,6528466944⟩,⟨17362944,0⟩⟩,⟨⟨35092766856,7106508288⟩,⟨56700864,544129344⟩,⟨2170368,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨34742184486,33798611190042⟩,⟨838869924600,557806800⟩,⟨2317500,6971040000⟩,⟨19312500,0⟩⟩,⟨⟨34503200796,6881810688⟩,⟨57195900,557775900⟩,⟨2317500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨34442258296,33521576863552⟩,⟨832082031600,553293800⟩,⟨2298750,6914640000⟩,⟨19156250,0⟩⟩,⟨⟨34208975016,6770815488⟩,⟨56273400,553263150⟩,⟨2298750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (627-R)⟩
def p265:CachedProfile:=⟨⟨24896,152,5111⟩,⟨⟨⟨19912446610920,161362290282503112⟩,⟨2925087543615744,233560982016⟩,⟨708645888,17750162202624⟩,⟨35904724992,0⟩⟩,⟨⟨19778653215216,3926639500416⟩,⟨23828217984,233559427968⟩,⟨708645888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19870889067330,161042630549980422⟩,⟨2938571799951816,234637673904⟩,⟨716596308,17949304322784⟩,⟨36546411708,0⟩⟩,⟨⟨19737878412036,3911290586976⟩,⟨23891227236,234636112692⟩,⟨716596308,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25048 153 (5111-R)⟩
def p266:CachedProfile:=⟨⟨24259,175,5015⟩,⟨⟨⟨18599723075208,146982792500691048⟩,⟨3144439636984800,257385004800⟩,⟨921690000,22520573460000⟩,⟨53765250000,0⟩⟩,⟨⟨18473324424720,3687858804960⟩,⟨26413002000,257383249200⟩,⟨921690000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18560134181458,146685980392694038⟩,⟨3156103116878976,258339716096⟩,⟨930395136,22733274753024⟩,⟨54583181312,0⟩⟩,⟨⟨18434489123100,3673167618120⟩,⟨26458111680,258337953984⟩,⟨930395136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨18544302830230,146567263990295434⟩,⟨3153581218356096,258133292032⟩,⟨929651712,22715109931008⟩,⟨54539567104,0⟩⟩,⟨⟨18418958367492,3667299353208⟩,⟨26415842112,258131531328⟩,⟨929651712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24434 176 (5015-R)⟩
def p267:CachedProfile:=⟨⟨42518,250,10475⟩,⟨⟨⟨120721256259588,1651109846178508164⟩,⟨28742835270636000,1344133656000⟩,⟨3928500000,168014088000000⟩,⟨327375000000,0⟩⟩,⟨⟨119570874536952,28159161148800⟩,⟨164604150000,1344128418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨120595062126638,1649499285637751714⟩,⟨28830259707506184,1348221998384⟩,⟨3956210796,169199223323328⟩,⟨331002969932,0⟩⟩,⟨⟨119447970096012,28105424867520⟩,⟨164947195140,1348216744452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42768 251 (10475-R)⟩
def p268:CachedProfile:=⟨⟨42767,250,10158⟩,⟨⟨⟨118038061077954,1628041405340482830⟩,⟨28198579176292500,1311049427000⟩,⟨3809625000,163878638625000⟩,⟨317468750000,0⟩⟩,⟨⟨116988931009272,26634867378444⟩,⟨154792683000,1311044347500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨117911565965214,1626407406452499690⟩,⟨28283504919278490,1314997932588⟩,⟨3836382894,165029682951198⟩,⟨320977368798,0⟩⟩,⟨⟨116865529462452,26582454605304⟩,⟨155106030312,1314992837790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43017 251 (10158-R)⟩
def p269:CachedProfile:=⟨⟨25314,190,5143⟩,⟨⟨⟨20757020749896,171377334825151656⟩,⟨3814426741216320,299126892160⟩,⟨1114190400,28416311961600⟩,⟨70565392000,0⟩⟩,⟨⟨20620697255088,4048340510208⟩,⟨30159374880,299124937440⟩,⟨1114190400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20714030891426,171040093459484966⟩,⟨3827048232861048,300116677264⟩,⟨1123760724,28660393504896⟩,⟨71546099428,0⟩⟩,⟨⟨20578499981028,4032614233728⟩,⟨30200334012,300114716076⟩,⟨1123760724,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25504 191 (5143-R)⟩
def p270:CachedProfile:=⟨⟨8268,2,2604⟩,⟨⟨⟨1157487069040,2993494673901520⟩,⟨2138124856080,517082080⟩,⟨62520,517040400⟩,⟨41680,0⟩⟩,⟨⟨1139779956660,336593300400⟩,⟨81401040,517071660⟩,⟨62520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1152369248160,2981474894398680⟩,⟨3194874690480,772645680⟩,⟨140130,1158875100⟩,⟨140130,0⟩⟩,⟨⟨1134864997440,334013556600⟩,⟨121165740,772630110⟩,⟨140130,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8270 3 (2604-R)⟩
def p271:CachedProfile:=⟨⟨32816,8,10191⟩,⟨⟨⟨71181490955120,731709708889415984⟩,⟨527098616099328,32116704256⟩,⟨3913728,128464207872⟩,⟨10436608,0⟩⟩,⟨⟨70122316616352,20455917850368⟩,⟨4985600256,32116541184⟩,⟨3913728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨71101278813930,730960050363750894⟩,⟨592404117021864,36095841648⟩,⟨4948452,162427988448⟩,⟨14845356,0⟩⟩,⟨⟨70045217973492,20415794449248⟩,⟨5597798868,36095658372⟩,⟨4948452,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 32824 9 (10191-R)⟩
def p272:CachedProfile:=⟨⟨42518,250,10190⟩,⟨⟨⟨117136923087888,1605259549748251464⟩,⟨27960876571446000,1307566446000⟩,⟨3821625000,163443258000000⟩,⟨318468750000,0⟩⟩,⟨⟨116077857695412,26647788784320⟩,⟨155769435000,1307561350500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨117011611996088,1603652640219366464⟩,⟨28045173190687824,1311508519544⟩,⟨3848479086,164591753550048⟩,⟨321989416862,0⟩⟩,⟨⟨115955659689672,26595515168640⟩,⟨156085725480,1311503408682⟩,⟨3848479086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨116999082567180,1603491956116230060⟩,⟨28042418502016560,1311379700320⟩,⟨3848101080,164575586989440⟩,⟨321957790360,0⟩⟩,⟨⟨115943441233320,26590290629760⟩,⟨156055063320,1311374589960⟩,⟨3848101080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42768 251 (10190-R)⟩
def p273:CachedProfile:=⟨⟨185796,1254,45845⟩,⟨⟨⟨10106137427914890,604495912812281628750⟩,⟨12068875303158983760,129044498153472⟩,⟨432561411216,80910611967952800⟩,⟨180810669888288,0⟩⟩,⟨⟨10009762803436140,2358861217101000⟩,⟨15814017461880,129044383171704⟩,⟨432561411216,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨10103240069169174,604334220230947130058⟩,⟨12075338100267463320,129113600655360⟩,⟨433138175100,81018495652455000⟩,⟨181196136583500,0⟩⟩,⟨⟨10006941093981348,2357626521000600⟩,⟨15818344206660,129113485612020⟩,⟨433138175100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 187050 1255 (45845-R)⟩
def p274:CachedProfile:=⟨⟨248755,1149,62405⟩,⟨⟨⟨24599577723087978,1963119895406216323758⟩,⟨26868592017327077064,215031452058864⟩,⟨494330781636,123535239653962944⟩,⟨189328689366588,0⟩⟩,⟨⟨24356513602605780,5839426443856320⟩,⟨26848313688420,215031308649876⟩,⟨494330781636,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨24593947182323376,1962701474647957810176⟩,⟨26886374376967800000,215173765769200⟩,⟨495088455000,123724585258320000⟩,⟨189783907750000,0⟩⟩,⟨⟨24351034919300880,5836993817343744⟩,⟨26860485986400,215173622265300⟩,⟨495088455000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 249904 1150 (62405-R)⟩
def p275:CachedProfile:=⟨⟨22146,101,5627⟩,⟨⟨⟨17604828212412,124947464149512396⟩,⟨1688027422899384,151754360016⟩,⟨344467368,7663365535896⟩,⟨11597068056,0⟩⟩,⟨⟨17426377710168,4227208888392⟩,⟨19191266136,151753223160⟩,⟨344467368,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨17560060356370,124651913373329890⟩,⟨1700802731622060,152902873560⟩,⟨350510760,7797812877720⟩,⟨11917365840,0⟩⟩,⟨⟨17382842590020,4207701028020⟩,⟨19291837320,152901728100⟩,⟨350510760,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 22247 102 (5627-R)⟩
def p276:CachedProfile:=⟨⟨104394,424,27238⟩,⟨⟨⟨1896687388849176,63289106218569270216⟩,⟨761346152999481600,14527032004864⟩,⟨29381510784,3079711197357312⟩,⟨4152586857472,0⟩⟩,⟨⟨1876472829020256,466609411676856⟩,⟨1887484883808,14527008906192⟩,⟨29381510784,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨1895685798420038,63258113219304317114⟩,⟨762777564252796200,14554344395200⟩,⟨29506177500,3092778513195000⟩,⟨4180041812500,0⟩⟩,⟨⟨1875500162654052,466164124687800⟩,⟨1890131017500,14554321253100⟩,⟨29506177500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 104818 425 (27238-R)⟩
def p277:CachedProfile:=⟨⟨66179,484,21010⟩,⟨⟨⟨606617179499618,12644122779449393594⟩,⟨271154708026559016,8135093104336⟩,⟨29531716896,1968672843438048⟩,⟨4764450325888,0⟩⟩,⟨⟨597339700465932,176566732295580⟩,⟨1281944983440,8135072765688⟩,⟨29531716896,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨606284352386718,12637826777257642494⟩,⟨271585623474515790,8148021322540⟩,⟨29639761350,1975875410875050⟩,⟨4791761418250,0⟩⟩,⟨⟨597020111407392,176398697538000⟩,⟨1283371110000,8148000951570⟩,⟨29639761350,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 66663 485 (21010-R)⟩
def p278:CachedProfile:=⟨⟨5488,40,1146⟩,⟨⟨⟨217890772600,389336529669112⟩,⟨8412853001280,3043862720⟩,⟨11011200,60869913600⟩,⟨146816000,0⟩⟩,⟨⟨216371717916,43598075616⟩,⟨315470880,3043770960⟩,⟨11011200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨215050551496,384521596393792⟩,⟨8517914176464,3081877832⟩,⟨11427438,63170877264⟩,⟨156174986,0⟩⟩,⟨⟨213586171656,42539817408⟩,⟨315508776,3081784926⟩,⟨11427438,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5528 41 (1146-R)⟩
def p279:CachedProfile:=⟨⟨51473,430,10691⟩,⟨⟨⟨178935457755780,3003102871590067092⟩,⟨74313381709139760,2863562660640⟩,⟨11861704800,615658064234400⟩,⟨1700177688000,0⟩⟩,⟨⟨177712279195176,35597622307896⟩,⟨294915083760,2863553465520⟩,⟨11861704800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨178685189397006,2999119352435391402⟩,⟨74388671249090004,2866463867992⟩,⟨11901335748,617715029328444⟩,⟨1709825235796,0⟩⟩,⟨⟨177466806799476,35504456630508⟩,⟨294827289516,2866454663556⟩,⟨11901335748,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 51903 431 (10691-R)⟩
def p280:CachedProfile:=⟨⟨5135,35,1056⟩,⟨⟨⟨175454127464,293444259515792⟩,⟨5933482733640,2295465760⟩,⟨7768950,40165471500⟩,⟨90637750,0⟩⟩,⟨⟨174264499332,34624275840⟩,⟨234400320,2295391770⟩,⟨7768950,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨172800327374,289227441466562⟩,⟨6016395580704,2327544576⟩,⟨8102592,41890400640⟩,⟨97231104,0⟩⟩,⟨⟨171660357492,33648076440⟩,⟨234299952,2327469552⟩,⟨8102592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5170 36 (1056-R)⟩
def p281:CachedProfile:=⟨⟨4748,29,1096⟩,⟨⟨⟨156832453614,240680758624482⟩,⟨4356202636638,1823902916⟩,⟨5535462,26442901974⟩,⟨53509466,0⟩⟩,⟨⟨155504238924,34460666544⟩,⟨209202288,1823839290⟩,⟨5535462,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨154511284674,237331152100182⟩,⟨4444791491160,1860996720⟩,⟨5842800,27911055600⟩,⟨58428000,0⟩⟩,⟨⟨153236564244,33524279004⟩,⟨210535560,1860931800⟩,⟨5842800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4777 30 (1096-R)⟩
def p282:CachedProfile:=⟨⟨73897,473,12055⟩,⟨⟨⟨408850493613320,9939306769049748200⟩,⟨189240064130837280,5089174010624⟩,⟨16183660944,1203578864405280⟩,⟨2551623875504,0⟩⟩,⟨⟨407096686014480,64851419397600⟩,⟨412460957040,5089162605648⟩,⟨16183660944,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨408284684037720,9926031871750007160⟩,⟨189388468707641280,5093165038080⟩,⟨16230594240,1207069293628800⟩,⟨2564433889920,0⟩⟩,⟨⟨406537845455280,64679392663200⟩,⟨412236548640,5093153624160⟩,⟨16230594240,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 74370 474 (12055-R)⟩
def p283:CachedProfile:=⟨⟨24592,171,5396⟩,⟨⟨⟨20643686856030,164761594101995982⟩,⟨3395579768918442,274248792468⟩,⟨946882062,23447640501306⟩,⟨53972277534,0⟩⟩,⟨⟨20486276108256,4326920014536⟩,⟨29879389512,274246946694⟩,⟨946882062,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20602532316690,164451597575469042⟩,⟨3409108450324344,275341464496⟩,⟨956214048,23678728470624⟩,⟨54822938752,0⟩⟩,⟨⟨20445994058676,4310898848796⟩,⟨29942842224,275339611368⟩,⟨956214048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20590189107336,164358605423720136⟩,⟨3407209897337280,275188127872⟩,⟨955681536,23665541875968⟩,⟨54792408064,0⟩⟩,⟨⟨20433911965776,4306098293616⟩,⟨29909498304,275186275776⟩,⟨955681536,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24763 172 (5396-R)⟩
def p284:CachedProfile:=⟨⟨24595,161,5396⟩,⟨⟨⟨20632461883992,164622633048773760⟩,⟨3195200680768656,258137862360⟩,⟨839373822,20779538337432⟩,⟨45046395114,0⟩⟩,⟨⟨20475051211776,4325696881632⟩,⟨28132056792,258136124526⟩,⟨839373822,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20591328143192,164312894005099160⟩,⟨3209089443418512,259259933520⟩,⟨848258568,20999489109408⟩,⟨45805962672,0⟩⟩,⟨⟨20434789960596,4309680244752⟩,⟨28201979304,259258188132⟩,⟨848258568,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24756 162 (5396-R)⟩
def p285:CachedProfile:=⟨⟨25057,147,5111⟩,⟨⟨⟨20152900368360,164383089302287944⟩,⟨2864213323144992,227284795584⟩,⟨662791248,16704990614592⟩,⟨32476771152,0⟩⟩,⟨⟨20019105377712,3951094776768⟩,⟨23044395024,227283292656⟩,⟨662791248,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20110872453570,164057520242996454⟩,⟨2878056640587168,228383315776⟩,⟨670525248,16899918350592⟩,⟨33079245568,0⟩⟩,⟨⟨19977860206452,3935650269648⟩,⟨23110468176,228381805584⟩,⟨670525248,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25204 148 (5111-R)⟩
def p286:CachedProfile:=⟨⟨25267,141,5143⟩,⟨⟨⟨20606167394376,169457290846845096⟩,⟨2809436394492000,221148090816⟩,⟨613607184,15590531331072⟩,⟨28839537648,0⟩⟩,⟨⟨20469844887216,4033102089216⟩,⟨22381430832,221146640208⟩,⟨613607184,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20563470796706,169123782129704486⟩,⟨2823861073910640,222283553312⟩,⟨621131856,15781718197248⟩,⟨29400241184,0⟩⟩,⟨⟨20427940872036,4017435008256⟩,⟨22452604344,222282095256⟩,⟨621131856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25408 142 (5143-R)⟩
def p287:CachedProfile:=⟨⟨25344,140,5143⟩,⟨⟨⟨20725546054216,170976131000691496⟩,⟨2806223888200320,220236450560⟩,⟨604934400,15416148249600⟩,⟨28230272000,0⟩⟩,⟨⟨20589222765168,4045165839168⟩,⟨22222697280,220235010240⟩,⟨604934400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25484 141 (5143-R)⟩
def p288:CachedProfile:=⟨⟨24634,150,5396⟩,⟨⟨⟨20677380812760,165178948853292864⟩,⟨2983632702170400,240773122800⟩,⟨728595000,18057498480000⟩,⟨36429750000,0⟩⟩,⟨⟨20519969838312,4330589413248⟩,⟨26209990800,240771503700⟩,⟨728595000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20636163842520,164868179004405624⟩,⟨2997958316760216,241929178792⟩,⟨736973922,18265161682848⟩,⟨37094354074,0⟩⟩,⟨⟨20479625358252,4314554660928⟩,⟨26287030092,241927551918⟩,⟨736973922,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24784 151 (5396-R)⟩
def p289:CachedProfile:=⟨⟨24880,144,5079⟩,⟨⟨⟨19742886655880,159880963948070120⟩,⟨2748514056814080,219672529920⟩,⟨632033280,15816000798720⟩,⟨30337597440,0⟩⟩,⟨⟨19611587507760,3873913390080⟩,⟨22292340480,219671066880⟩,⟨632033280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19701450086370,159562306528317030⟩,⟨2762152838382600,220762604400⟩,⟨639580500,16004862432000⟩,⟨30913057500,0⟩⟩,⟨⟨19570923904740,3858675275520⟩,⟨22358852100,220761134100⟩,⟨639580500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19680737506640,159402989412354560⟩,⟨2759428777711200,220544889800⟩,⟨638949750,15989078544000⟩,⟨30882571250,0⟩⟩,⟨⟨19550596667280,3851067479040⟩,⟨22314769200,220543420950⟩,⟨638949750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25024 145 (5079-R)⟩
def p290:CachedProfile:=⟨⟨24939,145,5237⟩,⟨⟨⟨20494116704826,166103615557887966⟩,⟨2867382037261800,228624662160⟩,⟨660773700,16574847490800⟩,⟨31937395500,0⟩⟩,⟨⟨20350195651620,4128536328624⟩,⟨23865323220,228623143140⟩,⟨660773700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20452255467396,165782193841212996⟩,⟨2881645048637280,229761900608⟩,⟨668640288,16772172984192⟩,⟨32540494016,0⟩⟩,⟨⟨20309156235480,4112786085024⟩,⟨23938238256,229760374032⟩,⟨668640288,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25084 146 (5237-R)⟩
def p291:CachedProfile:=⟨⟨24985,141,5237⟩,⟨⟨⟨20560394459754,166935559004088462⟩,⟨2797626758419800,222690008160⟩,⟨624820068,15699229028568⟩,⟨29366543196,0⟩⟩,⟨⟨20416472966556,4135449042936⟩,⟨23206969476,222688531044⟩,⟨624820068,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20518406689764,166612548976516452⟩,⟨2812089093360480,223841211520⟩,⟨632504352,15892304348352⟩,⟨29938539328,0⟩⟩,⟨⟨20375307018696,4119672427536⟩,⟨23282396112,223839726768⟩,⟨632504352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25126 142 (5237-R)⟩
def p292:CachedProfile:=⟨⟨24281,149,5079⟩,⟨⟨⟨18847491911240,148810333222929320⟩,⟨2710538352608160,221904722560⟩,⟨676686480,16531450706400⟩,⟨33608761840,0⟩⟩,⟨⟨18716198798160,3781957485600⟩,⟨23066380080,221903208720⟩,⟨676686480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18807817929810,148513468744733430⟩,⟨2723358278394000,222954264000⟩,⟨684450000,16721113500000⟩,⟨34222500000,0⟩⟩,⟨⟨18677297771340,3767081081400⟩,⟨23129847000,222952743000⟩,⟨684450000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨18784020842904,148335364895395128⟩,⟨2720135314497600,222690412800⟩,⟨683640000,16701325200000⟩,⟨34182000000,0⟩⟩,⟨⟨18653962996848,3758169310560⟩,⟨23075128800,222688893600⟩,⟨683640000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24430 150 (5079-R)⟩
def p293:CachedProfile:=⟨⟨24376,148,5079⟩,⟨⟨⟨18987754815880,150526925241910120⟩,⟨2713105164543360,221263504640⟩,⟨667633920,16373054254080⟩,⟨32936606720,0⟩⟩,⟨⟨18856460747760,3796509430080⟩,⟨22911572160,221262000960⟩,⟨667633920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18947804726370,150226681588377030⟩,⟨2726060021142120,222320027280⟩,⟨675354420,16562391796080⟩,⟨33542602860,0⟩⟩,⟨⟨18817283614740,3781575785520⟩,⟨22975648020,222318516420⟩,⟨675354420,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨18923841974616,150046550233944696⟩,⟨2722833860281632,222056926656⟩,⟨674555184,16542791332416⟩,⟨33502907472,0⟩⟩,⟨⟨18793783176528,3772629724608⟩,⟨22921294608,222055417584⟩,⟨674555184,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24524 149 (5079-R)⟩
def p294:CachedProfile:=⟨⟨40767,250,10158⟩,⟨⟨⟨107793481661954,1412778460802142830⟩,⟨25637474958292500,1250095427000⟩,⟨3809625000,156259388625000⟩,⟨317468750000,0⟩⟩,⟨⟨106744392229272,25396525914444⟩,⟨154792683000,1250090347500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨107677070789214,1411356358182519690⟩,⟨25714687388486490,1253860356588⟩,⟨3836382894,157356917163198⟩,⟨320977368798,0⟩⟩,⟨⟨106631074882452,25346549981304⟩,⟨155106030312,1253855261790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41017 251 (10158-R)⟩
def p295:CachedProfile:=⟨⟨42017,250,10158⟩,⟨⟨⟨114139199421954,1544912003902980330⟩,⟨27223879000792500,1288191677000⟩,⟨3809625000,161021419875000⟩,⟨317468750000,0⟩⟩,⟨⟨113090084591772,26170489329444⟩,⟨154792683000,1288186597500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨114016542149214,1543359834259382190⟩,⟨27305869225856490,1292071341588⟩,⟨3836382894,162152395780698⟩,⟨320977368798,0⟩⟩,⟨⟨112970520869952,26118990371304⟩,⟨155106030312,1292066246790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42267 251 (10158-R)⟩
def p296:CachedProfile:=⟨⟨42267,250,10158⟩,⟨⟨⟨115431200723954,1572297221792397830⟩,⟨27546874246792500,1295810927000⟩,⟨3809625000,161973826125000⟩,⟨317468750000,0⟩⟩,⟨⟨114382080814272,26325282012444⟩,⟨154792683000,1295805847500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨115307271671214,1570718095236504690⟩,⟨27629837241080490,1299713538588⟩,⟨3836382894,163111491504198⟩,⟨320977368798,0⟩⟩,⟨⟨114261245317452,26273478449304⟩,⟨155106030312,1299708443790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42517 251 (10158-R)⟩
def p297:CachedProfile:=⟨⟨42518,250,10174⟩,⟨⟨⟨116936440002800,1602688554262142600⟩,⟨27916977150150000,1305513550000⟩,⟨3815625000,163186650000000⟩,⟨317968750000,0⟩⟩,⟨⟨115882352615700,26564175633600⟩,⟨155280675000,1305508462500⟩,⟨3815625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨116811177762840,1601081843764265280⟩,⟨28001098172670480,1309447411960⟩,⟨3842430990,164333088580320⟩,⟨321483392830,0⟩⟩,⟨⟨115760193691560,26511984132480⟩,⟨155595492360,1309442309130⟩,⟨3842430990,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42768 251 (10174-R)⟩
def p298:CachedProfile:=⟨⟨25216,192,5095⟩,⟨⟨⟨20401363921848,167856736891358424⟩,⟨3789917140359168,298327830528⟩,⟨1127153664,28638720294912⟩,⟨72137834496,0⟩⟩,⟨⟨20268817772112,3958178165760⟩,⟨29910666240,298325873664⟩,⟨1127153664,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20358740972498,167523379124057174⟩,⟨3802180396686792,299293156592⟩,⟨1136690484,28881031817472⟩,⟨73127087804,0⟩⟩,⟨⟨20226972675972,3942657434880⟩,⟨29948554980,299291193396⟩,⟨1136690484,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25408 193 (5095-R)⟩
def p299:CachedProfile:=⟨⟨41267,250,10158⟩,⟨⟨⟨110308911015954,1464680988023227830⟩,⟨26266322137792500,1265333927000⟩,⟨3809625000,158164201125000⟩,⟨317468750000,0⟩⟩,⟨⟨109259811424272,25706111280444⟩,⟨154792683000,1265328847500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨110190024083214,1463207794601514690⟩,⟨26345428475684490,1269144750588⟩,⟨3836382894,159275108610198⟩,⟨320977368798,0⟩⟩,⟨⟨109144018027452,25655526137304⟩,⟨155106030312,1269139655790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41517 251 (10158-R)⟩
def p300:CachedProfile:=⟨⟨4275,32,852⟩,⟨⟨⟨98066999422,136867560432286⟩,⟨3038364654528,1410984832⟩,⟨5240832,22572263424⟩,⟨55902208,0⟩⟩,⟨⟨97440455568,18780828552⟩,⟨139537152,1410930240⟩,⟨5240832,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨96358181794,134595431065450⟩,⟨3081882884850,1431196404⟩,⟨5482026,23611085982⟩,⟨60302286,0⟩⟩,⟨⟨95761771932,18169045044⟩,⟨139210236,1431141030⟩,⟨5482026,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4307 33 (852-R)⟩
def p301:CachedProfile:=⟨⟨24832,192,5143⟩,⟨⟨⟨20008442824776,161921111167592616⟩,⟨3710855432595456,296586743808⟩,⟨1137770496,28471568891904⟩,⟨72817311744,0⟩⟩,⟨⟨19872124268208,3972148405248⟩,⟨30476841984,296584768512⟩,⟨1137770496,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19966908211106,161602253114085926⟩,⟨3722931163954824,297551895152⟩,⟨1147418196,28712992936704⟩,⟨73817237276,0⟩⟩,⟨⟨19831382229348,3956718106368⟩,⟨30516567876,297549913428⟩,⟨1147418196,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨19962755597256,161570369053189056⟩,⟨3722205999911760,297493938024⟩,⟨1147194702,28707400222848⟩,⟨73802859162,0⟩⟩,⟨⟨19827308703480,3955176728064⟩,⟨30504679848,297491956686⟩,⟨1147194702,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25024 193 (5143-R)⟩
def p302:CachedProfile:=⟨⟨9353,74,2353⟩,⟨⟨⟨1320530773914,3975475916467110⟩,⟨92887963229160,19707141872⟩,⟨77343024,729112687248⟩,⟨1907794592,0⟩⟩,⟨⟨1307453214012,313294768644⟩,⟨2459299128,19706793480⟩,⟨77343024,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1314370624424,3958197409814120⟩,⟨93743256222000,19888605600⟩,⟨79110000,745769970000⟩,⟨1977750000,0⟩⟩,⟨⟨1301458693392,310638051504⟩,⟨2471396400,19888254000⟩,⟨79110000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨1313754996642,3956469923716266⟩,⟨93703261256550,19880120700⟩,⟨79076250,745451808750⟩,⟨1976906250,0⟩⟩,⟨⟨1300859551068,310373001972⟩,⟨2469287700,19879769250⟩,⟨79076250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9427 75 (2353-R)⟩
def p303:CachedProfile:=⟨⟨25120,182,5143⟩,⟨⟨⟨20440261007624,167354031214665320⟩,⟨3596170539299520,284262707456⟩,⟨1022339136,25867224819072⟩,⟨62021907584,0⟩⟩,⟨⟨20303939590992,4016276332704⟩,⟨28889506464,284260835040⟩,⟨1022339136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨20393650374192,166991671081318416⟩,⟨3608197240497912,285213379248⟩,⟨1031394222,26096336605044⟩,⟨62915047542,0⟩⟩,⟨⟨20258200626468,3999116111472⟩,⟨28924126488,285211500570⟩,⟨1031394222,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25302 183 (5143-R)⟩
def p304:CachedProfile:=⟨⟨25120,182,5111⟩,⟨⟨⟨20304718139304,166299998914071432⟩,⟨3573798981165504,282494354688⟩,⟨1015979328,25706308957056⟩,⟨61636079232,0⟩⟩,⟨⟨20170922146704,3966457706784⟩,⟨28531155744,282492493920⟩,⟨1015979328,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25302 183 (5111-R)⟩
def p305:CachedProfile:=⟨⟨156427,1257,38394⟩,⟨⟨⟨6011017440430520,303245862879830449880⟩,⟨7200087888275157960,91323103083240⟩,⟨363995888130,57396327623890920⟩,⟨152514277126470,0⟩⟩,⟨⟨5954407291709940,1394687508293520⟩,⟨11117946005460,91323006558210⟩,⟨363995888130,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨6009304510510560,303165184535900115840⟩,⟨7203939117105107520,91371950639280⟩,⟨364480314840,57472713965230560⟩,⟨152838745356240,0⟩⟩,⟨⟨5952738577171320,1393961099103360⟩,⟨11120995552320,91371854062620⟩,⟨364480314840,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 157684 1258 (38394-R)⟩
def p306:CachedProfile:=⟨⟨46519,386,11421⟩,⟨⟨⟨158229747687414,2374469189914066362⟩,⟨58200069123608184,2481624222256⟩,⟨10210993872,478946667566160⟩,⟨1313814544864,0⟩⟩,⟨⟨156738799178892,36712729806660⟩,⟨302123733192,2481615404472⟩,⟨10210993872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨158063034833810,2372133306492567350⟩,⟨58294650919950990,2485657171476⟩,⟨10254084354,480967826624370⟩,⟨1322776881666,0⟩⟩,⟨⟨156576387958800,36642048099300⟩,⟨302323262220,2485648339362⟩,⟨10254084354,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 46905 387 (11421-R)⟩
def p307:CachedProfile:=⟨⟨18265,142,4279⟩,⟨⟨⟨9093334707640,53724810862961080⟩,⟨1235550093397920,134249321920⟩,⟨517811520,9531356648640⟩,⟨24509745280,0⟩⟩,⟨⟨9014811024240,2022648041040⟩,⟨15603630240,134248106400⟩,⟨517811520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨9065650814572,53571363851027836⟩,⟨1240762507879752,134815689008⟩,⟨523657992,9638972658744⟩,⟨24961030952,0⟩⟩,⟨⟨8987784982968,2011320667752⟩,⟨15625515048,134814468360⟩,⟨523657992,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18407 143 (4279-R)⟩
def p308:CachedProfile:=⟨⟨112683,411,30126⟩,⟨⟨⟨2448733447897800,87982415520896914344⟩,⟨950233058083766016,16804325307792⟩,⟨30534497802,3453268494419388⟩,⟨4183226198874,0⟩⟩,⟨⟨2421384095115672,615868759141128⟩,⟨2238156400932,16804300543398⟩,⟨30534497802,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨2447558889995646,87943384555726068306⟩,⟨952134029221296096,16837942923648⟩,⟨30670024896,3468595795588224⟩,⟨4212016752384,0⟩⟩,⟨⟨2420244921124548,615337362101448⟩,⟨2241666164304,16837918109712⟩,⟨30670024896,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 113094 412 (30126-R)⟩
def p309:CachedProfile:=⟨⟨165283,971,39295⟩,⟨⟨⟨6820380722534528,363543223561552581248⟩,⟨6327967883739096576,76124186679296⟩,⟨222299279616,36958144433278464⟩,⟨71950866835712,0⟩⟩,⟨⟨6759690819605760,1540313038471680⟩,⟨8996138200320,76124110366464⟩,⟨222299279616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨6817923748159296,363420589442286047256⟩,⟨6332389247540652480,76177374872256⟩,⟨222683699232,37022055732116928⟩,⟨72149518551168,0⟩⟩,⟨⟨6757294050438240,1539294053740344⟩,⟨8999445548592,76177298506104⟩,⟨222683699232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 166254 972 (39295-R)⟩
def p310:CachedProfile:=⟨⟨25648,193,5095⟩,⟨⟨⟨21079887994984,176550272541769672⟩,⟨3940608031306128,304992032800⟩,⟨1138925424,29430971881584⟩,⟨73270868944,0⟩⟩,⟨⟨20947337432112,4025632949520⟩,⟨30066450960,304990065744⟩,⟨1138925424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨21040328318242,176234895336603070⟩,⟨3954030050890404,306030867800⟩,⟨1148725992,29684228359272⟩,⟨74284280816,0⟩⟩,⟨⟨20908477968456,4011424844172⟩,⟨30115569048,306028894044⟩,⟨1148725992,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25841 194 (5095-R)⟩
def p311:CachedProfile:=⟨⟨7740,44,1456⟩,⟨⟨⟨545222221600,1379047529864704⟩,⟨23307194744064,5988712928⟩,⟨16924512,131740401408⟩,⟨248226176,0⟩⟩,⟨⟨542110792272,99077491968⟩,⟨560047488,5988584712⟩,⟨16924512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨538506275040,1362800900504160⟩,⟨23558766019200,6053356800⟩,⟨17496000,136188864000⟩,⟨262440000,0⟩⟩,⟨⟨535502018880,96778160640⟩,⟨559483200,6053227200⟩,⟨17496000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 18=>⟨⟨⟨538111609456,1361845443483976⟩,⟨23542404987960,6049153080⟩,⟨17483850,136094288400⟩,⟨262257750,0⟩⟩,⟨⟨535113579588,96643746528⟩,⟨558706140,6049023570⟩,⟨17483850,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7784 45 (1456-R)⟩
def p312:CachedProfile:=⟨⟨46012,342,9022⟩,⟨⟨⟨120001669945416,1804062567452708136⟩,⟨39783811977826560,1716531477696⟩,⟨6332197032,293522661221328⟩,⟨721870461648,0⟩⟩,⟨⟨119266392966000,22640824950744⟩,⟨167044098312,1716525305964⟩,⟨6332197032,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨119804105997576,1801232580299168016⟩,⟨39838229722595304,1718879434272⟩,⟨6359399046,294783583378284⟩,⟨727091290926,0⟩⟩,⟨⟨119072243918628,22570616996928⟩,⟨167013022176,1718873254098⟩,⟨6359399046,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 46354 343 (9022-R)⟩
def p313:CachedProfile:=⟨⟨13735,88,2821⟩,⟨⟨⟨3347903418910,14971799617633402⟩,⟨284713704085536,41194969024⟩,⟨131121408,1812491222784⟩,⟨3846227968,0⟩⟩,⟨⟨3325367810196,660257972556⟩,⟨4203335136,41194472352⟩,⟨131121408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨3330188082936,14896583801636472⟩,⟨286520523762096,41456402208⟩,⟨133453008,1844720929584⟩,⟨3959105904,0⟩⟩,⟨⟨3307985521776,653721960528⟩,⟨4209017904,41455902384⟩,⟨133453008,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13823 89 (2821-R)⟩
def p314:CachedProfile:=⟨⟨2994,21,631⟩,⟨⟨⟨35744363384,34815695582072⟩,⟨723973292784,480287136⟩,⟨1672272,5041900080⟩,⟨11705904,0⟩⟩,⟨⟨35488914672,7214147280⟩,⟨50247792,480260592⟩,⟨1672272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨34898552082,34034041722414⟩,⟨741644859384,492012048⟩,⟨1794672,5410936080⟩,⟨13160928,0⟩⟩,⟨⟨34659559740,6897825540⟩,⟨50332392,491984856⟩,⟨1794672,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3015 22 (631-R)⟩
def p315:CachedProfile:=⟨⟨46666,335,9953⟩,⟨⟨⟨136870197185610,2076910402229407710⟩,⟨44198934858858780,1880775451800⟩,⟨6702525900,315025419825900⟩,⟨748448725500,0⟩⟩,⟨⟨135883196261316,27938944116972⟩,⟨199135045620,1880768782620⟩,⟨6702525900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨136663852260180,2073947913718872660⟩,⟨44268521385836160,1883736556800⟩,⟨6733117440,316463252797440⟩,⟨754109153280,0⟩⟩,⟨⟨135681007693560,27860404881960⟩,⟨199168018560,1883729877120⟩,⟨6733117440,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 47001 336 (9953-R)⟩
def p316:CachedProfile:=⟨⟨12549,82,3046⟩,⟨⟨⟨3058428340242,12368007316829010⟩,⟨239182615230372,37872869320⟩,⟨122928168,1552705690008⟩,⟨3360036592,0⟩⟩,⟨⟨3030080947476,703382143332⟩,⟨4566331704,37872369612⟩,⟨122928168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨3044180662850,12314140175268830⟩,⟨241066521717564,38171178760⟩,⟨125407356,1584020313636⟩,⟨3469603516,0⟩⟩,⟨⟨3016193981916,697392017892⟩,⟨4582656756,38170675116⟩,⟨125407356,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨3043085325534,12309997326008382⟩,⟨240987063679650,38158597620⟩,⟨125366022,1583498223882⟩,⟨3468459942,0⟩⟩,⟨⟨3015126264096,696932300016⟩,⟨4579635888,38158094142⟩,⟨125366022,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12631 83 (3046-R)⟩
def p317:CachedProfile:=⟨⟨16524,111,3328⟩,⟨⟨⟨5712087972974,30773627458049798⟩,⟨613541693383434,73766338932⟩,⟨246099654,4093867744290⟩,⟨9105687198,0⟩⟩,⟨⟨5675106598008,1105786206720⟩,⟨7378555392,73765599894⟩,⟨246099654,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨5684699397914,30633311682862598⟩,⟨616279592015808,74095525504⟩,⟨249424896,4149183144960⟩,⟨9311862784,0⟩⟩,⟨⟨5648214779868,1095842136420⟩,⟨7378077504,74094783168⟩,⟨249424896,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨5682874289262,30623958357868134⟩,⟨616093625103264,74073167168⟩,⟨249349632,4147931128320⟩,⟨9309052928,0⟩⟩,⟨⟨5646422629080,1095180795360⟩,⟨7373624832,74072425056⟩,⟨249349632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16635 112 (3328-R)⟩
def p318:CachedProfile:=⟨⟨44768,250,10190⟩,⟨⟨⟨129214572726888,1870378506508015464⟩,⟨30980243121696000,1376355696000⟩,⟨3821625000,172041914250000⟩,⟨318468750000,0⟩⟩,⟨⟨128155461474912,28049713699320⟩,⟨155769435000,1376350600500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨129077410345088,1868511444140220464⟩,⟨31073642578528824,1380505156544⟩,⟨3848479086,173250831493548⟩,⟨321989416862,0⟩⟩,⟨⟨128021412224172,27994689998640⟩,⟨156085725480,1380500045682⟩,⟨3848479086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45018 251 (10190-R)⟩
def p319:CachedProfile:=⟨⟨44768,250,10475⟩,⟨⟨⟨133136667663588,1923643161117232164⟩,⟨31846640979636000,1414846656000⟩,⟨3928500000,176853213000000⟩,⟨327375000000,0⟩⟩,⟨⟨131986238798952,29640598498800⟩,⟨164604150000,1414841418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨132998622240638,1921772447583665714⟩,⟨31943506010732184,1419150080384⟩,⟨3956210796,178100697614328⟩,⟨331002969932,0⟩⟩,⟨⟨131851483113012,29584035182520⟩,⟨164947195140,1419144826452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45018 251 (10475-R)⟩
def p320:CachedProfile:=⟨⟨45018,250,10174⟩,⟨⟨⟨130373138002800,1898494959513642600⟩,⟨31276100775150000,1381826050000⟩,⟨3815625000,172725712500000⟩,⟨317968750000,0⟩⟩,⟨⟨129318999740700,28116982383600⟩,⟨155280675000,1381820962500⟩,⟨3815625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45268 251 (10174-R)⟩
def p321:CachedProfile:=⟨⟨44268,250,10475⟩,⟨⟨⟨130322688351588,1860654673009960164⟩,⟨31143156627636000,1399132656000⟩,⟨3928500000,174888963000000⟩,⟨327375000000,0⟩⟩,⟨⟨129172269962952,29311390198800⟩,⟨164604150000,1399127418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨130187329048638,1858844086572573714⟩,⟨31237881927404184,1403388284384⟩,⟨3956210796,176122592216328⟩,⟨331002969932,0⟩⟩,⟨⟨129040200387012,29255455112520⟩,⟨164947195140,1403383030452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44518 251 (10475-R)⟩
def p322:CachedProfile:=⟨⟨8268,2,2548⟩,⟨⟨⟨1128927058624,2926287227465488⟩,⟨2092157901648,505966304⟩,⟨61176,505925520⟩,⟨40784,0⟩⟩,⟨⟨1112336015268,322274556240⟩,⟨77938224,505956108⟩,⟨61176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 8270 3 (2548-R)⟩
def p323:CachedProfile:=⟨⟨97231,52,30033⟩,⟨⟨⟨1840923106904506,56118330702869034886⟩,⟨88683829129980240,1823214210272⟩,⟨487271616,47403244619328⟩,⟨8446041344,0⟩⟩,⟨⟨1813827163282236,526502087889156⟩,⟨281427470064,1823211086736⟩,⟨487271616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨1840009090529598,56092984233556470174⟩,⟨90350162783997462,1857471680652⟩,⟨505973934,49222662221322⟩,⟨8938872834,0⟩⟩,⟨⟨1812948312255312,526046393693160⟩,⟨286591273560,1857468498426⟩,⟨505973934,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 97283 53 (30033-R)⟩
def p324:CachedProfile:=⟨⟨24562,174,5396⟩,⟨⟨⟨20600408021592,164226034282712640⟩,⟨3447621029460384,278755913520⟩,⟨980397432,24251110877952⟩,⟨56863051056,0⟩⟩,⟨⟨20442997565256,4322202216192⟩,⟨30403589328,278754035364⟩,⟨980397432,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20559333672792,163917030102376440⟩,⟨3461010085171800,279838489000⟩,⟨989861250,24485207880000⟩,⟨57741906250,0⟩⟩,⟨⟨20402795705676,4306198518912⟩,⟨30465101100,279836603550⟩,⟨989861250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24736 175 (5396-R)⟩
def p325:CachedProfile:=⟨⟨24515,173,5396⟩,⟨⟨⟨20523584446680,163276810725440832⟩,⟨3414516995571696,276616067784⟩,⟨969160878,23926643756064⟩,⟨55888277298,0⟩⟩,⟨⟨20366174508456,4313815019136⟩,⟨30228856056,276614200422⟩,⟨969160878,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20482652442840,162969565374646392⟩,⟨3427890710611248,277699505232⟩,⟨978580872,24159204567936⟩,⟨56757690576,0⟩⟩,⟨⟨20326114992876,4297842376896⟩,⟨30291014808,277697630556⟩,⟨978580872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20470375994136,162877398575582136⟩,⟨3425981697466560,277544855424⟩,⟨978035904,24145750397952⟩,⟨56726082432,0⟩⟩,⟨⟨20314099660176,4293056361216⟩,⟨30257283168,277542981792⟩,⟨978035904,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24688 174 (5396-R)⟩
def p326:CachedProfile:=⟨⟨24850,166,5237⟩,⟨⟨⟨20387044944954,164762554247603262⟩,⟨3264884617325040,261026301600⟩,⟨866029968,21664605679488⟩,⟨47920324896,0⟩⟩,⟨⟨20243124604116,4117344314976⟩,⟨27321680376,261024562584⟩,⟨866029968,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20345388120964,164443692828094852⟩,⟨3278281868663760,262097415200⟩,⟨874822152,21884550954432⟩,⟨48698433128,0⟩⟩,⟨⟨20202289600056,4101636768576⟩,⟨27381409512,262095669048⟩,⟨874822152,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25016 167 (5237-R)⟩
def p327:CachedProfile:=⟨⟨24860,163,5143⟩,⟨⟨⟨20006898133016,161901784567878296⟩,⟨3150109865248080,251779726048⟩,⟨820025616,20519500989168⟩,⟨44554725136,0⟩⟩,⟨⟨19870579586736,3971989671696⟩,⟨25873568976,251778049104⟩,⟨820025616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19965366522246,161582964086137986⟩,⟨3163274169185520,252831921184⟩,⟨828504384,20731665200832⟩,⟨45291572992,0⟩⟩,⟨⟨19829840550756,3956559989436⟩,⟨25931176848,252830237232⟩,⟨828504384,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25023 164 (5143-R)⟩
def p328:CachedProfile:=⟨⟨24862,157,5237⟩,⟨⟨⟨20391762570606,164821565262579066⟩,⟨3088613448213660,246903878376⟩,⟨774668772,19381438006668⟩,⟨40540999068,0⟩⟩,⟨⟨20247842198340,4117838080284⟩,⟨25840384452,246902233644⟩,⟨774668772,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25019 158 (5237-R)⟩
def p329:CachedProfile:=⟨⟨25250,143,5143⟩,⟨⟨⟨20582647946136,169158591043258296⟩,⟨2845923363288720,224152536608⟩,⟨631137936,16026485608848⟩,⟨30084241616,0⟩⟩,⟨⟨20446325593296,4030721085936⟩,⟨22698897936,224151065424⟩,⟨631137936,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20539997070566,168825663011493386⟩,⟨2860253637243840,225281234304⟩,⟨638751744,16219823035392⟩,⟨30660083712,0⟩⟩,⟨⟨20404467299916,4015063254276⟩,⟨22768838208,225279755712⟩,⟨638751744,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25393 144 (5143-R)⟩
def p330:CachedProfile:=⟨⟨25426,137,5079⟩,⟨⟨⟨20573988219480,170391985244593560⟩,⟨2728763647841520,213495473440⟩,⟨572079120,14624058544560⟩,⟨26124946480,0⟩⟩,⟨⟨20442683595120,3957354858960⟩,⟨21208685040,213494081520⟩,⟨572079120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20530915623270,170052636510108690⟩,⟨2743270756101720,214630500240⟩,⟨579318480,14809118304240⟩,⟨26648650080,0⟩⟩,⟨⟨20400383976180,3941788525740⟩,⟨21279459240,214629100920⟩,⟨579318480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25563 138 (5079-R)⟩
def p331:CachedProfile:=⟨⟨25496,134,5079⟩,⟨⟨⟨20678535239240,171729990800337320⟩,⟨2683018635130560,209367688960⟩,⟨547298880,14027270294400⟩,⟨24446016640,0⟩⟩,⟨⟨20547229934160,3967726989600⟩,⟨20744261280,209366327520⟩,⟨547298880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20635256841810,171388008155885430⟩,⟨2697720132954600,210514917600⟩,⟨554404500,14209387335000⟩,⟨24948202500,0⟩⟩,⟨⟨20504724515340,3952119857400⟩,⟨20816862300,210513548700⟩,⟨554404500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨20617949742870,171251223756436650⟩,⟨2695591721323800,210348830880⟩,⟨553967100,14198176773000⟩,⟨24928519500,0⟩⟩,⟨⟨20487725755860,3945885616200⟩,⟨20784024900,210347463060⟩,⟨553967100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25630 135 (5079-R)⟩
def p332:CachedProfile:=⟨⟨24904,142,5079⟩,⟨⟨⟨19776462489160,160301245088100520⟩,⟨2715107891835840,216811961600⟩,⟨614598720,15393239541120⟩,⟨29091006080,0⟩⟩,⟨⟨19645163117520,3877319164320⟩,⟨21982724640,216810518880⟩,⟨614598720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19734959825490,159981760329883830⟩,⟨2728845943635240,217909005600⟩,⟨622058580,15580079194680⟩,⟨29651458980,0⟩⟩,⟨⟨19604433420780,3862067653080⟩,⟨22050454140,217907555580⟩,⟨622058580,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19714214198680,159822029544709360⟩,⟨2726154730607880,217694105200⟩,⟨621445110,15564714225060⟩,⟨29622216910,0⟩⟩,⟨⟨19584073136460,3854453168160⟩,⟨22006979280,217692656610⟩,⟨621445110,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25046 143 (5079-R)⟩
def p333:CachedProfile:=⟨⟨25002,139,5143⟩,⟨⟨⟨20189597869080,164193002746560120⟩,⟨2711684596126032,215720327200⟩,⟨596323344,14992165191504⟩,⟨27629648272,0⟩⟩,⟨⟨20053278108816,3990720230832⟩,⟨22063963728,215718897168⟩,⟨596323344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20147711087750,163869728035476410⟩,⟨2725883558746320,216849892000⟩,⟨603758400,15179089934400⟩,⟨28175392000,0⟩⟩,⟨⟨20012183904636,3975217787412⟩,⟨22136370480,216848454480⟩,⟨603758400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25141 140 (5143-R)⟩
def p334:CachedProfile:=⟨⟨24592,152,5143⟩,⟨⟨⟨19578340227656,156569772666583976⟩,⟨2872386707471616,232170695168⟩,⟨713081856,17644497444864⟩,⟨36129480704,0⟩⟩,⟨⟨19442024551728,3927703010688⟩,⟨24127499904,232169131392⟩,⟨713081856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24744 153 (5143-R)⟩
def p335:CachedProfile:=⟨⟨43518,250,10222⟩,⟨⟨⟨122846151121296,1725240950770728072⟩,⟨29375661710646000,1342341238000⟩,⟨3833625000,167790099000000⟩,⟨319468750000,0⟩⟩,⟨⟨121777062290436,27442406271648⟩,⟨156749259000,1342336126500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨122715549855416,1723521306659859392⟩,⟨29464314236356944,1346392290712⟩,⟨3860575278,168969658767504⟩,⟨323001464926,0⟩⟩,⟨⟨121649593717176,27388742326848⟩,⟨157068504936,1346387163786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43768 251 (10222-R)⟩
def p336:CachedProfile:=⟨⟨43518,250,10190⟩,⟨⟨⟨122428334871888,1719738530162035464⟩,⟨29283709135446000,1338139446000⟩,⟨3821625000,167264883000000⟩,⟨318468750000,0⟩⟩,⟨⟨121369249097412,27270866524320⟩,⟨155769435000,1338134350500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 43768 251 (10190-R)⟩
def p337:CachedProfile:=⟨⟨24799,153,5143⟩,⟨⟨⟨19897382794824,160533540354769320⟩,⟨2940096191597280,235662565824⟩,⟨722495376,18027704621952⟩,⟨36847264176,0⟩⟩,⟨⟨19761064978992,3960719589504⟩,⟨24286233456,235660991760⟩,⟨722495376,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19856064083234,160217379800544230⟩,⟨2953559471367120,236741718752⟩,⟨730547664,18228625312128⟩,⟨37501446752,0⟩⟩,⟨⟨19720538840772,3945333687264⟩,⟨24350007528,236740137480⟩,⟨730547664,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24952 154 (5143-R)⟩
def p338:CachedProfile:=⟨⟨24595,161,5079⟩,⟨⟨⟨19336240865160,154820260758447720⟩,⟨3007523191972320,242975790400⟩,⟨790072080,19559024412480⟩,⟨42400534960,0⟩⟩,⟨⟨19204944439920,3832424867520⟩,⟨24924075120,242974154640⟩,⟨790072080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19295604779490,154511565515898630⟩,⟨3020246268258960,244003687200⟩,⟨798342480,19763766434880⟩,⟨43110493920,0⟩⟩,⟨⟨19165081315380,3817349948880⟩,⟨24980234760,244002044520⟩,⟨798342480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24756 162 (5079-R)⟩
def p339:CachedProfile:=⟨⟨24400,167,5047⟩,⟨⟨⟨18923905090232,150350929836443576⟩,⟨3052801615381968,248531232992⟩,⟨844702032,20751794820144⟩,⟨47021746448,0⟩⟩,⟨⟨18795073350768,3755398488912⟩,⟨25528210512,248529546960⟩,⟨844702032,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18883876903782,150049230166556226⟩,⟨3064998003373152,249524159808⟩,⟨853155072,20959460653824⟩,⟨47776684032,0⟩⟩,⟨⟨18755808409668,3740532997212⟩,⟨25579417248,249522467040⟩,⟨853155072,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24567 168 (5047-R)⟩
def p340:CachedProfile:=⟨⟨24400,167,5015⟩,⟨⟨⟨18795868047000,149385598109684376⟩,⟨3033449144014608,246955757664⟩,⟨839347344,20620246200048⟩,⟨46723668816,0⟩⟩,⟨⟨18669468062256,3707932686480⟩,⟨25205550480,246954082320⟩,⟨839347344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18755888114630,149083995639477026⟩,⟨3045529650233952,247939250496⟩,⟨847736064,20826331884288⟩,⟨47473219584,0⟩⟩,⟨⟨18630241724676,3693161532060⟩,⟨25255470240,247937568480⟩,⟨847736064,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24567 168 (5015-R)⟩
def p341:CachedProfile:=⟨⟨24374,170,4920⟩,⟨⟨⟨18383309861168,146112094559717888⟩,⟨3023787833209920,246399981520⟩,⟨853301400,20943429561600⟩,⟨48353746000,0⟩⟩,⟨⟨18263948604720,3565455828480⟩,⟨24695546400,246398308380⟩,⟨853301400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18343539148368,145811605556979528⟩,⟨3035393913308616,247345736616⟩,⟨861615306,21147486070464⟩,⟨49112072442,0⟩⟩,⟨⟨18224903198100,3550978304640⟩,⟨24739948260,247344057054⟩,⟨861615306,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24544 171 (4920-R)⟩
def p342:CachedProfile:=⟨⟨29480,208,5971⟩,⟨⟨⟨32647596513980,313814694171311132⟩,⟨6569043706358016,442542590464⟩,⟨1550235648,46023395917824⟩,⟨107483004928,0⟩⟩,⟨⟨32434323154056,6351832863936⟩,⟨44502197376,442540106112⟩,⟨1550235648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨32589371688390,313282830023000442⟩,⟨6589572876080568,443925607312⟩,⟨1562556732,46389184259616⟩,⟨108858118996,0⟩⟩,⟨⟨32377166836476,6330576849696⟩,⟨44566510428,443923115196⟩,⟨1562556732,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29688 209 (5971-R)⟩
def p343:CachedProfile:=⟨⟨2984,24,734⟩,⟨⟨⟨41900656560,40318494378120⟩,⟨957802466880,636874560⟩,⟨2540160,7640801280⟩,⟨20321280,0⟩⟩,⟨⟨41500249140,9736715520⟩,⟨77686560,636839280⟩,⟨2540160,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨41277712600,39758122715200⟩,⟨984134430000,654385000⟩,⟨2718750,8178000000⟩,⟨22656250,0⟩⟩,⟨⟨40893323400,9473395200⟩,⟨78735000,654348750⟩,⟨2718750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (734-R)⟩
def p344:CachedProfile:=⟨⟨42268,250,10222⟩,⟨⟨⟨116230285556296,1582517461098748072⟩,⟨27721720876896000,1304004988000⟩,⟨3833625000,162998067750000⟩,⟨319468750000,0⟩⟩,⟨⟨115161222282936,26658659976648⟩,⟨156749259000,1303999876500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 42518 251 (10222-R)⟩
def p345:CachedProfile:=⟨⟨42768,250,10222⟩,⟨⟨⟨118853630032296,1638615450873540072⟩,⟨28377546772896000,1319339488000⟩,⟨3833625000,164914880250000⟩,⟨319468750000,0⟩⟩,⟨⟨117784556535936,26972158494648⟩,⟨156749259000,1319334376500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 43018 251 (10222-R)⟩
def p346:CachedProfile:=⟨⟨25216,192,5111⟩,⟨⟨⟨20469592449000,168390174296914632⟩,⟨3801816597694464,299264495616⟩,⟨1130692608,28728637784064⟩,⟨72364326912,0⟩⟩,⟨⟨20335795372656,3983074753536⟩,⟨30098801664,299262532608⟩,⟨1130692608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20426945027010,168056766527055942⟩,⟨3814141829621256,300234700144⟩,⟨1140266388,28971888386304⟩,⟨73357137628,0⟩⟩,⟨⟨20293930698276,3967505239296⟩,⟨30137299716,300232730772⟩,⟨1140266388,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25408 193 (5111-R)⟩
def p347:CachedProfile:=⟨⟨25360,187,5143⟩,⟨⟨⟨20824774956184,172242056092885720⟩,⟨3766868656238160,294900190816⟩,⟨1079283216,27572448319152⟩,⟨67275320464,0⟩⟩,⟨⟨20688451018992,4055166052944⟩,⟨29683174224,294898266960⟩,⟨1079283216,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20781653382694,171903133671824530⟩,⟨3779650223965200,295900841824⟩,⟨1088736576,27813953307072⟩,⟨68227492096,0⟩⟩,⟨⟨20646122030772,4039413261804⟩,⟨29725983216,295898911440⟩,⟨1088736576,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25547 188 (5143-R)⟩
def p348:CachedProfile:=⟨⟨25360,187,5111⟩,⟨⟨⟨20686840088184,171157615691583672⟩,⟨3743435202647184,293065663968⟩,⟨1072569168,27400924534896⟩,⟨66856811472,0⟩⟩,⟨⟨20553041590704,4004865031824⟩,⟨29314978704,293063752080⟩,⟨1072569168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20643767690374,170818794218871922⟩,⟨3756091459232016,294056504672⟩,⟨1081950528,27640590138816⟩,⟨67802233088,0⟩⟩,⟨⟨20510751943284,3989210341164⟩,⟨29356540656,294054586320⟩,⟨1081950528,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25547 188 (5111-R)⟩
def p349:CachedProfile:=⟨⟨24644,140,5143⟩,⟨⟨⟨19639487161416,157326886481929896⟩,⟨2654179676104320,214187106560⟩,⟨604934400,14992694169600⟩,⟨28230272000,0⟩⟩,⟨⟨19503171073968,3934052352768⟩,⟨22222697280,214185666240⟩,⟨604934400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19598669802146,157016959806231206⟩,⟨2667941401765608,215297657904⟩,⟨612414324,15178076606016⟩,⟨28783473228,0⟩⟩,⟨⟨19463146284708,3918770042688⟩,⟨22294487412,215296210116⟩,⟨612414324,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24784 141 (5143-R)⟩
def p350:CachedProfile:=⟨⟨24644,140,5237⟩,⟨⟨⟨20023928682426,160241768741715966⟩,⟨2702682231429600,218101101120⟩,⟨615988800,15266666419200⟩,⟨28746144000,0⟩⟩,⟨⟨19880010772020,4079159797824⟩,⟨23042381040,218099634480⟩,⟨615988800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19982965092996,159931538215188996⟩,⟨2716790400733680,219239609568⟩,⟨623627208,15455976723072⟩,⟨29310478776,0⟩⟩,⟨⟨19839868997880,4063597924224⟩,⟨23118435576,219238135272⟩,⟨623627208,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24784 141 (5237-R)⟩
def p351:CachedProfile:=⟨⟨9279,74,2353⟩,⟨⟨⟨1300900975066,3883315158130606⟩,⟨91435461238440,19552455824⟩,⟨77343024,723389303472⟩,⟨1907794592,0⟩⟩,⟨⟨1287823763556,310835469516⟩,⟨2459299128,19552107432⟩,⟨77343024,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1294824214696,3866428179337096⟩,⟨92277379566000,19732495200⟩,⟨79110000,739915830000⟩,⟨1977750000,0⟩⟩,⟨⟨1281912630576,308199607056⟩,⟨2471396400,19732143600⟩,⟨79110000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨1294216925826,3864739846015422⟩,⟨92238009974550,19724076900⟩,⟨79076250,739600166250⟩,⟨1976906250,0⟩⟩,⟨⟨1281321827016,307936638108⟩,⟨2469287700,19723725450⟩,⟨79076250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9353 75 (2353-R)⟩
def p352:CachedProfile:=⟨⟨24797,179,5237⟩,⟨⟨⟨20324197325754,163977092316798462⟩,⟨3509318928612600,281018071440⟩,⟨1006984548,25150446070848⟩,⟨60083411364,0⟩⟩,⟨⟨20180277403956,4110760777536⟩,⟨29461330044,281016196236⟩,⟨1006984548,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20282660485764,163659730467880452⟩,⟨3522186790027200,282048508800⟩,⟨1016323200,25383688243200⟩,⟨60979392000,0⟩⟩,⟨⟨20139562383096,4095078347136⟩,⟨29512896480,282046626720⟩,⟨1016323200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24976 180 (5237-R)⟩
def p353:CachedProfile:=⟨⟨89917,648,21522⟩,⟨⟨⟨1109055768583682,32190316355661784334⟩,⟨686360250406591056,15157327904352⟩,⟨54225562752,4910938090634880⟩,⟨11712721554432,0⟩⟩,⟨⟨1099082492197560,251708032280340⟩,⟨1800991607328,15157300010544⟩,⟨54225562752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨1108381882002290,32172010089026518550⟩,⟨687036180347847330,15172254937532⟩,⟨54362728266,4923360485410290⟩,⟨11760470214878,0⟩⟩,⟨⟨1098425274083760,251427427857900⟩,⟨1801760069340,15172227016254⟩,⟨54362728266,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 90565 649 (21522-R)⟩
def p354:CachedProfile:=⟨⟨74181,373,18949⟩,⟨⟨⟨666011978247450,15834765963819539550⟩,⟨235729620115421400,6323741737600⟩,⟨15818967300,1179367288084200⟩,⟨1966824934300,0⟩⟩,⟨⟨659204878461900,160626689920200⟩,⟨803628984900,6323727600900⟩,⟨15818967300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨665508450158360,15823637840681955344⟩,⟨236199454104774864,6336345651328⟩,⟨15892990872,1184886041471088⟩,⟨1981326195376,0⟩⟩,⟨⟨658715346718212,160406374798368⟩,⟨804678275808,6336331486452⟩,⟨15892990872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 74554 374 (18949-R)⟩
def p355:CachedProfile:=⟨⟨83586,511,18794⟩,⟨⟨⟨830750558887410,22482139465763726070⟩,⟨407547089203333590,9692335135140⟩,⟨29446615170,2476371995951490⟩,⟨5015740117290,0⟩⟩,⟨⟨824108732356560,178235129659860⟩,⟨1083013083180,9692315926650⟩,⟨29446615170,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨830130077716854,22466330373430463322⟩,⟨408062194733021184,9704585474048⟩,⟨29541531648,2484354187001856⟩,⟨5041754734592,0⟩⟩,⟨⟨823502019697644,177988647407844⟩,⟨1083631847424,9704566241280⟩,⟨29541531648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 84097 512 (18794-R)⟩
def p356:CachedProfile:=⟨⟨25648,193,5079⟩,⟨⟨⟨21009568227160,175989619378700920⟩,⟨3928235447358960,304034444000⟩,⟨1135349520,29338566946320⟩,⟨73040819120,0⟩⟩,⟨⟨20878260778320,4000391460720⟩,⟨29877928560,304032483120⟩,⟨1135349520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨20970030508834,175674286904641822⟩,⟨3941593360961124,305068317400⟩,⟨1145112936,29590863379176⟩,⟨74050636528,0⟩⟩,⟨⟨20839418881512,3986228008620⟩,⟨29926405080,305066349852⟩,⟨1145112936,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 10=>⟨⟨⟨20965638189990,175639251510249930⟩,⟨3940816067880120,305008158000⟩,⟨1144887120,29585028067920⟩,⟨74036033760,0⟩⟩,⟨⟨20835103723980,3984655842180⟩,⟨29914602120,305006190840⟩,⟨1144887120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25841 194 (5079-R)⟩
def p357:CachedProfile:=⟨⟨125580,801,23084⟩,⟨⟨⟨2273834535840270,93482481090017323890⟩,⟨1772060216362931790,28043209689300⟩,⟨88868154510,11231246235128310⟩,⟨23727797254170,0⟩⟩,⟨⟨2261527372501740,404086165844040⟩,⟨2561089236840,28043172707130⟩,⟨88868154510,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 18=>⟨⟨⟨2271965755827042,93408926400521195310⟩,⟨1772889073886544372,28056326589720⟩,⟨89020720008,11250527615331048⟩,⟨23798205815472,0⟩⟩,⟨⟨2259687350474136,403456244014692⟩,⟨2560289186664,28056289590252⟩,⟨89020720008,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 126381 802 (23084-R)⟩
def p358:CachedProfile:=⟨⟨115633,811,24876⟩,⟨⟨⟨2100869839453000,78939810260473490944⟩,⟨1641367899008144016,28191598941992⟩,⟨98172751902,11431627922476488⟩,⟨26539367264174,0⟩⟩,⟨⟨2085469775789472,432361405823328⟩,⟨3011276666232,28191558591498⟩,⟨98172751902,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2099600970198256,78894739078135579816⟩,⟨1642466927462124960,28210475554016⟩,⟨98359619232,11453387501851008⟩,⟨26622670272128,0⟩⟩,⟨⟨2084226886112940,431874893941584⟩,⟨3011597110032,28210435176504⟩,⟨98359619232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 116444 812 (24876-R)⟩
def p359:CachedProfile:=⟨⟨14162,104,3232⟩,⟨⟨⟨4117103447784,18884312968375632⟩,⟨410590150626240,57562918400⟩,⟨209808768,2993131884288⟩,⟨7273370624,0⟩⟩,⟨⟨4083239854836,894397397376⟩,⟨6520210944,57562245936⟩,⟨209808768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4097821507680,18801123548743320⟩,⟨412742983620240,57864744000⟩,⟨212936850,3037757102100⟩,⟨7452789750,0⟩⟩,⟨⟨4064395231416,886666880232⟩,⟨6526007460,57864068010⟩,⟨212936850,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 14266 105 (3232-R)⟩
def p360:CachedProfile:=⟨⟨2491,15,598⟩,⟨⟨⟨23654198520,18992715037320⟩,⟨338621217120,270268800⟩,⟨808650,2026476900⟩,⟨4043250,0⟩⟩,⟨⟨23436991536,5385925272⟩,⟨32238180,270250830⟩,⟨808650,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨23052926520,18539983322640⟩,⟨352752416640,281548800⟩,⟨898560,2251791360⟩,⟨4792320,0⟩⟩,⟨⟨22850476740,5136899040⟩,⟨32797440,281530080⟩,⟨898560,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2506 16 (598-R)⟩
def p361:CachedProfile:=⟨⟨17692,115,5487⟩,⟨⟨⟨11268097532272,62888018444221936⟩,⟨1200769756438560,134865295040⟩,⟨435472800,7754464149600⟩,⟨16693124000,0⟩⟩,⟨⟨11102673939168,3217296392352⟩,⟨20777732640,134864032800⟩,⟨435472800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨11235152579434,62720669216896390⟩,⟨1208121301331280,135691000928⟩,⟨441948864,7869783421248⟩,⟨17088689408,0⟩⟩,⟨⟨11070990915852,3200901060084⟩,⟨20851604592,135689730960⟩,⟨441948864,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 17807 116 (5487-R)⟩
def p362:CachedProfile:=⟨⟨52267,355,10968⟩,⟨⟨⟨188846442998584,3211228067545689520⟩,⟨64697095029575400,2458948810640⟩,⟨8294209350,436457884415700⟩,⟨981481439750,0⟩⟩,⟨⟨187525750520892,37985082930144⟩,⟨256256022960,2458941022650⟩,⟨8294209350,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨188588602523440,3207074123404620280⟩,⟨64796532641184960,2462728170560⟩,⟨8330357280,438360060788160⟩,⟨988535730560,0⟩⟩,⟨⟨187272957854640,37888177833240⟩,⟨256322285520,2462720370600⟩,⟨8330357280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 52622 356 (10968-R)⟩
def p363:CachedProfile:=⟨⟨39277,254,7942⟩,⟨⟨⟨76982830947074,985368041468918042⟩,⟨18916881582216540,957072086360⟩,⟨3074703528,121546105165368⟩,⟨260324898704,0⟩⟩,⟨⟨76481195341356,14962477016916⟩,⟨96138958344,957068051316⟩,⟨3074703528,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨76828016371064,983484701319002552⟩,⟨18955492801419600,959025583200⟩,⟨3093109200,122273699785200⟩,⟨262914282000,0⟩⟩,⟨⟨76329215223216,14906014889616⟩,⟨96153241680,959021539920⟩,⟨3093109200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 39531 255 (7942-R)⟩
def p364:CachedProfile:=⟨⟨17066,112,3343⟩,⟨⟨⟨6107897790896,34028357922314096⟩,⟨663117636572160,77206700032⟩,⟨251682816,4323407413248⟩,⟨9396158464,0⟩⟩,⟨⟨6070411534176,1152196347456⟩,⟨7512282624,77205950976⟩,⟨251682816,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨6078834242216,33874041796229456⟩,⟨666037192981080,77546631488⟩,⟨255048006,4381214647068⟩,⟨9606808226,0⟩⟩,⟨⟨6041849251956,1141881302016⟩,⟨7511502336,77545879134⟩,⟨255048006,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 17178 113 (3343-R)⟩
def p365:CachedProfile:=⟨⟨1713,10,467⟩,⟨⟨⟨8853407316,4839935906052⟩,⟨83388137040,96801120⟩,⟨280800,483818400⟩,⟨936000,0⟩⟩,⟨⟨8749728936,2259431928⟩,⟨13113360,96791760⟩,⟨280800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨8538407646,4680364785582⟩,⟨88786087434,103068372⟩,⟨328878,566656794⟩,⟨1205886,0⟩⟩,⟨⟨8444296896,2116767528⟩,⟨13513896,103058406⟩,⟨328878,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨8517517380,4669747085172⟩,⟨88590031992,102840848⟩,⟨328152,565405896⟩,⟨1203224,0⟩⟩,⟨⟨8424022536,2107421976⟩,⟨13454232,102830904⟩,⟨328152,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1723 11 (467-R)⟩
def p366:CachedProfile:=⟨⟨25390,168,5527⟩,⟨⟨⟨22511245134216,185520147056292072⟩,⟨3639901634917632,284837231616⟩,⟨936133632,23925703366656⟩,⟨52423483392,0⟩⟩,⟨⟨22342094719056,4685280701088⟩,⟨30797682048,284835374208⟩,⟨936133632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨22445597283096,185009162542259952⟩,⟨3651632035394616,285755196688⟩,⟨944740758,24145684292964⟩,⟨53220396034,0⟩⟩,⟨⟨22277818720716,4659886272288⟩,⟨30813083184,285753333294⟩,⟨944740758,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25558 169 (5527-R)⟩
def p367:CachedProfile:=⟨⟨2585,16,495⟩,⟨⟨⟨20751711984,17523339206832⟩,⟨322178950656,247761920⟩,⟨761856,1981587456⟩,⟨4063232,0⟩⟩,⟨⟨20627599392,3831585120⟩,⟨23569920,247746048⟩,⟨761856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨20044884960,16952365626720⟩,⟨331271144640,254755200⟩,⟨832320,2164864320⟩,⟨4716480,0⟩⟩,⟨⟨19932256320,3588131520⟩,⟨23451840,254738880⟩,⟨832320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2601 17 (495-R)⟩
def p368:CachedProfile:=⟨⟨43018,250,10475⟩,⟨⟨⟨123425237571588,1709270192071780164⟩,⟨29418820122636000,1359847656000⟩,⟨3928500000,169978338000000⟩,⟨327375000000,0⟩⟩,⟨⟨122274845372952,28488369448800⟩,⟨164604150000,1359842418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨123296462318638,1707604113199843714⟩,⟨29508300647834184,1363983794384⟩,⟨3956210796,171177328721328⟩,⟨331002969932,0⟩⟩,⟨⟨122149359822012,28434004937520⟩,⟨164947195140,1363978540452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43268 251 (10475-R)⟩
def p369:CachedProfile:=⟨⟨26018,132,5143⟩,⟨⟨⟨21786932224264,184677651813730408⟩,⟨2785967594137728,213078142464⟩,⟨537774336,14062798886400⟩,⟨23662070784,0⟩⟩,⟨⟨21650602083408,4150882384800⟩,⟨20952828864,213076784448⟩,⟨537774336,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21741940205074,184314554068371958⟩,⟨2801616341673912,214275006176⟩,⟨544891956,14248924649400⟩,⟨24156876716,0⟩⟩,⟨⟨21606402661548,4134757771800⟩,⟨21029551956,214273640532⟩,⟨544891956,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26150 133 (5143-R)⟩
def p370:CachedProfile:=⟨⟨25891,134,5237⟩,⟨⟨⟨22005640823022,185418725273644914⟩,⟨2852395451395848,219206486736⟩,⟨564321168,14686458397200⟩,⟨25206345504,0⟩⟩,⟨⟨21861709911900,4283414046900⟩,⟨22054850424,219205082952⟩,⟨564321168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21960893896172,185060427995803724⟩,⟨2868195680019720,220420740240⟩,⟨571681800,14878018845000⟩,⟨25725681000,0⟩⟩,⟨⟨21817784825160,4267072949400⟩,⟨22134672360,220419328680⟩,⟨571681800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26025 135 (5237-R)⟩
def p371:CachedProfile:=⟨⟨8268,2,2546⟩,⟨⟨⟨1127911523904,2923891556763672⟩,⟨2090516227488,505569312⟩,⟨61128,505528560⟩,⟨40752,0⟩⟩,⟨⟨1111359447072,321768928440⟩,⟨77815944,505559124⟩,⟨61128,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1122838429144,2911917873435952⟩,⟨3123461789352,755376528⟩,⟨136998,1132973460⟩,⟨136998,0⟩⟩,⟨⟨1106480269212,319246743840⟩,⟨115808976,755361306⟩,⟨136998,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8270 3 (2546-R)⟩
def p372:CachedProfile:=⟨⟨66144,16,20955⟩,⟨⟨⟨596386906998740,12330555138324718100⟩,⟨8805920780117760,266200882688⟩,⟨32188416,2129585602560⟩,⟨171671552,0⟩⟩,⟨⟨587182102504920,174318227740800⟩,⟨42156766080,266200212096⟩,⟨32188416,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 66160 17 (20955-R)⟩
def p373:CachedProfile:=⟨⟨24434,175,5396⟩,⟨⟨⟨20397470534910,161722564446820314⟩,⟨3431921842840050,278918579100⟩,⟨991698750,24404714538750⟩,⟨57849093750,0⟩⟩,⟨⟨20240061449412,4300011090648⟩,⟨30578322600,278916690150⟩,⟨991698750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20356772205170,161418198980851574⟩,⟨3445137430638816,279992643392⟩,⟨1001206272,24638685147648⟩,⟨58737434624,0⟩⟩,⟨⟨20200235606352,4284089559828⟩,⟨30639187392,279990747168⟩,⟨1001206272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20344565858696,161326896147198056⟩,⟨3443218812473088,279836716544⟩,⟨1000648704,24624963956736⟩,⟨58704723968,0⟩⟩,⟨⟨20188290375408,4279318859088⟩,⟨30605068032,279834821376⟩,⟨1000648704,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24609 176 (5396-R)⟩
def p374:CachedProfile:=⟨⟨24640,172,5396⟩,⟨⟨⟨20722350516504,165736523064817152⟩,⟨3428966746263744,276398417568⟩,⟨957989088,23769625251456⟩,⟨54924707712,0⟩⟩,⟨⟨20564939239824,4335481944864⟩,⟨30054122784,276396561000⟩,⟨957989088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20681050222744,165424720079038552⟩,⟨3442512080713896,277490274152⟩,⟨967365138,24002263804056⟩,⟨55784722958,0⟩⟩,⟨⟨20524511436804,4319429077104⟩,⟨30116928516,277488410250⟩,⟨967365138,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24812 173 (5396-R)⟩
def p375:CachedProfile:=⟨⟨24734,167,5237⟩,⟨⟨⟨20206629106254,162511118191000962⟩,⟨3254423956650900,261391599720⟩,⟨876495492,21825614246292⟩,⟨48791582388,0⟩⟩,⟨⟨20062709970156,4098416644836⟩,⟨27486268812,261389850228⟩,⟨876495492,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20165316718764,162196555117897452⟩,⟨3267661111485120,262454801280⟩,⟨885330432,22045613087232⟩,⟨49578504192,0⟩⟩,⟨⟨20022219400296,4082781306936⟩,⟨27545370048,262453044672⟩,⟨885330432,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20152926061950,162102192607180650⟩,⟨3265785987433200,262304196000⟩,⟨884822400,22032962582400⟩,⟨49550054400,0⟩⟩,⟨⟨20010074676900,4078096532400⟩,⟨27513763200,262302440400⟩,⟨884822400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24901 168 (5237-R)⟩
def p376:CachedProfile:=⟨⟨25019,157,5143⟩,⟨⟨⟨20243953745480,164876752008242600⟩,⟨3071371643527776,243994528960⟩,⟨760766736,19153063345536⟩,⟨39813459184,0⟩⟩,⟨⟨20107633625136,3996275905152⟩,⟨24921167664,243992913744⟩,⟨760766736,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20201961295650,164552148058524390⟩,⟨3084925607733744,245071284640⟩,⟨768991056,19360118825856⟩,⟨40500195616,0⟩⟩,⟨⟨20066433753156,3980751880032⟩,⟨24982475256,245069662296⟩,⟨768991056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25176 158 (5143-R)⟩
def p377:CachedProfile:=⟨⟨33072,8,10224⟩,⟨⟨⟨72481490912800,751238554358694400⟩,⟨537085800998400,32471982400⟩,⟨3926400,129885312000⟩,⟨10470400,0⟩⟩,⟨⟨71411993377200,20749178592000⟩,⟨5017939200,32471818800⟩,⟨3926400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 33080 9 (10224-R)⟩
def p378:CachedProfile:=⟨⟨24991,151,5143⟩,⟨⟨⟨20191149844744,164212512044796520⟩,⟨2946021205528800,234352985728⟩,⟨703730064,17693181269088⟩,⟨35421079888,0⟩⟩,⟨⟨20054830074192,3990878964384⟩,⟨23968766352,234351432240⟩,⟨703730064,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20149260046354,163889199406778230⟩,⟨2959766156389440,235446390016⟩,⟨711695616,17893451177472⟩,⟨36059244544,0⟩⟩,⟨⟨20013732852972,3975375904344⟩,⟨24033773664,235444829280⟩,⟨711695616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25142 152 (5143-R)⟩
def p379:CachedProfile:=⟨⟨25344,140,5111⟩,⟨⟨⟨20588228473320,169899565840273224⟩,⟨2788766544090240,218866394880⟩,⟨601171200,15320246860800⟩,⟨28054656000,0⟩⟩,⟨⟨20454430619952,3994988862528⟩,⟨21947042880,218864963520⟩,⟨601171200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25484 141 (5111-R)⟩
def p380:CachedProfile:=⟨⟨25344,140,5095⟩,⟨⟨⟨20519628628408,169361404130173528⟩,⟨2780037873325440,218181367040⟩,⟨599289600,15272296166400⟩,⟨27966848000,0⟩⟩,⟨⟨20387081704080,3970017804480⟩,⟨21809860800,218179940160⟩,⟨599289600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25484 141 (5095-R)⟩
def p381:CachedProfile:=⟨⟨25354,138,5095⟩,⟨⟨⟨20532098091960,169520313311161176⟩,⟨2742043787525952,215132002176⟩,⟨582289344,14843719957248⟩,⟨26785309824,0⟩⟩,⟨⟨20399551086096,3971264082240⟩,⟨21498291360,215130595680⟩,⟨582289344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25492 139 (5095-R)⟩
def p382:CachedProfile:=⟨⟨25496,134,5143⟩,⟨⟨⟨20955879106824,173919419492372328⟩,⟨2716820974086336,212005392128⟩,⟨554193984,14203991809920⟩,⟨24753997952,0⟩⟩,⟨⟨20819554315728,4068340937760⟩,⟨21270295968,212004013536⟩,⟨554193984,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25630 135 (5143-R)⟩
def p383:CachedProfile:=⟨⟨24728,149,5396⟩,⟨⟨⟨20826940220814,167035751113283682⟩,⟨2986025570999478,240065403396⟩,⟨718912782,17884393277814⟩,⟨35706001506,0⟩⟩,⟨⟨20669528242524,4346839607544⟩,⟨26035257528,240063795090⟩,⟨718912782,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20785446134754,166721540770221582⟩,⟨3000496030818300,241228782600⟩,⟨727245000,18091673865000⟩,⟨36362250000,0⟩⟩,⟨⟨20628906648504,4330744686084⟩,⟨26112943800,241227166500⟩,⟨727245000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24877 150 (5396-R)⟩
def p384:CachedProfile:=⟨⟨24985,141,5079⟩,⟨⟨⟨19898805145160,161835774312254120⟩,⟨2713237269801120,215972745600⟩,⟨605972880,15225674582880⟩,⟨28480725360,0⟩⟩,⟨⟨19767504960720,3889703797920⟩,⟨21827916720,215971313040⟩,⟨605972880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19857061649490,161513268778546230⟩,⟨2727101103114960,217076308800⟩,⟨613388880,15412008998880⟩,⟨29033740320,0⟩⟩,⟨⟨19726534433580,3874403571480⟩,⟨21896255160,217074868920⟩,⟨613388880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19836195606680,161352027605698160⟩,⟨2724411611141520,216862229600⟩,⟨612783960,15396809778960⟩,⟨29005107440,0⟩⟩,⟨⟨19706053734060,3866764764960⟩,⟨21853084320,216860791140⟩,⟨612783960,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25126 142 (5079-R)⟩
def p385:CachedProfile:=⟨⟨25002,139,5237⟩,⟨⟨⟨20584091957454,167233356580845762⟩,⟨2761237974174660,219662339400⟩,⟨607220388,15266127774708⟩,⟨28134544644,0⟩⟩,⟨⟨20440170307116,4137917869476⟩,⟨22877792604,219660883236⟩,⟨607220388,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25141 140 (5237-R)⟩
def p386:CachedProfile:=⟨⟨25002,139,5079⟩,⟨⟨⟨19921787827160,162124588923396920⟩,⟨2677946142832080,213036404000⟩,⟨588904080,14805637475280⟩,⟨27285889040,0⟩⟩,⟨⟨19790487490320,3892025916720⟩,⟨21518300880,213034991760⟩,⟨588904080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19879999089990,161801514847863930⟩,⟨2691902384917200,214146660000⟩,⟨596232000,14989868712000⟩,⟨27824160000,0⟩⟩,⟨⟨19749471721980,3876716556180⟩,⟨21587857200,214145240400⟩,⟨596232000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19859110426430,161639989404116810⟩,⟨2689247606291400,213935470000⟩,⟨595644000,14975085804000⟩,⟨27796720000,0⟩⟩,⟨⟨19728968401860,3869073189360⟩,⟨21545294400,213934051800⟩,⟨595644000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25141 140 (5079-R)⟩
def p387:CachedProfile:=⟨⟨25078,138,5143⟩,⟨⟨⟨20306167339080,165660510986391720⟩,⟨2708262234788544,214807267200⟩,⟨587774016,14821309587456⟩,⟨27037604736,0⟩⟩,⟨⟨20169846807216,4002625247232⟩,⟨21905230176,214805847456⟩,⟨587774016,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20264053945250,165334383374825510⟩,⟨2722584190915032,215943227600⟩,⟨595164084,15007657542144⟩,⟨27575935892,0⟩⟩,⟨⟨20128525992036,3987076557312⟩,⟨21978253548,215941800348⟩,⟨595164084,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25216 139 (5143-R)⟩
def p388:CachedProfile:=⟨⟨25078,138,5079⟩,⟨⟨⟨20036906977160,163573838603250920⟩,⟨2674566365319360,212134704000⟩,⟨580461120,14636907601920⟩,⟨26701211520,0⟩⟩,⟨⟨19905605878320,3903636510720⟩,⟨21363492960,212133301920⟩,⟨580461120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19994891627490,163247911628387430⟩,⟨2688644150613720,213251298000⟩,⟨587744820,14820573381120⟩,⟨27232176660,0⟩⟩,⟨⟨19864363498980,3888281479680⟩,⟨21433658220,213249888540⟩,⟨587744820,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨19973889657680,163084959735042560⟩,⟨2685992585540640,213040991000⟩,⟨587165190,14805957431040⟩,⟨27205320470,0⟩⟩,⟨⟨19843746873360,3880615311360⟩,⟨21391399440,213039582930⟩,⟨587165190,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25216 139 (5079-R)⟩
def p389:CachedProfile:=⟨⟨25078,138,5111⟩,⟨⟨⟨20171458645992,164617013972677320⟩,⟨2691414298358208,213470985600⟩,⟨584117568,14729108594688⟩,⟨26869408128,0⟩⟩,⟨⟨20037663532656,3952975951872⟩,⟨21633513696,213469574688⟩,⟨584117568,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25216 139 (5111-R)⟩
def p390:CachedProfile:=⟨⟨25152,137,5079⟩,⟨⟨⟨20149285589080,164992745183516920⟩,⟨2670580913021040,211207156960⟩,⟨572079120,14467308865680⟩,⟨26124946480,0⟩⟩,⟨⟨20017983748560,3914937488880⟩,⟨21208685040,211205765040⟩,⟨572079120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20107049021670,164664025041050730⟩,⟨2684778698735640,212330018160⟩,⟨579318480,14650385040720⟩,⟨26648650080,0⟩⟩,⟨⟨19976520152940,3899538005220⟩,⟨21279459240,212328618840⟩,⟨579318480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨20085936442990,164499676563970210⟩,⟨2682130946049180,212120619720⟩,⟨578747160,14635936929240⟩,⟨26622369360,0⟩⟩,⟨⟨19955792919180,3891849643440⟩,⟨21237504480,212119221780⟩,⟨578747160,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25289 138 (5079-R)⟩
def p391:CachedProfile:=⟨⟨25228,134,5079⟩,⟨⟨⟨20261989056840,166419867043120680⟩,⟨2627202906152640,207178493440⟩,⟨547298880,13880594194560⟩,⟨24446016640,0⟩⟩,⟨⟨20130686474640,3926238467040⟩,⟨20744261280,207177132000⟩,⟨547298880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20219530632210,166088337561242070⟩,⟨2641598562119400,208313726400⟩,⟨554404500,14060806929000⟩,⟨24948202500,0⟩⟩,⟨⟨20089001023260,3910794530760⟩,⟨20816862300,208312357500⟩,⟨554404500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨20198307124920,165922584414521040⟩,⟨2638993394305800,208108288800⟩,⟨553857750,14046940255500⟩,⟨24923598750,0⟩⟩,⟨⟨20068162861620,3903083975520⟩,⟨20775819600,208106921250⟩,⟨553857750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25362 135 (5079-R)⟩
def p392:CachedProfile:=⟨⟨24136,152,5079⟩,⟨⟨⟨18636626841480,146242121154019560⟩,⟨2733062336881920,225056842240⟩,⟨704209920,17103850536960⟩,⟨35679969280,0⟩⟩,⟨⟨18505335171120,3759974760960⟩,⟨23530803840,225055297920⟩,⟨704209920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18597367948770,145950312297785190⟩,⟨2745627478069320,226091539440⟩,⟨712101780,17295528032640⟩,⟨36317190780,0⟩⟩,⟨⟨18466849230180,3745184826240⟩,⟨23592443940,226089988020⟩,⟨712101780,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨18573819915096,145775241821460216⟩,⟨2742378158996640,225823975488⟩,⟨711259056,17275059952128⟩,⟨36274211856,0⟩⟩,⟨⟨18443763507216,3736324855296⟩,⟨23536631376,225822425904⟩,⟨711259056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24288 153 (5079-R)⟩
def p393:CachedProfile:=⟨⟨24236,151,5079⟩,⟨⟨⟨18783508650840,148029473328934680⟩,⟨2737260209298960,224487496160⟩,⟨694974480,16948342643760⟩,⟨34980382160,0⟩⟩,⟨⟨18652215974640,3775300745040⟩,⟨23375995920,224485962000⟩,⟨694974480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18743960620710,147734146002675570⟩,⟨2749963676222880,225529337280⟩,⟨702823680,17139761084160⟩,⟨35609733120,0⟩⟩,⟨⟨18613440898260,3760450525260⟩,⟨23438244960,225527796000⟩,⟨702823680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨18720239104584,147556964444449800⟩,⟨2746709225919360,225262438656⟩,⟨701991936,17119477343232⟩,⟨35567591424,0⟩⟩,⟨⟨18590181694032,3751554440304⟩,⟨23382797184,225260899200⟩,⟨701991936,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24387 152 (5079-R)⟩
def p394:CachedProfile:=⟨⟨39767,250,10158⟩,⟨⟨⟨102854053953954,1312708393186972830⟩,⟨24402638349292500,1219618427000⟩,⟨3809625000,152449763625000⟩,⟨317468750000,0⟩⟩,⟨⟨101804984839272,24777355182444⟩,⟨154792683000,1219613347500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨102742505201214,1311384795641529690⟩,⟨24476131805090490,1223291568588⟩,⟨3836382894,153520534269198⟩,⟨320977368798,0⟩⟩,⟨⟨101696529592452,24728597669304⟩,⟨155106030312,1223286473790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40017 251 (10158-R)⟩
def p395:CachedProfile:=⟨⟨43768,250,10174⟩,⟨⟨⟨123559398377800,1746392852356642600⟩,⟨29572691306400000,1343669800000⟩,⟨3815625000,167956181250000⟩,⟨317968750000,0⟩⟩,⟨⟨122505285553200,27340579008600⟩,⟨155280675000,1343664712500⟩,⟨3815625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨123427627087840,1744644907608615280⟩,⟨29661801439095480,1347718636960⟩,⟨3842430990,169136127317820⟩,⟨321483392830,0⟩⟩,⟨⟨122376617604060,27286862082480⟩,⟨155595492360,1347713534130⟩,⟨3842430990,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44018 251 (10174-R)⟩
def p396:CachedProfile:=⟨⟨24705,157,5143⟩,⟨⟨⟨19759007754504,158810302466895720⟩,⟨2995237151655840,240951462016⟩,⟨760766736,18914182590432⟩,⟨39813459184,0⟩⟩,⟨⟨19622690864592,3946433569824⟩,⟨24921167664,240949846800⟩,⟨760766736,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19717958045714,158497491964011830⟩,⟨3008455131907920,242014788544⟩,⟨768991056,19118655634272⟩,⟨40500195616,0⟩⟩,⟨⟨19582433727372,3931103163384⟩,⟨24982475256,242013166200⟩,⟨768991056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24862 158 (5143-R)⟩
def p397:CachedProfile:=⟨⟨24534,163,5237⟩,⟨⟨⟨19888632305262,158568133466672946⟩,⟨3124641597070212,253040635368⟩,⟨835010532,20622255108804⟩,⟨45368905572,0⟩⟩,⟨⟨19744715306268,4064840603892⟩,⟨26827915068,253038927780⟩,⟨835010532,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19847927013612,158261098174709196⟩,⟨3137809144068576,254106981824⟩,⟨843673728,20836210060416⟩,⟨46120830464,0⟩⟩,⟨⟨19704831828168,4049333357592⟩,⟨26889527904,254105267040⟩,⟨843673728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24697 164 (5237-R)⟩
def p398:CachedProfile:=⟨⟨24400,167,5063⟩,⟨⟨⟨18987981697224,150833713066307400⟩,⟨3062477852604720,249318970656⟩,⟨847379376,20817569130192⟩,⟨47170785264,0⟩⟩,⟨⟨18857922463632,3779244594864⟩,⟨25690310064,249317279280⟩,⟨847379376,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18947929268534,150531964332377810⟩,⟨3074732181491040,250316614464⟩,⟨855864576,21026025038592⟩,⟨47928416256,0⟩⟩,⟨⟨18818638128612,3764331934524⟩,⟨25742164896,250314916320⟩,⟨855864576,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24567 168 (5063-R)⟩
def p399:CachedProfile:=⟨⟨24518,166,5079⟩,⟨⟨⟨19227738892680,153479189304553320⟩,⟨3082913691635520,249793028480⟩,⟨839906880,20732261425920⟩,⟨46474847360,0⟩⟩,⟨⟨19096443198960,3821278697280⟩,⟨25698114720,249791341920⟩,⟨839906880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19187316393570,153173134010245830⟩,⟨3095380072919160,250803125040⟩,⟨848383380,20941495351920⟩,⟨47226674820,0⟩⟩,⟨⟨19056793659540,3806247622320⟩,⟨25751229660,250801431660⟩,⟨848383380,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24684 167 (5079-R)⟩
def p400:CachedProfile:=⟨⟨25057,147,5237⟩,⟨⟨⟨20683775884986,168487991579665566⟩,⟨2934811294624440,232886885616⟩,⟨679127652,17116733341008⟩,⟨33277254948,0⟩⟩,⟨⟨20539853574660,4148286940944⟩,⟨24194500092,232885345644⟩,⟨679127652,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20641552564356,168162017714355396⟩,⟨2949134865900480,234023515264⟩,⟨687084672,17317282073088⟩,⟨33896177152,0⟩⟩,⟨⟨20498452077720,4132461349344⟩,⟨24266159328,234021967776⟩,⟨687084672,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25204 148 (5237-R)⟩
def p401:CachedProfile:=⟨⟨29358,210,5971⟩,⟨⟨⟨32392799461820,310040159062555292⟩,⟨6578701411151520,444991874880⟩,⟨1580191200,46723093401600⟩,⟨110613384000,0⟩⟩,⟨⟨32179527535176,6326158519296⟩,⟨44930103120,444989366640⟩,⟨1580191200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨32335001289030,309514615387084602⟩,⟨6598960043125032,446362205168⟩,⟨1592605212,47090150908416⟩,⟨112013233244,0⟩⟩,⟨⟨32122797867996,6304988422656⟩,⟨44992984212,446359689204⟩,⟨1592605212,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29568 211 (5971-R)⟩
def p402:CachedProfile:=⟨⟨25344,140,5079⟩,⟨⟨⟨20451067916680,168823322330729320⟩,⟨2771309203420800,217496339200⟩,⟨597408000,15224345472000⟩,⟨27879040000,0⟩⟩,⟨⟨20319764094960,3945125033280⟩,⟨21673108800,217494916800⟩,⟨597408000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20408237289570,168487061563429830⟩,⟨2785609883632680,218618683920⟩,⟨604780020,15412214029680⟩,⟨28424660940,0⟩⟩,⟨⟨20277706443540,3929606806320⟩,⟨21742056180,218617254180⟩,⟨604780020,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25484 141 (5079-R)⟩
def p403:CachedProfile:=⟨⟨24250,171,4920⟩,⟨⟨⟨18205478926334,143935240589473802⟩,⟨3011166558634626,246607352460⟩,⟨863369766,21084353055486⟩,⟨49212076662,0⟩⟩,⟨⟨18086118880452,3547587874320⟩,⟨24840814320,246605669478⟩,⟨863369766,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18166069585074,143639175260055462⟩,⟨3022620821197272,247545437520⟩,⟨871722144,21288326478624⟩,⟨49978736256,0⟩⟩,⟨⟨18047434842912,3533182903260⟩,⟨24884626320,247543748136⟩,⟨871722144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24421 172 (4920-R)⟩
def p404:CachedProfile:=⟨⟨24128,176,4761⟩,⟨⟨⟨17417710513910,137247005800156394⟩,⟨2970406066590336,244440393472⟩,⟨885046272,21510164594688⟩,⟨51922714624,0⟩⟩,⟨⟨17309538212412,3306104520768⟩,⟨23941507392,244438717248⟩,⟨885046272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨17378873907120,136955554350881904⟩,⟨2981010103232832,245313028224⟩,⟨893252448,21709607496192⟩,⟨52701894432,0⟩⟩,⟨⟨17271380773152,3292232283648⟩,⟨23976510624,245311346016⟩,⟨893252448,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨17363343257316,136838981378884836⟩,⟨2978500795130160,245106535776⟩,⟨892500552,21691333415808⟩,⟨52657532568,0⟩⟩,⟨⟨17256120991800,3286691554944⟩,⟨23936158872,245104854984⟩,⟨892500552,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24304 177 (4761-R)⟩
def p405:CachedProfile:=⟨⟨41768,250,10190⟩,⟨⟨⟨113248618374888,1522839310699663464⟩,⟨26988815679696000,1284636696000⟩,⟨3821625000,160577039250000⟩,⟨318468750000,0⟩⟩,⟨⟨112189568268912,26180480479320⟩,⟨155769435000,1284631600500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 42018 251 (10190-R)⟩
def p406:CachedProfile:=⟨⟨2984,24,714⟩,⟨⟨⟨40656942040,39198387737080⟩,⟨931735696320,619544640⟩,⟨2471040,7432888320⟩,⟨19768320,0⟩⟩,⟨⟨40288136460,9213684480⟩,⟨73513440,619510320⟩,⟨2471040,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨40038314880,38639272181760⟩,⟨956981664000,636333000⟩,⟨2643750,7952400000⟩,⟨22031250,0⟩⟩,⟨⟨39684664320,8957583360⟩,⟨74448000,636297750⟩,⟨2643750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3008 25 (714-R)⟩
def p407:CachedProfile:=⟨⟨42768,250,10475⟩,⟨⟨⟨122069318415588,1680021022912144164⟩,⟨29079845571636000,1351990656000⟩,⟨3928500000,168996213000000⟩,⟨327375000000,0⟩⟩,⟨⟨120918931454952,28323765298800⟩,⟨164604150000,1351985418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨121941837472638,1678382864523297714⟩,⟨29168295065420184,1356102896384⟩,⟨3956210796,170188276022328⟩,⟨331002969932,0⟩⟩,⟨⟨120794740209012,28269714902520⟩,⟨164947195140,1356097642452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43018 251 (10475-R)⟩
def p408:CachedProfile:=⟨⟨25216,192,5079⟩,⟨⟨⟨20333174527880,167323379395990760⟩,⟨3778017684203520,297391165440⟩,⟨1123614720,28548802805760⟩,⟨71911342080,0⟩⟩,⟨⟨20201871478320,3933359631360⟩,⟨29723120640,297389214720⟩,⟨1123614720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20290575974370,166990071318501990⟩,⟨3790218964938120,298351613040⟩,⟨1133114580,28790175248640⟩,⟨72897037980,0⟩⟩,⟨⟨20160045898980,3917887683840⟩,⟨29760403140,298349656020⟩,⟨1133114580,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25408 193 (5079-R)⟩
def p409:CachedProfile:=⟨⟨25449,185,5111⟩,⟨⟨⟨20823418302120,172905151518735624⟩,⟨3728664773868960,290918603520⟩,⟨1049749200,26909270992800⟩,⟨64734534000,0⟩⟩,⟨⟨20689618915152,4018503551328⟩,⟨29001449520,290916712080⟩,⟨1049749200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20780078732530,172562911495444534⟩,⟨3741486232809456,291918970752⟩,⟨1059052752,27147758244768⟩,⟨65661270624,0⟩⟩,⟨⟨20647062097692,4002795548808⟩,⟨29044237032,291917072808⟩,⟨1059052752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25634 186 (5111-R)⟩
def p410:CachedProfile:=⟨⟨41768,250,10222⟩,⟨⟨⟨113637610080296,1527723455865956072⟩,⟨27073562230896000,1288670488000⟩,⟨3833625000,161081255250000⟩,⟨319468750000,0⟩⟩,⟨⟨112568557029936,26345161458648⟩,⟨156749259000,1288665376500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 42018 251 (10222-R)⟩
def p411:CachedProfile:=⟨⟨6243,45,1217⟩,⟨⟨⟨298034669646,607947739360962⟩,⟨13003577569080,4136181840⟩,⟨14798700,93054225600⟩,⟨221980500,0⟩⟩,⟨⟨296215385676,55924440768⟩,⟨400222620,4136072220⟩,⟨14798700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨294404992476,600884524989756⟩,⟨13139748770400,4179498176⟩,⟨15285984,96118267392⟩,⟨234385088,0⟩⟩,⟨⟨292647411336,54645687936⟩,⟨399761712,4179387408⟩,⟨15285984,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6288 46 (1217-R)⟩
def p412:CachedProfile:=⟨⟨4134,1,1286⟩,⟨⟨⟨142720554834,184804079965362⟩,⟨132052354434,63871236⟩,⟨7722,31930470⟩,⟨2574,0⟩⟩,⟨⟨140581475892,41062584420⟩,⟨9930492,63868662⟩,⟨7722,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 4135 2 (1286-R)⟩
def p413:CachedProfile:=⟨⟨24644,140,5095⟩,⟨⟨⟨19443704033208,155839526311706328⟩,⟨2629412425261440,212188471040⟩,⟨599289600,14852793446400⟩,⟨27966848000,0⟩⟩,⟨⟨19311164243280,3860968500480⟩,⟨21809860800,212187044160⟩,⟨599289600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19402960322258,155529750578658518⟩,⟨2642997243612456,213284746416⟩,⟨606688596,15036170163264⟩,⟨28514364012,0⟩⟩,⟨⟨19271198373060,3845828946240⟩,⟨21879514260,213283312164⟩,⟨606688596,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24784 141 (5095-R)⟩
def p414:CachedProfile:=⟨⟨66336,16,20676⟩,⟨⟨⟨590402466127544,12263454581548692032⟩,⟨8739183852125952,263419025024⟩,⟨31759872,2107331026944⟩,⟨169385984,0⟩⟩,⟨⟨581560367234184,170199907473024⟩,⟨41041694592,263418363360⟩,⟨31759872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 66352 17 (20676-R)⟩
def p415:CachedProfile:=⟨⟨24889,189,5095⟩,⟨⟨⟨19891942689528,161427052224833304⟩,⟨3634421614832736,289852407936⟩,⟨1092205296,27390324413088⟩,⟨68808933648,0⟩⟩,⟨⟨19759399903152,3906769208160⟩,⟨29443312080,289850481648⟩,⟨1092205296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25078 190 (5095-R)⟩
def p416:CachedProfile:=⟨⟨24986,187,5111⟩,⟨⟨⟨20104999036920,163779814129937112⟩,⟨3634633786245264,288775387296⟩,⟨1072569168,26999783666064⟩,⟨66856811472,0⟩⟩,⟨⟨19971204363216,3946235074416⟩,⟨29314978704,288773475408⟩,⟨1072569168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨20058872246958,163422988035766434⟩,⟨3646207376576712,289694930992⟩,⟨1081738464,27230602354272⟩,⟨67788943744,0⟩⟩,⟨⟨19925938422012,3929268673800⟩,⟨29345032800,289693013016⟩,⟨1081738464,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25173 188 (5111-R)⟩
def p417:CachedProfile:=⟨⟨25120,182,5079⟩,⟨⟨⟨20169332295240,165246288259879080⟩,⟨3551427427504320,280726001920⟩,⟨1009619520,25545393095040⟩,⟨61250250880,0⟩⟩,⟨⟨20038030322640,3916949991840⟩,⟨28175041440,280724152800⟩,⟨1009619520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25302 183 (5079-R)⟩
def p418:CachedProfile:=⟨⟨25032,184,5087⟩,⟨⟨⟨20070530227104,163834602511022112⟩,⟨3571704464348160,283291699200⟩,⟨1033555968,26062147289088⟩,⟨63391432704,0⟩⟩,⟨⟨19938608558016,3915942322176⟩,⟨28574452224,283289826816⟩,⟨1033555968,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25216 185 (5087-R)⟩
def p419:CachedProfile:=⟨⟨24710,181,5237⟩,⟨⟨⟨20190980057454,162316320753360762⟩,⟨3524417515102140,283190898600⟩,⟨1029612708,25628089914828⟩,⟨62119966716,0⟩⟩,⟨⟨20047061026116,4096770760476⟩,⟨29790506916,283189002444⟩,⟨1029612708,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20149697545964,162002129579309852⟩,⟨3537123590778960,284211855200⟩,⟨1039033632,25862586134112⟩,⟨63034707008,0⟩⟩,⟨⟨20006600332056,4081141701576⟩,⟨29840817552,284209952208⟩,⟨1039033632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24891 182 (5237-R)⟩
def p420:CachedProfile:=⟨⟨24710,181,5143⟩,⟨⟨⟨19803540669080,159364208416988120⟩,⟨3461168040574128,278108816800⟩,⟨1011135504,25168173830064⟩,⟨61005175408,0⟩⟩,⟨⟨19667223480816,3951036842832⟩,⟨28730772912,278106954672⟩,⟨1011135504,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19762404387750,159050321096179410⟩,⟨3473524675746216,279101695600⟩,⟨1020351696,25397574065136⟩,⟨61901336224,0⟩⟩,⟨⟨19626879771636,3935688554412⟩,⟨28777281624,279099826824⟩,⟨1020351696,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24891 182 (5143-R)⟩
def p421:CachedProfile:=⟨⟨24710,181,5111⟩,⟨⟨⟨19671958735992,158359880330952120⟩,⟨3439636313322096,276378746400⟩,⟨1004845392,25011606652272⟩,⟨60625671984,0⟩⟩,⟨⟨19538166945456,3902027459472⟩,⟨28374391152,276376895856⟩,⟨1004845392,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19630871630342,158046093953454770⟩,⟨3451873990072872,277362066800⟩,⟨1013991888,25239272084208⟩,⟨61515507872,0⟩⟩,⟨⟨19497862577076,3886774752492⟩,⟨28419629784,277360209672⟩,⟨1013991888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24891 182 (5111-R)⟩
def p422:CachedProfile:=⟨⟨24844,180,5237⟩,⟨⟨⟨20399626537146,164919948406928766⟩,⟨3542500958292000,283131080640⟩,⟨1018267200,25481118412800⟩,⟨61096032000,0⟩⟩,⟨⟨20255706112500,4118661022464⟩,⟨29625918480,283129194960⟩,⟨1018267200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20357945693316,164600786497179396⟩,⟨3555380753616240,284160495328⟩,⟨1027647048,25715839729152⟩,⟨62001371896,0⟩⟩,⟨⟨20214847088760,4102948452864⟩,⟨29676857016,284158602792⟩,⟨1027647048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25024 181 (5237-R)⟩
def p423:CachedProfile:=⟨⟨24797,179,5143⟩,⟨⟨⟨19934367249480,160995175644729000⟩,⟨3446340421613472,275974982720⟩,⟨988913424,24699101677824⟩,⟨59005167632,0⟩⟩,⟨⟨19798049186736,3964529194752⟩,⟨28413305808,275973141168⟩,⟨988913424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19892976639650,160678117650970790⟩,⟨3458856451854240,276977246400⟩,⟨998049600,24927286809600⟩,⟨59882976000,0⟩⟩,⟨⟨19757451150756,3949128493632⟩,⟨28461047760,276975398160⟩,⟨998049600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24976 180 (5143-R)⟩
def p424:CachedProfile:=⟨⟨24880,177,5143⟩,⟨⟨⟨20059452282264,162559755893851320⟩,⟨3429973285530480,273776457696⟩,⟨966938256,24228571880592⟩,⟨57049357104,0⟩⟩,⟨⟨19923133386192,3977386612464⟩,⟨28095838704,273774636720⟩,⟨966938256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20017818505574,162239656286720330⟩,⟨3442645973458680,274787985584⟩,⟨975993936,24455480054352⟩,⟨57908973536,0⟩⟩,⟨⟨19882292184972,3961935965124⟩,⟨28144813896,274786157880⟩,⟨975993936,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25057 178 (5143-R)⟩
def p425:CachedProfile:=⟨⟨44518,250,10166⟩,⟨⟨⟨127516132586400,1835161801594495272⟩,⟨30564962976078000,1365489102000⟩,⟨3812625000,170683596000000⟩,⟨317718750000,0⟩⟩,⟨⟨126464487672036,27762710990976⟩,⟨155036583000,1365484018500⟩,⟨3812625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 44768 251 (10166-R)⟩
def p426:CachedProfile:=⟨⟨83198,711,21502⟩,⟨⟨⟨958103063760946,25621306068515895046⟩,⟨645861875425436430,15394369185828⟩,⟨65221308378,5472654764689602⟩,⟨15457450085586,0⟩⟩,⟨⟨948157844076480,232775735825724⟩,⟨1972417120596,15394338608562⟩,⟨65221308378,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨957611292669166,25609092657136285426⟩,⟨646469477379043440,15408851658656⟩,⟨65374484352,5485507607491968⟩,⟨15515544286208,0⟩⟩,⟨⟨947679938723340,232559275778424⟩,⟨1973354519232,15408821052624⟩,⟨65374484352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 83909 712 (21502-R)⟩
def p427:CachedProfile:=⟨⟨25269,227,6731⟩,⟨⟨⟨27783134528292,225213424822376100⟩,⟨5960384952830352,467557057440⟩,⟨2081359368,53066338446528⟩,⟨157489525512,0⟩⟩,⟨⟨27477788827896,6931815561792⟩,⟨61716431304,467554001112⟩,⟨2081359368,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨27737342923342,224869739713269250⟩,⟨5977749157692768,468919191360⟩,⟨2096618688,53455390069248⟩,⟨159343020288,0⟩⟩,⟨⟨27433355039916,6911235700512⟩,⟨61804272816,468916126128⟩,⟨2096618688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25496 228 (6731-R)⟩
def p428:CachedProfile:=⟨⟨5043,40,1273⟩,⟨⟨⟨207874998786,337353155101326⟩,⟨7900665645600,3108763840⟩,⟨12230400,62167123200⟩,⟨163072000,0⟩⟩,⟨⟨205797493356,49461717396⟩,⟨389232480,3108661920⟩,⟨12230400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨205904038146,334372565261802⟩,⟨8028253940274,3158970132⟩,⟨12738618,64750395294⟩,⟨174094446,0⟩⟩,⟨⟨203879689116,48610945188⟩,⟨392100876,3158866566⟩,⟨12738618,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5083 41 (1273-R)⟩
def p429:CachedProfile:=⟨⟨74315,579,17591⟩,⟨⟨⟨619282699382760,14876442235489064904⟩,⟨342800784550674144,9154316389248⟩,⟨35385358032,2650151004448608⟩,⟨6829374100176,0⟩⟩,⟨⟨613836338112912,139060575285408⟩,⟨1075067069328,9154296017712⟩,⟨35385358032,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨618861462521968,14866960638706064848⟩,⟨343178121702504480,9164393017280⟩,⟨35485490400,2657650318017600⟩,⟨6860528144000,0⟩⟩,⟨⟨613425308530740,138886719948720⟩,⟨1075577450400,9164372623320⟩,⟨35485490400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 74894 580 (17591-R)⟩
def p430:CachedProfile:=⟨⟨108076,443,28105⟩,⟨⟨⟨2096949863967218,72461680864045353998⟩,⟨879766979870874108,16214085742088⟩,⟨33094646364,3591397928774916⟩,⟨4886976113084,0⟩⟩,⟨⟨2074743086748540,514327404410820⟩,⟨2099605047540,16214060840172⟩,⟨33094646364,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨2095877332930446,72427299321665255526⟩,⟨881345066593272840,16243169880912⟩,⟨33228849888,3605961560995872⟩,⟨4917869783424,0⟩⟩,⟨⟨2073701350766760,513851717451384⟩,⟨2102398313184,16243144934328⟩,⟨33228849888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 108519 444 (28105-R)⟩
def p431:CachedProfile:=⟨⟨61915,362,14716⟩,⟨⟨⟨358416041687534,7156453514269128482⟩,⟨123976043875513164,3981451585928⟩,⟨11571447288,720635022754776⟩,⟨1396287972752,0⟩⟩,⟨⟨355227085451964,80925986652264⟩,⟨470401707984,3981440930820⟩,⟨11571447288,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨358071323370864,7150007767250435760⟩,⟨124208703751065120,3988923411264⟩,⟨11625188256,723981849018912⟩,⟨1406647778976,0⟩⟩,⟨⟨354890807543712,80783075883744⟩,⟨470868162336,3988912736160⟩,⟨11625188256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 62277 363 (14716-R)⟩
def p432:CachedProfile:=⟨⟨37486,212,9014⟩,⟨⟨⟨80534743581240,972580538377679880⟩,⟨16296523671922560,864587253120⟩,⟨2431020960,91644628150080⟩,⟨171792147840,0⟩⟩,⟨⟨79801575339360,18380310567480⟩,⟨103364259120,864583430760⟩,⟨2431020960,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨80408067824630,971149499646025322⟩,⟨16349782661230536,867412843584⟩,⟨2450470428,92377834194744⟩,⟨173983400388,0⟩⟩,⟨⟨79678065064836,18327335528376⟩,⟨103552508556,867409008732⟩,⟨2450470428,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 37698 213 (9014-R)⟩
def p433:CachedProfile:=⟨⟨20220,144,5230⟩,⟨⟨⟨13731860687888,89104486201736168⟩,⟨1874284844690304,184079643264⟩,⟨650820096,13253300434944⟩,⟨31239364608,0⟩⟩,⟨⟨13588564619820,3342725755920⟩,⟨23637424320,184078136736⟩,⟨650820096,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨13702881682488,88929858048196608⟩,⟨1883692705104720,185003628920⟩,⟨658629150,13412324010600⟩,⟨31833742250,0⟩⟩,⟨⟨13560405145200,3329956306080⟩,⟨23710649400,185002114830⟩,⟨658629150,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 20364 145 (5230-R)⟩
def p434:CachedProfile:=⟨⟨3341,24,793⟩,⟨⟨⟨56463008194,60928386260518⟩,⟨1294833590496,769633728⟩,⟨2744064,9233775360⟩,⟨21952512,0⟩⟩,⟨⟨55958358468,12712471980⟩,⟨90668448,769595616⟩,⟨2744064,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨55612930482,60067917958374⟩,⟨1330096468050,790595100⟩,⟨2936250,9880481250⟩,⟨24468750,0⟩⟩,⟨⟨55128837600,12362458140⟩,⟨91845900,790555950⟩,⟨2936250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3365 25 (793-R)⟩
def p435:CachedProfile:=⟨⟨1051,7,315⟩,⟨⟨⟨2281963348,759610071124⟩,⟨14864560368,28101248⟩,⟨92904,98292432⟩,⟨216776,0⟩⟩,⟨⟨2249939592,631879920⟩,⟨4180680,28096824⟩,⟨92904,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨2184026896,729672728656⟩,⟨16342602240,30896128⟩,⟨116736,123506688⟩,⟨311296,0⟩⟩,⟨⟨2155473696,584726976⟩,⟨4421376,30891264⟩,⟨116736,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨2175925416,727185463272⟩,⟨16288814592,30794496⟩,⟨116352,123100416⟩,⟨310272,0⟩⟩,⟨⟨2147649456,580880088⟩,⟨4392288,30789648⟩,⟨116352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1058 8 (315-R)⟩
def p436:CachedProfile:=⟨⟨25648,193,5087⟩,⟨⟨⟨21044723227104,176269936002422112⟩,⟨3934421739184320,304513238400⟩,⟨1137137472,29384769413952⟩,⟨73155844032,0⟩⟩,⟨⟨20912795198016,4013002282176⟩,⟨29972115648,304511274432⟩,⟨1137137472,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨21005174538210,175954581197941230⟩,⟨3947811705776772,305549592600⟩,⟨1146919464,29637545869224⟩,⟨74167458672,0⟩⟩,⟨⟨20873944524696,3998816503452⟩,⟨30020912568,305547621948⟩,⟨1146919464,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25841 194 (5087-R)⟩
def p437:CachedProfile:=⟨⟨25694,190,5111⟩,⟨⟨⟨21218468550120,177993187827639624⟩,⟨3904497102047040,301695108480⟩,⟨1107259200,28660297132800⟩,⟨70126416000,0⟩⟩,⟨⟨21084666607152,4057694699328⟩,⟨29785272480,301693165920⟩,⟨1107259200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25884 191 (5111-R)⟩
def p438:CachedProfile:=⟨⟨18255,82,3458⟩,⟨⟨⟨7185781411314,42800216186334630⟩,⟨572243894042580,62415109176⟩,⟨139549896,2558926442952⟩,⟨3814363824,0⟩⟩,⟨⟨7144292650272,1315997566884⟩,⟨5884921224,62414541900⟩,⟨139549896,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 19=>⟨⟨⟨7144056439920,42562771948853040⟩,⟨576040792004640,62829247040⟩,⟨142188960,2607318959520⟩,⟨3933894560,0⟩⟩,⟨⟨7103246361120,1301577863520⟩,⟨5891419680,62828676000⟩,⟨142188960,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18337 83 (3458-R)⟩
def p439:CachedProfile:=⟨⟨34211,247,7413⟩,⟨⟨⟨54857490263466,609713278142505966⟩,⟨13046269376317320,757232508032⟩,⟨2713924356,93516405459048⟩,⟨223446438644,0⟩⟩,⟨⟨54449560973676,11362866358536⟩,⟨81450693324,757228845516⟩,⟨2713924356,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨54746228977400,608544854872059800⟩,⟨13074352709894400,758862540800⟩,⟨2730777600,94097134540800⟩,⟨225744281600,0⟩⟩,⟨⟨54340604511600,11319990544800⟩,⟨81471868800,758858870400⟩,⟨2730777600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 34458 248 (7413-R)⟩
def p440:CachedProfile:=⟨⟨37850,301,7204⟩,⟨⟨⟨64793127616910,802886566914026870⟩,⟨18939472643546070,992876523100⟩,⟨3916681230,149425305605730⟩,⟨392973683410,0⟩⟩,⟨⟨64418655537720,11881324726920⟩,⟨93740104920,992872185690⟩,⟨3916681230,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨64659982700754,801310792111239762⟩,⟨18965470655642652,994239453240⟩,⟨3935087784,150127534047384⟩,⟨396132170256,0⟩⟩,⟨⟨64287687357972,11835193300740⟩,⟨93686361480,994235109876⟩,⟨3935087784,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 38151 302 (7204-R)⟩
def p441:CachedProfile:=⟨⟨129707,991,24282⟩,⟨⟨⟨2560423195730736,108776014827758809272⟩,⟨2466416193565769424,37742303053952⟩,⟨143087237538,18701215771741524⟩,⟨47266484133386,0⟩⟩,⟨⟨2546099214482376,462388460187528⟩,⟨3505998286476,37742254925046⟩,⟨143087237538,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2558864543204816,108712700465021277296⟩,⟨2467481594844645120,37758606405632⟩,⟨143293495296,18728173248196608⟩,⟨47382382444544,0⟩⟩,⟨⟨2544565315872636,461855436625296⟩,⟨3505490467584,37758558255936⟩,⟨143293495296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 130698 992 (24282-R)⟩
def p442:CachedProfile:=⟨⟨65500,468,12606⟩,⟨⟨⟨339201058526960,7263765956516913032⟩,⟨154055783576219616,4670641763424⟩,⟨16567413408,1092919127698944⟩,⟨2584516491648,0⟩⟩,⟨⟨337196001257556,62903328054336⟩,⟨446258148336,4670629963272⟩,⟨16567413408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨338802165087456,7255615491409861632⟩,⟨154213518007838016,4675423964008⟩,⟨16619813238,1096375839684384⟩,⟨2598230802874,0⟩⟩,⟨⟨336803776880256,62763692533248⟩,⟨446218951584,4675412151774⟩,⟨16619813238,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 65968 469 (12606-R)⟩
def p443:CachedProfile:=⟨⟨6221,45,1303⟩,⟨⟨⟨318330282760,644633806357480⟩,⟨13824548652960,4412736000⟩,⟨15843600,99275997600⟩,⟨237654000,0⟩⟩,⟨⟨316099998096,63879814752⟩,⟨458760240,4412618640⟩,⟨15843600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨314678532630,637620530811210⟩,⟨13980029517360,4462368000⟩,⟨16377840,102623545440⟩,⟨251126880,0⟩⟩,⟨⟨312519004260,62515004760⟩,⟨458935560,4462249320⟩,⟨16377840,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6266 46 (1303-R)⟩
def p444:CachedProfile:=⟨⟨64562,470,13401⟩,⟨⟨⟨352116739468214,7404319538361204842⟩,⟨159836402188226640,4915642384480⟩,⟨17763010800,1155164118345600⟩,⟨2782871692000,0⟩⟩,⟨⟨349708174043484,70078562018784⟩,⟨506472569640,4915629786600⟩,⟨17763010800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨351723806190372,7396483814809276836⟩,⟨160009154993177424,4920955293216⟩,⟨17820043848,1158873091523136⟩,⟨2797746884136,0⟩⟩,⟨⟨349322777730168,69932222069952⟩,⟨506490290856,4920942681720⟩,⟨17820043848,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 65032 471 (13401-R)⟩
def p445:CachedProfile:=⟨⟨35489,269,6040⟩,⟨⟨⟨47449116222648,553752917070581424⟩,⟨12467027263516056,697306444016⟩,⟨2622796806,93785968188948⟩,⟨235177446938,0⟩⟩,⟨⟨47228298848892,7828350186720⟩,⟨58891050960,697303193958⟩,⟨2622796806,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨47334062339760,552460346738297592⟩,⟨12484373110503840,698276648160⟩,⟨2636209800,94265590028400⟩,⟨237258882000,0⟩⟩,⟨⟨47114774814576,7792104876696⟩,⟨58836297240,698273393580⟩,⟨2636209800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 35758 270 (6040-R)⟩
def p446:CachedProfile:=⟨⟨4092,29,889⟩,⟨⟨⟨94235155330,125238561933910⟩,⟨2630207126340,1276562600⟩,⟨4490940,18507163740⟩,⟨43412420,0⟩⟩,⟨⟨93524434260,19563458460⟩,⟨137670540,1276510980⟩,⟨4490940,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨92644611564,123239288679372⟩,⟨2678098772880,1299808800⟩,⟨4730400,19493978400⟩,⟨47304000,0⟩⟩,⟨⟨91966704072,18952479000⟩,⟨137970000,1299756240⟩,⟨4730400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4121 30 (889-R)⟩
def p447:CachedProfile:=⟨⟨22746,147,4661⟩,⟨⟨⟨15167135252430,112347206160704802⟩,⟨2155033350894564,188272203336⟩,⟨604446948,13837603980564⟩,⟨29617900452,0⟩⟩,⟨⟨15065640216396,2984731924356⟩,⟨19165491324,188270832708⟩,⟨604446948,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨15118559718696,112005580960598472⟩,⟨2163177730228032,188983738496⟩,⟨610858752,13984389409536⟩,⟨30135698432,0⟩⟩,⟨⟨15017975162736,2966830605648⟩,⟨19180139328,188982362688⟩,⟨610858752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 15=>⟨⟨⟨15115091084370,111981181112063142⟩,⟨2162712322291176,188943079344⟩,⟨610727328,13981380719904⟩,⟨30129214848,0⟩⟩,⟨⟨15014571353376,2965554000396⟩,⟨19171886256,188941703832⟩,⟨610727328,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 22893 148 (4661-R)⟩
def p448:CachedProfile:=⟨⟨47983,353,9598⟩,⟨⟨⟨138986102660720,2176584809273607560⟩,⟨47500363327038744,1965434797880⟩,⟨7176730746,346894457338656⟩,⟨844461984446,0⟩⟩,⟨⟨138100899429396,26719522679232⟩,⟨195133885836,1965428020986⟩,⟨7176730746,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨138770523047520,2173373183253795840⟩,⟨47565449856466560,1968127923600⟩,⟨7206923160,348353837861760⟩,⟨850416932880,0⟩⟩,⟨⟨137889184904640,26641635402240⟩,⟨195116247360,1968121137420⟩,⟨7206923160,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 48336 354 (9598-R)⟩
def p449:CachedProfile:=⟨⟨37107,255,7773⟩,⟨⟨⟨67462199452674,814573562545205190⟩,⟨16603553119069800,888799554240⟩,⟨3033026100,113319921148200⟩,⟨257807218500,0⟩⟩,⟨⟨66991917129852,13546109143944⟩,⟨92453772060,888795589500⟩,⟨3033026100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨67322992447464,812980728558271080⟩,⟨16636502401597440,890563371008⟩,⟨3050962944,113990077513728⟩,⟨260348837888,0⟩⟩,⟨⟨66855425113872,13493881551384⟩,⟨92458478592,890559398400⟩,⟨3050962944,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 37362 256 (7773-R)⟩
def p450:CachedProfile:=⟨⟨177830,886,42888⟩,⟨⟨⟨8613606746292240,493015318713890058240⟩,⟨7282138424105559168,81494057968400⟩,⟨202006160664,36101733009227424⟩,⟨59659152782768,0⟩⟩,⟨⟨8534702224239576,1972406388439872⟩,⟨9778374964512,81493981969092⟩,⟨202006160664,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨8610099243919344,492827611049447907072⟩,⟨7287637822834406400,81555601554600⟩,⟨202386884022,36169774364875752⟩,⟨59839055375838,0⟩⟩,⟨⟨8531282986289976,1970935009603776⟩,⟨9782108784432,81555525497898⟩,⟨202386884022,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 178716 887 (42888-R)⟩
def p451:CachedProfile:=⟨⟨133046,752,30856⟩,⟨⟨⟨3461323020082200,148727821947508321392⟩,⟨2492433225298364544,37256716126976⟩,⟨104698541568,14008455464715264⟩,⟨26244434419712,0⟩⟩,⟨⟨3431936037317676,764353394174496⟩,⟨4295981647104,37256669718048⟩,⟨104698541568,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨3459376029394808,148649293951404499184⟩,⟨2494453529368692792,37286915556432⟩,⟨104922747414,14038453758498372⟩,⟨26335609600914,0⟩⟩,⟨⟨3430034728656972,763560920394720⟩,⟨4297234435920,37286869109886⟩,⟨104922747414,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 133798 753 (30856-R)⟩
def p452:CachedProfile:=⟨⟨19420,114,4121⟩,⟨⟨⟨9787856579910,61740996908471514⟩,⟨1075860187220304,110153953728⟩,⟨321417072,6278561084448⟩,⟨12213848736,0⟩⟩,⟨⟨9717693095412,1990916453448⟩,⟨11618945208,110153013912⟩,⟨321417072,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨9747161721558,61497992887797738⟩,⟨1081084763829240,110688891040⟩,⟨325811100,6364394027400⟩,⟨12489425500,0⟩⟩,⟨⟨9677810999700,1975488656520⟩,⟨11630039700,110687946660⟩,⟨325811100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 19534 115 (4121-R)⟩
def p453:CachedProfile:=⟨⟨4131,1,1270⟩,⟨⟨⟨140497153440,182014992012936⟩,⟨130221301464,63031432⟩,⟨7626,31510632⟩,⟨2542,0⟩⟩,⟨⟨138436653996,40018502640⟩,⟨9685020,63028890⟩,⟨7626,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨139232205320,180521768625536⟩,⟨258393184608,125071024⟩,⟨30264,125050848⟩,⟨20176,0⟩⟩,⟨⟨137219820816,39391017120⟩,⟨19066320,125065980⟩,⟨30264,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4132 2 (1270-R)⟩
def p454:CachedProfile:=⟨⟨4132,1,1270⟩,⟨⟨⟨140560192498,182145244827574⟩,⟨130284330354,63046684⟩,⟨7626,31518258⟩,⟨2542,0⟩⟩,⟨⟨138499690512,40028187660⟩,⟨9685020,63044142⟩,⟨7626,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 4133 2 (1270-R)⟩
def p455:CachedProfile:=⟨⟨8266,2,2540⟩,⟨⟨⟨1124362434888,2914621327774464⟩,⟨2084582652768,504256368⟩,⟨60984,504215712⟩,⟨40656,0⟩⟩,⟨⟨1107926901312,320176977120⟩,⟨77449680,504246204⟩,⟨60984,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 8268 3 (2540-R)⟩
def p456:CachedProfile:=⟨⟨44268,250,10174⟩,⟨⟨⟨126262000477800,1806212603444442600⟩,⟨30248331656400000,1358932300000⟩,⟨3815625000,169863993750000⟩,⟨317968750000,0⟩⟩,⟨⟨125207877478200,27651140358600⟩,⟨155280675000,1358927212500⟩,⟨3815625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 44518 251 (10174-R)⟩
def p457:CachedProfile:=⟨⟨26016,132,5143⟩,⟨⟨⟨21783703891016,184635443411808296⟩,⟨2785541465013120,213061846272⟩,⟨537774336,14061723337728⟩,⟨23662070784,0⟩⟩,⟨⟨21647373770736,4150564917696⟩,⟨20952828864,213060488256⟩,⟨537774336,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21738718147746,184272427721340486⟩,⟨2801187818974440,214258618448⟩,⟨544891956,14247834865488⟩,⟨24156876716,0⟩⟩,⟨⟨21603180624756,4134441537936⟩,⟨21029551956,214257252804⟩,⟨544891956,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26148 133 (5143-R)⟩
def p458:CachedProfile:=⟨⟨25202,149,5555⟩,⟨⟨⟨22282578291444,182003019430367172⟩,⟨3192254104532904,251846701680⟩,⟨740092536,18762085880136⟩,⟨36757929288,0⟩⟩,⟨⟨22110849404232,4694535699480⟩,⟨27592040520,251845045992⟩,⟨740092536,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25351 150 (5555-R)⟩
def p459:CachedProfile:=⟨⟨24912,164,5237⟩,⟨⟨⟨20481504941754,165945465618018462⟩,⟨3241039685220000,258499909440⟩,⟨845287488,21196429049088⟩,⟨46209049344,0⟩⟩,⟨⟨20337583972356,4127219621136⟩,⟨26992503504,258498191376⟩,⟨845287488,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25076 165 (5237-R)⟩
def p460:CachedProfile:=⟨⟨24214,174,4761⟩,⟨⟨⟨17534576851190,138669605033972042⟩,⟨2956985638072848,242497878432⟩,⟨865045872,21096738726336⟩,⟨50172660576,0⟩⟩,⟨⟨17426403749676,3317531149296⟩,⟨23669444808,242496221256⟩,⟨865045872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨17495494830000,138375166138154352⟩,⟨2967734475921600,243379382400⟩,⟨873180000,21295113840000⟩,⟨50935500000,0⟩⟩,⟨⟨17388000897696,3303610966656⟩,⟨23705589600,243377719200⟩,⟨873180000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨17479866014436,138257398187596452⟩,⟨2965236343045200,243174517600⟩,⟨872445000,21277188660000⟩,⟨50892625000,0⟩⟩,⟨⟨17372642951256,3298051087968⟩,⟨23665693800,243172855800⟩,⟨872445000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24388 175 (4761-R)⟩
def p461:CachedProfile:=⟨⟨24808,156,5143⟩,⟨⟨⟨19915870577736,160764247049348136⟩,⟨3000629153628288,240398955264⟩,⟨751106304,18750617773056⟩,⟨39057527808,0⟩⟩,⟨⟨19779552638448,3962624392128⟩,⟨24762434112,240397350336⟩,⟨751106304,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19874515925666,160447637991045446⟩,⟨3013993206068136,241469639888⟩,⟨759287796,18954860539344⟩,⟨39736061324,0⟩⟩,⟨⟨19738990559988,3947231090448⟩,⟨24824358324,241468027812⟩,⟨759287796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24964 157 (5143-R)⟩
def p462:CachedProfile:=⟨⟨25144,146,5111⟩,⟨⟨⟨20286096554664,166064475551809032⟩,⟨2864175008480064,226508875776⟩,⟨653804352,16534712062080⟩,⟨31818478464,0⟩⟩,⟨⟨20152300684752,3964576531680⟩,⟨22887630432,226507383072⟩,⟨653804352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25290 147 (5111-R)⟩
def p463:CachedProfile:=⟨⟨25426,137,5143⟩,⟨⟨⟨20850014959256,172564556909031896⟩,⟨2763142313769840,216185180192⟩,⟨579286416,14808298652208⟩,⟨26454079664,0⟩⟩,⟨⟨20713690857456,4057705789776⟩,⟨21746496624,216183770736⟩,⟨579286416,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25563 138 (5143-R)⟩
def p464:CachedProfile:=⟨⟨25496,134,5111⟩,⟨⟨⟨20817128660904,172824544319123592⟩,⟨2699919802961856,210686540544⟩,⟨550746432,14115631052160⟩,⟨24600007296,0⟩⟩,⟨⟨20683329314832,4017876492960⟩,⟨21006455328,210685170528⟩,⟨550746432,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25630 135 (5111-R)⟩
def p465:CachedProfile:=⟨⟨24794,145,5095⟩,⟨⟨⟨19679361571688,158768905489456808⟩,⟨2757489438696720,221141021920⟩,⟨642860400,16032295515600⟩,⟨31071586000,0⟩⟩,⟨⟨19546820202000,3885115132080⟩,⟨22588784400,221139544080⟩,⟨642860400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24939 146 (5095-R)⟩
def p466:CachedProfile:=⟨⟨24880,144,5111⟩,⟨⟨⟨19875586228200,160900876738046664⟩,⟨2765827813860864,221056293888⟩,⟨636014592,15915629150208⟩,⟨30528700416,0⟩⟩,⟨⟨19741793077872,3922877150208⟩,⟨22574101248,221054821632⟩,⟨636014592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19834100790210,160582119628872774⟩,⟨2779586828739720,222155977840⟩,⟨643617300,16105879315200⟩,⟨31108169500,0⟩⟩,⟨⟨19701090379812,3907542943488⟩,⟨22642012740,222154498260⟩,⟨643617300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25024 145 (5111-R)⟩
def p467:CachedProfile:=⟨⟨24985,141,5111⟩,⟨⟨⟨20032486881192,162868001068531080⟩,⟨2730328804977696,217333203840⟩,⟨609790032,15321584344032⟩,⟨28660131504,0⟩⟩,⟨⟨19898692688016,3938867138592⟩,⟨22103807472,217331762256⟩,⟨609790032,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25126 142 (5111-R)⟩
def p468:CachedProfile:=⟨⟨25141,139,5237⟩,⟨⟨⟨20804361517242,170009888817339774⟩,⟨2791854633358008,220876780176⟩,⟨607220388,15350531408640⟩,⟨28134544644,0⟩⟩,⟨⟨20660438410740,4160795662080⟩,⟨22877792604,220875324012⟩,⟨607220388,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25280 140 (5237-R)⟩
def p469:CachedProfile:=⟨⟨24592,152,5396⟩,⟨⟨⟨20613226457880,164384596864012224⟩,⟨3013663272100992,243589665984⟩,⟨748153728,18512315845632⟩,⟨37906455552,0⟩⟩,⟨⟨20455815915192,4323600082368⟩,⟨26559457344,243588025296⟩,⟨748153728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24744 153 (5396-R)⟩
def p470:CachedProfile:=⟨⟨25152,137,5143⟩,⟨⟨⟨20419961744536,167097293843463736⟩,⟨2704226568116976,213868034528⟩,⟨579286416,14649574174224⟩,⟨26454079664,0⟩⟩,⟨⟨20283640461648,4014212796528⟩,⟨21746496624,213866625072⟩,⟨579286416,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25289 138 (5143-R)⟩
def p471:CachedProfile:=⟨⟨25152,137,5111⟩,⟨⟨⟨20284545154680,166044858690449304⟩,⟨2687403738885552,212537595744⟩,⟨575682768,14558441519952⟩,⟨26289513072,0⟩⟩,⟨⟨20150749294992,3964419767088⟩,⟨21476749104,212536195056⟩,⟨575682768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25289 138 (5111-R)⟩
def p472:CachedProfile:=⟨⟨24334,159,5063⟩,⟨⟨⟨18877671410376,149480770373725416⟩,⟨2898233467786800,236660550624⟩,⟨768137904,18814001682672⟩,⟨40711308912,0⟩⟩,⟨⟨18747612926256,3767860864656⟩,⟨24459636528,236658940272⟩,⟨768137904,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24493 160 (5063-R)⟩
def p473:CachedProfile:=⟨⟨24334,159,5047⟩,⟨⟨⟨18813943335096,149002261916034072⟩,⟨2889076177922256,235912807968⟩,⟨765710928,18754557759504⟩,⟨40582679184,0⟩⟩,⟨⟨18685112342736,3744086587248⟩,⟨24305302224,235911202704⟩,⟨765710928,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18774132980966,148703233978523642⟩,⟨2901487167047040,236926257920⟩,⟨773836800,18953584742400⟩,⟨41271296000,0⟩⟩,⟨⟨18646065232476,3729265872948⟩,⟨24361349760,236924645760⟩,⟨773836800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24493 160 (5047-R)⟩
def p474:CachedProfile:=⟨⟨24334,159,5015⟩,⟨⟨⟨18686603355288,148045479732255864⟩,⟨2870761601123856,234417322656⟩,⟨760856976,18635669913168⟩,⟨40325419728,0⟩⟩,⟨⟨18560204112912,3696763759920⟩,⟨23998098960,234415727568⟩,⟨760856976,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18646841255238,147746548993857114⟩,⟨2883057405459840,235421367040⟩,⟨768921600,18833196748800⟩,⟨41009152000,0⟩⟩,⟨⟨18521195606172,3682037098740⟩,⟨24052828800,235419765120⟩,⟨768921600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24493 160 (5015-R)⟩
def p475:CachedProfile:=⟨⟨25203,149,5555⟩,⟨⟨⟨22284268571100,182024444799670716⟩,⟨3192505949578896,251856635808⟩,⟨740092536,18762825972672⟩,⟨36757929288,0⟩⟩,⟨⟨22112539672776,4694720880960⟩,⟨27592040520,251854980120⟩,⟨740092536,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25352 150 (5555-R)⟩
def p476:CachedProfile:=⟨⟨25204,149,5555⟩,⟨⟨⟨22285958917428,182045871859242804⟩,⟨3192757804559016,251866569936⟩,⟨740092536,18763566065208⟩,⟨36757929288,0⟩⟩,⟨⟨22114230007992,4694906062440⟩,⟨27592040520,251864914248⟩,⟨740092536,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25353 150 (5555-R)⟩
def p477:CachedProfile:=⟨⟨29724,174,5971⟩,⟨⟨⟨33095974512860,320493925089190652⟩,⟨5573273741965728,372822500352⟩,⟨1084849632,32434834297536⟩,⟨62921278656,0⟩⟩,⟨⟨32882698644696,6396762967056⟩,⟨37227799728,372820422096⟩,⟨1084849632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨33001622097708,319625067932662284⟩,⟨5590286291293200,373960563200⟩,⟨1094415000,32720819670000⟩,⟨63840875000,0⟩⟩,⟨⟨32790054131832,6362529996240⟩,⟨37241379000,373958478600⟩,⟨1094415000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29898 175 (5971-R)⟩
def p478:CachedProfile:=⟨⟨40017,250,10158⟩,⟨⟨⟨104077482005954,1337263798768640330⟩,⟨24708490282792500,1227237677000⟩,⟨3809625000,153402169875000⟩,⟨317468750000,0⟩⟩,⟨⟨103028407811772,24932147865444⟩,⟨154792683000,1227232597500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨103964728973214,1335916029833402190⟩,⟨24782904877064490,1230933765588⟩,⟨3836382894,154479629992698⟩,⟨320977368798,0⟩⟩,⟨⟨102918748289952,24883085747304⟩,⟨155106030312,1230928670790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40267 251 (10158-R)⟩
def p479:CachedProfile:=⟨⟨24808,156,5396⟩,⟨⟨⟨20967357736920,168785373844316544⟩,⟨3148213198044096,252222620832⟩,⟨788048352,19672839059328⟩,⟨40978514304,0⟩⟩,⟨⟨20809944819552,4362041402208⟩,⟨27258390432,252220936968⟩,⟨788048352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24964 157 (5396-R)⟩
def p480:CachedProfile:=⟨⟨24754,155,5143⟩,⟨⟨⟨19831207899416,159708661941915896⟩,⟨2968271987042640,238331705120⟩,⟨741507600,18470212808400⟩,⟨38311226000,0⟩⟩,⟨⟨19694890525968,3953894046768⟩,⟨24603700560,238330110480⟩,⟨741507600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19790017832646,159394104988079706⟩,⟨2981614446998928,239403020064⟩,⟨749646144,18672935800896⟩,⟨38981599488,0⟩⟩,⟨⟨19654493031708,3938534659188⟩,⟨24666241392,239401418256⟩,⟨749646144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24909 156 (5143-R)⟩
def p481:CachedProfile:=⟨⟨24469,165,5396⟩,⟨⟨⟨20437336284960,162213337219852464⟩,⟨3242389693906440,263247526080⟩,⟨881599950,21717333168300⟩,⟨48487997250,0⟩⟩,⟨⟨20279926929612,4304379422448⟩,⟨28830989880,263245745070⟩,⟨881599950,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20396564088720,161908062394063224⟩,⟨3255996259537056,264352243072⟩,⟨890665032,21940642398288⟩,⟨49283465104,0⟩⟩,⟨⟨20240027220552,4288441717128⟩,⟨28898324472,264350454588⟩,⟨890665032,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24634 166 (5396-R)⟩
def p482:CachedProfile:=⟨⟨24584,164,5079⟩,⟨⟨⟨19324169484680,154670866899085160⟩,⟨3061584343712640,247423310080⟩,⟨819790080,20288164899840⟩,⟨44815191040,0⟩⟩,⟨⟨19192873140720,3831186404160⟩,⟨25388498880,247421643840⟩,⟨819790080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19283557161570,154362465743803590⟩,⟨3074188951290600,248441965200⟩,⟨828184500,20495910006000⟩,⟨45550147500,0⟩⟩,⟨⟨19153033778580,3816116357040⟩,⟨25442831700,248440292100⟩,⟨828184500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24748 165 (5079-R)⟩
def p483:CachedProfile:=⟨⟨24909,155,5237⟩,⟨⟨⟨20462594839866,165708429839403966⟩,⟨3060246763423800,244197026640⟩,⟨755057700,18924766192800⟩,⟨39011314500,0⟩⟩,⟨⟨20318673996180,4125244559904⟩,⟨25511207580,244195402860⟩,⟨755057700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20420793781636,165387762594456196⟩,⟨3074110104686400,245303280768⟩,⟨763371648,19133146985472⟩,⟨39695325696,0⟩⟩,⟨⟨20277694758840,4109506874304⟩,⟨25577843616,245301649632⟩,⟨763371648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25064 156 (5237-R)⟩
def p484:CachedProfile:=⟨⟨25144,146,5237⟩,⟨⟨⟨20820255075882,170210821129120494⟩,⟨2934772027664112,232091841024⟩,⟨669919248,16942257781920⟩,⟨32602736736,0⟩⟩,⟨⟨20676331864620,4162441546440⟩,⟨24029911656,232090311528⟩,⟨669919248,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25290 147 (5237-R)⟩
def p485:CachedProfile:=⟨⟨24327,169,5075⟩,⟨⟨⟨18929969128764,149894523420326172⟩,⟨3088568666508624,252171822240⟩,⟨869853816,21307939076736⟩,⟨49001764968,0⟩⟩,⟨⟨18798984892872,3786204643200⟩,⟨26121349800,252170106552⟩,⟨869853816,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24496 170 (5075-R)⟩
def p486:CachedProfile:=⟨⟨25026,149,5111⟩,⟨⟨⟨20108087666424,163818690307066872⟩,⟨2896505296018416,230112038304⟩,⟨680949072,17142892887600⟩,⟨33820470576,0⟩⟩,⟨⟨19974292972272,3946548603600⟩,⟨23357924208,230110514928⟩,⟨680949072,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25175 150 (5111-R)⟩
def p487:CachedProfile:=⟨⟨24250,171,5079⟩,⟨⟨⟨18834090739160,148646669737150520⟩,⟨3108460531219920,254575360800⟩,⟨891265680,21765599171280⟩,⟨50802143760,0⟩⟩,⟨⟨18702797717520,3780564214320⟩,⟨26472154320,254573623440⟩,⟨891265680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18794443137990,148350127436646330⟩,⟨3120483757818960,255560042400⟩,⟨899945280,21977563682880⟩,⟨51596862720,0⟩⟩,⟨⟨18663923070780,3765693290580⟩,⟨26522224560,255558298320⟩,⟨899945280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24421 172 (5079-R)⟩
def p488:CachedProfile:=⟨⟨24296,172,5071⟩,⟨⟨⟨18872299479920,149264102860626992⟩,⟨3133742033566464,256152879616⟩,⟨900300288,22028547446784⟩,⟨51617216512,0⟩⟩,⟨⟨18741624588576,3775918202496⟩,⟨26543155584,256151134848⟩,⟨900300288,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18832526177130,148965900183796302⟩,⟨3145746923843976,257134171024⟩,⟨909003588,22241499791184⟩,⟨52419206908,0⟩⟩,⟨⟨18702621807396,3761042147856⟩,⟨26592295716,257132419572⟩,⟨909003588,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24468 173 (5071-R)⟩
def p489:CachedProfile:=⟨⟨25250,143,5111⟩,⟨⟨⟨20446219311480,168093332686403352⟩,⟨2828219049214416,222758119584⟩,⟨627211728,15926787409104⟩,⟨29897092368,0⟩⟩,⟨⟨20312422388496,3980723284656⟩,⟨22417336656,222756657552⟩,⟨627211728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25393 144 (5111-R)⟩
def p490:CachedProfile:=⟨⟨25354,138,5143⟩,⟨⟨⟨20738132969544,171136536995156520⟩,⟨2767871924395200,217158363264⟩,⟨587774016,14983535215872⟩,⟨27037604736,0⟩⟩,⟨⟨20601809598192,4046435707584⟩,⟨21905230176,217156943520⟩,⟨587774016,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25492 139 (5143-R)⟩
def p491:CachedProfile:=⟨⟨25354,138,5079⟩,⟨⟨⟨20463498229640,168981732573989480⟩,⟨2733434410265280,214456548480⟩,⟨580461120,14797114871040⟩,⟨26701211520,0⟩⟩,⟨⟨20332194326640,3946363496640⟩,⟨21363492960,214455146400⟩,⟨580461120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20420643133410,168645159970635270⟩,⟨2747822053892760,215585363760⟩,⟨587744820,14982790951440⟩,⟨27232176660,0⟩⟩,⟨⟨20290112206260,3930840398160⟩,⟨21433658220,215583954300⟩,⟨587744820,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25492 139 (5079-R)⟩
def p492:CachedProfile:=⟨⟨24259,175,4602⟩,⟨⟨⟨16976871283696,134748236340333496⟩,⟨2885533417914000,236192818400⟩,⟨845801250,20666307742500⟩,⟨49338406250,0⟩⟩,⟨⟨16879162150680,3105513411624⟩,⟨22242156300,236191207350⟩,⟨845801250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨16937877601416,134452571006351376⟩,⟨2895717451144320,237026431488⟩,⟨853636608,20857756879872⟩,⟨50080014336,0⟩⟩,⟨⟨16840803021540,3092033173824⟩,⟨22272155136,237024814752⟩,⟨853636608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24434 176 (4602-R)⟩
def p493:CachedProfile:=⟨⟨24259,175,5079⟩,⟨⟨⟨18853449572680,148883111267873320⟩,⟨3184560761676000,260669024000⟩,⟨933450000,22807917300000⟩,⟨54451250000,0⟩⟩,⟨⟨18722156418960,3782576717280⟩,⟨27091386000,260667246000⟩,⟨933450000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18813763863570,148586103523375830⟩,⟨3196453502436480,261642501120⟩,⟨942289920,23023911905280⟩,⟨55281008640,0⟩⟩,⟨⟨18683243664540,3767697877320⟩,⟨27139020480,261640716480⟩,⟨942289920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24434 176 (5079-R)⟩
def p494:CachedProfile:=⟨⟨24214,174,5079⟩,⟨⟨⟨18784995353480,148047601623315560⟩,⟨3154452562751040,258691562880⟩,⟨922812480,22505550762240⟩,⟨53523123840,0⟩⟩,⟨⟨18653702667120,3775455552960⟩,⟨26936578080,258689795040⟩,⟨922812480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18745444396770,147752238610829190⟩,⟨3166336254627000,259666134000⟩,⟨931612500,22720165650000⟩,⟨54344062500,0⟩⟩,⟨⟨18614924664180,3760604724240⟩,⟨26984821500,259664359500⟩,⟨931612500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24388 175 (5079-R)⟩
def p495:CachedProfile:=⟨⟨24128,176,4602⟩,⟨⟨⟨16801880505656,132616081432083896⟩,⟨2871224645900160,236278691968⟩,⟨855495168,20791954563072⟩,⟨50189049856,0⟩⟩,⟨⟨16704172569420,3088990666944⟩,⟨22369254336,236277071712⟩,⟨855495168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨16763266990176,132325048268184576⟩,⟨2881265158497600,237104953416⟩,⟨863364582,20983212800928⟩,⟨50938510338,0⟩⟩,⟨⟨16666193604480,3075582150144⟩,⟨22398701472,237103327494⟩,⟨863364582,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨16747825443336,132208642110956736⟩,⟨2878755853096656,236898460968⟩,⟨862612686,20964938720544⟩,⟨50894148474,0⟩⟩,⟨⟨16651005106008,3070226909568⟩,⟨22359700584,236896836462⟩,⟨862612686,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24304 177 (4602-R)⟩
def p496:CachedProfile:=⟨⟨2984,24,773⟩,⟨⟨⟨44351468586,42510359545326⟩,⟨1008633332160,670667904⟩,⟨2674944,8046231552⟩,⟨21399552,0⟩⟩,⟨⟨43884324756,10798154496⟩,⟨86155488,670630752⟩,⟨2674944,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 3008 25 (773-R)⟩
def p497:CachedProfile:=⟨⟨43018,250,10174⟩,⟨⟨⟨119562729602800,1659177798912442600⟩,⟨28573539375150000,1320776050000⟩,⟨3815625000,165094462500000⟩,⟨317968750000,0⟩⟩,⟨⟨118508632040700,26874736983600⟩,⟨155280675000,1320770962500⟩,⟨3815625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 43268 251 (10174-R)⟩
def p498:CachedProfile:=⟨⟨25159,195,5095⟩,⟨⟨⟨20317548379128,166793086458282648⟩,⟨3832790994133920,302345272320⟩,⟨1162652400,29477888949600⟩,⟨75572406000,0⟩⟩,⟨⟨20185002779760,3949765790880⟩,⟨30378020400,302343284880⟩,⟨1162652400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20275089902978,166461815950063238⟩,⟨3844886467392096,303299419136⟩,⟨1172302656,29722561540224⟩,⟨76590440192,0⟩⟩,⟨⟨20143322155740,3934278046440⟩,⟨30414076560,303297425424⟩,⟨1172302656,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25354 196 (5095-R)⟩
def p499:CachedProfile:=⟨⟨25216,192,5087⟩,⟨⟨⟨20367264340896,167590048186193952⟩,⟨3783967412133888,297859497984⟩,⟨1125384192,28593761550336⟩,⟨72024588288,0⟩⟩,⟨⟨20235340718016,3945759141888⟩,⟨29816819712,297857544192⟩,⟨1125384192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20324653599066,167256715302830622⟩,⟨3796199680664232,298822384816⟩,⟨1134902532,28835603533056⟩,⟨73012062892,0⟩⟩,⟨⟨20193505387956,3930262802688⟩,⟨29854404948,298820424708⟩,⟨1134902532,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25408 193 (5087-R)⟩
def p500:CachedProfile:=⟨⟨25314,190,5079⟩,⟨⟨⟨20482151014280,169219534427711720⟩,⟨3766968124468800,295405251200⟩,⟨1100328000,28062765312000⟩,⟨69687440000,0⟩⟩,⟨⟨20350846989360,3948221191680⟩,⟨29413504800,295403320800⟩,⟨1100328000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20439259199970,168882493703171430⟩,⟨3779339836853880,296375448720⟩,⟨1109752020,28303115518080⟩,⟨70654211940,0⟩⟩,⟨⟨20308728151140,3932690785920⟩,⟨29452005180,296373511980⟩,⟨1109752020,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25504 191 (5079-R)⟩
def p501:CachedProfile:=⟨⟨44018,250,10174⟩,⟨⟨⟨124906883802800,1776133817813042600⟩,⟨29909557575150000,1351301050000⟩,⟨3815625000,168910087500000⟩,⟨317968750000,0⟩⟩,⟨⟨123852765890700,27495859683600⟩,⟨155280675000,1351295962500⟩,⟨3815625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 44268 251 (10174-R)⟩
def p502:CachedProfile:=⟨⟨26530,139,5079⟩,⟨⟨⟨22334819851480,193388116564974520⟩,⟨3013348962601680,225983820320⟩,⟨588904080,15705482909520⟩,⟨27285889040,0⟩⟩,⟨⟨22203503990160,4128572418480⟩,⟨21518300880,225982408080⟩,⟨588904080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨22288281051270,193003499182559130⟩,⟨3029053182901200,227161552800⟩,⟨596232000,15900911208000⟩,⟨27824160000,0⟩⟩,⟨⟨22157738189340,4112332597620⟩,⟨21587857200,227160133200⟩,⟨596232000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26669 140 (5079-R)⟩
def p503:CachedProfile:=⟨⟨25484,182,5143⟩,⟨⟨⟨21012875779080,174650337367801320⟩,⟨3700383701466816,288352064000⟩,⟨1022339136,26239356264576⟩,⟨62021907584,0⟩⟩,⟨⟨20876550617616,4074055345632⟩,⟨28889506464,288350191584⟩,⟨1022339136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20969388535250,174306733144665110⟩,⟨3713482250118504,289372776000⟩,⟨1031595156,26476921273896⟩,⟨62927304516,0⟩⟩,⟨⟨20833855961436,4058229176712⟩,⟨28935398556,289370896956⟩,⟨1031595156,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25666 183 (5143-R)⟩
def p504:CachedProfile:=⟨⟨8268,2,2544⟩,⟨⟨⟨1126896294760,2921496198058480⟩,⟨2088874553520,505172320⟩,⟨61080,505131600⟩,⟨40720,0⟩⟩,⟨⟨1110383123340,321263697600⟩,⟨77693760,505162140⟩,⟨61080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 8270 3 (2544-R)⟩
def p505:CachedProfile:=⟨⟨24644,140,5111⟩,⟨⟨⟨19508925778920,156335232459342024⟩,⟨2637668174682240,212854682880⟩,⟨601171200,14899427020800⟩,⟨28054656000,0⟩⟩,⟨⟨19375135082352,3885253648128⟩,⟨21947042880,212853251520⟩,⟨601171200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19468157595330,156025406726132934⟩,⟨2651311962130536,213955716912⟩,⟨608597172,15083472310848⟩,⟨28604067084,0⟩⟩,⟨⟨19335149633892,3870066508608⟩,⟨22017405492,213954278148⟩,⟨608597172,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24784 141 (5111-R)⟩
def p506:CachedProfile:=⟨⟨24703,141,5079⟩,⟨⟨⟨19469283545480,156469974625180520⟩,⟨2652676340173920,213548854080⟩,⟨605972880,15054790230720⟩,⟨28480725360,0⟩⟩,⟨⟨19337986226160,3846047964480⟩,⟨21827916720,213547421520⟩,⟨605972880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24844 142 (5079-R)⟩
def p507:CachedProfile:=⟨⟨33168,8,10477⟩,⟨⟨⟨74949195432514,777303447170653702⟩,⟨553574331385920,33372010880⟩,⟨4023552,133485361152⟩,⟨10729472,0⟩⟩,⟨⟨73798356027396,21851970762336⟩,⟨5269344288,33371843232⟩,⟨4023552,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 33176 9 (10477-R)⟩
def p508:CachedProfile:=⟨⟨16983,137,3920⟩,⟨⟨⟨7197164887200,39588744559564800⟩,⟨944686691858880,110361940296⟩,⟨441559494,7559498537280⟩,⟨20164550226,0⟩⟩,⟨⟨7136778977760,1578839270400⟩,⟨12634403040,110360865942⟩,⟨441559494,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨7177278220480,39485972241831400⟩,⟨949155263843760,110883983664⟩,⟨446886504,7650696948480⟩,⟨20556779184,0⟩⟩,⟨⟨7117352548740,1570795267200⟩,⟨12661784280,110882904228⟩,⟨446886504,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 17120 138 (3920-R)⟩
def p509:CachedProfile:=⟨⟨9353,74,2417⟩,⟨⟨⟨1360124199642,4086218680673766⟩,⟨95413516811496,20242935024⟩,⟨79445808,748935632016⟩,⟨1959663264,0⟩⟩,⟨⟨1345952923068,330565635972⟩,⟨2594871864,20242577160⟩,⟨79445808,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 9427 75 (2417-R)⟩
def p510:CachedProfile:=⟨⟨24511,189,5396⟩,⟨⟨⟨20542776351384,163513770973953792⟩,⟨3733937646996816,302345941464⟩,⟨1156717422,28570920323400⟩,⟨72873197586,0⟩⟩,⟨⟨20385366283632,4315911818400⟩,⟨33024588408,302343901398⟩,⟨1156717422,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20501808787224,163206086556205272⟩,⟨3746738658990960,303382480240⟩,⟨1166824200,28820557740000⟩,⟨73898866000,0⟩⟩,⟨⟨20345271207972,4299931412400⟩,⟨33076395480,303380433180⟩,⟨1166824200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24700 190 (5396-R)⟩
def p511:CachedProfile:=⟨⟨24769,195,5237⟩,⟨⟨⟨20305362651066,163741943726727966⟩,⟨3819328403974200,305989922160⟩,⟨1195049700,29833220710800⟩,⟨77678230500,0⟩⟩,⟨⟨20161442854980,4108785716304⟩,⟨32094745020,305987879340⟩,⟨1195049700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20263861768836,163425030813536196⟩,⟨3831585610104000,306971932288⟩,⟨1205033088,30082446008832⟩,⟨78728828416,0⟩⟩,⟨⟨20120763791640,4093110820704⟩,⟨32136265056,306969882912⟩,⟨1205033088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24964 196 (5237-R)⟩
def p512:CachedProfile:=⟨⟨24889,189,5087⟩,⟨⟨⟨19858642827936,161170457377350432⟩,⟨3628715994078336,289397380608⟩,⟨1090490688,27347325473664⟩,⟨68700913344,0⟩⟩,⟨⟨19726722563136,3894511483008⟩,⟨29350931904,289395457344⟩,⟨1090490688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25078 190 (5087-R)⟩
def p513:CachedProfile:=⟨⟨24986,187,5079⟩,⟨⟨⟨19970863390680,162741879531983160⟩,⟨3611881410279120,286967716640⟩,⟨1065855120,26830770935760⟩,⟨66438302480,0⟩⟩,⟨⟨19839562728720,3896979770160⟩,⟨28949081040,286965816720⟩,⟨1065855120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25173 188 (5079-R)⟩
def p514:CachedProfile:=⟨⟨25032,184,5083⟩,⟨⟨⟨20053717382100,163704218071709460⟩,⟨3568896475684992,283068985600⟩,⟨1032743424,26041658179584⟩,⟨63341596672,0⟩⟩,⟨⟨19922106242136,3909786995712⟩,⟨28529537088,283067114688⟩,⟨1032743424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25216 185 (5083-R)⟩
def p515:CachedProfile:=⟨⟨25120,182,5095⟩,⟨⟨⟨20237005650680,165773103632206616⟩,⟨3562613203775808,281610178304⟩,⟨1012799424,25625851026048⟩,⟨61443165056,0⟩⟩,⟨⟨20104460581296,3941664985440⟩,⟨28352819040,281608323360⟩,⟨1012799424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25302 183 (5095-R)⟩
def p516:CachedProfile:=⟨⟨25204,180,5079⟩,⟨⟨⟨20296018188680,166851573120057320⟩,⟨3535203613449600,278540870400⟩,⟨987552000,25068019968000⟩,⟨59253120000,0⟩⟩,⟨⟨20164715382960,3929644241280⟩,⟨27865425600,278539041600⟩,⟨987552000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨20249241073416,166485957580024896⟩,⟨3547146016358928,279481829224⟩,⟨996393054,25292441282736⟩,⟨60115714258,0⟩⟩,⟨⟨20118788371368,3912642850368⟩,⟨27899005512,279479994246⟩,⟨996393054,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25384 181 (5079-R)⟩
def p517:CachedProfile:=⟨⟨25032,184,5079⟩,⟨⟨⟨20036906977160,163573838603250920⟩,⟨3566088487092480,282846272000⟩,⟨1031930880,26021169070080⟩,⟨63291760640,0⟩⟩,⟨⟨19905605878320,3903636510720⟩,⟨28484657280,282844402560⟩,⟨1031930880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨19990690929480,163215320632259520⟩,⟨3577705467299280,283767689000⟩,⟨1040919150,26247817286400⟩,⟨64190014250,0⟩⟩,⟨⟨19860239930616,3886747640832⟩,⟨28515558120,283765813470⟩,⟨1040919150,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25216 185 (5079-R)⟩
def p518:CachedProfile:=⟨⟨24664,184,5143⟩,⟨⟨⟨19737527686216,158543361626480296⟩,⟨3506389403408640,282229963264⟩,⟨1044931584,25964459999232⟩,⟨64089137152,0⟩⟩,⟨⟨19601210940336,3944211300096⟩,⟨29206973568,282228070272⟩,⟨1044931584,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19696519734946,158231070068536486⟩,⟨3518592242953800,283212181360⟩,⟨1054266900,26196423931200⟩,⟨65013125500,0⟩⟩,⟨⟨19560995560356,3928889526336⟩,⟨29251632420,283210281780⟩,⟨1054266900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24848 185 (5143-R)⟩
def p519:CachedProfile:=⟨⟨25708,148,5111⟩,⟨⟨⟨21174032265192,177418410458882760⟩,⟨3034821341950848,234750401280⟩,⟨671839488,17371081801728⟩,⟨33144081408,0⟩⟩,⟨⟨21040230608496,4053305290752⟩,⟨23201159616,234748888128⟩,⟨671839488,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25856 149 (5111-R)⟩
def p520:CachedProfile:=⟨⟨45553,334,10721⟩,⟨⟨⟨141624628763754,2085204340303087302⟩,⟨45243612408277368,1971966308496⟩,⟨7176620592,329313589105104⟩,⟨798997092576,0⟩⟩,⟨⟨140391259787724,31648418630964⟩,⟨230360926248,1971959146200⟩,⟨7176620592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨141466706746930,2083024420599303106⟩,⟨45332516191181790,1975841246620⟩,⟨7212251850,330948600640950⟩,⟨805368123250,0⟩⟩,⟨⟨140237128140516,31583510918820⟩,⟨230576768100,1975834070250⟩,⟨7212251850,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45887 335 (10721-R)⟩
def p521:CachedProfile:=⟨⟨47851,314,11851⟩,⟨⟨⟨173298087704204,2668407723311086412⟩,⟨51801234250658736,2150998525664⟩,⟨7011358752,337702094290080⟩,⟨733855549376,0⟩⟩,⟨⟨171632377626792,40590972447480⟩,⟨264622969968,2150991082608⟩,⟨7011358752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨173105795923520,2665646108950717760⟩,⟨51913590670972800,2155664044800⟩,⟨7048944000,339512387760000⟩,⟨740139120000,0⟩⟩,⟨⟨171445138231680,40508814902400⟩,⟨264928406400,2155656585600⟩,⟨7048944000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 48165 315 (11851-R)⟩
def p522:CachedProfile:=⟨⟨90376,696,21727⟩,⟨⟨⟨1132588073918112,33048341677594449696⟩,⟨752579295413105664,16527162279936⟩,⟨63152345088,5751410371854336⟩,⟨14651344060416,0⟩⟩,⟨⟨1122327141663168,257961944174592⟩,⟨1971423853056,16527132034560⟩,⟨63152345088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨1131905961331260,33029720519792192796⟩,⟨753244351568639568,16541767421344⟩,⟨63298969464,5764763747025408⟩,⟨14706460572136,0⟩⟩,⟨⟨1121662016650056,257677080430080⟩,⟨1972076215080,16541737149240⟩,⟨63298969464,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 91072 697 (21727-R)⟩
def p523:CachedProfile:=⟨⟨65420,391,15321⟩,⟨⟨⟨416156990983842,8789846395197712590⟩,⟨155683833978800556,4731254945480⟩,⟨14054656092,924950972070612⟩,⟨1831790177324,0⟩⟩,⟨⟨412558394617356,92694146709492⟩,⟨550719657252,4731242963676⟩,⟨14054656092,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨415773422394750,8782248435972120270⟩,⟨155949573140904816,4739330826720⟩,⟨14114653056,928899432268416⟩,⟨1844314665984,0⟩⟩,⟨⟨412183974960576,92536915016952⟩,⟨551191604544,4739318824464⟩,⟨14114653056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 65811 392 (15321-R)⟩
def p524:CachedProfile:=⟨⟨209615,1389,47232⟩,⟨⟨⟨13144576413656896,892440054066849398656⟩,⟨17525940170371918560,166119678855672⟩,⟨546765712758,115369752454789032⟩,⟨253152525006954,0⟩⟩,⟨⟨13039186184420040,2824384406713344⟩,⟨18592396072704,166119547642398⟩,⟨546765712758,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨13140668715118620,892190317896277374780⟩,⟨17533730667565519200,166193521204800⟩,⟨547402572000,115504132302288000⟩,⟨253629858360000,0⟩⟩,⟨⟨13035365472262440,2822829886228320⟩,⟨18595541041200,166193389933200⟩,⟨547402572000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 211004 1390 (47232-R)⟩
def p525:CachedProfile:=⟨⟨46861,354,12445⟩,⟨⟨⟨176115008237910,2644067736584144850⟩,⟨58931723976483960,2496321003792⟩,⟨9358097616,441842578939440⟩,⟨1104255518688,0⟩⟩,⟨⟨174186221062980,43878921246300⟩,⟨328987358280,2496312192024⟩,⟨9358097616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨175958034304340,2641885498913699300⟩,⟨59050713555504600,2501361370640⟩,⟨9403481400,443985374301000⟩,⟨1112745299000,0⟩⟩,⟨⟨174033890930760,43808435861400⟩,⟨329386735800,2501352541080⟩,⟨9403481400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 47215 355 (12445-R)⟩
def p526:CachedProfile:=⟨⟨78413,542,18899⟩,⟨⟨⟨740688781007700,18732961670364692100⟩,⟨383154781925084400,9705672698400⟩,⟨33312837600,2630215092708000⟩,⟨6018519326400,0⟩⟩,⟨⟨733935241909800,169212139803000⟩,⟨1161585457200,9705652210800⟩,⟨33312837600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨740132925098754,18719813422209836442⟩,⟨383597676103409262,9716891666988⟩,⟨33412878378,2638113812334990⟩,⟨6047730986418,0⟩⟩,⟨⟨733393308681132,168979435099860⟩,⟨1162128215556,9716871155706⟩,⟨33412878378,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 78955 543 (18899-R)⟩
def p527:CachedProfile:=⟨⟨6457,47,1509⟩,⟨⟨⟨400531352010,836265955821390⟩,⟨18014329577880,5539634320⟩,⟨20013540,130168064160⟩,⟨313545460,0⟩⟩,⟨⟨397073317620,88919696160⟩,⟨642562380,5539492380⟩,⟨20013540,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨396790628400,828932995440384⟩,⟨18239211929088,5608791936⟩,⟨20694528,134597210112⟩,⟨331112448,0⟩⟩,⟨⟨393420845472,87394716288⟩,⟨644979456,5608648224⟩,⟨20694528,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6504 48 (1509-R)⟩
def p528:CachedProfile:=⟨⟨25596,196,5079⟩,⟨⟨⟨20932451317640,174994185266357480⟩,⟨3974181578021760,308174908160⟩,⟨1170919680,30200360386560⟩,⟨76500085760,0⟩⟩,⟨⟨20801144366640,3992805872640⟩,⟨30342352320,308172916800⟩,⟨1170919680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 9=>⟨⟨⟨20893050223760,174680616383506376⟩,⟨3987381111058488,309198464344⟩,⟨1180802634,30455261536128⟩,⟨77539372966,0⟩⟩,⟨⟨20762439093396,3978669277440⟩,⟨30389184540,309196466370⟩,⟨1180802634,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25792 197 (5079-R)⟩
def p529:CachedProfile:=⟨⟨402978,1946,77696⟩,⟨⟨⟨78782225972869440,10353503724188527787904⟩,⟨148746167545337320896,734687356000752⟩,⟨1765392074712,714849620460681888⟩,⟨1145150992463184,0⟩⟩,⟨⟨78313132024191432,14666540295932928⟩,⟨70485047603712,734687053604028⟩,⟨1765392074712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 19=>⟨⟨⟨78761814028028866,10350945152770027035046⟩,⟨148786211357386467480,734885140644336⟩,⟨1766774769012,715409506567415088⟩,⟨1146636825088788,0⟩⟩,⟨⟨78293064103651860,14659368024513264⟩,⟨70486781578092,734884838166204⟩,⟨1766774769012,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 404924 1947 (77696-R)⟩
def p530:CachedProfile:=⟨⟨86625,460,20828⟩,⟨⟨⟨992971535743374,27701050129914622098⟩,⟨435980032944483240,10012768577520⟩,⟨26444498400,2302919143164000⟩,⟨4054823088000,0⟩⟩,⟨⟨983932171447308,226678638534120⟩,⟨1197360897120,10012749414840⟩,⟨26444498400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨992243444989970,27682051855956184310⟩,⟨436634137435889370,10027790855020⟩,⟨26541747690,2311388097583650⟩,⟨4078581895030,0⟩⟩,⟨⟨983222291305680,226374014159100⟩,⟨1198351272060,10027771663590⟩,⟨26541747690,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 87085 461 (20828-R)⟩
def p531:CachedProfile:=⟨⟨16773,125,3340⟩,⟨⟨⟨5910811296208,32368035853217584⟩,⟨715514617233000,84687668000⟩,⟨313218750,5292770437500⟩,⟨13050781250,0⟩⟩,⟨⟨5873427524172,1131382608720⟩,⟨8369205000,84686832750⟩,⟨313218750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨5884490318280,32230840323679272⟩,⟨718216412239872,85007458368⟩,⟨316916712,5355258599376⟩,⟨13310501904,0⟩⟩,⟨⟨5847573686736,1121919255576⟩,⟨8365595112,85006619964⟩,⟨316916712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16898 126 (3340-R)⟩
def p532:CachedProfile:=⟨⟨10908,79,2221⟩,⟨⟨⟨1664370339654,5919012072910002⟩,⟨127144221226308,23145036376⟩,⟨83205012,914173466844⟩,⟨2191065316,0⟩⟩,⟨⟨1653360740724,325329157164⟩,⟨2339219388,23144685300⟩,⟨83205012,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1653199304352,5881259917469856⟩,⟨127942383006720,23290337280⟩,⟨84787200,931556966400⟩,⟨2260992000,0⟩⟩,⟨⟨1642395951168,321241597632⟩,⟨2339066880,23289984000⟩,⟨84787200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10987 80 (2221-R)⟩
def p533:CachedProfile:=⟨⟨58175,425,11325⟩,⟨⟨⟨240626867966450,4574804383670333750⟩,⟨99177883109445000,3384926868400⟩,⟨12274552500,719288776500000⟩,⟨1738894937500,0⟩⟩,⟨⟨239172917350500,45098659620000⟩,⟨327080722500,3384917241300⟩,⟨12274552500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨240311506145424,4569088524852491472⟩,⟨99288360389683584,3388697469696⟩,⟨12317139072,721784349619200⟩,⟨1749033748224,0⟩⟩,⟨⟨238862937567072,44987231251200⟩,⟨327040281792,3388687831872⟩,⟨12317139072,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 58600 426 (11325-R)⟩
def p534:CachedProfile:=⟨⟨58122,413,11587⟩,⟨⟨⟨246011636788612,4666327054520915284⟩,⟨98388416579926536,3361710829232⟩,⟨11859321432,694185380022120⟩,⟨1632633250472,0⟩⟩,⟨⟨244454491883880,47157021488760⟩,⟨332721446568,3361701257544⟩,⟨11859321432,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨245695654632654,4660624149325273098⟩,⟨98507488964285736,3365779292208⟩,⟨11902423824,696708378537840⟩,⟨1642534487712,0⟩⟩,⟨⟨244144143740628,47043140241420⟩,⟨332721620568,3365769708936⟩,⟨11902423824,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 58535 414 (11587-R)⟩
def p535:CachedProfile:=⟨⟨38532,286,7610⟩,⟨⟨⟨71017548459888,893752597729038264⟩,⟨19680208874355744,1013980528704⟩,⟨3735296136,144996725407248⟩,⟨356098231632,0⟩⟩,⟨⟨70576188579192,13489963816680⟩,⟨99390222360,1013976175212⟩,⟨3735296136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨70878829122320,892090097033087792⟩,⟨19712693230890744,1015654234336⟩,⟨3754543758,145743879598044⟩,⟨359184686182,0⟩⟩,⟨⟨70439898377676,13440378169296⟩,⟨99371130264,1015649873658⟩,⟨3754543758,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 38818 287 (7610-R)⟩
def p536:CachedProfile:=⟨⟨60354,439,12303⟩,⟨⟨⟨282156104247056,5551901771764152656⟩,⟨119776642568342880,3940491786944⟩,⟨14227435104,864928462277472⟩,⟨2081948003552,0⟩⟩,⟨⟨280292227946976,55215647860896⟩,⟨398724679008,3940480984032⟩,⟨14227435104,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨281813898522090,5545506420726444030⟩,⟨119912884127071200,3944973982400⟩,⟨14276064000,867884758752000⟩,⟨2093822720000,0⟩⟩,⟨⟨279956374317060,55090060951980⟩,⟨398723978400,3944963167200⟩,⟨14276064000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 60793 440 (12303-R)⟩
def p537:CachedProfile:=⟨⟨4326,32,810⟩,⟨⟨⟨95105944048,134714806271224⟩,⟨2957560094208,1357393408⟩,⟨4982784,21714972672⟩,⟨53149696,0⟩⟩,⟨⟨94566778272,17176882680⟩,⟨126126720,1357341504⟩,⟨4982784,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨93374543440,132367104838672⟩,⟨2997328659336,1375647504⟩,⟨5207598,22694712084⟩,⟨57283578,0⟩⟩,⟨⟨92862604836,16588604976⟩,⟨125613576,1375594902⟩,⟨5207598,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4358 33 (810-R)⟩
def p538:CachedProfile:=⟨⟨2160,16,407⟩,⟨⟨⟨11936579784,8439342209832⟩,⟨185491422720,170511360⟩,⟨626688,1363673088⟩,⟨3342336,0⟩⟩,⟨⟨11867219376,2168027136⟩,⟨15941376,170498304⟩,⟨626688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨11504916230,8146964953850⟩,⟨190320803256,174951760⟩,⟨683196,1486634496⟩,⟨3871444,0⟩⟩,⟨⟨11442348636,2021617152⟩,⟨15793884,174938364⟩,⟨683196,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2176 17 (407-R)⟩
def p539:CachedProfile:=⟨⟨7984,54,2013⟩,⟨⟨⟨821683479746,2108683384192166⟩,⟨42162615259920,10491038784⟩,⟨35236944,283234555872⟩,⟨634264992,0⟩⟩,⟨⟨813490034316,195525089496⟩,⟨1313554968,10490821272⟩,⟨35236944,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨815409942000,2093684486574000⟩,⟨42644871720000,10611040000⟩,⟨36300000,291779400000⟩,⟨665500000,0⟩⟩,⟨⟨807385788000,192815544000⟩,⟨1319340000,10610820000⟩,⟨36300000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8038 55 (2013-R)⟩
def p540:CachedProfile:=⟨⟨25454,190,5414⟩,⟨⟨⟨22160678351040,183504075131201160⟩,⟨4059588369128400,316614183600⟩,⟨1172889000,30077565516000⟩,⟨74282970000,0⟩⟩,⟨⟨22001679417180,4510801653840⟩,⟨33421163400,316612125900⟩,⟨1172889000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨22099295291568,183022986550618368⟩,⟨4070403505846656,317457687976⟩,⟨1182203286,30316421066184⟩,⟨75266942542,0⟩⟩,⟨⟨21941525125080,4487505105600⟩,⟨33423548400,317455624794⟩,⟨1182203286,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25644 191 (5414-R)⟩
def p541:CachedProfile:=⟨⟨28803,206,6326⟩,⟨⟨⟨33213387768930,310521478013741934⟩,⟨6580946356034076,453721165992⟩,⟨1610955432,46732206126888⟩,⟨110618939664,0⟩⟩,⟨⟨32959825056792,6966442076508⟩,⟨49470408072,453718559268⟩,⟨1610955432,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨33134310173326,309823757024750866⟩,⟨6598259872089930,454914855756⟩,⟨1623034422,47082605547798⟩,⟨111989375118,0⟩⟩,⟨⟨32882425501020,6935643917424⟩,⟨49490788752,454912242174⟩,⟨1623034422,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29009 207 (6326-R)⟩
def p542:CachedProfile:=⟨⟨117362,790,26812⟩,⟨⟨⟨2342243881951592,88967994563908894016⟩,⟨1774220418855915360,30032900238640⟩,⟨100403959800,11862928658289600⟩,⟨26439709414000,0⟩⟩,⟨⟨2322962126829768,509644036510272⟩,⟨3407634139440,30032857874100⟩,⟨100403959800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2340920345587344,88920732024741183240⟩,⟨1775538709092829800,30055215496488⟩,⟨100605750714,11886770658360528⟩,⟨26526382938258,0⟩⟩,⟨⟨2321668771862052,509111959773024⟩,⟨3408385471092,30055173100470⟩,⟨100605750714,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 118152 791 (26812-R)⟩
def p543:CachedProfile:=⟨⟨44058,299,11078⟩,⟨⟨⟨137592849987954,1948951886508629910⟩,⟨39106794852004230,1763281657332⟩,⟨5942842074,263606645876418⟩,⟨592303260042,0⟩⟩,⟨⟨136232229156912,32664449201004⟩,⟨220183292628,1763275032090⟩,⟨5942842074,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨137401830118270,1946432046604034890⟩,⟨39188003597109000,1766943294000⟩,⟨5975100000,265037510700000⟩,⟨597510000000,0⟩⟩,⟨⟨136046358655620,32581944648720⟩,⟨220361688000,1766936655000⟩,⟨5975100000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 44357 300 (11078-R)⟩
def p544:CachedProfile:=⟨⟨65265,452,14352⟩,⟨⟨⟨386709986784382,8189746066975964026⟩,⟨168108903568463448,5116164512272⟩,⟨17594251872,1156241450272224⟩,⟨2650867282048,0⟩⟩,⟨⟨383751670750068,81223947129312⟩,⟨558656422272,5116151537160⟩,⟨17594251872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨386303990190274,8181633654579004750⟩,⟨168316487648956530,5122482083004⟩,⟨17654951106,1160230421833002⟩,⟨2665897617006,0⟩⟩,⟨⟨383354319117432,81065566267764⟩,⟨558800637876,5122469091870⟩,⟨17654951106,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 65717 453 (14352-R)⟩
def p545:CachedProfile:=⟨⟨21398,142,5419⟩,⟨⟨⟨15885155851460,109204486297490180⟩,⟨2142596661493920,198942704320⟩,⟨655733280,14124494851200⟩,⟨31038041920,0⟩⟩,⟨⟨15725761017240,3795905455200⟩,⟨25024074960,198941165040⟩,⟨655733280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨15840027914130,108915738427140150⟩,⟨2152111883458680,199826216304⟩,⟨663283764,14287132276560⟩,⟨31616526084,0⟩⟩,⟨⟨15681864004500,3776319133200⟩,⟨25070270940,199824670188⟩,⟨663283764,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 21540 143 (5419-R)⟩
def p546:CachedProfile:=⟨⟨135296,724,28972⟩,⟨⟨⟨3337882920140552,146530876801804310144⟩,⟨2328574751645972928,34238771824096⟩,⟨91121707488,12394374652517760⟩,⟨21990705407104,0⟩⟩,⟨⟨3313555774762800,685055825586720⟩,⟨3646378604064,34238729871192⟩,⟨91121707488,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨3336029006086802,146453920395337143734⟩,⟨2330583788569132200,34268312248400⟩,⟨91326292500,12422202305850000⟩,⟨22070520687500,0⟩⟩,⟨⟨3311739618061140,684346658112720⟩,⟨3647635106100,34268270259300⟩,⟨91326292500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 136020 725 (28972-R)⟩
def p547:CachedProfile:=⟨⟨2934,21,429⟩,⟨⟨⟨22934846790,22231186481970⟩,⟨473147600940,320276040⟩,⟨1137780,3362139900⟩,⟨7964460,0⟩⟩,⟨⟨22853167860,3270653100⟩,⟨23243220,320257980⟩,⟨1137780,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨22108543170,21452141045610⟩,⟨478385687340,323822840⟩,⟨1205160,3561247800⟩,⟨8837840,0⟩⟩,⟨⟨22034961180,3046191300⟩,⟨22678920,323804580⟩,⟨1205160,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2955 22 (429-R)⟩
def p548:CachedProfile:=⟨⟨3769,26,698⟩,⟨⟨⟨62127068274,76668574318338⟩,⟨1570606639524,827789352⟩,⟨2835144,10759371480⟩,⟨24571248,0⟩⟩,⟨⟨61781207268,11109528540⟩,⟨76112712,827753004⟩,⟨2835144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨60723003564,75008182520988⟩,⟨1596010949928,841180464⟩,⟨2991816,11353941720⟩,⟨26926344,0⟩⟩,⟨⟨60398733528,10637506440⟩,⟨75681864,841143528⟩,⟨2991816,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3795 27 (698-R)⟩
def p549:CachedProfile:=⟨⟨1755,12,318⟩,⟨⟨⟨6142066194,3532309211970⟩,⟨71727341400,81199536⟩,⟨275616,487013472⟩,⟨1102464,0⟩⟩,⟨⟨6108680292,1075488084⟩,⟨7303824,81191880⟩,⟨275616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨5839086384,3364797328560⟩,⟨74050086240,83829824⟩,⟨308256,544688352⟩,⟨1335776,0⟩⟩,⟨⟨5810102112,976571424⟩,⟨7184736,83821920⟩,⟨308256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1767 13 (318-R)⟩
def p550:CachedProfile:=⟨⟨15466,105,3161⟩,⟨⟨⟨4758262155042,23976627453929550⟩,⟨482999574837780,62039388600⟩,⟨209166300,3256928457300⟩,⟨7320820500,0⟩⟩,⟨⟨4726569229836,933800530932⟩,⟨6296901660,62038724580⟩,⟨209166300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨4734201049842,23861469214788450⟩,⟨485286419800836,62333132520⟩,⟨212158152,3303514584792⟩,⟨7496254704,0⟩⟩,⟨⟨4702956192516,924960562812⟩,⟨6296693832,62332465356⟩,⟨212158152,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 15571 106 (3161-R)⟩
def p551:CachedProfile:=⟨⟨17332,100,3668⟩,⟨⟨⟨6936852291864,39054311934793920⟩,⟨668965746744000,76752544800⟩,⟨220140000,3837480480000⟩,⟨7338000000,0⟩⟩,⟨⟨6887360827992,1407587840064⟩,⟨8074735200,76751811000⟩,⟨220140000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨6904462327672,38881640430233536⟩,⟨672708893888304,77182015976⟩,⟨223585518,3897542749776⟩,⟨7527379106,0⟩⟩,⟨⟨6855614528568,1395336351552⟩,⟨8084498136,77181278070⟩,⟨223585518,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 17432 101 (3668-R)⟩
def p552:CachedProfile:=⟨⟨3267,20,715⟩,⟨⟨⟨48265606540,51137901500956⟩,⟨928434250080,564952640⟩,⟨1718400,5648380800⟩,⟨11456000,0⟩⟩,⟨⟨47894862456,10096480680⟩,⟨61432800,564924000⟩,⟨1718400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨47035658274,49905469954890⟩,⟨951706946610,579115908⟩,⟨1849554,6079483998⟩,⟨12946878,0⟩⟩,⟨⟨46690507452,9622403244⟩,⟨61475652,579086550⟩,⟨1849554,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3287 21 (715-R)⟩
def p553:CachedProfile:=⟨⟨5542,27,1241⟩,⟨⟨⟨240736866210,431502401556054⟩,⟨6240592156572,2241278424⟩,⟨5432508,30253637052⟩,⟨48892572,0⟩⟩,⟨⟨238810252212,51501733308⟩,⟨249694164,2241211356⟩,⟨5432508,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨237185046350,425499872769650⟩,⟨6383135812200,2292474800⟩,⟨5762400,32090805600⟩,⟨53782400,0⟩⟩,⟨⟨235336136700,50100951600⟩,⟨251899200,2292406200⟩,⟨5762400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5569 28 (1241-R)⟩
def p554:CachedProfile:=⟨⟨3684,26,788⟩,⟨⟨⟨67633534464,80994012021648⟩,⟨1694334464784,913447392⟩,⟨3200184,11872682640⟩,⟨27734928,0⟩⟩,⟨⟨67137755268,13839754320⟩,⟨96990192,913406364⟩,⟨3200184,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 3710 27 (788-R)⟩
def p555:CachedProfile:=⟨⟨44768,250,10174⟩,⟨⟨⟨128995127577800,1867391266482242600⟩,⟨30931603256400000,1374194800000⟩,⟨3815625000,171771806250000⟩,⟨317968750000,0⟩⟩,⟨⟨127940994403200,27961701708600⟩,⟨155280675000,1374189712500⟩,⟨3815625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45018 251 (10174-R)⟩
def p556:CachedProfile:=⟨⟨45268,250,10158⟩,⟨⟨⟨131535066876616,1926858818060666536⟩,⟨31572779810640000,1387272404000⟩,⟨3809625000,173406510750000⟩,⟨317468750000,0⟩⟩,⟨⟨130485885992616,28183413379176⟩,⟨154792683000,1387267324500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨131395286001696,1924930675549228176⟩,⟨31667867680076280,1391450471376⟩,⟨3836382894,174624476569092⟩,⟨320977368798,0⟩⟩,⟨⟨130349198733636,28127953337616⟩,⟨155106030312,1391445376578⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45518 251 (10158-R)⟩
def p557:CachedProfile:=⟨⟨45455,250,10158⟩,⟨⟨⟨132574878135234,1950572411858942478⟩,⟨31832728825828500,1392971603000⟩,⟨3809625000,174118910625000⟩,⟨317468750000,0⟩⟩,⟨⟨131525693451768,28299198306060⟩,⟨154792683000,1392966523500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨132434073723294,1948620926670899178⟩,⟨31928599587288474,1397166834732⟩,⟨3836382894,175341880170270⟩,⟨320977368798,0⟩⟩,⟨⟨131387982659508,28243510419960⟩,⟨155106030312,1397161739934⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45705 251 (10158-R)⟩
def p558:CachedProfile:=⟨⟨45459,250,10158⟩,⟨⟨⟨132597166656146,1951081780095897206⟩,⟨31838300874784500,1393093511000⟩,⟨3809625000,174134149125000⟩,⟨317468750000,0⟩⟩,⟨⟨131547981891408,28301674988988⟩,⟨154792683000,1393088431500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45709 251 (10158-R)⟩
def p559:CachedProfile:=⟨⟨45465,250,10158⟩,⟨⟨⟨132630603094754,1951845999622550618⟩,⟨31846659862528500,1393276373000⟩,⟨3809625000,174157006875000⟩,⟨317468750000,0⟩⟩,⟨⟨131581418208108,28305390013380⟩,⟨154792683000,1393271293500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45715 251 (10158-R)⟩
def p560:CachedProfile:=⟨⟨45472,250,10158⟩,⟨⟨⟨132669617819944,1952737842644763880⟩,⟨31856413401600000,1393489712000⟩,⟨3809625000,174183674250000⟩,⟨317468750000,0⟩⟩,⟨⟨131620432791072,28309724208504⟩,⟨154792683000,1393484632500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45722 251 (10158-R)⟩
def p561:CachedProfile:=⟨⟨45478,250,10158⟩,⟨⟨⟨132703063767376,1953502496900587336⟩,⟨31864774766550000,1393672574000⟩,⟨3809625000,174206532000000⟩,⟨317468750000,0⟩⟩,⟨⟨131653878616596,28313439232896⟩,⟨154792683000,1393667494500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45728 251 (10158-R)⟩
def p562:CachedProfile:=⟨⟨45485,250,10158⟩,⟨⟨⟨132742089586194,1954394847178940898⟩,⟨31874531079028500,1393885913000⟩,⟨3809625000,174233199375000⟩,⟨317468750000,0⟩⟩,⟨⟨131692904293188,28317773428020⟩,⟨154792683000,1393880833500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45735 251 (10158-R)⟩
def p563:CachedProfile:=⟨⟨45491,250,10158⟩,⟨⟨⟨132775545042450,1955159936287549110⟩,⟨31882894821184500,1394068775000⟩,⟨3809625000,174256057125000⟩,⟨317468750000,0⟩⟩,⟨⟨131726359627536,28321488452412⟩,⟨154792683000,1394063695500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45741 251 (10158-R)⟩
def p564:CachedProfile:=⟨⟨26034,193,5079⟩,⟨⟨⟨21622178513240,183964028867757080⟩,⟨4046466204973680,308575842080⟩,⟨1135349520,29776811861040⟩,⟨73040819120,0⟩⟩,⟨⟨21490867142640,4060147317840⟩,⟨29877928560,308573881200⟩,⟨1135349520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 26227 194 (5079-R)⟩
def p565:CachedProfile:=⟨⟨45209,250,10158⟩,⟨⟨⟨131207882770146,1919417295901487706⟩,⟨31490984982784500,1385474261000⟩,⟨3809625000,173181742875000⟩,⟨317468750000,0⟩⟩,⟨⟨130158703084908,28146882305988⟩,⟨154792683000,1385469181500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨131068423958526,1917496478515707966⟩,⟨31585826509612938,1389646912884⟩,⟨3836382894,174398129978346⟩,⟨320977368798,0⟩⟩,⟨⟨130022337888048,28091494151208⟩,⟨155106030312,1389641818086⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45459 251 (10158-R)⟩
def p566:CachedProfile:=⟨⟨45215,250,10158⟩,⟨⟨⟨131241136346754,1920173179298147118⟩,⟨31499298255028500,1385657123000⟩,⟨3809625000,173204600625000⟩,⟨317468750000,0⟩⟩,⟨⟨130191956539608,28150597330380⟩,⟨154792683000,1385652043500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨131101644802014,1918251617852105418⟩,⟨31594164819053274,1389830325612⟩,⟨3836382894,174421148275710⟩,⟨320977368798,0⟩⟩,⟨⟨130055558609748,28095201865080⟩,⟨155106030312,1389825230814⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45465 251 (10158-R)⟩
def p567:CachedProfile:=⟨⟨45220,250,10158⟩,⟨⟨⟨131268851013064,1920803234547627688⟩,⟨31506226820016000,1385809508000⟩,⟨3809625000,173223648750000⟩,⟨317468750000,0⟩⟩,⟨⟨130219671104328,28153693184040⟩,⟨154792683000,1385804428500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45470 251 (10158-R)⟩
def p568:CachedProfile:=⟨⟨45222,250,10158⟩,⟨⟨⟨131279937732944,1921055295448663880⟩,⟨31508998459350000,1385870462000⟩,⟨3809625000,173231268000000⟩,⟨317468750000,0⟩⟩,⟨⟨130230757783572,28154931525504⟩,⟨154792683000,1385865382500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨131140407994104,1919132865684075840⟩,⟨31603894237613520,1390044307128⟩,⟨3836382894,174448002955968⟩,⟨320977368798,0⟩⟩,⟨⟨130094321659752,28099527531264⟩,⟨155106030312,1390039212330⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45472 251 (10158-R)⟩
def p569:CachedProfile:=⟨⟨45224,250,10158⟩,⟨⟨⟨131291024940456,1921307378523302376⟩,⟨31511770220592000,1385931416000⟩,⟨3809625000,173238887250000⟩,⟨317468750000,0⟩⟩,⟨⟨130241844950448,28156169866968⟩,⟨154792683000,1385926336500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45474 251 (10158-R)⟩
def p570:CachedProfile:=⟨⟨45228,250,10158⟩,⟨⟨⟨131313200818376,1921811611197287336⟩,⟨31517314108800000,1386053324000⟩,⟨3809625000,173254125750000⟩,⟨317468750000,0⟩⟩,⟨⟨130264020747096,28158646549896⟩,⟨154792683000,1386048244500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 45478 251 (10158-R)⟩
def p571:CachedProfile:=⟨⟨24896,152,5555⟩,⟨⟨⟨21773494201308,175588667357149884⟩,⟨3179148942503808,253846795008⟩,⟨770194944,19291842957312⟩,⟨39023210496,0⟩⟩,⟨⟨21601768681032,4638425711040⟩,⟨28147584960,253845105984⟩,⟨770194944,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21731226905958,175267491447371034⟩,⟨3194304639107832,255056946192⟩,⟨778957884,19511337078432⟩,⟨39726852084,0⟩⟩,⟨⟨21560426072892,4621742240160⟩,⟨28230859260,255055249116⟩,⟨778957884,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25048 153 (5555-R)⟩
def p572:CachedProfile:=⟨⟨4930,17,1158⟩,⟨⟨⟨178003352994,282512684849130⟩,⟨2893400327250,1169806516⟩,⟨2009706,9942015582⟩,⟨11388334,0⟩⟩,⟨⟨176437708572,39836865204⟩,⟨136896444,1169767110⟩,⟨2009706,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨176335014654,280028622220590⟩,⟨3037164729660,1227931704⟩,⟨2233656,11049896232⟩,⟨13401936,0⟩⟩,⟨⟨174809374752,39152101464⟩,⟨142457616,1227890340⟩,⟨2233656,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4947 18 (1158-R)⟩
def p573:CachedProfile:=⟨⟨24917,161,5555⟩,⟨⟨⟨21823625544828,176216882764362204⟩,⟨3375458956248624,269199223104⟩,⟨864102456,21669961391568⟩,⟨46373498472,0⟩⟩,⟨⟨21651899691192,4643981155440⟩,⟨29814218280,269197434072⟩,⟨864102456,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25078 162 (5555-R)⟩
def p574:CachedProfile:=⟨⟨40018,250,10158⟩,⟨⟨⟨104082391017616,1337362635184226536⟩,⟨24709717515390000,1227268154000⟩,⟨3809625000,153405979500000⟩,⟨317468750000,0⟩⟩,⟨⟨103033316803116,24932767036176⟩,⟨154792683000,1227263074500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨103935811731438,1335610433219350914⟩,⟨24776809631937864,1230600466704⟩,⟨3835248876,154437801738768⟩,⟨320882489292,0⟩⟩,⟨⟨102890757893532,24868994121360⟩,⟨155014342020,1230595373412⟩,⟨3835248876,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40268 251 (10158-R)⟩
def p575:CachedProfile:=⟨⟨132288,32,41910⟩,⟨⟨⟨4770933541682080,197281385971019055400⟩,⟨140890696309712640,2129545520896⟩,⟨257501184,34072556666880⟩,⟨2746679296,0⟩⟩,⟨⟨4697307954035940,1394512548739200⟩,⟨337246081920,2129542838592⟩,⟨257501184,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 132320 33 (41910-R)⟩
def p576:CachedProfile:=⟨⟨24394,178,5079⟩,⟨⟨⟨19059586178440,151408574585298280⟩,⟨3275844549420480,266635057280⟩,⟨965728320,23729876279040⟩,⟨57299880320,0⟩⟩,⟨⟨18928291622640,3803940210240⟩,⟨27555809760,266633248800⟩,⟨965728320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨19007470208664,151016007638682072⟩,⟨3285817866352728,267446839896⟩,⟨974110482,23935842763704⟩,⟨58121925426,0⟩⟩,⟨⟨18877179904164,3784494224304⟩,⟨27568959228,267445025910⟩,⟨974110482,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24572 179 (5079-R)⟩
def p577:CachedProfile:=⟨⟨40518,250,9205⟩,⟨⟨⟨95707266433338,1254775270679753214⟩,⟨22951224063306000,1125949036000⟩,⟨3452250000,140741328000000⟩,⟨287687500000,0⟩⟩,⟨⟨94926472790772,20728382787840⟩,⟨127111845000,1125944433000⟩,⟨3452250000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨95594844093188,1253388877953420164⟩,⟨23017998236171664,1129224879904⟩,⟨3476143176,141715404999168⟩,⟨290837312392,0⟩⟩,⟨⟨94816590650232,20683372469760⟩,⟨127343173320,1129220263512⟩,⟨3476143176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40768 251 (9205-R)⟩
def p578:CachedProfile:=⟨⟨40518,250,10094⟩,⟨⟨⟨105815481658320,1378458801305242440⟩,⟨25167592306710000,1234679070000⟩,⟨3785625000,154332360000000⟩,⟨315468750000,0⟩⟩,⟨⟨104786090752980,24925293469440⟩,⟨152848395000,1234674022500⟩,⟨3785625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 40768 251 (10094-R)⟩
def p579:CachedProfile:=⟨⟨25064,155,5143⟩,⟨⟨⟨20310837340056,165719393257042776⟩,⟨3042612572988240,241297735520⟩,⟨741507600,18700080164400⟩,⟨38311226000,0⟩⟩,⟨⟨20174516777328,4003101447888⟩,⟨24603700560,241296140880⟩,⟨741507600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25219 156 (5143-R)⟩
def p580:CachedProfile:=⟨⟨25064,155,5111⟩,⟨⟨⟨20176099595640,164675529940265784⟩,⟨3023684663291280,239796660960⟩,⟨736894800,18583749961200⟩,⟨38072898000,0⟩⟩,⟨⟨20042304451632,3953446245648⟩,⟨24298511760,239795076240⟩,⟨736894800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25219 156 (5111-R)⟩
def p581:CachedProfile:=⟨⟨25064,155,5079⟩,⟨⟨⟨20041518875480,163631988267850520⟩,⟨3004756757403600,238295586400⟩,⟨732282000,18467419758000⟩,⟨37834570000,0⟩⟩,⟨⟨19910217746160,3904100934480⟩,⟨23995227600,238294011600⟩,⟨732282000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19999494447270,163305946823318130⟩,⟨3018189153966480,239360865120⟩,⟨740301120,18669653945280⟩,⟨38495658240,0⟩⟩,⟨⟨19868966288340,3888744076620⟩,⟨24055040880,239359283280⟩,⟨740301120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨19986890085810,163208140420466754⟩,⟨3016403214768216,239219231472⟩,⟨739863072,18658606812768⟩,⟨38472879744,0⟩⟩,⟨⟨19856593224612,3884142920508⟩,⟨24026578992,239217650568⟩,⟨739863072,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25219 156 (5079-R)⟩
def p582:CachedProfile:=⟨⟨25162,154,5872⟩,⟨⟨⟨23597804021344,191778669780595072⟩,⟨3478004215963200,274769479600⟩,⟨835704408,21156692792928⟩,⟨42899492944,0⟩⟩,⟨⟨23395003364376,5238324341376⟩,⟨31865300544,274767670716⟩,⟨835704408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25316 155 (5872-R)⟩
def p583:CachedProfile:=⟨⟨40768,250,9523⟩,⟨⟨⟨100465273827196,1322806764437595676⟩,⟨24036128855820000,1171985344000⟩,⟨3571500000,146495787000000⟩,⟨297625000000,0⟩⟩,⟨⟨99600784490136,22321270073616⟩,⟨136045578000,1171980582000⟩,⟨3571500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨100350731783926,1321391941420397866⟩,⟨24106934704409400,1175437803136⟩,⟨3596349084,147515046727512⟩,⟨300894540028,0⟩⟩,⟨⟨99488961227556,22274418493656⟩,⟨136303063092,1175433027108⟩,⟨3596349084,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨100316374737688,1320967515722277064⟩,⟨24099333104476704,1175067158464⟩,⟨3595215066,147468531577188⟩,⟨300799660522,0⟩⟩,⟨⟨99455418702192,22260372617880⟩,⟨136217112660,1175062383942⟩,⟨3595215066,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41018 251 (9523-R)⟩
def p584:CachedProfile:=⟨⟨24799,165,5143⟩,⟨⟨⟨19915870577736,160764247049348136⟩,⟨3173742374029920,254268125760⟩,⟨840272400,20976560193600⟩,⟨46214982000,0⟩⟩,⟨⟨19779552638448,3962624392128⟩,⟨26191036080,254266428240⟩,⟨840272400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24964 166 (5143-R)⟩
def p585:CachedProfile:=⟨⟨25162,154,5079⟩,⟨⟨⟨20190932577160,165519626169122920⟩,⟨3008380332914880,237668816000⟩,⟨722863680,18300016922880⟩,⟨37107002240,0⟩⟩,⟨⟨20059630462320,3919117302720⟩,⟨23840419680,237667251360⟩,⟨722863680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20148614027490,165189868842935430⟩,⟨3021954712709400,238741230000⟩,⟨730840500,18501958098000⟩,⟨37760092500,0⟩⟩,⟨⟨20018084884980,3903701377680⟩,⟨23900841900,238739658300⟩,⟨730840500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 13=>⟨⟨⟨20135921429592,165090947675632920⟩,⟨3020166545552280,238599963000⟩,⟨730408050,18491010193800⟩,⟨37737749250,0⟩⟩,⟨⟨20005623585396,3899082524112⟩,⟨23872562460,238598392230⟩,⟨730408050,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25316 155 (5079-R)⟩
def p586:CachedProfile:=⟨⟨24172,177,4602⟩,⟨⟨⟨16862348597666,133351561445293646⟩,⟨2898240981279930,238061139276⟩,⟨865244322,21067833996378⟩,⟨51049414998,0⟩⟩,⟨⟨16764640247160,3094710078564⟩,⟨22496352372,238059509814⟩,⟨865244322,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨16823603715486,133058930429059626⟩,⟨2908283135512140,238886008584⟩,⟨873147672,21260272665528⟩,⟨51806761872,0⟩⟩,⟨⟨16726529916420,3081276735264⟩,⟨22525247808,238884373476⟩,⟨873147672,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨16808109621966,132941885130928146⟩,⟨2905750300191804,238677965032⟩,⟨872387256,21241757296344⟩,⟨51761643856,0⟩⟩,⟨⟨16711288871628,3075911579208⟩,⟨22486026576,238676331348⟩,⟨872387256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24349 178 (4602-R)⟩
def p587:CachedProfile:=⟨⟨24172,177,4761⟩,⟨⟨⟨17480267336450,138007891679998214⟩,⟨2998355627941812,246284411304⟩,⟨895132188,21795573645612⟩,⟨52812799092,0⟩⟩,⟨⟨17372094606372,3312225928908⟩,⟨24077538684,246282725556⟩,⟨895132188,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24349 178 (4761-R)⟩
def p588:CachedProfile:=⟨⟨25026,149,5237⟩,⟨⟨⟨20637858644622,167909681111928714⟩,⟨2967899212246428,235783813896⟩,⟨697733028,17565428979900⟩,⟨34654073724,0⟩⟩,⟨⟨20493936638100,4143513876300⟩,⟨24523676964,235782252972⟩,⟨697733028,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25175 150 (5237-R)⟩
def p589:CachedProfile:=⟨⟨25354,138,5111⟩,⟨⟨⟨20600737087464,170058973959037512⟩,⟨2750653165634496,215807455872⟩,⟨584117568,14890325043456⟩,⟨26869408128,0⟩⟩,⟨⟨20466939152304,3996242979264⟩,⟨21633513696,215806044960⟩,⟨584117568,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25492 139 (5111-R)⟩
def p590:CachedProfile:=⟨⟨25561,133,5079⟩,⟨⟨⟨20778656593480,173014635004932520⟩,⟨2676311902188960,208324135040⟩,⟨539160720,13853195539680⟩,⟨23902791920,0⟩⟩,⟨⟨20647350638160,3977634696480⟩,⟨20589453360,208322783760⟩,⟨539160720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20735181106770,172670123494368630⟩,⟨2691126524520720,209477311680⟩,⟨546221520,14034615734880⟩,⟨24397894560,0⟩⟩,⟨⟨20604648131340,3961988592120⟩,⟨20662663320,209475952920⟩,⟨546221520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 14=>⟨⟨⟨20717795172118,172532327548518058⟩,⟨2689003315191024,209312043584⟩,⟨545790576,14023543059744⟩,⟨24378645728,0⟩⟩,⟨⟨20587570536660,3955738783560⟩,⟨20630069160,209310685896⟩,⟨545790576,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25694 134 (5079-R)⟩
def p591:CachedProfile:=⟨⟨24689,151,5079⟩,⟨⟨⟨19463225909640,156394733510943720⟩,⟨2839894735479840,228657343040⟩,⟨694974480,17263166083200⟩,⟨34980382160,0⟩⟩,⟨⟨19331928630960,3845428732800⟩,⟨23375995920,228655808880⟩,⟨694974480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24840 152 (5079-R)⟩
def p592:CachedProfile:=⟨⟨24672,148,5083⟩,⟨⟨⟨19449287210964,156143321875269588⟩,⟨2781180840123072,224110366336⟩,⟨668159616,16583721669120⟩,⟨32962541056,0⟩⟩,⟨⟨19317680097528,3848386470240⟩,⟨22947671136,224108861472⟩,⟨668159616,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24820 149 (5083-R)⟩
def p593:CachedProfile:=⟨⟨24794,145,5087⟩,⟨⟨⟨19646395432416,158516483624680416⟩,⟨2753160499051200,220793861760⟩,⟨641851200,16007127076800⟩,⟨31022808000,0⟩⟩,⟨⟨19514476582080,3872925347904⟩,⟨22517910720,220792386240⟩,⟨641851200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24939 146 (5087-R)⟩
def p594:CachedProfile:=⟨⟨24794,145,5111⟩,⟨⟨⟨19745323215480,159273809212075704⟩,⟨2766147318655920,221835342240⟩,⟨644878800,16082632393200⟩,⟨31169142000,0⟩⟩,⟨⟨19611530934192,3909552159888⟩,⟨22730865840,221833859760⟩,⟨644878800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨19683483026670,158800459625888694⟩,⟨2777051456555436,222709826712⟩,⟨651885912,16257382759368⟩,⟨31725114384,0⟩⟩,⟨⟨19550863704552,3886640201808⟩,⟨22753497312,222708338388⟩,⟨651885912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24939 146 (5111-R)⟩
def p595:CachedProfile:=⟨⟨24904,142,5111⟩,⟨⟨⟨19909373562792,161323805361515400⟩,⟨2732211212421312,218177706240⟩,⟨618470208,15490204829568⟩,⟨29274256512,0⟩⟩,⟨⟨19775580187536,3926325971232⟩,⟨22260572064,218176254432⟩,⟨618470208,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25046 143 (5111-R)⟩
def p596:CachedProfile:=⟨⟨2984,24,619⟩,⟨⟨⟨34862284420,33909457326340⟩,⟨807921682560,537227520⟩,⟨2142720,6445301760⟩,⟨17141760,0⟩⟩,⟨⟨34620994680,6926461440⟩,⟨55264320,537197760⟩,⟨2142720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 3008 25 (619-R)⟩
def p597:CachedProfile:=⟨⟨24273,161,5079⟩,⟨⟨⟨18853449572680,148883111267873320⟩,⟨2929795900741920,239815502080⟩,⟨790072080,19304621202720⟩,⟨42400534960,0⟩⟩,⟨⟨18722156418960,3782576717280⟩,⟨24924075120,239813866320⟩,⟨790072080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24434 162 (5079-R)⟩
def p598:CachedProfile:=⟨⟨25002,139,5111⟩,⟨⟨⟨20055614335992,163158635013756120⟩,⟨2694815367771024,214378365600⟩,⟨592613712,14898901333392⟩,⟨27457768656,0⟩⟩,⟨⟨19921819989456,3941218607472⟩,⟨21790278288,214376944464⟩,⟨592613712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25141 140 (5111-R)⟩
def p599:CachedProfile:=⟨⟨25046,142,5237⟩,⟨⟨⟨20658435698106,168168759074299422⟩,⟨2831389569870768,224822754144⟩,⟨633714192,15961993068096⟩,⟨29995805088,0⟩⟩,⟨⟨20514513555396,4145653525968⟩,⟨23371557912,224821266552⟩,⟨633714192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25188 143 (5237-R)⟩
def p600:CachedProfile:=⟨⟨25078,138,5237⟩,⟨⟨⟨20702791584954,168727682094011262⟩,⟨2757753067666320,218732594400⟩,⟨598514832,15092150003712⟩,⟨27531682272,0⟩⟩,⟨⟨20558869148916,4150262002176⟩,⟨22713204168,218731148712⟩,⟨598514832,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25216 139 (5237-R)⟩
def p601:CachedProfile:=⟨⟨40267,250,10158⟩,⟨⟨⟨105308529307954,1362126008690057830⟩,⟨25016247028792500,1234856927000⟩,⟨3809625000,154354576125000⟩,⟨317468750000,0⟩⟩,⟨⟨104259450034272,25086940548444⟩,⟨154792683000,1234851847500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨105194564495214,1360753766362524690⟩,⟨25091588498288490,1238575962588⟩,⟨3836382894,155438725716198⟩,⟨320977368798,0⟩⟩,⟨⟨104148578737452,25037573825304⟩,⟨155106030312,1238570867790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40517 251 (10158-R)⟩
def p602:CachedProfile:=⟨⟨24480,176,5396⟩,⟨⟨⟨20472451627992,162646042046564160⟩,⟨3464729140029696,281048127360⟩,⟨1003064832,24731566497792⟩,⟨58846470144,0⟩⟩,⟨⟨20315042035176,4308223554432⟩,⟨30753055872,281046227616⟩,⟨1003064832,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20431614367192,162339965455901560⟩,⟨3477958779293352,282121284120⟩,⟨1012615938,24967058567328⟩,⟨59744340342,0⟩⟩,⟨⟨20275077261996,4292271615552⟩,⟨30813273684,282119377122⟩,⟨1012615938,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24656 177 (5396-R)⟩
def p603:CachedProfile:=⟨⟨24705,157,5111⟩,⟨⟨⟨19627702853544,157809420197974152⟩,⟨2976603952940064,239452541568⟩,⟨756034128,18796520490336⟩,⟨39565786032,0⟩⟩,⟨⟨19493911359504,3897481286304⟩,⟨24612040944,239450936400⟩,⟨756034128,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19586702320434,157496710638178902⟩,⟨2989703251611216,240506320832⟩,⟨764197968,18999489880416⟩,⟨40247759648,0⟩⟩,⟨⟨19453693563084,3882246349944⟩,⟨24671986296,240504708600⟩,⟨764197968,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24862 158 (5111-R)⟩
def p604:CachedProfile:=⟨⟨24705,157,5079⟩,⟨⟨⟨19496554976840,156808859564640680⟩,⟨2957970758082720,237953621120⟩,⟨751301520,18678858390240⟩,⟨39318112880,0⟩⟩,⟨⟨19365257474640,3848834507040⟩,⟨24304843440,237952026000⟩,⟨751301520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19455603312210,156496249693022070⟩,⟨2970951375197520,238997853120⟩,⟨759404880,18880324126560⟩,⟨39995323680,0⟩⟩,⟨⟨19325078773260,3833695040760⟩,⟨24363438840,238996251000⟩,⟨759404880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24862 158 (5079-R)⟩
def p605:CachedProfile:=⟨⟨24754,155,5079⟩,⟨⟨⟨19567856830680,157696041755515320⟩,⟨2931341093211600,235366458400⟩,⟨732282000,18240412338000⟩,⟨37834570000,0⟩⟩,⟨⟨19436558850960,3856110479280⟩,⟨23995227600,235364883600⟩,⟨732282000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19526764808070,157381685433666330⟩,⟨2944445291732880,236418642720⟩,⟨740301120,18440160598080⟩,⟨38495658240,0⟩⟩,⟨⟨19396239792540,3840942392820⟩,⟨24055040880,236417060880⟩,⟨740301120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24909 156 (5079-R)⟩
def p606:CachedProfile:=⟨⟨24799,153,5079⟩,⟨⟨⟨19633208399240,158510657127663080⟩,⟨2903515859789280,232730527680⟩,⟨713506320,17803409696640⟩,⟨36388822320,0⟩⟩,⟨⟨19501909982640,3862767219840⟩,⟨23685611760,232728973200⟩,⟨713506320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19591987731810,158194697206085670⟩,⟨2916740054788560,233790516960⟩,⟨721440720,18001388845440⟩,⟨37033956960,0⟩⟩,⟨⟨19461462280260,3847572948960⟩,⟨23746642920,233788955400⟩,⟨721440720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24952 154 (5079-R)⟩
def p607:CachedProfile:=⟨⟨24704,160,5396⟩,⟨⟨⟨20806000389720,166775361509434944⟩,⟨3203120128642560,257653643520⟩,⟨828979200,20611738828800⟩,⟨44212224000,0⟩⟩,⟨⟨20648588551752,4344568075008⟩,⟨27957323520,257651916480⟩,⟨828979200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24864 161 (5396-R)⟩
def p608:CachedProfile:=⟨⟨24652,159,5079⟩,⟨⟨⟨19419337219160,155849959756551320⟩,⟨2983374620315280,240490552800⟩,⟨770564880,19118485237680⟩,⟨40839938640,0⟩⟩,⟨⟨19288040235120,3840939303120⟩,⟨24614459280,240488937360⟩,⟨770564880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19378537557990,155539237514008530⟩,⟨2996228164924800,241526688000⟩,⟨778752000,19321615872000⟩,⟨41533440000,0⟩⟩,⟨⟨19248013536180,3825830892780⟩,⟨24671836800,241525065600⟩,⟨778752000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24811 160 (5079-R)⟩
def p609:CachedProfile:=⟨⟨24400,167,5071⟩,⟨⟨⟨19020034575824,151075134240018512⟩,⟨3067315971600864,249712839488⟩,⟨848718048,20850456285216⟩,⟨47245304672,0⟩⟩,⟨⟨18889358680224,3791195949024⟩,⟨25771552224,249711145440⟩,⟨848718048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24567 168 (5071-R)⟩
def p610:CachedProfile:=⟨⟨24374,170,5063⟩,⟨⟨⟨18953660427096,150412329424926456⟩,⟨3111657967287360,253560151680⟩,⟨878097600,21552027494400⟩,⟨49758864000,0⟩⟩,⟨⟨18823601426448,3775706408448⟩,⟨26151812640,253558429920⟩,⟨878097600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24544 171 (5063-R)⟩
def p611:CachedProfile:=⟨⟨24327,169,5071⟩,⟨⟨⟨18914022644592,149774830909662000⟩,⟨3086134765107264,251973105280⟩,⟨869168352,21291147950592⟩,⟨48963150496,0⟩⟩,⟨⟨18783347469216,3780239181312⟩,⟨26080193568,251971390944⟩,⟨869168352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18874167080042,149475621259890350⟩,⟨3098275159887120,252964338400⟩,⟨877750800,21501383596800⟩,⟨49739212000,0⟩⟩,⟨⟨18744262426836,3765346103232⟩,⟨26131157640,252962617320⟩,⟨877750800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24496 170 (5071-R)⟩
def p612:CachedProfile:=⟨⟨25168,144,5079⟩,⟨⟨⟨20184759848840,165441498765672680⟩,⟨2812142111178240,222200663040⟩,⟨632033280,15998026383360⟩,⟨30337597440,0⟩⟩,⟨⟨20053457774640,3918498071040⟩,⟨22292340480,222199200000⟩,⟨632033280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20142453450210,165111895236020070⟩,⟨2826096632353800,223303282800⟩,⟨639580500,16189061616000⟩,⟨30913057500,0⟩⟩,⟨⟨20011924348260,3903084581760⟩,⟨22358852100,223301812500⟩,⟨639580500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25312 145 (5079-R)⟩
def p613:CachedProfile:=⟨⟨25144,146,5095⟩,⟨⟨⟨20218442349560,165538317444008600⟩,⟨2855210311611840,225799927808⟩,⟨651758016,16482960224640⟩,⟨31718890112,0⟩⟩,⟨⟨20085897402480,3939795568800⟩,⟨22744569120,225798439776⟩,⟨651758016,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25290 147 (5095-R)⟩
def p614:CachedProfile:=⟨⟨24250,171,5015⟩,⟨⟨⟨18580608132504,146749329810986232⟩,⟨3069298164998736,251368112160⟩,⟨880037136,21491386898256⟩,⟨50162116752,0⟩⟩,⟨⟨18454209612432,3685896696240⟩,⟨25809276240,251366396688⟩,⟨880037136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18541057346694,146452983146782842⟩,⟨3081092374554192,252334037920⟩,⟨888585024,21700134871104⟩,⟨50945541376,0⟩⟩,⟨⟨18415412418492,3671213325780⟩,⟨25856790960,252332315856⟩,⟨888585024,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24421 172 (5015-R)⟩
def p615:CachedProfile:=⟨⟨24259,175,5047⟩,⟨⟨⟨18726508794856,147932795066232136⟩,⟨3164500197180000,259027014400⟩,⟨927570000,22664245380000⟩,⟨54108250000,0⟩⟩,⟨⟨18597678398160,3735067638624⟩,⟨26751118800,259025247600⟩,⟨927570000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24434 176 (5047-R)⟩
def p616:CachedProfile:=⟨⟨25426,137,5111⟩,⟨⟨⟨20711923077240,171478110250404792⟩,⟨2745952979122224,214840326816⟩,⟨575682768,14716178598384⟩,⟨26289513072,0⟩⟩,⟨⟨20578124416176,4007373265296⟩,⟨21476749104,214838926128⟩,⟨575682768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25563 138 (5111-R)⟩
def p617:CachedProfile:=⟨⟨41768,250,10475⟩,⟨⟨⟨116724211791588,1566384628033600164⟩,⟨27743589867636000,1320562656000⟩,⟨3928500000,165067713000000⟩,⟨327375000000,0⟩⟩,⟨⟨115573845782952,27665348698800⟩,⟨164604150000,1320557418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨116601833088638,1564854943977113714⟩,⟨27827974980764184,1324579304384⟩,⟨3956210796,166232065226328⟩,⟨331002969932,0⟩⟩,⟨⟨115454756757012,27612554762520⟩,⟨164947195140,1324574050452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42018 251 (10475-R)⟩
def p618:CachedProfile:=⟨⟨42018,250,10222⟩,⟨⟨⟨114930114193296,1554958418820852072⟩,⟨27396683147646000,1296337738000⟩,⟨3833625000,162039661500000⟩,⟨319468750000,0⟩⟩,⟨⟨113861056031436,26501910717648⟩,⟨156749259000,1296332626500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 42268 251 (10222-R)⟩
def p619:CachedProfile:=⟨⟨42018,250,11110⟩,⟨⟨⟨125965671530688,1693401020780717064⟩,⟨29776469632326000,1408941466000⟩,⟨4166625000,176114905500000⟩,⟨347218750000,0⟩⟩,⟨⟨124593278188092,31306185601680⟩,⟨185164815000,1408935910500⟩,⟨4166625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨125839973410088,1691835818711473664⟩,⟨29868668889470544,1413304099624⟩,⟨4196244606,177366867006408⟩,⟨351085798702,0⟩⟩,⟨⟨124471280765952,31249856728800⟩,⟨185570976600,1413298526922⟩,⟨4196244606,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42268 251 (11110-R)⟩
def p620:CachedProfile:=⟨⟨2984,24,754⟩,⟨⟨⟨43153184680,41441218006360⟩,⟨983869467840,654204480⟩,⟨2609280,7848714240⟩,⟨20874240,0⟩⟩,⟨⟨42719413020,10274184960⟩,⟨81974880,654168240⟩,⟨2609280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 3008 25 (754-R)⟩
def p621:CachedProfile:=⟨⟨25159,195,5111⟩,⟨⟨⟨20385513749160,167323184249038344⟩,⟨3844825066199520,303294551040⟩,⟨1166302800,29570441191200⟩,⟨75809682000,0⟩⟩,⟨⟨20251717224912,3974609465568⟩,⟨30569095440,303292557360⟩,⟨1166302800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20343030800370,166991863738468854⟩,⟨3856982251895136,304253565952⟩,⟨1175990592,29816065469568⟩,⟨76831385344,0⟩⟩,⟨⟨20210017022652,3959073041448⟩,⟨30605755152,304251565968⟩,⟨1175990592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25354 196 (5111-R)⟩
def p622:CachedProfile:=⟨⟨43767,250,10222⟩,⟨⟨⟨124186926011682,1754665875947820126⟩,⟨29710850342188500,1349977819000⟩,⟨3833625000,168744671625000⟩,⟨319468750000,0⟩⟩,⟨⟨123117832089768,27598528533612⟩,⟨156749259000,1349972707500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 44017 251 (10222-R)⟩
def p623:CachedProfile:=⟨⟨25360,187,5095⟩,⟨⟨⟨20617931599720,170615516361622696⟩,⟨3731718477575088,292148400544⟩,⟨1069212144,27315162642768⟩,⟨66647556976,0⟩⟩,⟨⟨20485384033296,3979832241840⟩,⟨29131742640,292146494640⟩,⟨1069212144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25547 188 (5095-R)⟩
def p624:CachedProfile:=⟨⟨25360,187,5079⟩,⟨⟨⟨20549062244440,170073496942704280⟩,⟨3720001753651920,291231137120⟩,⟨1065855120,27229400750640⟩,⟨66438302480,0⟩⟩,⟨⟨20417757782640,3954877932240⟩,⟨28949081040,291229237200⟩,⟨1065855120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20506038715110,169734775163429970⟩,⟨3732532699119120,292212167520⟩,⟨1075164480,27467226970560⟩,⟨67376974080,0⟩⟩,⟨⟨20375507230260,3939321342060⟩,⟨28989408240,292210261200⟩,⟨1075164480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25547 188 (5079-R)⟩
def p625:CachedProfile:=⟨⟨25449,185,5095⟩,⟨⟨⟨20754082338808,172357582507947928⟩,⟨3716994280577760,290008060160⟩,⟨1046463600,26825047922400⟩,⟨64531922000,0⟩⟩,⟨⟨20621533885680,3993385512480⟩,⟨28820173200,290006174640⟩,⟨1046463600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25634 186 (5095-R)⟩
def p626:CachedProfile:=⟨⟨25449,185,5079⟩,⟨⟨⟨20684785508680,171810093408737320⟩,⟨3705323788423200,289097516800⟩,⟨1043178000,26740824852000⟩,⟨64329310000,0⟩⟩,⟨⟨20553480162960,3968346221280⟩,⟨28639465200,289095637200⟩,⟨1043178000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20641494807570,171467953079551830⟩,⟨3718019081303280,290088040320⟩,⟨1052410320,26977486142880⟩,⟨65249439840,0⟩⟩,⟨⟨20510962440540,3952736653320⟩,⟨28681010280,290086154280⟩,⟨1052410320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25634 186 (5079-R)⟩
def p627:CachedProfile:=⟨⟨25360,187,5087⟩,⟨⟨⟨20583492038112,170344496694576096⟩,⟨3725860115469888,291689768832⟩,⟨1067533632,27272281696704⟩,⟨66542929728,0⟩⟩,⟨⟨20451567000768,3967345276992⟩,⟨29040340032,291687865920⟩,⟨1067533632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20540456320462,170005750109160346⟩,⟨3738422388714192,292673251808⟩,⟨1076860992,27510567762624⟩,⟨67483288832,0⟩⟩,⟨⟨20409306697668,3951764161692⟩,⟨29080974768,292671342480⟩,⟨1076860992,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25547 188 (5087-R)⟩
def p628:CachedProfile:=⟨⟨24620,142,5087⟩,⟨⟨⟨19377831061152,155179524607853856⟩,⟨2658063440026368,214691131392⟩,⟨615566592,15242659951104⟩,⟨29136818688,0⟩⟩,⟨⟨19245914011968,3845437967232⟩,⟨22052022912,214689686400⟩,⟨615566592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24762 143 (5087-R)⟩
def p629:CachedProfile:=⟨⟨24620,142,5143⟩,⟨⟨⟨19605844125704,156910171222463720⟩,⟨2687319346107840,217054084096⟩,⟨622341696,15410425076352⟩,⟨29457506944,0⟩⟩,⟨⟨19469528264592,3930560214624⟩,⟨22540164384,217052623200⟩,⟨622341696,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24762 143 (5143-R)⟩
def p630:CachedProfile:=⟨⟨42768,250,10190⟩,⟨⟨⟨118448311158888,1633384188046447464⟩,⟨28288718493696000,1315209696000⟩,⟨3821625000,164398664250000⟩,⟨318468750000,0⟩⟩,⟨⟨117389240670912,26803558219320⟩,⟨155769435000,1315204600500⟩,⟨3821625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 43018 251 (10190-R)⟩
def p631:CachedProfile:=⟨⟨9612,81,2493⟩,⟨⟨⟨1483638872886,4581929823163146⟩,⟨113886485395740,23499076536⟩,⟨98178804,951647147172⟩,⟨2650827708,0⟩⟩,⟨⟨1468090191996,361599807636⟩,⟨3021725412,23498672508⟩,⟨98178804,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1477071971316,4563093832081236⟩,⟨114830187509520,23693802912⟩,⟨100214496,971379109728⟩,⟨2739196224,0⟩⟩,⟨⟨1461709238616,358705283976⟩,⟨3034543824,23693395536⟩,⟨100214496,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 11=>⟨⟨⟨1476415691426,4561210642227902⟩,⟨114783957132468,23684264344⟩,⟨100174152,970988055336⟩,⟨2738093488,0⟩⟩,⟨⟨1461071471496,358416471348⟩,⟨3032100552,23683857132⟩,⟨100174152,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9693 82 (2493-R)⟩
def p632:CachedProfile:=⟨⟨24889,189,5143⟩,⟨⟨⟨20091947845896,162967043023585896⟩,⟨3668655345455520,292582571904⟩,⟨1102492944,27648318049632⟩,⟨69457055472,0⟩⟩,⟨⟨19955628733776,3980720017056⟩,⟨30000641328,292580627472⟩,⟨1102492944,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨20046082050096,162614064237598992⟩,⟨3680179480283760,293501654880⟩,⟨1111807800,27881916008400⟩,⟨70414494000,0⟩⟩,⟨⟨19910634601956,3963711716208⟩,⟨30030513840,293499704340⟩,⟨1111807800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25078 190 (5143-R)⟩
def p633:CachedProfile:=⟨⟨24889,189,5111⟩,⟨⟨⟨19958571777960,161940301913505672⟩,⟨3645832857212448,290762462592⟩,⟨1095634512,27476322291936⟩,⟨69024974256,0⟩⟩,⟨⟨19824778075536,3931342438176⟩,⟨29628507888,290760530256⟩,⟨1095634512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25078 190 (5111-R)⟩
def p634:CachedProfile:=⟨⟨24986,187,5095⟩,⟨⟨⟨20037911647208,163260806876587784⟩,⟨3623257597687728,287871551968⟩,⟨1069212144,26915277300912⟩,⟨66647556976,0⟩⟩,⟨⟨19905367892592,3921568756560⟩,⟨29131742640,287869646064⟩,⟨1069212144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25173 188 (5095-R)⟩
def p635:CachedProfile:=⟨⟨24986,187,5087⟩,⟨⟨⟨20004382634976,163001333246985312⟩,⟨3617569503839808,287419634304⟩,⟨1067533632,26873024118336⟩,⟨66542929728,0⟩⟩,⟨⟨19872461403456,3909264596928⟩,⟨29040340032,287417731392⟩,⟨1067533632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25173 188 (5087-R)⟩
def p636:CachedProfile:=⟨⟨25204,180,5143⟩,⟨⟨⟨20568542943816,168979540460022696⟩,⟨3579742322835840,282050046720⟩,⟨999993600,25383837542400⟩,⟨59999616000,0⟩⟩,⟨⟨20432220683568,4029292483968⟩,⟨28572039360,282048194880⟩,⟨999993600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25384 181 (5143-R)⟩
def p637:CachedProfile:=⟨⟨25234,177,5143⟩,⟨⟨⟨20610872950680,169517073147291480⟩,⟨3527572165338096,277644210720⟩,⟨966938256,24570868023216⟩,⟨57049357104,0⟩⟩,⟨⟨20474550412656,4033578289872⟩,⟨28095838704,277642389744⟩,⟨966938256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25411 178 (5143-R)⟩
def p638:CachedProfile:=⟨⟨25234,177,5111⟩,⟨⟨⟨20474268732792,168449584695357240⟩,⟨3505627356514992,275917030560⟩,⟨960923088,24418016589168⟩,⟨56694462192,0⟩⟩,⟨⟨20340471625776,3983545047312⟩,⟨27747332784,275915220912⟩,⟨960923088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25411 178 (5111-R)⟩
def p639:CachedProfile:=⟨⟨25234,177,5095⟩,⟨⟨⟨20406025569384,167915961338826792⟩,⟨3494654953734672,275053440480⟩,⟨957915504,24341590872144⟩,⟨56517014736,0⟩⟩,⟨⟨20273479389072,3958645519920⟩,⟨27573895440,275051636496⟩,⟨957915504,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25411 178 (5095-R)⟩
def p640:CachedProfile:=⟨⟨24568,186,5237⟩,⟨⟨⟨19977221017386,159663323286811566⟩,⟨3582019001311920,289412155008⟩,⟨1087283088,26914605560352⟩,⟨67411551456,0⟩⟩,⟨⟨19833303421260,4074222144744⟩,⟨30613449096,289410206472⟩,⟨1087283088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19936346598756,159354197104143396⟩,⟨3594401760161520,290412639616⟩,⟨1096907592,27152850532368⟩,⟨68373906568,0⟩⟩,⟨⟨19793250817320,4058679108144⟩,⟨30660620232,290410684344⟩,⟨1096907592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24754 187 (5237-R)⟩
def p641:CachedProfile:=⟨⟨24880,177,5237⟩,⟨⟨⟨20451568127022,165570263741127186⟩,⟨3492652692300588,278779371192⟩,⟨984607812,24671317945284⟩,⟨58091860908,0⟩⟩,⟨⟨20307647356668,4124092440852⟩,⟨29132153172,278777516940⟩,⟨984607812,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25057 178 (5237-R)⟩
def p642:CachedProfile:=⟨⟨25708,148,5079⟩,⟨⟨⟨21033204705160,176295099903679720⟩,⟨3015823736549760,233280915200⟩,⟨667633920,17262342635520⟩,⟨32936606720,0⟩⟩,⟨⟨20901897103920,4002713579520⟩,⟨22911572160,233279411520⟩,⟨667633920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25856 149 (5079-R)⟩
def p643:CachedProfile:=⟨⟨25728,146,5111⟩,⟨⟨⟨21202592927400,177787767361344264⟩,⟨2997979991942976,231739310592⟩,⟨653804352,16916533803648⟩,⟨31818478464,0⟩⟩,⟨⟨21068791086672,4056127053408⟩,⟨22887630432,231737817888⟩,⟨653804352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25874 147 (5111-R)⟩
def p644:CachedProfile:=⟨⟨24797,179,5111⟩,⟨⟨⟨19801971465192,159980701405972680⟩,⟨3424900938529824,274258186560⟩,⟨982761552,24545452522752⟩,⟨58638105936,0⟩⟩,⟨⟨19668178805616,3915352449792⟩,⟨28060861968,274256356464⟩,⟨982761552,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 24976 180 (5111-R)⟩
def p645:CachedProfile:=⟨⟨24880,177,5111⟩,⟨⟨⟨19926278364024,161535548492986392⟩,⟨3408635623704624,272073338208⟩,⟨960923088,24077849816016⟩,⟨56694462192,0⟩⟩,⟨⟨19792484876304,3928050381744⟩,⟨27747332784,272071528560⟩,⟨960923088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25057 178 (5111-R)⟩
def p646:CachedProfile:=⟨⟨25728,146,5079⟩,⟨⟨⟨21061586583880,176662144677742120⟩,⟨2979213009222720,230288673280⟩,⟨649711680,16810640008320⟩,⟨31619301760,0⟩⟩,⟨⟨20930278799760,4005500122080⟩,⟨22601956320,230287189920⟩,⟨649711680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25874 147 (5079-R)⟩
def p647:CachedProfile:=⟨⟨24756,182,5143⟩,⟨⟨⟨19875824949256,160264662860081896⟩,⟨3493445902914240,280173350912⟩,⟨1022339136,25495093373568⟩,⟨62021907584,0⟩⟩,⟨⟨19739507277456,3958497319776⟩,⟨28889506464,280171478496⟩,⟨1022339136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19834548146386,159949025015676886⟩,⟨3505811930732520,281165111808⟩,⟨1031595156,25725920000328⟩,⟨62927304516,0⟩⟩,⟨⟨19699023047676,3943120050216⟩,⟨28935398556,281163232764⟩,⟨1031595156,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24938 183 (5143-R)⟩
def p648:CachedProfile:=⟨⟨58470,426,13758⟩,⟨⟨⟨299386819599600,5657749721827864200⟩,⟨121989588238841328,4142556417840⟩,⟨14981569704,882354529286784⟩,⟨2127382897968,0⟩⟩,⟨⟨296780860101396,66892777083072⟩,⟨483841399032,4142544695172⟩,⟨14981569704,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨299103021287592,5652721569826013400⟩,⟨122169304177226712,4148659290440⟩,⟨15038860578,885728732601888⟩,⟨2140531155602,0⟩⟩,⟨⟨296503871763516,66776141800512⟩,⟨484131563244,4148647550502⟩,⟨15038860578,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 58896 427 (13758-R)⟩
def p649:CachedProfile:=⟨⟨38371,222,9793⟩,⟨⟨⟨92223834433386,1135183921503460446⟩,⟨19430640399629880,1006955693232⟩,⟨2896124976,111770151198768⟩,⟨214313248224,0⟩⟩,⟨⟨91283805970596,22209339556236⟩,⟨127755639144,1006951344696⟩,⟨2896124976,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨92099349500910,1133759263444486482⟩,⟨19494251056358676,1010252209864⟩,⟨2918694468,112641175603524⟩,⟨216956288788,0⟩⟩,⟨⟨91162770472956,22154946582036⟩,⟨128016818796,1010247847092⟩,⟨2918694468,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 38593 223 (9793-R)⟩
def p650:CachedProfile:=⟨⟨204232,79,63692⟩,⟨⟨⟨17244435460624974,1102884774388641205542⟩,⟨1260244674629984610,12336535389780⟩,⟨2385048078,487291557864258⟩,⟨62806266054,0⟩⟩,⟨⟨16986027896923176,4973012963225496⟩,⟨1922892179544,12336525326286⟩,⟨2385048078,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 204311 80 (63692-R)⟩
def p651:CachedProfile:=⟨⟨263888,1028,70902⟩,⟨⟨⟨31638382852453664,2661735787739459814152⟩,⟨30692073645877657440,231711854836000⟩,⟨449574935712,119099593669080192⟩,⟨154054344637312,0⟩⟩,⟨⟨31281909267970956,7990657873628976⟩,⟨31007550673008,231711709059432⟩,⟨449574935712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨31631928630481830,2661233862087316655610⟩,⟨30716296899632913240,231894729990000⟩,⟨450367430940,119309538334901040⟩,⟨154476028812420,0⟩⟩,⟨⟨31275651075435660,7987727962010160⟩,⟨31026333150540,231894584098380⟩,⟨450367430940,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 264916 1029 (70902-R)⟩
def p652:CachedProfile:=⟨⟨5271,46,1850⟩,⟨⟨⟨345732871170,568401456530526⟩,⟨14444604579564,5433336552⟩,⟨23500296,124951073832⟩,⟨360337872,0⟩⟩,⟨⟨339378140136,109243613700⟩,⟨945120600,5433166260⟩,⟨23500296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨343525353150,565141496713626⟩,⟨14678874126378,5521460924⟩,⟨24400614,129738064638⟩,⟨382276286,0⟩⟩,⟨⟨337272886356,108066110880⟩,⟨955258080,5521287870⟩,⟨24400614,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5317 47 (1850-R)⟩
def p653:CachedProfile:=⟨⟨25648,193,5083⟩,⟨⟨⟨21027144507100,176129775205014460⟩,⟨3931328593234584,304273841200⟩,⟨1136243496,29361668180136⟩,⟨73098331576,0⟩⟩,⟨⟨20895527012136,4006694390712⟩,⟨29925003576,304271878776⟩,⟨1136243496,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25841 194 (5083-R)⟩
def p654:CachedProfile:=⟨⟨25694,190,5095⟩,⟨⟨⟨21147896122808,177429693575971928⟩,⟨3892276267938240,300750835840⟩,⟨1103793600,28570593542400⟩,⟨69906928000,0⟩⟩,⟨⟨21015345121680,4032331692480⟩,⟨29599096800,300748899360⟩,⟨1103793600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | R=>parts 25884 191 (5095-R)⟩
def p655:CachedProfile:=⟨⟨218086,1524,40970⟩,⟨⟨⟨12199764882898320,870708417316061633400⟩,⟨18068318739871968960,164549363795712⟩,⟨570949567776,125386234579287360⟩,⟨290042380430208,0⟩⟩,⟨⟨12130975388401800,2211800186824200⟩,⟨15348952619280,164549238916104⟩,⟨570949567776,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨12195046744808340,870386545908472910100⟩,⟨18073555200799074000,164597052691200⟩,⟨571489785000,125504871683850000⟩,⟨290507307375000,0⟩⟩,⟨⟨12126332764818120,2210180927626800⟩,⟨15347779767000,164596927775400⟩,⟨571489785000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 219610 1525 (40970-R)⟩
def p656:CachedProfile:=⟨⟨110729,679,23037⟩,⟨⟨⟨1776803652781746,63994758744175717302⟩,⟨1164930903394820856,20912924565008⟩,⟨63728775348,7099895403969984⟩,⟨14423946153764,0⟩⟩,⟨⟨1764572175331716,354763004637888⟩,⟨2162179378044,20912893279404⟩,⟨63728775348,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨1775484825719490,63949727539278676422⟩,⟨1165836315539338560,20929178643840⟩,⟨63872236800,7115878157414400⟩,⟨14477707008000,0⟩⟩,⟨⟨1763278808644836,354270395894976⟩,⟨2162357004960,20929147333920⟩,⟨63872236800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 111408 680 (23037-R)⟩
def p657:CachedProfile:=⟨⟨250455,476,72881⟩,⟨⟨⟨29470460174972442,2331332205586896211110⟩,⟨13106542044442872816,104463350681760⟩,⟨99079872192,24862211409010752⟩,⟨15720673054464,0⟩⟩,⟨⟨29083300640052156,7997240792052612⟩,⟨15170252447952,104463281298096⟩,⟨99079872192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨29464513173916030,2330901269394281563390⟩,⟨13131734059149821766,104664139175340⟩,⟨99478864206,24962330874075786⟩,⟨15817139408754,0⟩⟩,⟨⟨29077560764432496,7994388082979112⟩,⟨15196699951704,104664069658314⟩,⟨99478864206,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 250931 477 (72881-R)⟩
def p658:CachedProfile:=⟨⟨29643,267,7446⟩,⟨⟨⟨42039188920344,401623836874738632⟩,⟨10672936389121248,713674129872⟩,⟨3185335098,95273372781180⟩,⟨283494823722,0⟩⟩,⟨⟨41625860045352,9951121964520⟩,⟨88831479924,713670153174⟩,⟨3185335098,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨41977203726384,401072147348074512⟩,⟨10698524156764512,715385139648⟩,⟨3204930528,95859472092480⟩,⟨286307127168,0⟩⟩,⟨⟨41565536653092,9924412932720⟩,⟨88924863456,715381153416⟩,⟨3204930528,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29910 268 (7446-R)⟩
def p659:CachedProfile:=⟨⟨79625,573,18744⟩,⟨⟨⟨756317298640120,19461537803447123440⟩,⟨414496553860514520,10336855869840⟩,⟨36927162630,2961484588600740⟩,⟨7053088062330,0⟩⟩,⟨⟨749728469904780,169068425660640⟩,⟨1207962890640,10336834388070⟩,⟨36927162630,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨755791003732336,19448842094431049872⟩,⟨414954120346701936,10348266856928⟩,⟨37032443448,2969927899642704⟩,⟨7085540846384,0⟩⟩,⟨⟨749214817427076,168852023868528⟩,⟨1208522178864,10348245351444⟩,⟨37032443448,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 80198 574 (18744-R)⟩
def p660:CachedProfile:=⟨⟨90572,685,15992⟩,⟨⟨⟨819585636805422,24374207942335525986⟩,⟨547401272011690590,11996957353860⟩,⟨45025892550,4108927876435350⟩,⟨10280912132250,0⟩⟩,⟨⟨815492603043468,140039372582352⟩,⟨1051173830160,11996935443450⟩,⟨45025892550,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨818832425636754,24352699446340329510⟩,⟨547720510816655820,12003953896648⟩,⟨45117920904,4117326107936328⟩,⟨10316964580048,0⟩⟩,⟨⟨814750126727712,139794296068404⟩,⟨1050866093592,12003931973460⟩,⟨45117920904,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 91257 686 (15992-R)⟩
def p661:CachedProfile:=⟨⟨47701,354,9631⟩,⟨⟨⟨137929109752224,2146434177903107232⟩,⟨47244556010687616,1966281026304⟩,⟨7242262272,348026913480960⟩,⟨854586948096,0⟩⟩,⟨⟨137034756677952,26747160807360⟩,⟨197034542208,1966274206848⟩,⟨7242262272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨137715672217242,2143276868168478294⟩,⟨47309151240642060,1968969452520⟩,⟨7272650700,349487229388500⟩,⟨860596999500,0⟩⟩,⟨⟨136825210856460,26669459908980⟩,⟨197017131780,1968962623740⟩,⟨7272650700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 48055 355 (9631-R)⟩
def p662:CachedProfile:=⟨⟨64555,464,13058⟩,⟨⟨⟨342379885891986,7208156855825013186⟩,⟨153695944156910112,4727743292736⟩,⟨16869302784,1096825197712896⟩,⟨2609118830592,0⟩⟩,⟨⟨340151479823268,66523964364108⟩,⟨474739990848,4727731173984⟩,⟨16869302784,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨341988999531870,7200335832756054030⟩,⟨153862058384401950,4732853058300⟩,⟨16923930750,1100377053434250⟩,⟨2623209266250,0⟩⟩,⟨⟨339767749451040,66381400323720⟩,⟨474743554200,4732840926450⟩,⟨16923930750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 65019 465 (13058-R)⟩
def p663:CachedProfile:=⟨⟨39602,294,8214⟩,⟨⟨⟨81228519112480,1047924483145513960⟩,⟨23065843516687440,1156305939600⟩,⟨4260430440,169974132834240⟩,⟨417522183120,0⟩⟩,⟨⟨80673599247060,16152616121760⟩,⟨119031209640,1156301109180⟩,⟨4260430440,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨81080666485264,1046115355812067072⟩,⟨23104855854796320,1158261674200⟩,⟨4282152150,170840742176400⟩,⟨421078294750,0⟩⟩,⟨⟨80528576871072,16097605123200⟩,⟨119029314000,1158256835610⟩,⟨4282152150,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 39896 295 (8214-R)⟩
def p664:CachedProfile:=⟨⟨41845,303,8321⟩,⟨⟨⟨91585877370510,1251032153492984802⟩,⟨26876926372770216,1275367737744⟩,⟨4584206988,193215156130224⟩,⟨463004905788,0⟩⟩,⟨⟨91008968559996,17511826881456⟩,⟨125891704116,1275362694612⟩,⟨4584206988,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨91422133143836,1248903379028515772⟩,⟨26920264723904256,1277424255488⟩,⟨4606752768,194165415665664⟩,⟨466817613824,0⟩⟩,⟨⟨90848128895976,17452953037728⟩,⟨125882550144,1277419204224⟩,⟨4606752768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42148 304 (8321-R)⟩
def p665:CachedProfile:=⟨⟨16579,116,3731⟩,⟨⟨⟨6501446206164,34928706595155492⟩,⟨723994635528864,86733053376⟩,⟨301306752,5030316224640⟩,⟨11650527744,0⟩⟩,⟨⟨6449370807432,1394776295640⟩,⟨9691168032,86732187552⟩,⟨301306752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨6475118551902,34795501119653274⟩,⟨727496532286524,87152582088⟩,⟨305374212,5098222469340⟩,⟨11909594268,0⟩⟩,⟨⟨6423626188980,1384329967020⟩,⟨9701503812,87151712076⟩,⟨305374212,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16695 117 (3731-R)⟩
def p666:CachedProfile:=⟨⟨63193,434,12752⟩,⟨⟨⟨320150965296942,6596589458059800966⟩,⟨134443239698217996,4225998440664⟩,⟨14412624408,917032053207816⟩,⟨2085026331024,0⟩⟩,⟨⟨318075532410168,62084524743072⟩,⟨423478770624,4225987371060⟩,⟨14412624408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨319776779123154,6589260802962209250⟩,⟨134605086527317950,4231085854380⟩,⟨14463223650,920251531178550⟩,⟨2097167429250,0⟩⟩,⟨⟨317708170646532,61948283811084⟩,⟨423523087020,4231074771450⟩,⟨14463223650,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 63627 435 (12752-R)⟩
def p667:CachedProfile:=⟨⟨7123,46,1535⟩,⟨⟨⟨491840890368,1137629297622528⟩,⟨21789306095616,6078959616⟩,⟨19501056,139803070464⟩,⟨299016192,0⟩⟩,⟨⟨488199705600,101416688640⟩,⟨650741760,6078818304⟩,⟨19501056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨487032336730,1127109197725774⟩,⟨22060056798012,6154499224⟩,⟨20172588,144617283372⟩,⟨316037212,0⟩⟩,⟨⟨483489457092,99575775468⟩,⟨652819284,6154356156⟩,⟨20172588,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7169 47 (1535-R)⟩
def p668:CachedProfile:=⟨⟨7819,61,2036⟩,⟨⟨⟨801274303704,2011008064992192⟩,⟨46297019011824,11750735976⟩,⟨45478062,358367128560⟩,⟨924720594,0⟩⟩,⟨⟨792798232632,196085856960⟩,⟨1517923512,11750487462⟩,⟨45478062,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨796060645200,1998858471609600⟩,⟨46778760878400,11873012400⟩,⟨46704600,368032248000⟩,⟨965228400,0⟩⟩,⟨⟨787733164800,193781808000⟩,⟨1524679200,11872761300⟩,⟨46704600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7880 62 (2036-R)⟩
def p669:CachedProfile:=⟨⟨55560,400,14767⟩,⟨⟨⟨293586780528912,5223588824606612304⟩,⟨110992193152588800,3966850201600⟩,⟨14177280000,793360588800000⟩,⟨1890304000000,0⟩⟩,⟨⟨290364754274400,73222223842560⟩,⟨523389734400,3966838387200⟩,⟨14177280000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨293300028224840,5218865092631429720⟩,⟨111171724056087240,3973266651640⟩,⟨14235712530,796630473178800⟩,⟨1902840241510,0⟩⟩,⟨⟨290086500831660,73093363855200⟩,⟨523774819620,3973254818130⟩,⟨14235712530,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 55960 401 (14767-R)⟩
def p670:CachedProfile:=⟨⟨11838,100,2882⟩,⟨⟨⟨2585260919616,9880210601423832⟩,⟨246533877518400,41303011200⟩,⟨172980000,2065035240000⟩,⟨5766000000,0⟩⟩,⟨⟨2561246106216,595143156168⟩,⟨4985283600,41302434600⟩,⟨172980000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨2575467040536,9845222490931152⟩,⟨248135500528344,41571344672⟩,⟨175844838,2099235676044⟩,⟨5920109546,0⟩⟩,⟨⟨2551700837556,591020964768⟩,⟨5000261136,41570764326⟩,⟨175844838,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11938 101 (2882-R)⟩
def p671:CachedProfile:=⟨⟨6482,47,1298⟩,⟨⟨⟨343255416306,726040871877126⟩,⟨15616296420966,4783868868⟩,⟨17216946,112409440434⟩,⟨269732154,0⟩⟩,⟨⟨341049893568,66051359748⟩,⟨475480764,4783746762⟩,⟨17216946,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨339323686910,718124589874490⟩,⟨15776661762720,4832998080⟩,⟨17763840,115980111360⟩,⟨284221440,0⟩⟩,⟨⟨337188384420,64634749560⟩,⟨475182720,4832874720⟩,⟨17763840,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6529 48 (1298-R)⟩
def p672:CachedProfile:=⟨⟨40268,250,10158⟩,⟨⟨⟨105313468796616,1362226076147866536⟩,⟨25017481880640000,1234887404000⟩,⟨3809625000,154358385750000⟩,⟨317468750000,0⟩⟩,⟨⟨104264389502616,25087559719176⟩,⟨154792683000,1234882324500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨105176708841120,1360579282001410392⟩,⟨25087882121427312,1238362446928⟩,⟨3835626882,155411930004876⟩,⟨320914115794,0⟩⟩,⟨⟨104131341035376,25028324023896⟩,⟨155044901772,1238357353134⟩,⟨3835626882,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 40518 251 (10158-R)⟩
def p673:CachedProfile:=⟨⟨69188,489,13540⟩,⟨⟨⟨406860312832270,9194896642299174466⟩,⟨192882202712115246,5536489008468⟩,⟨19427624766,1353658610820582⟩,⟨3166702836858,0⟩⟩,⟨⟨404375932644156,76649635918680⟩,⟨537934640760,5536475765370⟩,⟨19427624766,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨406414032250194,9185285858154082182⟩,⟨193076815577313780,5542075206360⟩,⟨19486996200,1357795434227400⟩,⟨3182876046000,0⟩⟩,⟨⟨403937346360384,76491216340524⟩,⟨537920633880,5542061949900⟩,⟨19486996200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 69677 490 (13540-R)⟩
def p674:CachedProfile:=⟨⟨26534,193,5442⟩,⟨⟨⟨24135876905442,208721867516165466⟩,⟨4502502246078522,336928645268⟩,⟨1216477842,32512803283134⟩,⟨78260074502,0⟩⟩,⟨⟨23974389529068,4750051691772⟩,⟨34300893348,336926544270⟩,⟨1216477842,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨24069665673614,208178251855741910⟩,⟨4514190156060060,337803281432⟩,⟨1225955064,32766100995528⟩,⟨79278427472,0⟩⟩,⟨⟨23909419845912,4725645557544⟩,⟨34301464368,337801174980⟩,⟨1225955064,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26727 194 (5442-R)⟩
def p675:CachedProfile:=⟨⟨14496,91,3135⟩,⟨⟨⟨4158171375680,19565568502254656⟩,⟨364345541798784,49955639552⟩,⟨155815296,2272877722752⟩,⟨4726397312,0⟩⟩,⟨⟨4127258572416,860460289920⟩,⟨5367922560,49955068800⟩,⟨155815296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4138240836954,19476931593765702⟩,⟨366704874015984,50279135648⟩,⟨158547648,2312734541376⟩,⟨4862127872,0⟩⟩,⟨⟨4107739474524,852793537764⟩,⟨5378556624,50278561200⟩,⟨158547648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 14587 92 (3135-R)⟩
def p676:CachedProfile:=⟨⟨45267,250,10158⟩,⟨⟨⟨131529517847954,1926732529715907830⟩,⟨31571392573792500,1387241927000⟩,⟨3809625000,173402701125000⟩,⟨317468750000,0⟩⟩,⟨⟨130480336984272,28182794208444⟩,⟨154792683000,1387236847500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨131389742435214,1924804511517474690⟩,⟨31666476265268490,1391419902588⟩,⟨3836382894,174620640186198⟩,⟨320977368798,0⟩⟩,⟨⟨130343655187452,28127335385304⟩,⟨155106030312,1391414807790⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45517 251 (10158-R)⟩
def p677:CachedProfile:=⟨⟨29022,233,6579⟩,⟨⟨⟨35214801578740,331389511070010820⟩,⟨7872994476507720,538236393520⟩,⟨2143329720,62703110958600⟩,⟨166465274920,0⟩⟩,⟨⟨34929612857160,7598662104600⟩,⟨60519168360,538233327240⟩,⟨2143329720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨35145399322792,330774910049896744⟩,⟨7892364263910048,539560622016⟩,⟨2157824448,63127154226240⟩,⟨168310306944,0⟩⟩,⟨⟨34861766817360,7570969789680⟩,⟨60557406624,539557548192⟩,⟨2157824448,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29255 234 (6579-R)⟩
def p678:CachedProfile:=⟨⟨45745,379,11133⟩,⟨⟨⟨149024692643506,2200485666809224726⟩,⟨53864192015235672,2335634671856⟩,⟨9595793364,442596373121136⟩,⟨1212268561652,0⟩⟩,⟨⟨147643676520948,34303753259568⟩,⟨281873265228,2335626232284⟩,⟨9595793364,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨148863846419176,2198266147012839736⟩,⟨53952956999272800,2339483683040⟩,⟨9636967200,444495475132800⟩,⟨1220682512000,0⟩⟩,⟨⟨147486917657940,34236001900464⟩,⟨282058813680,2339475229560⟩,⟨9636967200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 46124 380 (11133-R)⟩
def p679:CachedProfile:=⟨⟨9431,67,1906⟩,⟨⟨⟨1066997012000,3281582098707992⟩,⟨69160707567024,14563621696⟩,⟨51363138,487847084724⟩,⟨1147110082,0⟩⟩,⟨⟨1060032968376,207136677096⟩,⟨1461166284,14563366158⟩,⟨51363138,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1058660462016,3257201041077552⟩,⟨69677622567072,14672476416⟩,⟨52519392,498829185216⟩,⟨1190439552,0⟩⟩,⟨⟨1051848198636,204105713328⟩,⟨1461274848,14672218968⟩,⟨52519392,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9498 68 (1906-R)⟩
def p680:CachedProfile:=⟨⟨18023,136,3581⟩,⟨⟨⟨7317187543350,43064723550267954⟩,⟨963849064322016,106158215232⟩,⟨397516032,7218493625088⟩,⟨18020726784,0⟩⟩,⟨⟨7271123456772,1397568429468⟩,⟨10466947872,106157240928⟩,⟨397516032,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨7286803436016,42894482978430576⟩,⟨967141270527840,106520827456⟩,⟨401806752,7296408809568⟩,⟨18349175008,0⟩⟩,⟨⟨7241276444640,1386663659424⟩,⟨10461640032,106519849824⟩,⟨401806752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18159 137 (3581-R)⟩
def p681:CachedProfile:=⟨⟨26362,202,5698⟩,⟨⟨⟨25055291636296,214717691083184056⟩,⟨4874108960852496,366974293648⟩,⟨1395251976,37063473490464⟩,⟨93946966384,0⟩⟩,⟨⟨24869958264228,5175661012368⟩,⟨39357157224,366971991252⟩,⟨1395251976,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨24993930770938,214220691258511198⟩,⟨4887064652341368,367949748208⟩,⟨1405886244,37345962185616⟩,⟨95131635844,0⟩⟩,⟨⟨24809861571780,5152073455440⟩,⟨39371740380,367947439692⟩,⟨1405886244,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26564 203 (5698-R)⟩
def p682:CachedProfile:=⟨⟨81380,607,15977⟩,⟨⟨⟨664816131314802,17676552337173653406⟩,⟨391159978442000748,9542032264392⟩,⟨35322468732,2895983243930484⟩,⟨7146912840108,0⟩⟩,⟨⟨660734894693868,125578097072532⟩,⟨929731602852,9542012867100⟩,⟨35322468732,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨664197923483484,17660892835734957900⟩,⟨391461091049283840,9549377703424⟩,⟨35407896576,2902987216576512⟩,⟨7176000372736,0⟩⟩,⟨⟨660127401323832,125358122344104⟩,⟨929631995136,9549358291200⟩,⟨35407896576,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 81987 608 (15977-R)⟩
def p683:CachedProfile:=⟨⟨6757,46,1474⟩,⟨⟨⟨425693268850,933703826134450⟩,⟨18842117474700,5539545400⟩,⟨18726600,127397059800⟩,⟨287141200,0⟩⟩,⟨⟨422468502900,88744454700⟩,⟨600065400,5539409700⟩,⟨18726600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨421042977460,924065448045220⟩,⟨19055936080440,5602411280⟩,⟨19350840,131643764520⟩,⟨303163160,0⟩⟩,⟨⟨417915238440,86948054520⟩,⟨600699480,5602274040⟩,⟨19350840,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6803 47 (1474-R)⟩
def p684:CachedProfile:=⟨⟨25159,135,5079⟩,⟨⟨⟨20156994641480,165090230911684520⟩,⟨2632635024991200,208164988800⟩,⟨555498000,14050766412000⟩,⟨24997410000,0⟩⟩,⟨⟨20025692750160,3915711528480⟩,⟨20899069200,208163617200⟩,⟨555498000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20114742898770,164761318865136630⟩,⟨2646915202226880,209294142720⟩,⟨562648320,14231626606080⟩,⟨25506723840,0⟩⟩,⟨⟨19984213979340,3900309000120⟩,⟨20971061280,209292763680⟩,⟨562648320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25294 136 (5079-R)⟩
def p685:CachedProfile:=⟨⟨31312,270,9397⟩,⟨⟨⟨60394610234922,599917187973945486⟩,⟨15185807725585680,961677040320⟩,⟨4110685200,129823659986400⟩,⟨369961668000,0⟩⟩,⟨⟨59564139302268,16734608132952⟩,⟨143067069720,961671965400⟩,⟨4110685200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨60321529579172,599253963430160036⟩,⟨15225832753522224,964211738816⟩,⟨4136784648,130647932753136⟩,⟨373689546536,0⟩⟩,⟨⟨59493705756168,16699012060752⟩,⟨143291503656,964206650520⟩,⟨4136784648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 31582 271 (9397-R)⟩
def p686:CachedProfile:=⟨⟨15483,114,3686⟩,⟨⟨⟨5632495626834,28165813142570022⟩,⟨613514094494148,78671760696⟩,⟨287497512,4484098694664⟩,⟨10924905456,0⟩⟩,⟨⟨5582286835104,1271805770124⟩,⟨9295752888,78670920060⟩,⟨287497512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨5610878501954,28064554400413190⟩,⟨616713565350300,79082041720⟩,⟨291531900,4547023044300⟩,⟨11175389500,0⟩⟩,⟨⟨5561198222052,1262851844364⟩,⟨9311275380,79081196700⟩,⟨291531900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 15597 115 (3686-R)⟩
def p687:CachedProfile:=⟨⟨12167,92,2113⟩,⟨⟨⟨1953599465706,7809930896388726⟩,⟨175374466582896,28612296608⟩,⟨107357376,1316094072384⟩,⟨3292292864,0⟩⟩,⟨⟨1944109112988,328557038628⟩,⟨2465718864,28611907632⟩,⟨107357376,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1940042498100,7757813985492900⟩,⟨176106633532200,28731754800⟩,⟨108977400,1335953946600⟩,⟨3378299400,0⟩⟩,⟨⟨1930738828200,324218676600⟩,⟨2459608200,28731364200⟩,⟨108977400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12259 93 (2113-R)⟩
def p688:CachedProfile:=⟨⟨9692,74,1906⟩,⟨⟨⟨1126073308992,3566103897376920⟩,⟨80757796554144,16539029600⟩,⟨62656392,611902324272⟩,⟨1545524336,0⟩⟩,⟨⟨1119108243216,212981342232⟩,⟨1613825448,16538747364⟩,⟨62656392,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1117303057824,3539633973613392⟩,⟨81248209299000,16639470000⟩,⟨63888750,623937532500⟩,⟨1597218750,0⟩⟩,⟨⟨1110489779796,209864855376⟩,⟨1611700200,16639186050⟩,⟨63888750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9766 75 (1906-R)⟩
def p689:CachedProfile:=⟨⟨17935,122,3825⟩,⟨⟨⟨7765390109850,45269041539083886⟩,⟨913182188952168,101145758224⟩,⟨341677104,6169663466928⟩,⟨13894868896,0⟩⟩,⟨⟨7709275166436,1585525581900⟩,⟨10712417400,101144824680⟩,⟨341677104,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨7734937498724,45101048813545892⟩,⟨917298328217976,101601678192⟩,⟨346030488,6248272521816⟩,⟨14187250008,0⟩⟩,⟨⟨7679435407704,1573941871944⟩,⟨10721318616,101600740440⟩,⟨346030488,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18057 123 (3825-R)⟩
def p690:CachedProfile:=⟨⟨43444,319,9125⟩,⟨⟨⟨108671472521118,1536767302326104394⟩,⟨33453434220493716,1528854285816⟩,⟨5572025316,243848543904108⟩,⟨592492025268,0⟩⟩,⟨⟨107910791665092,21866117305500⟩,⟨159387871500,1528848463428⟩,⟨5572025316,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨108480393354018,1534207232140025994⟩,⟨33503145104983680,1531126145280⟩,⟨5597798400,244976451379200⟩,⟨597098496000,0⟩⟩,⟨⟨107723454881532,21794291719380⟩,⟨159362323200,1531120314240⟩,⟨5597798400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43763 320 (9125-R)⟩
def p691:CachedProfile:=⟨⟨18557,146,4482⟩,⟨⟨⟨9859970550146,59066856856040042⟩,⟨1373746255977684,146902637992⟩,⟨573357768,10723510334904⟩,⟨27903411376,0⟩⟩,⟨⟨9769746902556,2254774503708⟩,⟨17601298056,146901328956⟩,⟨573357768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨9831176017778,58905511208811554⟩,⟨1379452980811878,147512901228⟩,⟨579683034,10841811784902⟩,⟨28404468666,0⟩⟩,⟨⟨9741674171652,2242718250660⟩,⟨17627096340,147511586754⟩,⟨579683034,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18703 147 (4482-R)⟩
def p692:CachedProfile:=⟨⟨4565,36,1406⟩,⟨⟨⟨192673181442,278102058255630⟩,⟨6434428814856,2797003440⟩,⟨10940832,50338768032⟩,⟨131289984,0⟩⟩,⟨⟨189878825976,54611348652⟩,⟨427300272,2796902136⟩,⟨10940832,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨190795519890,275630829639030⟩,⟨6556753273410,2850180300⟩,⟨11458530,52720696530⟩,⟨141321870,0⟩⟩,⟨⟨188071868880,53683455780⟩,⟨431707860,2850077070⟩,⟨11458530,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4601 37 (1406-R)⟩
def p693:CachedProfile:=⟨⟨21868,162,4821⟩,⟨⟨⟨14602566210314,103656427814151662⟩,⟨2274736485065328,206514764352⟩,⟨759291408,16727189718240⟩,⟨41001736032,0⟩⟩,⟨⟨14490280631292,3072770219160⟩,⟨22595949864,206513202024⟩,⟨759291408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨14556929175192,103350778346050104⟩,⟨2282132790863136,207186259072⟩,⟨766462512,16885169139360⟩,⟨41644463152,0⟩⟩,⟨⟨14445617681520,3054951562080⟩,⟨22603590768,207184691664⟩,⟨766462512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 22030 163 (4821-R)⟩
def p694:CachedProfile:=⟨⟨12158,87,2593⟩,⟨⟨⟨2421139837354,9571462208873038⟩,⟨203036011968348,33162930744⟩,⟨117803916,1442508951420⟩,⟨3416313564,0⟩⟩,⟨⟨2403635164788,494176999740⟩,⟨3511098324,33162479388⟩,⟨117803916,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2407138640340,9519074400306420⟩,⟨204261326089920,33363073920⟩,⟨119877120,1467895334400⟩,⟨3516395520,0⟩⟩,⟨⟨2389915254360,488856155400⟩,⟨3513216960,33362619840⟩,⟨119877120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12245 88 (2593-R)⟩
def p695:CachedProfile:=⟨⟨23450,170,4739⟩,⟨⟨⟨16399999199820,125435454778364460⟩,⟨2697402017354400,228402398400⟩,⟨821916000,19413655920000⟩,⟨46575240000,0⟩⟩,⟨⟨16293323788680,3183436519200⟩,⟨22912117200,228400786800⟩,⟨821916000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨16344746875800,125033726988374400⟩,⟨2704682648026800,229018897800⟩,⟨828982350,19580563107000⟩,⟨47251993950,0⟩⟩,⟨⟨16239079735200,3163317948000⟩,⟨22901243400,229017281850⟩,⟨828982350,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 23620 171 (4739-R)⟩
def p696:CachedProfile:=⟨⟨24600,158,5079⟩,⟨⟨⟨19339259319880,154857624313326760⟩,⟨2951959290156480,238467554560⟩,⟨760902720,18838429541760⟩,⟨40074209920,0⟩⟩,⟨⟨19207962874320,3832734483360⟩,⟨24459651360,238465949280⟩,⟨760902720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19298617292370,154548855519255990⟩,⟨2964794758459560,239504447520⟩,⟨769048020,19040090879160⟩,⟨40759545060,0⟩⟩,⟨⟨19168093807980,3817658346840⟩,⟨24517637820,239502835260⟩,⟨769048020,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24758 159 (5079-R)⟩
def p697:CachedProfile:=⟨⟨15034,110,2976⟩,⟨⟨⟨4228692748800,20759127699308544⟩,⟨450624959516160,59513087920⟩,⟨216130200,3273075748800⟩,⟨7924774000,0⟩⟩,⟨⟨4202236554672,805014332928⟩,⟨5847304320,59512432980⟩,⟨216130200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4207574703656,20660398789333016⟩,⟨452583066284280,59771698248⟩,⟨219042738,3317183224272⟩,⟨8104581306,0⟩⟩,⟨⟨4181489245740,797459354784⟩,⟨5845086396,59771040462⟩,⟨219042738,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 15144 111 (2976-R)⟩
def p698:CachedProfile:=⟨⟨4948,29,965⟩,⟨⟨⟨148108129470,239106359661666⟩,⟨4163853998556,1673332248⟩,⟨4874436,24260067972⟩,⟨47119548,0⟩⟩,⟨⟨147198950556,27837057780⟩,⟨162201060,1673276220⟩,⟨4874436,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨145347327294,234853239204090⟩,⟨4231625638500,1700570040⟩,⟨5124600,25505134200⟩,⟨51246000,0⟩⟩,⟨⟨144485010852,26865408024⟩,⟨161937360,1700513100⟩,⟨5124600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4977 30 (965-R)⟩
def p699:CachedProfile:=⟨⟨10093,77,2069⟩,⟨⟨⟨1329069795210,4373606168026830⟩,⟨98917151560920,19453230720⟩,⟨73638180,748900290600⟩,⟨1890046620,0⟩⟩,⟨⟨1320166516140,261338286600⟩,⟨1978667460,19452911940⟩,⟨73638180,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1319487333720,4343655553486200⟩,⟨99524069686080,19572593664⟩,⟨75052224,763281118080⟩,⟨1951357824,0⟩⟩,⟨⟨1310762975280,257814381600⟩,⟨1977337440,19572272928⟩,⟨75052224,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10170 78 (2069-R)⟩
def p700:CachedProfile:=⟨⟨15362,118,2867⟩,⟨⟨⟨4241801881692,21346683478819644⟩,⟨486591714076896,62868349632⟩,⟨239604192,3709072892160⟩,⟨9424431552,0⟩⟩,⟨⟨4218139020360,763711001280⟩,⟨5821569648,62867672784⟩,⟨239604192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4219952914314,21241492803854478⟩,⟨488319912818136,63091642768⟩,⟨242492964,3753791082720⟩,⟨9618887572,0⟩⟩,⟨⟨4196634110388,756271870560⟩,⟨5813717868,63090963516⟩,⟨242492964,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 15480 119 (2867-R)⟩
def p701:CachedProfile:=⟨⟨4470,33,903⟩,⟨⟨⟨113702343816,165793466107656⟩,⟨3629745654480,1612240608⟩,⟨5906736,26598032208⟩,⟨64974096,0⟩⟩,⟨⟨112957072656,22055117616⟩,⟨161629776,1612180944⟩,⟨5906736,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨111829800290,163195185020030⟩,⟨3681816567720,1635371440⟩,⟨6173040,27797199120⟩,⟨69961120,0⟩⟩,⟨⟨111118399260,21376911780⟩,⟨161406840,1635310920⟩,⟨6173040,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4503 34 (903-R)⟩
def p702:CachedProfile:=⟨⟨15405,115,2958⟩,⟨⟨⟨4406250734864,22201524700946888⟩,⟨491799583140360,63377400680⟩,⟨234796650,3644044008000⟩,⟨9000538250,0⟩⟩,⟨⟨4380268335828,815053472640⟩,⟨6039378180,63376720110⟩,⟨234796650,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4384186536960,22095397179310080⟩,⟨493728945039360,63626041760⟩,⟨237767520,3690151910400⟩,⟨9193677440,0⟩⟩,⟨⟨4358570408640,807357849600⟩,⟨6034375680,63625358520⟩,⟨237767520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 15520 116 (2958-R)⟩
def p703:CachedProfile:=⟨⟨51190,348,9359⟩,⟨⟨⟨153273538931760,2570372630193204720⟩,⟨51911613283196160,2014510417920⟩,⟨6801200640,350520278584320⟩,⟨788939274240,0⟩⟩,⟨⟨152452723494240,27088447014720⟩,⟨182909301120,2014503903360⟩,⟨6801200640,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨153014799514920,2566216581442404240⟩,⟨51977353254152760,2017061581920⟩,⟨6829382070,351972693123660⟩,⟨794484780810,0⟩⟩,⟨⟨152197921179780,27001690007040⟩,⟨182847409920,2017055059110⟩,⟨6829382070,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 51538 349 (9359-R)⟩
def p704:CachedProfile:=⟨⟨18255,98,4287⟩,⟨⟨⟨9060727942336,53357770732445632⟩,⟨849292495709952,92551814656⟩,⟨247091712,4534874190336⟩,⟨8071662592,0⟩⟩,⟨⟨8981764100736,2024261313408⟩,⟨10809001728,92550974208⟩,⟨247091712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨9026289225166,53167582432717762⟩,⟨854957414580786,93169158588⟩,⟨251278038,4611705831414⟩,⟨8292175254,0⟩⟩,⟨⟨8948150198796,2010122162208⟩,⟨10843028064,93168312534⟩,⟨251278038,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18353 99 (4287-R)⟩
def p705:CachedProfile:=⟨⟨25267,141,5079⟩,⟨⟨⟨20333174527880,167323379395990760⟩,⟨2774481736836960,218396637120⟩,⟨605972880,15396558935040⟩,⟨28480725360,0⟩⟩,⟨⟨20201871478320,3933359631360⟩,⟨21827916720,218395204560⟩,⟨605972880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20290575974370,166990071318501990⟩,⟨2788658513063280,219512585760⟩,⟨613388880,15584984663040⟩,⟨29033740320,0⟩⟩,⟨⟨20160045898980,3917887683840⟩,⟨21896255160,219511145880⟩,⟨613388880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25408 142 (5079-R)⟩
def p706:CachedProfile:=⟨⟨13372,112,3261⟩,⟨⟨⟨3732362573170,16109322582927574⟩,⟨398571550161792,59118504704⟩,⟨245511168,3310472589312⟩,⟨9165750272,0⟩⟩,⟨⟨3697586100852,860606753328⟩,⟨7148320704,59117774016⟩,⟨245511168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨3719861711580,16058898231743484⟩,⟨400897408624848,59463496416⟩,⟨249148728,3359521448352⟩,⟨9384602088,0⟩⟩,⟨⟨3685403620392,855337475808⟩,⟨7167986856,59462761464⟩,⟨249148728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13484 113 (3261-R)⟩
def p707:CachedProfile:=⟨⟨7447,68,1986⟩,⟨⟨⟨712610570514,1702530951239682⟩,⟨45787459091112,12185841808⟩,⟨55127328,414281869920⟩,⟨1249552768,0⟩⟩,⟨⟨704743588452,177933346380⟩,⟨1610042256,12185571576⟩,⟨55127328,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨708632523054,1693728065011062⟩,⟨46226963832606,12302815644⟩,⟨56474982,424409489730⟩,⟨1298924586,0⟩⟩,⟨⟨700883461992,176146429680⟩,⟨1617312528,12302542818⟩,⟨56474982,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7515 69 (1986-R)⟩
def p708:CachedProfile:=⟨⟨5444,43,1110⟩,⟨⟨⟨207589938930,368670674185506⟩,⟨8630495044182,3145947596⟩,⟨12325434,67629656358⟩,⟨176664554,0⟩⟩,⟨⟨206208883716,40599739620⟩,⟨318168180,3145852050⟩,⟨12325434,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨204804614654,363967893091502⟩,⟨8719911820488,3178544336⟩,⟨12742752,69919480224⟩,⟨186893696,0⟩⟩,⟨⟨203474842224,39582515664⟩,⟨317410368,3178447800⟩,⟨12742752,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5487 44 (1110-R)⟩
def p709:CachedProfile:=⟨⟨16281,119,3015⟩,⟨⟨⟨5004594638680,26691263355211000⟩,⟨579197904186720,70635178432⟩,⟨256257456,4202622278400⟩,⟨10164879088,0⟩⟩,⟨⟨4977079595280,894774816000⟩,⟨6492573360,70634460624⟩,⟨256257456,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4980099475414,26566215828614602⟩,⟨581353875362880,70898113920⟩,⟨259372800,4253713920000⟩,⟨10374912000,0⟩⟩,⟨⟨4952964994812,886485796800⟩,⟨6486481440,70897393440⟩,⟨259372800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16400 120 (3015-R)⟩
def p710:CachedProfile:=⟨⟨9180,68,1893⟩,⟨⟨⟨1005994385866,3009325970556046⟩,⟨66092929906080,14293851328⟩,⟨52547136,485955913728⟩,⟨1191068416,0⟩⟩,⟨⟨999172302036,198943456896⟩,⟨1462819536,14293593744⟩,⟨52547136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨998061865480,2986797962214760⟩,⟨66569135199840,14396844480⟩,⟨53704080,496655331840⟩,⟨1235193840,0⟩⟩,⟨⟨991389487920,196012469760⟩,⟨1462463280,14396585040⟩,⟨53704080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9248 69 (1893-R)⟩
def p711:CachedProfile:=⟨⟨24296,172,4761⟩,⟨⟨⟨17646252989430,140033603146150602⟩,⟨2942205068981664,240496847936⟩,⟨845274048,20682165406464⟩,⟨48462378752,0⟩⟩,⟨⟨17538079125996,3328413652656⟩,⟨23397382224,240495209808⟩,⟨845274048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨17606936453040,139736299865964912⟩,⟨2953096385126976,241387115904⟩,⟨853335648,20879416635264⟩,⟨49209022368,0⟩⟩,⟨⟨17499441760416,3314447807616⟩,⟨23434668576,241385471712⟩,⟨853335648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24468 173 (4761-R)⟩
def p712:CachedProfile:=⟨⟨25429,135,5079⟩,⟨⟨⟨20575546611080,170411904006594920⟩,⟨2689138059559200,210386980800⟩,⟨555498000,14200750872000⟩,⟨24997410000,0⟩⟩,⟨⟨20444241976560,3957509666880⟩,⟨20899069200,210385609200⟩,⟨555498000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20532470947170,170072516061340230⟩,⟨2703724727446080,211528187520⟩,⟨562648320,14383541652480⟩,⟨25506723840,0⟩⟩,⟨⟨20401939289940,3941942724720⟩,⟨20971061280,211526808480⟩,⟨562648320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25564 136 (5079-R)⟩
def p713:CachedProfile:=⟨⟨16590,134,3730⟩,⟨⟨⟨6521261212648,35100455483694328⟩,⟨839021710900464,100338767984⟩,⟨401963016,6722429479584⟩,⟨17954348048,0⟩⟩,⟨⟨6469227388260,1396450320720⟩,⟨11188970520,100337768076⟩,⟨401963016,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨6498624870976,34985696347875016⟩,⟨842564314192680,100762437240⟩,⟨406672650,6801193398600⟩,⟨18300269250,0⟩⟩,⟨⟨6447090792108,1387480771248⟩,⟨11200066020,100761433110⟩,⟨406672650,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16724 135 (3730-R)⟩
def p714:CachedProfile:=⟨⟨13165,89,3196⟩,⟨⟨⟨3533310333200,14993209437991184⟩,⟨299911851587784,45256680848⟩,⟨151940622,2013821003988⟩,⟨4507571786,0⟩⟩,⟨⟨3500570099172,812545376688⟩,⟨5456204808,45256111782⟩,⟨151940622,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨3518828691560,14935759270817840⟩,⟨302143232991600,45593402400⟩,⟨154791000,2051599914000⟩,⟨4643730000,0⟩⟩,⟨⟨3486455192220,806456064960⟩,⟨5476161600,45592829100⟩,⟨154791000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13254 90 (3196-R)⟩
def p715:CachedProfile:=⟨⟨84618,594,16808⟩,⟨⟨⟨756064942096464,20880622830179873280⟩,⟨434993833642642560,10209717481392⟩,⟨35584921944,3032262368692128⟩,⟨7045814544912,0⟩⟩,⟨⟨751313385944472,144447465374784⟩,⟨1006921495008,10209697512300⟩,⟨35584921944,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨755395720664760,20863032274452544920⟩,⟨435363234109435800,10218387699800⟩,⟨35675099250,3039946557291000⟩,⟨7075561351250,0⟩⟩,⟨⟨750656022861060,144206941552560⟩,⟨1006937171100,10218367713750⟩,⟨35675099250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 85212 595 (16808-R)⟩
def p716:CachedProfile:=⟨⟨24348,181,5237⟩,⟨⟨⟨19628716711086,155369501123082066⟩,⟨3422650595043420,279072447768⟩,⟨1029612708,25255370114532⟩,⟨62119966716,0⟩⟩,⟨⟨19484801472060,4037189746644⟩,⟨29790506916,279070551612⟩,⟨1029612708,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19588507630956,155068572527472396⟩,⟨3434989781779920,280078556576⟩,⟨1039033632,25486455959328⟩,⟨63034707008,0⟩⟩,⟨⟨19445414202120,4021787987544⟩,⟨29840817552,280076653584⟩,⟨1039033632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24529 182 (5237-R)⟩
def p717:CachedProfile:=⟨⟨25188,142,5079⟩,⟨⟨⟨20212544807240,165793266557985320⟩,⟨2777029942073280,219270356480⟩,⟨614598720,15567785577600⟩,⟨29091006080,0⟩⟩,⟨⟨20081242550160,3921284613600⟩,⟨21982724640,219268913760⟩,⟨614598720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20170183713810,165462970561097430⟩,⟨2791081312442280,220379839680⟩,⟨622058580,15756743831400⟩,⟨29651458980,0⟩⟩,⟨⟨20039654429340,3905860163400⟩,⟨22050454140,220378389660⟩,⟨622058580,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25330 143 (5079-R)⟩
def p718:CachedProfile:=⟨⟨10041,86,2561⟩,⟨⟨⟨1660730716554,5365545217068582⟩,⟨135585153331992,26777388624⟩,⟨113691312,1151351916624⟩,⟨3259150944,0⟩⟩,⟨⟨1643875382604,398676616884⟩,⟨3385621512,26776947960⟩,⟨113691312,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨1652883179890,5341954962911266⟩,⟨136572788883438,26972447484⟩,⟨115851114,1173224231478⟩,⟨3359682306,0⟩⟩,⟨⟨1636243634436,395259848100⟩,⟨3395636100,26972003610⟩,⟨115851114,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10127 87 (2561-R)⟩
def p719:CachedProfile:=⟨⟨8780,73,1698⟩,⟨⟨⟨823579875906,2366358028923726⟩,⟨58326677118810,13177124588⟩,⟨54323826,480928831578⟩,⟨1321879766,0⟩⟩,⟨⟨818651229816,153240224436⟩,⟨1263587076,13176876534⟩,⟨54323826,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨816394507310,2346654031761170⟩,⟨58638447852780,13247564360⟩,⟨55362360,490122973080⟩,⟨1365604880,0⟩⟩,⟨⟨811586255340,150724449720⟩,⟨1259867760,13247314980⟩,⟨55362360,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8853 74 (1698-R)⟩
def p720:CachedProfile:=⟨⟨6270,47,1233⟩,⟨⟨⟨304898424154,624553680121630⟩,⟨13887141456540,4396944376⟩,⟨16355436,103317289212⟩,⟨256235164,0⟩⟩,⟨⟨303006797172,57668726844⟩,⟨429069204,4396828380⟩,⟨16355436,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨301229849860,617389668784420⟩,⟨14021697870720,4439550720⟩,⟨16865280,106537973760⟩,⟨269844480,0⟩⟩,⟨⟨299401563960,56367096360⟩,⟨428307840,4439433600⟩,⟨16865280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6317 48 (1233-R)⟩
def p721:CachedProfile:=⟨⟨20742,149,4015⟩,⟨⟨⟨10840708349104,73496051545151152⟩,⟨1566959138830944,150014868800⟩,⟨534955296,11175751088736⟩,⟨26569446368,0⟩⟩,⟨⟨10775801728992,2021108987040⟩,⟨14415070560,150013672032⟩,⟨534955296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨10800671320842,73237126049433270⟩,⟨1571976374189400,150495210000⟩,⟨540270000,11286780570000⟩,⟨27013500000,0⟩⟩,⟨⟨10736440089276,2007040402692⟩,⟨14410801800,150494009400⟩,⟨540270000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 20891 150 (4015-R)⟩
def p722:CachedProfile:=⟨⟨31766,237,6288⟩,⟨⟨⟨39891852587086,413850597221962966⟩,⟨9159418587062430,572414893692⟩,⟨2119481046,67829751915138⟩,⟨167439002634,0⟩⟩,⟨⟨39642789634536,7593396358176⟩,⟨56233319904,572411912706⟩,⟨2119481046,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨39797530937650,412918889607356050⟩,⟨9177589773909900,573550511800⟩,⟨2132646600,68251089139800⟩,⟨169189963600,0⟩⟩,⟨⟨39550125998100,7559623848300⟩,⟨56219431800,573547524900⟩,⟨2132646600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 32003 238 (6288-R)⟩
def p723:CachedProfile:=⟨⟨41954,300,9086⟩,⟨⟨⟨101097748176360,1377910263449799144⟩,⟨29203379312140800,1382285361600⟩,⟨4906980000,207339532920000⟩,⟨490698000000,0⟩⟩,⟨⟨100346799368712,20932077734568⟩,⟨148616067600,1382279909400⟩,⟨4906980000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨100930458087016,1375755893786826736⟩,⟨29255580924937080,1384756245488⟩,⟨4932137238,208402526854452⟩,⟨494857769546,0⟩⟩,⟨⟨100182972703500,20867625342144⟩,⟨148652322336,1384750783542⟩,⟨4932137238,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42254 301 (9086-R)⟩
def p724:CachedProfile:=⟨⟨8131,57,1763⟩,⟨⟨⟨737122572396,1946670541283916⟩,⟨40448572108560,9880248672⟩,⟨34387416,281564162208⟩,⟨653360904,0⟩⟩,⟨⟨731610875016,152784739296⟩,⟨1063596744,9880047576⟩,⟨34387416,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨730393915416,1929872089618176⟩,⟨40808193259680,9968096688⟩,⟨35301816,289051269408⟩,⟨682501776,0⟩⟩,⟨⟨725021197296,150196676256⟩,⟨1063923696,9967893804⟩,⟨35301816,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8188 58 (1763-R)⟩
def p725:CachedProfile:=⟨⟨25328,166,5479⟩,⟨⟨⟨22193870293880,182514135639668120⟩,⟨3547506353651520,278303860480⟩,⟨906041280,23098616392320⟩,⟨50134284160,0⟩⟩,⟨⟨22029084342960,4592731862880⟩,⟨29904820320,278302041120⟩,⟨906041280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨22128635222840,182007165735029360⟩,⟨3559107886016520,279214020080⟩,⟨914480310,23313761023140⟩,⟨50906070590,0⟩⟩,⟨⟨21965197380780,4567621292640⟩,⟨29920481520,279212194770⟩,⟨914480310,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25494 167 (5479-R)⟩
def p726:CachedProfile:=⟨⟨33610,219,6876⟩,⟨⟨⟨48847941058670,534726522795291554⟩,⟨10341366465615354,611395311228⟩,⟨1978966782,66946467268278⟩,⟨144464575086,0⟩⟩,⟨⟨48522335505852,9597879713448⟩,⟨62134135128,611392299102⟩,⟨1978966782,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨48734324775110,533545576686219194⟩,⟨10365927628459920,612847415840⟩,⟨1992724800,67411887259200⟩,⟨146133152000,0⟩⟩,⟨⟨48410843377212,9556052861268⟩,⟨62145840240,612844396560⟩,⟨1992724800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 33829 220 (6876-R)⟩
def p727:CachedProfile:=⟨⟨12549,71,2594⟩,⟨⟨⟨2567328809160,10477781914594680⟩,⟨176067751446360,27903536760⟩,⟨78488370,990523229400⟩,⟨1857558090,0⟩⟩,⟨⟨2549801981940,509703879600⟩,⟨2867589180,27903168270⟩,⟨78488370,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨2550432251944,10412344922536888⟩,⟨177446671887168,28122076224⟩,⟨80217216,1012341265920⟩,⟨1925213184,0⟩⟩,⟨⟨2533226907348,503436686640⟩,⟨2872221984,28121704848⟩,⟨80217216,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12620 72 (2594-R)⟩
def p728:CachedProfile:=⟨⟨25057,147,5079⟩,⟨⟨⟨20018464870280,163341378273455720⟩,⟨2846283688513440,225862042560⟩,⟨658642320,16600421033280⟩,⟨32273473680,0⟩⟩,⟨⟨19887163893360,3901778815680⟩,⟨22756764240,225860549040⟩,⟨658642320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19976485823970,163015908904967430⟩,⟨2860005036788640,226950884160⟩,⟨666319680,16793921214720⟩,⟨32871770880,0⟩⟩,⟨⟨19845957817140,3886431091920⟩,⟨22821449040,226949383440⟩,⟨666319680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25204 148 (5079-R)⟩
def p729:CachedProfile:=⟨⟨25084,145,5079⟩,⟨⟨⟨20056895832280,163825920420193720⟩,⟨2813131082540400,223010069600⟩,⟨640842000,16167802818000⟩,⟨30974030000,0⟩⟩,⟨⟨19925594601360,3905649013680⟩,⟨22447148400,223008596400⟩,⟨640842000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20014841134470,163499497213371930⟩,⟨2826956047364280,224106046320⟩,⟨648432720,16359309092880⟩,⟨31557059040,0⟩⟩,⟨⟨19884312874140,3890286066420⟩,⟨22513051080,224104565880⟩,⟨648432720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25229 146 (5079-R)⟩
def p730:CachedProfile:=⟨⟨177049,567,48527⟩,⟨⟨⟨9757065271871664,549387411026847607152⟩,⟨5208254634047290560,58646272406400⟩,⟨93607309152,16626155822341632⟩,⟨17691781429728,0⟩⟩,⟨⟨9642770914964256,2509626965746176⟩,⟨8011431906912,58646217375648⟩,⟨93607309152,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨9754145467387080,549235781747262174360⟩,⟨5216042581788934080,58733966728000⟩,⟨93912620160,16680383942338560⟩,⟨17780789416960,0⟩⟩,⟨⟨9639942931677660,2508282541220160⟩,⟨8021262067680,58733911614960⟩,⟨93912620160,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 177616 568 (48527-R)⟩
def p731:CachedProfile:=⟨⟨10298,79,2623⟩,⟨⟨⟨1785846330944,5912418080863040⟩,⟨133938972528000,25814985472⟩,⟨98258304,1019626420608⟩,⟨2587468672,0⟩⟩,⟨⟨1767738413952,428533905024⟩,⟨3262424448,25814570880⟩,⟨98258304,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨1776859015604,5884731683409332⟩,⟨135014093189760,26022206720⟩,⟨100300800,1040821401600⟩,⟨2674688000,0⟩⟩,⟨⟨1758997963704,424622606184⟩,⟨3273567360,26021788800⟩,⟨100300800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10377 80 (2623-R)⟩
def p732:CachedProfile:=⟨⟨8848,67,2032⟩,⟨⟨⟨1011587975182,2898420617657974⟩,⟨64957355135874,14572942468⟩,⟨54756822,488157068130⟩,⟨1222902358,0⟩⟩,⟨⟨1003157421000,220970185440⟩,⟨1660684512,14572670046⟩,⟨54756822,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨1004587436260,2879560676202580⟩,⟨65505277714080,14695871680⟩,⟨56042880,499622275200⟩,⟨1270305280,0⟩⟩,⟨⟨996317170440,218152546200⟩,⟨1663979040,14695596960⟩,⟨56042880,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8915 68 (2032-R)⟩
def p733:CachedProfile:=⟨⟨10711,76,2250⟩,⟨⟨⟨1628732457010,5677064545714306⟩,⟨119442391518264,22146130352⟩,⟨78010656,841500946272⟩,⟨1976269952,0⟩⟩,⟨⟨1617288206436,327800749500⟩,⟨2309526000,22145788200⟩,⟨78010656,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1617900098494,5641279538463502⟩,⟨120261331490454,22297977548⟩,⟨79579038,858419082906⟩,⟨2042528642,0⟩⟩,⟨⟨1606667517504,323735042904⟩,⟨2310892584,22297633050⟩,⟨79579038,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10787 77 (2250-R)⟩
def p734:CachedProfile:=⟨⟨48672,363,10334⟩,⟨⟨⟨154621501736130,2448487947771430890⟩,⟨54123322464229590,2207549426940⟩,⟨8170995690,400664773659150⟩,⟨988690478490,0⟩⟩,⟨⟨153516797451420,31422184056900⟩,⟨232614516420,2207541923730⟩,⟨8170995690,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨154397126138670,2445124861928406150⟩,⟨54198903373884360,2210632201232⟩,⟨8204947296,402329590659360⟩,⟨995533605248,0⟩⟩,⟨⟨153296902687800,31337107351200⟩,⟨232623780480,2210624687544⟩,⟨8204947296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 49035 364 (10334-R)⟩
def p735:CachedProfile:=⟨⟨3551,27,692⟩,⟨⟨⟨54911124576,63737149501872⟩,⟨1437394138488,803525184⟩,⟨3031182,10845569196⟩,⟨27280638,0⟩⟩,⟨⟨54574312716,10295108208⟩,⟨77688072,803487762⟩,⟨3031182,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨53736673816,62435740346056⟩,⟨1460514007680,816451328⟩,⟨3194016,11428189248⟩,⟨29810816,0⟩⟩,⟨⟨53419689456,9883051416⟩,⟨77340816,816413304⟩,⟨3194016,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3578 28 (692-R)⟩
def p736:CachedProfile:=⟨⟨24887,196,4896⟩,⟨⟨⟨19073843745390,155142441139262022⟩,⟨3623290382543832,288907251248⟩,⟨1128738912,28312158129696⟩,⟨73744275584,0⟩⟩,⟨⟨18956212996536,3608296704576⟩,⟨28195437312,288905331624⟩,⟨1128738912,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨19015971308306,154693982857827362⟩,⟨3631364946120018,289551098804⟩,⟨1137026082,28520025214806⟩,⟨74664712718,0⟩⟩,⟨⟨18899345296836,3587692625388⟩,⟨28177468692,289549174902⟩,⟨1137026082,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25083 197 (4896-R)⟩
def p737:CachedProfile:=⟨⟨28611,193,6628⟩,⟨⟨⟨34456999111416,318782742440244096⟩,⟨6368968805434704,442231249432⟩,⟨1481541726,42674327875704⟩,⟨95312517706,0⟩⟩,⟨⟨34165402712448,7593370161888⟩,⟨50879059896,442228690638⟩,⟨1481541726,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨34378096364640,318097283405335560⟩,⟨6388447903089840,443583801360⟩,⟨1493772840,43026632883360⟩,⟨96597310320,0⟩⟩,⟨⟨34088342139180,7561328246640⟩,⟨50926874040,443581234740⟩,⟨1493772840,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 28804 194 (6628-R)⟩
def p738:CachedProfile:=⟨⟨86305,616,17944⟩,⟨⟨⟨842378288314990,23673367090921075330⟩,⟨501102900273008880,11530110407200⟩,⟨40856027520,3551246768065920⟩,⟨8389104317440,0⟩⟩,⟨⟨836597109564780,167934021352080⟩,⟨1190130775680,11530088298960⟩,⟨40856027520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨841676068646994,23654655477002401542⟩,⟨501524801260788762,11539818166620⟩,⟨40956806754,3560006599864434⟩,⟨8423449922406,0⟩⟩,⟨⟨835908405744192,167672084918580⟩,⟨1190203476660,11539796039766⟩,⟨40956806754,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 86921 617 (17944-R)⟩
def p739:CachedProfile:=⟨⟨7858,56,1654⟩,⟨⟨⟨644678068280,1648399342355720⟩,⟨34829906200320,8802375680⟩,⟨31140480,246445758720⟩,⟨581288960,0⟩⟩,⟨⟨640124262960,129981277080⟩,⟨919756320,8802190320⟩,⟨31140480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨638429976440,1633256760436760⟩,⟨35130535953120,8878356480⟩,⟨31970160,253011846240⟩,⟨607433040,0⟩⟩,⟨⟨633998452080,127635092640⟩,⟨919282320,8878169520⟩,⟨31970160,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7914 57 (1654-R)⟩
def p740:CachedProfile:=⟨⟨35094,218,5746⟩,⟨⟨⟨43947312632104,507206374068392152⟩,⟨9373409168323536,530895998192⟩,⟨1638722568,57866571321216⟩,⟨119080506608,0⟩⟩,⟨⟨43757160838524,6996492694464⟩,⟨43193118696,530893492500⟩,⟨1638722568,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨43811724527790,505696363430295330⟩,⟨9388551858994440,531753672240⟩,⟨1648899180,58225927844160⟩,⟨120369640140,0⟩⟩,⟨⟨43623252995340,6955158162240⟩,⟨43134901380,531751162500⟩,⟨1648899180,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 35312 219 (5746-R)⟩
def p741:CachedProfile:=⟨⟨24968,148,5079⟩,⟨⟨⟨19883490977160,161643422710978920⟩,⟨2845670555698560,226604576000⟩,⟨667633920,16768293534720⟩,⟨32936606720,0⟩⟩,⟨⟨19752190894320,3888155718720⟩,⟨22911572160,226603072320⟩,⟨667633920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19841777627490,161321295828239430⟩,⟨2859258405692520,227686602000⟩,⟨675354420,16962201612720⟩,⟨33542602860,0⟩⟩,⟨⟨19711250512980,3872861581680⟩,⟨22975648020,227685091140⟩,⟨675354420,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25116 149 (5079-R)⟩
def p742:CachedProfile:=⟨⟨13701,119,3730⟩,⟨⟨⟨4535541348520,19891989306662200⟩,⟨508811021049240,73634687672⟩,⟨317008146,4381052577720⟩,⟨12574656458,0⟩⟩,⟨⟨4483529193780,1153966959600⟩,⟨9936473820,73633799694⟩,⟨317008146,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨4521998832400,19837118762444800⟩,⟨511711491340800,74054448960⟩,⟨321494400,4443052608000⟩,⟨12859776000,0⟩⟩,⟨⟨4470403297560,1147788590400⟩,⟨9966326400,74053555920⟩,⟨321494400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13820 120 (3730-R)⟩
def p743:CachedProfile:=⟨⟨12632,103,2951⟩,⟨⟨⟨3001390316424,12271109151654792⟩,⟨295881990186672,46468270368⟩,⟨187906608,2392990652880⟩,⟨6451460208,0⟩⟩,⟨⟨2975607929232,665634406320⟩,⟨5383615536,46467662256⟩,⟨187906608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨2988150476220,12220303248402060⟩,⟨297540137119680,46728689280⟩,⟨190794240,2429764646400⟩,⟨6614200320,0⟩⟩,⟨⟨2962680694680,660232830600⟩,⟨5391771840,46728077760⟩,⟨190794240,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12735 104 (2951-R)⟩
def p744:CachedProfile:=⟨⟨125683,962,23047⟩,⟨⟨⟨2279230927916552,93915620215581771944⟩,⟨2133717467081045664,33696120131648⟩,⟨127977799872,16207748464789440⟩,⟨41038214492288,0⟩⟩,⟨⟨2266982817399600,403633260216720⟩,⟨3066012841632,33696075787296⟩,⟨127977799872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2277772160170914,93858059199319261638⟩,⟨2134638037920135132,33710658041016⟩,⟨128166105276,16231596402679020⟩,⟨41141319793596,0⟩⟩,⟨⟨2265546349193028,403143042244140⟩,⟨3065472380916,33710613677532⟩,⟨128166105276,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 126645 963 (23047-R)⟩
def p745:CachedProfile:=⟨⟨6469,48,1294⟩,⟨⟨⟨340914756210,719811112596870⟩,⟨15841057165920,4861657920⟩,⟨17902080,116667855360⟩,⟨286433280,0⟩⟩,⟨⟨338729482560,65524394460⟩,⟨482610240,4861533600⟩,⟨17902080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨336998344830,711938851484826⟩,⟨15996246167286,4909289028⟩,⟨18454086,120265278462⟩,⟨301416738,0⟩⟩,⟨⟨334882857876,64114767360⟩,⟨482065920,4909163490⟩,⟨18454086,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6517 49 (1294-R)⟩
def p746:CachedProfile:=⟨⟨37507,274,7231⟩,⟨⟨⟨63830914096192,782783481381040960⟩,⟨16971160017763584,898403299840⟩,⟨3257697792,123079080279552⟩,⟨297536398336,0⟩⟩,⟨⟨63452225437056,11854451882112⟩,⟨85972309248,898399336704⟩,⟨3257697792,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨63700047415674,781252270880790942⟩,⟨17000124858931500,899936631000⟩,⟨3275167500,123739103317500⟩,⟨300223687500,0⟩⟩,⟨⟨63323551836756,11808596477916⟩,⟨85952304900,899932661100⟩,⟨3275167500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 37781 275 (7231-R)⟩
def p747:CachedProfile:=⟨⟨13033,98,2690⟩,⟨⟨⟨2881603244754,12238845691740642⟩,⟨272835059852628,41556682440⟩,⟨155066184,2036174062104⟩,⟨5065495344,0⟩⟩,⟨⟨2862060228612,570315308940⟩,⟨4256408520,41556155004⟩,⟨155066184,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2865606016542,12174357505062510⟩,⟨274185130804794,41762324340⟩,⟨157423662,2067130105722⟩,⟨5194980846,0⟩⟩,⟨⟨2846365780416,564395486472⟩,⟨4255209288,41761794294⟩,⟨157423662,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13131 99 (2690-R)⟩
def p748:CachedProfile:=⟨⟨9283,67,1980⟩,⟨⟨⟨1078091420560,3254357675338000⟩,⟨69623110538520,14893031216⟩,⟨53356254,498880974900⟩,⟨1191623006,0⟩⟩,⟨⟨1070288063460,220045518000⟩,⟨1576796760,14892765762⟩,⟨53356254,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1069929020104,3231033996139432⟩,⟨70162859031552,15008493248⟩,⟨54572448,510252388800⟩,⟨1236975488,0⟩⟩,⟨⟨1062289475352,216945544200⟩,⟨1577785776,15008225736⟩,⟨54572448,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9350 68 (1980-R)⟩
def p749:CachedProfile:=⟨⟨24934,150,5079⟩,⟨⟨⟨19834526604680,161028926166441320⟩,⟨2876781102408000,229374192000⟩,⟨685800000,17202607200000⟩,⟨34290000000,0⟩⟩,⟨⟨19703226846960,3883201865280⟩,⟨23221188000,229372668000⟩,⟨685800000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19792909641570,160708008942037830⟩,⟨2890258843263480,230448819120⟩,⟨693606420,17398423439280⟩,⟨34911523140,0⟩⟩,⟨⟨19662382851540,3867927214320⟩,⟨23284045980,230447287980⟩,⟨693606420,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25084 151 (5079-R)⟩
def p750:CachedProfile:=⟨⟨14305,99,3319⟩,⟨⟨⟨4316172543720,19966748972452680⟩,⟨409170814636320,56814310080⟩,⟨195235920,2812178191680⟩,⟨6442785360,0⟩⟩,⟨⟨4279504574640,952312969920⟩,⟨6545333520,56813652720⟩,⟨195235920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨4297847705240,19887143310128024⟩,⟨411685443117600,57163479200⟩,⟨198420000,2858041680000⟩,⟨6614000000,0⟩⟩,⟨⟨4261608130932,944868579408⟩,⟨6559765200,57162817800⟩,⟨198420000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 14404 100 (3319-R)⟩
def p751:CachedProfile:=⟨⟨9977,80,2554⟩,⟨⟨⟨1634074875090,5241232630528230⟩,⟨124048345024800,24669444800⟩,⟨98112000,986712384000⟩,⟨2616320000,0⟩⟩,⟨⟨1617357433440,393759910740⟩,⟨3132225600,24669036000⟩,⟨98112000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨1626326490864,5218119002911920⟩,⟨125058183020640,24870276288⟩,⟨100147104,1007179424928⟩,⟨2703971808,0⟩⟩,⟨⟨1609823656992,390376052064⟩,⟨3144124512,24869864160⟩,⟨100147104,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10057 81 (2554-R)⟩
def p752:CachedProfile:=⟨⟨5444,35,1151⟩,⟨⟨⟨215178376320,380797696946304⟩,⟨7262860066560,2651281920⟩,⟨8467200,46391788800⟩,⟨98784000,0⟩⟩,⟨⟨213639581952,43589346048⟩,⟨278449920,2651201280⟩,⟨8467200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨212381067386,376106346533366⟩,⟨7379577720720,2693891808⟩,⟨8849088,48484153152⟩,⟨106189056,0⟩⟩,⟨⟨210897426060,42535865844⟩,⟨279483696,2693809872⟩,⟨8849088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5479 36 (1151-R)⟩
def p753:CachedProfile:=⟨⟨14108,105,2856⟩,⟨⟨⟨3579704748670,16473750754550122⟩,⟨363608964442710,51166641540⟩,⟨188990550,2686122687150⟩,⟨6614669250,0⟩⟩,⟨⟨3556319740836,695833686576⟩,⟨5140542960,51166041570⟩,⟨188990550,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨3561029279746,16392049354421662⟩,⟨365273114051844,51400825912⟩,⟨191663688,2724115997544⟩,⟨6772116976,0⟩⟩,⟨⟨3537985655976,689029696068⟩,⟨5138756616,51400223196⟩,⟨191663688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 14213 106 (2856-R)⟩
def p754:CachedProfile:=⟨⟨8842,61,1856⟩,⟨⟨⟨915276432990,2633144251677102⟩,⟨53874849993102,12102967788⟩,⟨41459382,369112877946⟩,⟨843007434,0⟩⟩,⟨⟨908846492496,184110051456⟩,⟨1261452672,12102741234⟩,⟨41459382,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨907898995426,2613025474424122⟩,⟨54345201892428,12208636504⟩,⟨42506952,378439393656⟩,⟨878477008,0⟩⟩,⟨⟨901612946316,181343746908⟩,⟨1262867832,12208407972⟩,⟨42506952,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8903 62 (1856-R)⟩
def p755:CachedProfile:=⟨⟨29053,194,6155⟩,⟨⟨⟨32762160990540,309464238044077596⟩,⟨6129435673837296,419153224608⟩,⟨1390123296,40656936038112⟩,⟨89894639808,0⟩⟩,⟨⟨32528586843576,6649044566760⟩,⟨44104169520,419150836080⟩,⟨1390123296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨32682366437814,308750672545799922⟩,⟨6147019061026740,420355654680⟩,⟨1401297300,40983742133100⟩,⟨91084324500,0⟩⟩,⟨⟨32450380794564,6618833936604⟩,⟨44130085740,420353259300⟩,⟨1401297300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29247 195 (6155-R)⟩
def p756:CachedProfile:=⟨⟨24340,156,5079⟩,⟨⟨⟨18945918049160,150014220885964520⟩,⟨2853233139669120,232957420800⟩,⟨741761280,18170184314880⟩,⟨38571586560,0⟩⟩,⟨⟨18814624265520,3792174808320⟩,⟨24150035520,232955835840⟩,⟨741761280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨18906050315490,149714986510009830⟩,⟨2865870395654760,233989220400⟩,⟨749822580,18367653919680⟩,⟨39240715020,0⟩⟩,⟨⟨18775529487780,3777258214080⟩,⟨24209239860,233987628420⟩,⟨749822580,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24496 157 (5079-R)⟩
def p757:CachedProfile:=⟨⟨24511,189,5237⟩,⟨⟨⟨19893289777722,158625649193602014⟩,⟨3623930924708808,293438584656⟩,⟨1122639588,27729197823600⟩,⟨70726294044,0⟩⟩,⟨⟨19749372747300,4065334369200⟩,⟨31107214404,293436604692⟩,⟨1122639588,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19852575594372,158318504095008324⟩,⟨3636149897803680,294427994560⟩,⟨1132384800,27969904560000⟩,⟨71717704000,0⟩⟩,⟨⟨19709480377560,4049825239200⟩,⟨31152501840,294426007920⟩,⟨1132384800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24700 190 (5237-R)⟩
def p758:CachedProfile:=⟨⟨7097,66,1824⟩,⟨⟨⟨592298723950,1352820939118150⟩,⟨37083339225900,10354363800⟩,⟨47698200,341662206600⟩,⟨1049360400,0⟩⟩,⟨⟨586200847800,143065166400⟩,⟨1318204800,10354122900⟩,⟨47698200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨588723066690,1345226499051930⟩,⟨37438918297110,10453652220⟩,⟨48885210,350164759230⟩,⟨1091769690,0⟩⟩,⟨⟨582724633260,141501196980⟩,⟨1323548820,10453409010⟩,⟨48885210,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7163 67 (1824-R)⟩
def p759:CachedProfile:=⟨⟨338321,1033,93177⟩,⟨⟨⟨68428012280138406,7358278120023331443546⟩,⟨66507650261290365480,391966343663744⟩,⟨596575313052,202450218785448408⟩,⟨205420766127572,0⟩⟩,⟨⟨67618981992194820,17677723259982744⟩,⟨53811324244188,391966151157996⟩,⟨596575313052,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨68417336914471440,7357219962580254923760⟩,⟨66562745266087385040,392291049068160⟩,⟨597647512440,202814073936563760⟩,⟨205989175954320,0⟩⟩,⟨⟨67608645186714780,17672790859543440⟩,⟨53848387668240,392290856402940⟩,⟨597647512440,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 339354 1034 (93177-R)⟩
def p760:CachedProfile:=⟨⟨16647,128,3364⟩,⟨⟨⟨5872352886670,31899314448072310⟩,⟨727246650504960,86707381760⟩,⟨330792960,5549051904000⟩,⟨14113832960,0⟩⟩,⟨⟨5834159981880,1139343909000⟩,⟨8693652480,86706520320⟩,⟨330792960,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨5846346109650,31765002601511250⟩,⟨729878862262050,87021220932⟩,⟨334583946,5612645694150⟩,⟨14387109678,0⟩⟩,⟨⟨5808627086100,1129881802500⟩,⟨8688807900,87020356374⟩,⟨334583946,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16775 129 (3364-R)⟩
def p761:CachedProfile:=⟨⟨24535,188,4953⟩,⟨⟨⟨18776795005986,150332569609456206⟩,⟨3415658774883120,276317236768⟩,⟨1050565056,25973119879488⟩,⟨65835410176,0⟩⟩,⟨⟨18655017487116,3639793536756⟩,⟨27677918736,276315374064⟩,⟨1050565056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨18720311006540,149902633801809980⟩,⟨3424123022949720,277001983440⟩,⟨1058770440,26175981588120⟩,⟨66702537720,0⟩⟩,⟨⟨18599561761560,3619248427080⟩,⟨27668080440,277000116120⟩,⟨1058770440,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24723 189 (4953-R)⟩
def p762:CachedProfile:=⟨⟨6351,42,1265⟩,⟨⟨⟨320649306138,664258668359214⟩,⟨13039788236328,4079568528⟩,⟨13399344,85662006192⟩,⟨187590816,0⟩⟩,⟨⟨318607234212,61429953420⟩,⟨403575480,4079462184⟩,⟨13399344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨316614136338,656297844723414⟩,⟨13192071273342,4127214132⟩,⟨13878594,88725851442⟩,⟨198926514,0⟩⟩,⟨⟨314643453552,59982322500⟩,⟨403447500,4127106546⟩,⟨13878594,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6393 43 (1265-R)⟩
def p763:CachedProfile:=⟨⟨20154,132,3706⟩,⟨⟨⟨9408264635792,62085074308646840⟩,⟨1208226709052352,119121034560⟩,⟨387544608,7861729917888⟩,⟨17051962752,0⟩⟩,⟨⟨9357200681136,1672151691672⟩,⟨10880608464,119120055912⟩,⟨387544608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨9368146705892,61831567247155940⟩,⟨1212453848690448,119537803840⟩,⟨391846728,7949002724208⟩,⟨17371871608,0⟩⟩,⟨⟨9317699022216,1658644867152⟩,⟨10874483256,119536821768⟩,⟨391846728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 20286 133 (3706-R)⟩
def p764:CachedProfile:=⟨⟨24250,171,4761⟩,⟨⟨⟨17580598943042,139231171827626150⟩,⟨2913872689802556,238639344120⟩,⟨835473852,20403106939692⟩,⟨47622009564,0⟩⟩,⟨⟨17472425527236,3322020181932⟩,⟨23261350932,238637715516⟩,⟨835473852,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨17541420277392,138935553646309200⟩,⟨2924757988935552,239530832640⟩,⟨843499008,20599089274368⟩,⟨48360609792,0⟩⟩,⟨⟨17433926031456,3308081163552⟩,⟨23299208064,239529197952⟩,⟨843499008,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24421 172 (4761-R)⟩
def p765:CachedProfile:=⟨⟨6614,57,1596⟩,⟨⟨⟨446850319342,954913404582550⟩,⟨24307710363342,7287781740⟩,⟨31131918,207681024978⟩,⟨591506442,0⟩⟩,⟨⟨442761108216,102018749112⟩,⟨871693704,7287599682⟩,⟨31131918,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨443494938874,948202246328662⟩,⟨24563782482408,7364559280⟩,⟨32011824,213550877904⟩,⟨618895264,0⟩⟩,⟨⟨439489389612,100617759060⟩,⟨874805880,7364375304⟩,⟨32011824,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6671 58 (1596-R)⟩
def p766:CachedProfile:=⟨⟨9019,69,1846⟩,⟨⟨⟨946893067680,2784684036603432⟩,⟨63157260900888,13899443352⟩,⟨52761402,479495621376⟩,⟨1213512246,0⟩⟩,⟨⟨940565445156,185916596736⟩,⟨1411558668,13899188466⟩,⟨52761402,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨939243776016,2763313363180032⟩,⟨63586900802880,13994001840⟩,⟨53890200,489754137600⟩,⟨1257438000,0⟩⟩,⟨⟨933058500816,183108077568⟩,⟨1410383520,13993745220⟩,⟨53890200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9088 70 (1846-R)⟩
def p767:CachedProfile:=⟨⟨10329,76,2206⟩,⟨⟨⟨1487526788274,4996615246411782⟩,⟨108960488849304,20944359376⟩,⟨76485792,795834665760⟩,⟨1937640064,0⟩⟩,⟨⟨1476740636352,303949320060⟩,⟨2220100752,20944023912⟩,⟨76485792,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1477415534142,4964470231360794⟩,⟨109693870872894,21085335348⟩,⟨78013782,811733401710⟩,⟨2002353738,0⟩⟩,⟨⟨1466832831060,300104506080⟩,⟨2220859872,21084997626⟩,⟨78013782,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10405 77 (2206-R)⟩
def p768:CachedProfile:=⟨⟨10249,76,2095⟩,⟨⟨⟨1386851233840,4633964098726000⟩,⟨101895102541440,19738048768⟩,⟨72638976,749997427200⟩,⟨1840187392,0⟩⟩,⟨⟨1377608555040,272029884000⟩,⟨2002350720,19737730176⟩,⟨72638976,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1376979245994,4602627202128462⟩,⟨102546248358708,19864187112⟩,⟨74065068,764721827100⟩,⟨1901003412,0⟩⟩,⟨⟨1367920024692,268407171900⟩,⟨2001680604,19863866484⟩,⟨74065068,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10325 77 (2095-R)⟩
def p769:CachedProfile:=⟨⟨26074,174,5697⟩,⟨⟨⟨24480006557006,207146278848551042⟩,⟨4098477551159376,312291516768⟩,⟨1035075888,27168671908224⟩,⟨60034401504,0⟩⟩,⟨⟨24294774235116,5112297656928⟩,⟨33889812264,312289533864⟩,⟨1035075888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨24406094464350,206555755850413842⟩,⟨4110457151442600,313204340400⟩,⟨1044067500,27404683740000⟩,⟨60903937500,0⟩⟩,⟨⟨24222416672076,5083624761696⟩,⟨33893414100,313202351700⟩,⟨1044067500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26248 175 (5697-R)⟩
def p770:CachedProfile:=⟨⟨24896,152,5079⟩,⟨⟨⟨19779516300680,160339489098013160⟩,⟨2906776839947520,232098941440⟩,⟨704209920,17639050076160⟩,⟨35679969280,0⟩⟩,⟨⟨19648216908720,3877628780160⟩,⟨23530803840,232097397120⟩,⟨704209920,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19738007625570,160019929055095590⟩,⟨2920140632302920,233166014640⟩,⟨712101780,17836725385440⟩,⟨36317190780,0⟩⟩,⟨⟨19607481200580,3862376051040⟩,⟨23592443940,233164463220⟩,⟨712101780,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25048 153 (5079-R)⟩
def p771:CachedProfile:=⟨⟨42018,250,10475⟩,⟨⟨⟨118048702947588,1594293612989236164⟩,⟨28074707418636000,1328419656000⟩,⟨3928500000,166049838000000⟩,⟨327375000000,0⟩⟩,⟨⟨116898331700952,27829952848800⟩,⟨164604150000,1328414418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨117925059934638,1592737287739659714⟩,⟨28160099665178184,1332460202384⟩,⟨3956210796,167221117925328⟩,⟨331002969932,0⟩⟩,⟨⟨116777978370012,27776844797520⟩,⟨164947195140,1332454948452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42268 251 (10475-R)⟩
def p772:CachedProfile:=⟨⟨9131,74,2353⟩,⟨⟨⟨1262105435514,3703322530510878⟩,⟨88564797559656,19243083728⟩,⟨77343024,711942535920⟩,⟨1907794592,0⟩⟩,⟨⟨1249028920788,305916871260⟩,⟨2459299128,19242735336⟩,⟨77343024,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1256193482024,3687200217933128⟩,⟨89380282762800,19420274400⟩,⟨79110000,728207550000⟩,⟨1977750000,0⟩⟩,⟨⟨1243282591728,303322718160⟩,⟨2471396400,19419922800⟩,⟨79110000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9205 75 (2353-R)⟩
def p773:CachedProfile:=⟨⟨9835,92,2513⟩,⟨⟨⟨1566051704154,4959338487451350⟩,⟨136761087043440,27553802016⟩,⟨127670976,1267389778752⟩,⟨3915243264,0⟩⟩,⟨⟨1550125456332,376293775284⟩,⟨3487360464,27553339440⟩,⟨127670976,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨1559194328264,4939136110949960⟩,⟨137697681672720,27742507104⟩,⟨129942576,1289939951952⟩,⟨4028219856,0⟩⟩,⟨⟨1543457031312,373305549744⟩,⟨3497271696,27742041360⟩,⟨129942576,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9927 93 (2513-R)⟩
def p774:CachedProfile:=⟨⟨25592,195,5509⟩,⟨⟨⟨22821201920830,189896794561180810⟩,⟨4286929060872900,332490701400⟩,⟨1257106500,32417005315500⟩,⟨81711922500,0⟩⟩,⟨⟨22653694311780,4696522873980⟩,⟨35514870300,332488552500⟩,⟨1257106500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨22763426510254,189442249097698102⟩,⟨4298746924234392,333407298224⟩,⟨1267036512,32673070534944⟩,⟨82779718784,0⟩⟩,⟨⟨22597100538024,4674385559664⟩,⟨35528738112,333405143400⟩,⟨1267036512,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25787 196 (5509-R)⟩
def p775:CachedProfile:=⟨⟨12479,94,2736⟩,⟨⟨⟨2698727187870,10937001677589162⟩,⟨244031992258068,38819133752⟩,⟨145104792,1824402549816⟩,⟨4546616816,0⟩⟩,⟨⟨2678170013316,564912333216⟩,⟨4223475648,38818619196⟩,⟨145104792,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨2684942331876,10884257096003076⟩,⟨245456621127000,39045761520⟩,⟨147504600,1854575335800⟩,⟨4670979000,0⟩⟩,⟨⟨2664676112376,559557743976⟩,⟨4227947640,39045243960⟩,⟨147504600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12573 95 (2736-R)⟩
def p776:CachedProfile:=⟨⟨11282,84,3132⟩,⟨⟨⟨2582406730384,9298134467030032⟩,⟨203998649531040,35896660800⟩,⟨132638688,1507571327808⟩,⟨3713883264,0⟩⟩,⟨⟨2551602585636,669177068976⟩,⟨4945528224,35896134456⟩,⟨132638688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨2570423565840,9258358800908880⟩,⟨205570619092800,36173280000⟩,⟨135252000,1537274232000⟩,⟨3832140000,0⟩⟩,⟨⟨2540000779680,663634370880⟩,⟨4962952800,36172749600⟩,⟨135252000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11366 85 (3132-R)⟩
def p777:CachedProfile:=⟨⟨92302,578,23263⟩,⟨⟨⟨1267115444691104,37573915587755632928⟩,⟨696001593129745152,14987141152256⟩,⟨46632781056,4331252704481280⟩,⟨8984582483456,0⟩⟩,⟨⟨1254521410150848,301594603944960⟩,⟨1876848418176,14987114259072⟩,⟨46632781056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨1266217342048544,37549122744486960128⟩,⟨696756206242495296,15003390439128⟩,⟨46764108054,4343450356055520⟩,⟨9025472854422,0⟩⟩,⟨⟨1253647647815808,301205800834560⟩,⟨1877671820448,15003363516786⟩,⟨46764108054,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 92880 579 (23263-R)⟩
def p778:CachedProfile:=⟨⟨51118,327,12578⟩,⟨⟨⟨209704449702594,3450484141202151438⟩,⟨65318408013853638,2539357900884⟩,⟨8070359346,415179636554970⟩,⟨879669168714,0⟩⟩,⟨⟨207713081118648,48837354399540⟩,⟨310425014844,2539349674218⟩,⟨8070359346,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨209430694032084,3446280108086534388⟩,⟨65440029734194752,2544086169216⟩,⟨8110112256,417224725009920⟩,⟨886705606656,0⟩⟩,⟨⟨207446438155608,48720945682440⟩,⟨310632134976,2544077927232⟩,⟨8110112256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 51445 328 (12578-R)⟩
def p779:CachedProfile:=⟨⟨58602,410,10154⟩,⟨⟨⟨217423707196440,4184497618292873880⟩,⟨86995789738347600,2948426259600⟩,⟨10242333000,604420554996000⟩,⟨1399785510000,0⟩⟩,⟨⟨216375490426740,36509734178640⟩,⟨253660120200,2948417932500⟩,⟨10242333000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨217087116448020,4178269591994302740⟩,⟨87079158516851280,2951251786080⟩,⟨10277153640,606475390603680⟩,⟨1407970048680,0⟩⟩,⟨⟨216043534569720,36401951121120⟩,⟨253528128360,2951243451000⟩,⟨10277153640,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 59012 411 (10154-R)⟩
def p780:CachedProfile:=⟨⟨2772,17,663⟩,⟨⟨⟨32464692376,29018269876216⟩,⟨526913477616,377877088⟩,⟨1151376,3211187664⟩,⟨6524464,0⟩⟩,⟨⟨32169114768,7366842288⟩,⟨44903664,377854512⟩,⟨1151376,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨31667470846,28349861500906⟩,⟨545302933164,391066632⟩,⟨1261656,3518758584⟩,⟨7569936,0⟩⟩,⟨⟨31391333028,7037517168⟩,⟨45419616,391043268⟩,⟨1261656,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2789 18 (663-R)⟩
def p781:CachedProfile:=⟨⟨27543,195,5971⟩,⟨⟨⟨28635010908380,256186371189044732⟩,⟨5376042448442640,387633442560⟩,⟨1362511800,37793352308400⟩,⟨88563267000,0⟩⟩,⟨⟨28421760839256,5934624763536⟩,⟨41720810040,387631113480⟩,⟨1362511800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨28583505080790,255751005962604042⟩,⟨5394563511698592,388968892928⟩,⟨1374217152,38118035362176⟩,⟨89782187264,0⟩⟩,⟨⟨28371323480676,5914764910296⟩,⟨41794430832,388966555824⟩,⟨1374217152,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 19=>⟨⟨⟨28537165127976,255359213780269392⟩,⟨5386419965422944,388381720832⟩,⟨1372142688,38060493879744⟩,⟨89646655616,0⟩⟩,⟨⟨28325942091636,5896919501568⟩,⟨41668333056,388379387256⟩,⟨1372142688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 27738 196 (5971-R)⟩
def p782:CachedProfile:=⟨⟨19568,148,3629⟩,⟨⟨⟨8705963771010,55817363380824870⟩,⟨1253041107104160,127110984000⟩,⟨477069120,9405894769920⟩,⟨23535409920,0⟩⟩,⟨⟨8658014836020,1558345147920⟩,⟨11697863760,127109909520⟩,⟨477069120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨8670553348704,55600085432182752⟩,⟨1256642191983744,127476294400⟩,⟨481672896,9496662817536⟩,⟨23923087168,0⟩⟩,⟨⟨8623156060992,1546346384640⟩,⟨11686224960,127475216832⟩,⟨481672896,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 19716 149 (3629-R)⟩
def p783:CachedProfile:=⟨⟨8756,65,1684⟩,⟨⟨⟨810676183470,2321388406615890⟩,⟨51135081724350,11594316500⟩,⟨42714750,376786809750⟩,⟨925486250,0⟩⟩,⟨⟨805868039340,150179642040⟩,⟨1106640600,11594097450⟩,⟨42714750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨803548230834,2301901054179702⟩,⟨51490359221796,11674875960⟩,⟨43673256,385241791176⟩,⟨960811632,0⟩⟩,⟨⟨798858499152,147693707820⟩,⟨1105065720,11674655388⟩,⟨43673256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8821 66 (1684-R)⟩
def p784:CachedProfile:=⟨⟨5817,42,1196⟩,⟨⟨⟨255162850110,483646623628014⟩,⟨10355520868812,3535066584⟩,⟨12669048,74227952232⟩,⟨177366672,0⟩⟩,⟨⟨253436615712,50326888248⟩,⟨360766224,3534966036⟩,⟨12669048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨251981533986,477918530577306⟩,⟨10478071397430,3576904604⟩,⟨13124202,76894699518⟩,⟨188113562,0⟩⟩,⟨⟨250314873900,49156049124⟩,⟨360762948,3576802866⟩,⟨13124202,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5859 43 (1196-R)⟩
def p785:CachedProfile:=⟨⟨12236,94,2488⟩,⟨⟨⟨2347693834904,9370591871235728⟩,⟨213424546993296,34619481088⟩,⟨131956824,1627027639920⟩,⟨4134647152,0⟩⟩,⟨⟨2332225187748,458130915360⟩,⟨3492644448,34619013156⟩,⟨131956824,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2333628910800,9317239666673400⟩,⟨214481751066000,34790976000⟩,⟨134021250,1652482012500⟩,⟨4244006250,0⟩⟩,⟨⟨2318419204200,452990637000⟩,⟨3490195500,34790505750⟩,⟨134021250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12330 95 (2488-R)⟩
def p786:CachedProfile:=⟨⟨6283,43,1445⟩,⟨⟨⟨362372341434,736647517061982⟩,⟨14930616357288,4720553760⟩,⟨16041924,101481211224⟩,⟨229934244,0⟩⟩,⟨⟨359334762492,79307923320⟩,⟨539083260,4720429404⟩,⟨16041924,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨358575565192,729389492149480⟩,⟨15129911178624,4783567360⟩,⟨16634112,105227392512⟩,⟨243966976,0⟩⟩,⟨⟨355625053776,77779131552⟩,⟨540986688,4783441344⟩,⟨16634112,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6326 44 (1445-R)⟩
def p787:CachedProfile:=⟨⟨7573,55,1606⟩,⟨⟨⟨581860503040,1433413039756552⟩,⟨30858524654760,8091116440⟩,⟨29167050,222486257400⟩,⟨534729250,0⟩⟩,⟨⟨577691154396,118119976656⟩,⟨851677860,8090939670⟩,⟨29167050,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨576434747376,1420752201622272⟩,⟨31145849892864,8166457152⟩,⟨29973888,228640817664⟩,⟨559512576,0⟩⟩,⟨⟨572373043416,116070211008⟩,⟨852114816,8166278736⟩,⟨29973888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7628 56 (1606-R)⟩
def p788:CachedProfile:=⟨⟨29792,182,5971⟩,⟨⟨⟨33259023490140,322934421664287804⟩,⟨5859190465888032,390955021184⟩,⟨1186899168,35576115661632⟩,⟨72005216192,0⟩⟩,⟨⟨33045746714232,6413023385328⟩,⟨38939422704,390952847376⟩,⟨1186899168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨33170157226080,322113734947848144⟩,⟨5876586109254168,392115760176⟩,⟨1196963838,35877794080212⟩,⟨73014794118,0⟩⟩,⟨⟨32958481879092,6380845696848⟩,⟨38956921416,392113579914⟩,⟨1196963838,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29974 183 (5971-R)⟩
def p789:CachedProfile:=⟨⟨7493,61,1831⟩,⟨⟨⟨658062451640,1590929044712024⟩,⟨38263825347936,10130989312⟩,⟨40901232,308967906528⟩,⟨831658384,0⟩⟩,⟨⟨651892882032,152034463008⟩,⟨1227707472,10130765808⟩,⟨40901232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨653353375220,1580287909016180⟩,⟨38636339720160,10229623040⟩,⟨41976480,317090329920⟩,⟨867513920,0⟩⟩,⟨⟨647303933640,150048727920⟩,⟨1231535760,10229397360⟩,⟨41976480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7554 62 (1831-R)⟩
def p790:CachedProfile:=⟨⟨11638,93,2939⟩,⟨⟨⟨2554820301180,9568391854964460⟩,⟨225772035524280,38492067600⟩,⟨152568360,1789779431160⟩,⟨4729619160,0⟩⟩,⟨⟨2529356423160,608181494760⟩,⟨4821488280,38491520760⟩,⟨152568360,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨2543361854064,9528425475741552⟩,⟨227268224873280,38747160960⟩,⟨155230848,1821013077888⟩,⟨4863899904,0⟩⟩,⟨⟨2518208018016,603226038816⟩,⟨4833624384,38746610496⟩,⟨155230848,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11731 94 (2939-R)⟩
def p791:CachedProfile:=⟨⟨23458,148,4946⟩,⟨⟨⟨17146167124992,130753970517294360⟩,⟨2447977327103808,207405151680⟩,⟨650154528,15347547787968⟩,⟨32074290048,0⟩⟩,⟨⟨17024915521776,3465530102232⟩,⟨21727461456,207403687368⟩,⟨650154528,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨17094232396384,130378863440846032⟩,⟨2457543010816200,208215615760⟩,⟨657105198,15511625303988⟩,⟨32636224834,0⟩⟩,⟨⟨16974006129396,3445940993616⟩,⟨21750623064,208214145726⟩,⟨657105198,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 23606 149 (4946-R)⟩
def p792:CachedProfile:=⟨⟨1275,10,257⟩,⟨⟨⟨2644084362,1100263132014⟩,⟨25568919720,39804240⟩,⟨154800,198918000⟩,⟨516000,0⟩⟩,⟨⟨2626380660,511219260⟩,⟨3978360,39799080⟩,⟨154800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2492060084,1039865588948⟩,⟨26599153944,41408752⟩,⟨177144,227630040⟩,⟨649528,0⟩⟩,⟨⟨2477025048,457141320⟩,⟨3913272,41403384⟩,⟨177144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1285 11 (257-R)⟩
def p793:CachedProfile:=⟨⟨13854,102,2759⟩,⟨⟨⟨3330760236120,15063754983390840⟩,⟨328999114860480,47148969600⟩,⟨172290240,2404482589440⟩,⟨5857868160,0⟩⟩,⟨⟨3309673855440,637636242240⟩,⟨4660282080,47148406560⟩,⟨172290240,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨3312807019734,14986464724485162⟩,⟨330539351633928,47369708240⟩,⟨174793884,2439423445104⟩,⟨6001256684,0⟩⟩,⟨⟨3292039194732,631182708720⟩,⟨4658341860,47369142564⟩,⟨174793884,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13956 103 (2759-R)⟩
def p794:CachedProfile:=⟨⟨21966,161,4573⟩,⟨⟨⟨13915812185494,99547563780451090⟩,⟨2163348421775100,195541482248⟩,⟨711375924,15740615070348⟩,⟨38177174588,0⟩⟩,⟨⟨13819956774852,2776969743324⟩,⟨20205727332,195540009420⟩,⟨711375924,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨13870303907280,99238860924878160⟩,⟨2170122586943040,196153799040⟩,⟨718035840,15887979031680⟩,⟨38773935360,0⟩⟩,⟨⟨13775324875680,2759994528480⟩,⟨20206946880,196152321600⟩,⟨718035840,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 22127 162 (4573-R)⟩
def p795:CachedProfile:=⟨⟨29449,213,6192⟩,⟨⟨⟨33881651960552,324729319141107056⟩,⟨6963681633686712,469539486768⟩,⟨1685821302,50004831459924⟩,⟨119693312442,0⟩⟩,⟨⟨33643839596268,6824702250432⟩,⟨49007537568,469536848550⟩,⟨1685821302,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨33799707958944,323985272123046360⟩,⟨6980558629557600,470677465312⟩,⟨1697840904,50361356894448⟩,⟨121112651152,0⟩⟩,⟨⟨33563503276512,6793878567864⟩,⟨49015238808,470674820700⟩,⟨1697840904,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29662 214 (6192-R)⟩
def p796:CachedProfile:=⟨⟨16968,109,3756⟩,⟨⟨⟨6839338160174,37622151934493282⟩,⟨716561197789398,83922318116⟩,⟨267821502,4573587789654⟩,⟨9730847906,0⟩⟩,⟨⟨6786207830844,1445871200904⟩,⟨9228784968,83921499090⟩,⟨267821502,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨6809927634134,37469566119523082⟩,⟨720247928374920,84354109840⟩,⟨271669200,4639294928400⟩,⟨9961204000,0⟩⟩,⟨⟨6757430236764,1434347299764⟩,⟨9239222520,84353286600⟩,⟨271669200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 17077 110 (3756-R)⟩
def p797:CachedProfile:=⟨⟨2471,17,439⟩,⟨⟨⟨16775110440,13595941852680⟩,⟨277853067360,223382720⟩,⟨762960,1898244480⟩,⟨4323440,0⟩⟩,⟨⟨16688123760,2883492480⟩,⟨19702320,223367760⟩,⟨762960,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨16175710800,13128692217600⟩,⟨284166532800,228459600⟩,⟨826200,2055585600⟩,⟨4957200,0⟩⟩,⟨⟨16097191200,2690025600⟩,⟨19461600,228444300⟩,⟨826200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2488 18 (439-R)⟩
def p798:CachedProfile:=⟨⟨8093,54,1729⟩,⟨⟨⟨714935462890,1880214797109430⟩,⟨37205673594840,9133860240⟩,⟨30268080,246594047760⟩,⟨544825440,0⟩⟩,⟨⟨709735541340,146214371940⟩,⟨969139080,9133673400⟩,⟨30268080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨708293693170,1863681127329490⟩,⟨37566084090150,9222343900⟩,⟨31127250,253593705750⟩,⟨570666250,0⟩⟩,⟨⟨703227428820,143689127820⟩,⟨970038300,9222155250⟩,⟨31127250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8147 55 (1729-R)⟩
def p799:CachedProfile:=⟨⟨5936,31,1295⟩,⟨⟨⟨287797516560,553619586258576⟩,⟨8583444669024,2877083712⟩,⟨7472736,44589815712⟩,⟨77218272,0⟩⟩,⟨⟨285608625696,60087212640⟩,⟨312167520,2877003360⟩,⟨7472736,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨283980842240,546681541479680⟩,⟨8750935326720,2933227520⟩,⟨7864320,46926397440⟩,⟨83886080,0⟩⟩,⟨⟨281871690240,58612170240⟩,⟨314327040,2933145600⟩,⟨7864320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5967 32 (1295-R)⟩
def p800:CachedProfile:=⟨⟨29457,179,5971⟩,⟨⟨⟨32537057756092,312175308027544540⟩,⟨5633381427412464,380174892320⟩,⟨1148093112,34024887467232⟩,⟨68502889016,0⟩⟩,⟨⟨32323785017256,6340707314592⟩,⟨38297564088,380172754344⟩,⟨1148093112,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨32479018025542,311646189037240090⟩,⟨5655367015325280,381658622400⟩,⟨1159012800,34348503340800⟩,⟨69540768000,0⟩⟩,⟨⟨32266813793676,6319488531312⟩,⟨38382640560,381656476080⟩,⟨1159012800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨32444202773644,311328738155386732⟩,⟨5649675525506880,381274531200⟩,⟨1157846400,34313935910400⟩,⟨69470784000,0⟩⟩,⟨⟨32232637928712,6306774331680⟩,⟨38305418400,381272387040⟩,⟨1157846400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29636 180 (5971-R)⟩
def p801:CachedProfile:=⟨⟨4217,38,1178⟩,⟨⟨⟨136298254914,183651183151578⟩,⟨4867481301372,2287948536⟩,⟨10214856,43464212280⟩,⟨129388176,0⟩⟩,⟨⟨134652142188,35457646860⟩,⟨316660536,2287858932⟩,⟨10214856,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨135005058174,182044646106078⟩,⟨4953196172106,2328241188⟩,⟨10668294,45393590970⟩,⟨138687822,0⟩⟩,⟨⟨133400332128,34858457760⟩,⟨319501728,2328150006⟩,⟨10668294,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4255 39 (1178-R)⟩
def p802:CachedProfile:=⟨⟨4305,36,1374⟩,⟨⟨⟨168495995250,228623400051750⟩,⟨5597567613000,2578950000⟩,⟨10692000,46413972000⟩,⟨128304000,0⟩⟩,⟨⟨165888228000,49207405500⟩,⟨408078000,2578851000⟩,⟨10692000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨166942667540,226709332684340⟩,⟨5707024495656,2629382800⟩,⟨11203896,48636112536⟩,⟨138181384,0⟩⟩,⟨⟨164396828376,48422952072⟩,⟨412727304,2629281864⟩,⟨11203896,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4341 37 (1374-R)⟩
def p803:CachedProfile:=⟨⟨11023,88,3254⟩,⟨⟨⟨2583701501010,9043336601698770⟩,⟨212184719152560,38193909600⟩,⟨151240320,1680431195520⟩,⟨4436382720,0⟩⟩,⟨⟨2549163548820,706110938820⟩,⟨5592454560,38193336720⟩,⟨151240320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨2573810831980,9011640950605180⟩,⟨213870662122872,38497391440⟩,⟨154174344,1713031136184⟩,⟨4573838872,0⟩⟩,⟨⟨2539621436856,701345786472⟩,⟨5617835928,38496814008⟩,⟨154174344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11111 89 (3254-R)⟩
def p804:CachedProfile:=⟨⟨31727,237,6666⟩,⟨⟨⟨42352988210200,437447398071486424⟩,⟨9686301044277672,606080382504⟩,⟨2246872338,71819027411832⟩,⟨177502914702,0⟩⟩,⟨⟨42056310150372,8523307104048⟩,⟨63196839684,606077222346⟩,⟨2246872338,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨42264643238706,436582876295093526⟩,⟨9708204229671024,607450899552⟩,⟨2261455056,72285149409984⟩,⟨179408767776,0⟩⟩,⟨⟨41969695792308,8490097786608⟩,⟨63216220536,607447732248⟩,⟨2261455056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 31964 238 (6666-R)⟩
def p805:CachedProfile:=⟨⟨6345,48,1280⟩,⟨⟨⟨324693017838,672223848933714⟩,⟨15079197464352,4717605312⟩,⟨17708544,113210721792⟩,⟨283336704,0⟩⟩,⟨⟨322577848572,62894845440⟩,⟨472227840,4717482336⟩,⟨17708544,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨320918620050,664789543714422⟩,⟨15225103676538,4763256092⟩,⟨18252402,116687605986⟩,⟨298122566,0⟩⟩,⟨⟨318871728336,61527075876⟩,⟨471582468,4763131926⟩,⟨18252402,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6393 49 (1280-R)⟩
def p806:CachedProfile:=⟨⟨5288,39,1107⟩,⟨⟨⟨195488483092,336560692324516⟩,⟨7357917163896,2762629584⟩,⟨10111608,53864535816⟩,⟨131450904,0⟩⟩,⟨⟨194118880968,39203182872⟩,⟨287014104,2762543160⟩,⟨10111608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨192849905374,332251543509370⟩,⟨7451220434400,2797664320⟩,⟨10502400,55946284800⟩,⟨140032000,0⟩⟩,⟨⟨191531303892,38218305804⟩,⟨286978080,2797576800⟩,⟨10502400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5327 40 (1107-R)⟩
def p807:CachedProfile:=⟨⟨4092,28,881⟩,⟨⟨⟨93282019614,124006034044242⟩,⟨2515459780512,1221167808⟩,⟨4148928,17093583360⟩,⟨38723328,0⟩⟩,⟨⟨92590177932,19208478240⟩,⟨130543056,1221118416⟩,⟨4148928,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨91695119852,122009235043724⟩,⟨2563939470288,1244705056⟩,⟨4379928,18045303360⟩,⟨42339304,0⟩⟩,⟨⟨91035501480,18603184320⟩,⟨130944744,1244654712⟩,⟨4379928,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4120 29 (881-R)⟩
def p808:CachedProfile:=⟨⟨11528,87,2136⟩,⟨⟨⟨1778751230014,6718645242294382⟩,⟨150496779178458,25914877572⟩,⟨97049718,1127232474570⟩,⟨2814441822,0⟩⟩,⟨⟨1768951533552,318109204080⟩,⟨2382737904,25914505734⟩,⟨97049718,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1766465362882,6674221482883834⟩,⟨151229322650736,26041023712⟩,⟨98643072,1145739281280⟩,⟨2893530112,0⟩⟩,⟨⟨1756856422860,313953868140⟩,⟨2378643168,26040650064⟩,⟨98643072,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11615 88 (2136-R)⟩
def p809:CachedProfile:=⟨⟨13640,97,2782⟩,⟨⟨⟨3259015713602,14489622053666606⟩,⟨305655906504498,44501962252⟩,⟨157111482,2158240428234⟩,⟨5079937918,0⟩⟩,⟨⟨3237400158168,638136345132⟩,⟨4506022092,44501422350⟩,⟨157111482,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨3240297996752,14410559226307856⟩,⟨307142520831552,44718412928⟩,⟨159503232,2191095897984⟩,⟨5210438912,0⟩⟩,⟨⟨3219029340768,631274713632⟩,⟨4503524928,44717870400⟩,⟨159503232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13737 98 (2782-R)⟩
def p810:CachedProfile:=⟨⟨13218,98,2981⟩,⟨⟨⟨3305366383242,14162241012991470⟩,⟨310918912830288,46699312800⟩,⟨171834768,2288151770688⟩,⟨5613269088,0⟩⟩,⟨⟨3278787838116,710222868432⟩,⟨5226933096,46698728328⟩,⟨171834768,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨3289808525680,14099470213630720⟩,⟨312722229866112,46970173800⟩,⟨174595014,2324907206424⟩,⟨5761635462,0⟩⟩,⟨⟨3263575463016,704042912832⟩,⟨5234323248,46969585938⟩,⟨174595014,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13316 99 (2981-R)⟩
def p811:CachedProfile:=⟨⟨43216,272,9377⟩,⟨⟨⟨110540775798126,1550361029540979042⟩,⟨28945000376500608,1331179041024⟩,⟨4162931712,181037574291456⟩,⟨377439141888,0⟩⟩,⟨⟨109715370143436,22945357565568⟩,⟨143514009792,1331173939392⟩,⟨4162931712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨110363470422396,1548011966478855516⟩,⟨29008045820229840,1334078517408⟩,⟨4187337336,182098926067968⟩,⟨381047697576,0⟩⟩,⟨⟨109541753718216,22876896842496⟩,⟨143611866216,1334073404664⟩,⟨4187337336,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43488 273 (9377-R)⟩
def p812:CachedProfile:=⟨⟨18358,135,3500⟩,⟨⟨⟨7398842684238,44436556787743314⟩,⟨969841487334690,104889049740⟩,⟨382834350,7079755634550⟩,⟨17227545750,0⟩⟩,⟨⟨7355825946252,1359623853000⟩,⟨9925335000,104888104470⟩,⟨382834350,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨7367550456530,44257063602405302⟩,⟨973118432969232,105243462368⟩,⟨386973312,7156297458816⟩,⟨17542790144,0⟩⟩,⟨⟨7325046778896,1348770163356⟩,⟨9919036512,105242513904⟩,⟨386973312,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18493 136 (3500-R)⟩
def p813:CachedProfile:=⟨⟨27930,208,5582⟩,⟨⟨⟨27393057344616,249739701990800232⟩,⟨5516641821929472,392117047296⟩,⟨1449257472,40779206747136⟩,⟨100481851392,0⟩⟩,⟨⟨27218783999616,5261407453368⟩,⟨38893053888,392114724768⟩,⟨1449257472,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨27320019414056,249106155593087696⟩,⟨5529263835742680,393014220544⟩,⟨1459556934,41069013008892⟩,⟨101682466402,0⟩⟩,⟨⟨27147052399956,5235051038976⟩,⟨38884272768,393011892702⟩,⟨1459556934,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 28138 209 (5582-R)⟩
def p814:CachedProfile:=⟨⟨15337,114,3233⟩,⟨⟨⟨4801817085450,23969538846443190⟩,⟨528105955236552,68359903920⟩,⟨252174384,3896346407184⟩,⟨9582626592,0⟩⟩,⟨⟨4767914445756,969289622532⟩,⟨7151577048,68359166568⟩,⟨252174384,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨4779575627540,23864358795472580⟩,⟨530432174290200,68661026000⟩,⟨255507000,3947838657000⟩,⟨9794435000,0⟩⟩,⟨⟨4746110608680,960914377080⟩,⟨7151974200,68660285400⟩,⟨255507000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 15451 115 (3233-R)⟩
def p815:CachedProfile:=⟨⟨9822,56,2392⟩,⟨⟨⟨1469640446776,4646390385922672⟩,⟨78458736896064,15885844352⟩,⟨45026688,444773624064⟩,⟨840498176,0⟩⟩,⟨⟨1455901228716,339253351008⟩,⟨1923282816,15885576336⟩,⟨45026688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨1459577702806,4616652826471402⟩,⟨79359177674088,16068165024⟩,⟨46356732,457911798696⟩,⟨880777908,0⟩⟩,⟨⟨1446094716276,335012725608⟩,⟨1933157052,16067893932⟩,⟨46356732,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 9878 57 (2392-R)⟩
def p816:CachedProfile:=⟨⟨30590,203,7207⟩,⟨⟨⟨42881964043176,423638602148297352⟩,⟨8324778214679472,540696385376⟩,⟨1782206832,54879494977776⟩,⟨120595995632,0⟩⟩,⟨⟨42507130491696,9597818930448⟩,⟨63272732208,540693458928⟩,⟨1782206832,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨42778492290200,422680294337711672⟩,⟨8347216688278848,542153788032⟩,⟨1795813632,55298489170176⟩,⟨122115326976,0⟩⟩,⟨⟨42406147584336,9555253643376⟩,⟨63302430528,542150853696⟩,⟨1795813632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 30793 204 (7207-R)⟩
def p817:CachedProfile:=⟨⟨10809,70,2221⟩,⟨⟨⟨1632884528550,5746897585760034⟩,⟨110455564138920,20306680240⟩,⟨65326800,710690257200⟩,⟨1524292000,0⟩⟩,⟨⟨1621875409572,322131236988⟩,⟨2072726040,20306369160⟩,⟨65326800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨1620345413078,5704992602272658⟩,⟨111226748819556,20448464056⟩,⟨66722676,725875992204⟩,⟨1579103332,0⟩⟩,⟨⟨1609571787780,317507749020⟩,⟨2072161980,20448150804⟩,⟨66722676,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10879 71 (2221-R)⟩
def p818:CachedProfile:=⟨⟨4671,31,784⟩,⟨⟨⟨106575751080,163623295835760⟩,⟨3228335415720,1373272720⟩,⟨4526310,21282709620⟩,⟨46771870,0⟩⟩,⟨⟨106085863980,17362793280⟩,⟨114471840,1373224050⟩,⟨4526310,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 17=>⟨⟨⟨104166465792,160055568143616⟩,⟨3260302000128,1386872832⟩,⟨4718592,22186819584⟩,⟨50331648,0⟩⟩,⟨⟨103707437568,16618447872⟩,⟨113098752,1386823680⟩,⟨4718592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4702 32 (784-R)⟩
def p819:CachedProfile:=⟨⟨24544,160,5079⟩,⟨⟨⟨19257846630280,153850925717695720⟩,⟨2976300184243200,240959436800⟩,⟨780288000,19276234752000⟩,⟨41615360000,0⟩⟩,⟨⟨19126550733360,3824374855680⟩,⟨24769267200,240957811200⟩,⟨780288000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19217364863970,153544138646627430⟩,⟨2989006485945480,241988139120⟩,⟨788516820,19479519521280⟩,⟨42317069340,0⟩⟩,⟨⟨19086841927140,3809331601920⟩,⟨24826035780,241986506580⟩,⟨788516820,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24704 161 (5079-R)⟩
def p820:CachedProfile:=⟨⟨4708,44,1291⟩,⟨⟨⟨185871030884,280157172984932⟩,⟨7703160725568,3242155136⟩,⟨15007872,71317407744⟩,⟨220115456,0⟩⟩,⟨⟨183705399864,47557217664⟩,⟨440344608,3242041440⟩,⟨15007872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨184267509774,277924437450882⟩,⟨7817248605240,3290176080⟩,⟨15576300,74018577600⟩,⟨233644500,0⟩⟩,⟨⟨182151613644,46823603904⟩,⟨443405340,3290060700⟩,⟨15576300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4752 45 (1291-R)⟩
def p821:CachedProfile:=⟨⟨6712,51,1474⟩,⟨⟨⟨420890432850,917415517836450⟩,⟨20645253157950,6105561900⟩,⟨23018850,155676482550⟩,⟨391320450,0⟩⟩,⟨⟨417665784900,88222658700⟩,⟨665289900,6105411450⟩,⟨23018850,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨416901938990,909205487022842⟩,⟨20864524213104,6170411936⟩,⟨23719488,160414897344⟩,⟨411137792,0⟩⟩,⟨⟨413761494276,86673877596⟩,⟨666426384,6170259888⟩,⟨23719488,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6763 52 (1474-R)⟩
def p822:CachedProfile:=⟨⟨19358,148,3873⟩,⟨⟨⟨9135157969470,57732072987233970⟩,⟨1308934345159584,134210236160⟩,⟨509136576,9931218051456⟩,⟨25117404416,0⟩⟩,⟨⟨9076896337236,1756008378072⟩,⟨13323553776,134209089456⟩,⟨509136576,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨9100055713820,57521003063127740⟩,⟨1313016164373360,134628771200⟩,⟨514175160,10029500670960⟩,⟨25537366280,0⟩⟩,⟨⟨9042422466840,1743337826640⟩,⟨13316791560,134627620920⟩,⟨514175160,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 19506 149 (3873-R)⟩
def p823:CachedProfile:=⟨⟨12236,94,2511⟩,⟨⟨⟨2370832299504,9458273737302192⟩,⟨215396795604096,34939387904⟩,⟨133176192,1642062447360⟩,⟨4172854016,0⟩⟩,⟨⟨2354931889632,466638615360⟩,⟨3557504448,34938915648⟩,⟨133176192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2356743293342,9404897427087314⟩,⟨216474980310840,35114286080⟩,⟨135266700,1667838411000⟩,⟨4283445500,0⟩⟩,⟨⟨2341106640180,461450693880⟩,⟨3555378420,35113811460⟩,⟨135266700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 12330 95 (2511-R)⟩
def p824:CachedProfile:=⟨⟨6603,49,1354⟩,⟨⟨⟨372241708440,801185038443480⟩,⟨17628594346440,5300445640⟩,⟨19520130,129847904760⟩,⟨318828790,0⟩⟩,⟨⟨369739538340,73225349040⟩,⟨539392980,5300312850⟩,⟨19520130,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨368142745320,792803421167616⟩,⟨17802492703200,5352735600⟩,⟨20115000,133804980000⟩,⟨335250000,0⟩⟩,⟨⟨365717005056,71719469280⟩,⟨539082000,5352601500⟩,⟨20115000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6652 50 (1354-R)⟩
def p825:CachedProfile:=⟨⟨24917,161,5396⟩,⟨⟨⟨21152095104000,171096512934821712⟩,⟨3278859390859752,261495357648⟩,⟨839373822,21049816708116⟩,⟨45046395114,0⟩⟩,⟨⟨20994680956116,4381960995216⟩,⟨28132056792,261493619814⟩,⟨839373822,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨21097372729176,170678264784114936⟩,⟨3291277847428800,262485764352⟩,⟨847786176,21260781721728⟩,⟨45780453504,0⟩⟩,⟨⟨20941092195696,4360874409696⟩,⟨28170573984,262484019936⟩,⟨847786176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25078 162 (5396-R)⟩
def p826:CachedProfile:=⟨⟨29532,177,5971⟩,⟨⟨⟨32692292096660,314478384167902964⟩,⟨5597914479134472,376853098704⟩,⟨1122580728,33350750848152⟩,⟨66232262952,0⟩⟩,⟨⟨32479018485912,6356325874248⟩,⟨37869658344,376850984616⟩,⟨1122580728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨32633992429170,313945408668337974⟩,⟨5620114428127848,378347613776⟩,⟨1133400048,33672182026032⟩,⟨67248402848,0⟩⟩,⟨⟨32421787326852,6335054824428⟩,⟨37956166776,378345491304⟩,⟨1133400048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | 16=>⟨⟨⟨32599021215108,313625643881012388⟩,⟨5614458416443728,377966854688⟩,⟨1132259424,33638295227616⟩,⟨67180725824,0⟩⟩,⟨⟨32387455500600,6322309306920⟩,⟨37879802640,377964734352⟩,⟨1132259424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29709 178 (5971-R)⟩
def p827:CachedProfile:=⟨⟨3853,33,905⟩,⟨⟨⟨85829003094,107042414610282⟩,⟨2709262162728,1394442720⟩,⟨5919804,23004358344⟩,⟨65117844,0⟩⟩,⟨⟨85079925012,19117487880⟩,⟨162346140,1394382924⟩,⟨5919804,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨84698353640,105718426479080⟩,⟨2757466302720,1419255200⟩,⟨6207720,24123199920⟩,⟨70354160,0⟩⟩,⟨⟨83976081480,18655831080⟩,⟨163226520,1419194340⟩,⟨6207720,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3886 34 (905-R)⟩
def p828:CachedProfile:=⟨⟨293336,876,80915⟩,⟨⟨⟨44673958848300540,4164297376832002896156⟩,⟨36813858506793491904,250254055573632⟩,⟨372557978496,109611027969265152⟩,⟨108786929720832,0⟩⟩,⟨⟨44144134988086056,11557797387634080⟩,⟨34412704143840,250253913808800⟩,⟨372557978496,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨44665930562153152,4163607680642914058056⟩,⟨36849962165979398328,250499481895912⟩,⟨373349060922,109843773911983464⟩,⟨109142375476198,0⟩⟩,⟨⟨44136362012921868,11554083901435632⟩,⟨34440918730572,250499339992050⟩,⟨373349060922,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 294212 877 (80915-R)⟩
def p829:CachedProfile:=⟨⟨3968,28,1192⟩,⟨⟨⟨122815494224,154335084564992⟩,⟨3200851449600,1602055840⟩,⟨5611872,22425040512⟩,⟨52377472,0⟩⟩,⟨⟨121110869016,34095214656⟩,⟨238905408,1601989032⟩,⟨5611872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨121645580784,152990840561832⟩,⟨3287374959960,1645363720⟩,⟨5969418,23853794328⟩,⟨57704374,0⟩⟩,⟨⟨119983328556,33525784656⟩,⟨243305244,1645295106⟩,⟨5969418,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3996 29 (1192-R)⟩
def p830:CachedProfile:=⟨⟨1983,10,591⟩,⟨⟨⟨15152728400,9503462870672⟩,⟨141129165120,141630080⟩,⟨355200,707913600⟩,⟨1184000,0⟩⟩,⟨⟨14943594336,4183769376⟩,⟨20992320,141618240⟩,⟨355200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨14862653310,9336796372482⟩,⟨152618980932,153161448⟩,⟨422532,842106276⟩,⟨1549284,0⟩⟩,⟨⟨14663872956,4043502036⟩,⟨22317372,153148644⟩,⟨422532,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1993 11 (591-R)⟩
def p831:CachedProfile:=⟨⟨2652,21,664⟩,⟨⟨⟨29989349390,25609711154930⟩,⟨598784874030,448053060⟩,⟨1759590,4703384070⟩,⟨12317130,0⟩⟩,⟨⟨29692598460,7081739280⟩,⟨55636560,448025130⟩,⟨1759590,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨29445898086,25176502464906⟩,⟨616920175080,461624592⟩,⟨1899216,5076604368⟩,⟨13927584,0⟩⟩,⟨⟨29163530316,6849220356⟩,⟨56372184,461595816⟩,⟨1899216,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2673 22 (664-R)⟩
def p832:CachedProfile:=⟨⟨3779,30,937⟩,⟨⟨⟨85801746226,104484845803366⟩,⟨2449928338200,1286448240⟩,⟨5065200,19293346800⟩,⟨50652000,0⟩⟩,⟨⟨84971065620,20086517724⟩,⟨158203080,1286391960⟩,⟨5065200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨84600594358,103118750028058⟩,⟨2499201370116,1312323496⟩,⟨5339316,20337454644⟩,⟨55172932,0⟩⟩,⟨⟨83801231340,19575593700⟩,⟨159318300,1312266084⟩,⟨5339316,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3809 31 (937-R)⟩
def p833:CachedProfile:=⟨⟨14306,105,4099⟩,⟨⟨⟨5453795469700,24826498955278900⟩,⟨536450662377000,74450670000⟩,⟨271215000,3908479365000⟩,⟨9492525000,0⟩⟩,⟨⟨5384789915400,1453138949400⟩,⟨10587717000,74449809000⟩,⟨271215000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨5434328455042,24745101994938490⟩,⟨539842508157876,74921412680⟩,⟨275529192,3970651185912⟩,⟨9735364784,0⟩⟩,⟨⟨5365976576076,1443937410612⟩,⟨10620870552,74920546236⟩,⟨275529192,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 14411 106 (4099-R)⟩
def p834:CachedProfile:=⟨⟨8194,60,1652⟩,⟨⟨⟨698369278656,1866795134180496⟩,⟨40543883445600,9824374080⟩,⟨35704800,294707419200⟩,⟨714096000,0⟩⟩,⟨⟨693830782020,135237960144⟩,⟨983072160,9824175720⟩,⟨35704800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨692076967736,1850795855862536⟩,⟨40870490594208,9903519824⟩,⟨36592314,302032959756⟩,⟨744043718,0⟩⟩,⟨⟨687652402008,132956191368⟩,⟨982593612,9903319866⟩,⟨36592314,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8254 61 (1652-R)⟩
def p835:CachedProfile:=⟨⟨6354,53,1248⟩,⟨⟨⟨317419818334,659534348218990⟩,⟨16305173055390,5090019724⟩,⟨21050646,134871488922⟩,⟨371894746,0⟩⟩,⟨⟨315458491152,59921544384⟩,⟨495683136,5089887330⟩,⟨21050646,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨313647266530,652060435186810⟩,⟨16426594096380,5127927480⟩,⟨21607560,138439636920⟩,⟨388936080,0⟩⟩,⟨⟨311750837580,58585223580⟩,⟨493772760,5127794100⟩,⟨21607560,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6407 54 (1248-R)⟩
def p836:CachedProfile:=⟨⟨4342,32,868⟩,⟨⟨⟨103059145376,146048643908816⟩,⟨3192404894976,1459808768⟩,⟨5339136,23353380864⟩,⟨56950784,0⟩⟩,⟨⟨102396817908,19795639248⟩,⟨144824064,1459753152⟩,⟨5339136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨101295728280,143668481643720⟩,⟨3239124435360,1481174640⟩,⟨5586570,24435657180⟩,⟨61452270,0⟩⟩,⟨⟨100664683560,19162581480⟩,⟨144573660,1481118210⟩,⟨5586570,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4374 33 (868-R)⟩
def p837:CachedProfile:=⟨⟨3431,22,858⟩,⟨⟨⟨64639246626,71304612590286⟩,⟨1352143395900,783208712⟩,⟨2494536,8613632808⟩,⟨18293264,0⟩⟩,⟨⟨64000949496,15269621796⟩,⟨97286904,783170916⟩,⟨2494536,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨63485057870,70116295859090⟩,⟨1390562239170,805464140⟩,⟨2682030,9261049590⟩,⟨20562230,0⟩⟩,⟨⟨62877298380,14775663240⟩,⟨98418840,805425270⟩,⟨2682030,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3453 23 (858-R)⟩
def p838:CachedProfile:=⟨⟨19819,146,3765⟩,⟨⟨⟨9274342630350,60144596655012450⟩,⟨1315016660485080,131734107568⟩,⟨481656336,9616268748240⟩,⟨23440608352,0⟩⟩,⟨⟨9220808356620,1698501212100⟩,⟨12420795240,131733007896⟩,⟨481656336,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨9237891412904,59918772716483912⟩,⟨1319101510346928,132143323872⟩,⟨486461808,9712209996720⟩,⟨23836628592,0⟩⟩,⟨⟨9184950951792,1685894752080⟩,⟨12413049264,132142220784⟩,⟨486461808,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 19965 147 (3765-R)⟩
def p839:CachedProfile:=⟨⟨5565,40,1152⟩,⟨⟨⟨225041172542,407908279557434⟩,⟨8694080000880,3102400160⟩,⟨11068800,62040624000⟩,⟨147584000,0⟩⟩,⟨⟨223498096500,44669249280⟩,⟨318781440,3102307920⟩,⟨11068800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨222126055554,402891570168078⟩,⟨8803219430394,3141348332⟩,⟨11487954,64389982170⟩,⟨157002038,0⟩⟩,⟨⟨220638232248,43590600660⟩,⟨318860772,3141254934⟩,⟨11487954,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5605 41 (1152-R)⟩
def p840:CachedProfile:=⟨⟨8874,64,1873⟩,⟨⟨⟨931271105166,2688902744751426⟩,⟨57491266429440,12864815104⟩,⟨46055424,411643379712⟩,⟨982515712,0⟩⟩,⟨⟨924663371796,188234387256⟩,⟨1347840768,12864575232⟩,⟨46055424,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨923827945260,2668540086110220⟩,⟨57953339074800,12968217600⟩,⟨47151000,421435638000⟩,⟨1021605000,0⟩⟩,⟨⟨917366757240,185431680720⟩,⟨1348518600,12967975800⟩,⟨47151000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8938 65 (1873-R)⟩
def p841:CachedProfile:=⟨⟨4200,25,955⟩,⟨⟨⟨106784803260,145079867545500⟩,⟨2560053519000,1211921200⟩,⟨3585000,15146625000⟩,⟨29875000,0⟩⟩,⟨⟨105904829160,23144043000⟩,⟨136947000,1211873400⟩,⟨3585000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨104855151020,142610525094860⟩,⟨2617891039920,1239303520⟩,⟨3812640,16108404000⟩,⟨33042880,0⟩⟩,⟨⟨104018390280,22375431000⟩,⟨137694960,1239254640⟩,⟨3812640,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4225 26 (955-R)⟩
def p842:CachedProfile:=⟨⟨16983,137,3888⟩,⟨⟨⟨7133568805984,39259937740761088⟩,⟨936976725945408,109461256264⟩,⟨437955846,7497804083520⟩,⟨19999983634,0⟩⟩,⟨⟨7074647407008,1553170775040⟩,⟨12428995104,109460190678⟩,⟨437955846,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨7113719574144,39157223938806888⟩,⟨941389021866672,109976725296⟩,⟨443230056,7588098558720⟩,⟨20388582576,0⟩⟩,⟨⟨7055250926148,1545192512640⟩,⟨12455406936,109975654692⟩,⟨443230056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 17120 138 (3888-R)⟩
def p843:CachedProfile:=⟨⟨20661,164,4869⟩,⟨⟨⟨13250275998910,88533896961331330⟩,⟨2078278914725040,199596521440⟩,⟨785901120,16366390824000⟩,⟨42962594560,0⟩⟩,⟨⟨13134619289340,2962818148500⟩,⟨23332637520,199594924080⟩,⟨785901120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨13214791397122,88311593165614294⟩,⟨2085798990193380,200318755560⟩,⟨793554300,16525768297500⟩,⟨43645486500,0⟩⟩,⟨⟨13099986660180,2948233484700⟩,⟨23359352940,200317152420⟩,⟨793554300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 20825 165 (4869-R)⟩
def p844:CachedProfile:=⟨⟨1050,9,322⟩,⟨⟨⟨2343824306,779326319186⟩,⟨19572104250,36965412⟩,⟨156978,166239702⟩,⟨470934,0⟩⟩,⟨⟨2309650260,660854124⟩,⟨5616324,36959598⟩,⟨156978,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨2261331726,754215123366⟩,⟨21073131900,39801080⟩,⟨187800,198880200⟩,⟨626000,0⟩⟩,⟨⟨2230200120,620506224⟩,⟨5859360,39794820⟩,⟨187800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1059 10 (322-R)⟩
def p845:CachedProfile:=⟨⟨4106,30,993⟩,⟨⟨⟨106958669230,141678165948130⟩,⟨3061049599440,1480264800⟩,⟨5367600,22200393600⟩,⟨53676000,0⟩⟩,⟨⟨105970314156,24494434272⟩,⟨177667560,1480205160⟩,⟨5367600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨105668221984,140078128829032⟩,⟨3128076609480,1512679720⟩,⟨5667978,23442757008⟩,⟨58569106,0⟩⟩,⟨⟨104712160116,23955033696⟩,⟨179546916,1512618774⟩,⟨5667978,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4136 31 (993-R)⟩
def p846:CachedProfile:=⟨⟨25694,190,5079⟩,⟨⟨⟨21077362828680,176866279237417320⟩,⟨3880055434996800,299806563200⟩,⟨1100328000,28480889952000⟩,⟨69687440000,0⟩⟩,⟨⟨20946054942960,4007048201280⟩,⟨29413504800,299804632800⟩,⟨1100328000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21033299337570,176514185634421830⟩,⟨3892798559290680,300791215920⟩,⟨1109752020,28724821285680⟩,⟨70654211940,0⟩⟩,⟨⟨20902764435540,3991286398320⟩,⟨29452005180,300789279180⟩,⟨1109752020,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25884 191 (5079-R)⟩
def p847:CachedProfile:=⟨⟨50003,418,8921⟩,⟨⟨⟨139647196291842,2293700684140832550⟩,⟨56887350680159208,2256508343760⟩,⟨9353325168,471604008295728⟩,⟨1303229973408,0⟩⟩,⟨⟨138936245981316,24079000927212⟩,⟨199619650296,2256500884968⟩,⟨9353325168,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨139416951132684,2290071708393817932⟩,⟨56933965575749160,2258357407120⟩,⟨9383384328,473119621202088⟩,⟨1310546011144,0⟩⟩,⟨⟨138709339778856,24003488622456⟩,⟨199469699784,2258349942216⟩,⟨9383384328,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 50421 419 (8921-R)⟩
def p848:CachedProfile:=⟨⟨2355,16,516⟩,⟨⟨⟨18136942142,13860713621150⟩,⟨279064506336,235421120⟩,⟨794112,1882839552⟩,⟨4235264,0⟩⟩,⟨⟨17996836176,3795098472⟩,⟨25610112,235404576⟩,⟨794112,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨17609948514,13479701098602⟩,⟨288475424370,243361460⟩,⟨872202,2067990942⟩,⟨4942478,0⟩⟩,⟨⟨17480805276,3592150356⟩,⟨25755612,243344358⟩,⟨872202,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2371 17 (516-R)⟩
def p849:CachedProfile:=⟨⟨10474,75,2254⟩,⟨⟨⟨1563120642930,5320789333160070⟩,⟨112927376157750,21410548500⟩,⟨76106250,802844831250⟩,⟨1902656250,0⟩⟩,⟨⟨1551616503360,321708844380⟩,⟨2287246500,21410210250⟩,⟨76106250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1552711087998,5287276411875738⟩,⟨113722596650376,21561324336⟩,⟨77664096,819278548704⟩,⟨1967490432,0⟩⟩,⟨⟨1541419365780,317725752960⟩,⟨2289047040,21560983704⟩,⟨77664096,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10549 76 (2254-R)⟩
def p850:CachedProfile:=⟨⟨49265,375,9784⟩,⟨⟨⟨149356552752880,2403012085283203840⟩,⟨54251324119980000,2185802655000⟩,⟨8256093750,409832493750000⟩,⟨1032011718750,0⟩⟩,⟨⟨148418895969120,28514141289600⟩,⟨215406990000,2185795316250⟩,⟨8256093750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨149129484543960,2399534638624956600⟩,⟨54318166013096640,2188495760448⟩,⟨8288309376,411431677424640⟩,⟨1038801441792,0⟩⟩,⟨⟨148195844193180,28432601632800⟩,⟨215363783520,2188488412656⟩,⟨8288309376,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 49640 376 (9784-R)⟩
def p851:CachedProfile:=⟨⟨10392,75,2296⟩,⟨⟨⟨1570676981774,5296608777009062⟩,⟨113249465215650,21639807300⟩,⟨77523750,811441091250⟩,⟨1938093750,0⟩⟩,⟨⟨1558519994424,331212221424⟩,⟨2373260400,21639462750⟩,⟨77523750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1560372178482,5263820029445826⟩,⟨114059980780344,21794686896⟩,⟨79119648,828145355616⟩,⟨2004364416,0⟩⟩,⟨⟨1548435608868,327186236412⟩,⟨2375671536,21794339880⟩,⟨79119648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10467 76 (2296-R)⟩
def p852:CachedProfile:=⟨⟨4479,30,1120⟩,⟨⟨⟨143820710558,207173374725578⟩,⟨4102857511380,1819921080⟩,⟨6053400,27294780600⟩,⟨60534000,0⟩⟩,⟨⟨142404418980,33966838080⟩,⟨225993600,1819853820⟩,⟨6053400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨141852031650,204527583030654⟩,⟨4186665695286,1857098772⟩,⟨6382962,28780775658⟩,⟨65957274,0⟩⟩,⟨⟨140487926472,33123348468⟩,⟨227727612,1857030138⟩,⟨6382962,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4509 31 (1120-R)⟩
def p853:CachedProfile:=⟨⟨21324,148,4322⟩,⟨⟨⟨12363172808712,85945737260787096⟩,⟨1769910642336672,164859576288⟩,⟨568145952,12199229881344⟩,⟨28028533632,0⟩⟩,⟨⟨12282234887868,2407097860992⟩,⟨16591397328,164858296680⟩,⟨568145952,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨12320531587544,85664017479548480⟩,⟨1776098820428400,165435988552⟩,⟨573984654,12324598490688⟩,⟨28507904482,0⟩⟩,⟨⟨12240376396872,2391530575104⟩,⟨16595475768,165434704470⟩,⟨573984654,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 21472 149 (4322-R)⟩
def p854:CachedProfile:=⟨⟨5444,38,1203⟩,⟨⟨⟨225865886204,398901828341660⟩,⟨8250384041760,3010115584⟩,⟨10431456,57185241792⟩,⟨132131776,0⟩⟩,⟨⟨224110245912,47641167504⟩,⟨330237936,3010024080⟩,⟨10431456,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨222838689344,393854476487600⟩,⟨8361998962200,3050840832⟩,⟨10850814,59484162348⟩,⟨141060582,0⟩⟩,⟨⟨221147565132,46461002544⟩,⟨330532488,3050748090⟩,⟨10850814,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5482 39 (1203-R)⟩
def p855:CachedProfile:=⟨⟨4772,31,1143⟩,⟨⟨⟨165863765496,255292898899896⟩,⟨4909159878480,2044286816⟩,⟨6596304,31682048112⟩,⟨68161808,0⟩⟩,⟨⟨164358198576,37682186256⟩,⟨243212112,2044215888⟩,⟨6596304,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨163496647566,251879044008006⟩,⟨5001068617920,2082562432⟩,⟨6936576,33316374528⟩,⟨73990144,0⟩⟩,⟨⟨162049280856,36700068816⟩,⟨244514304,2082490176⟩,⟨6936576,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4803 32 (1143-R)⟩
def p856:CachedProfile:=⟨⟨24656,184,5369⟩,⟨⟨⟨20655672044310,165450773237078730⟩,⟨3658087589106240,294534791040⟩,⟨1090840320,27096473548800⟩,⟨66904872960,0⟩⟩,⟨⟨20500608778140,4297051231200⟩,⟨31830009120,294532814880⟩,⟨1090840320,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20614331894480,165138028642714640⟩,⟨3671119277572800,295584060800⟩,⟨1100676000,27340791840000⟩,⟨67875020000,0⟩⟩,⟨⟨20460132407520,4281060729600⟩,⟨31883906400,295582077600⟩,⟨1100676000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5369-R)⟩
def p857:CachedProfile:=⟨⟨24656,184,5371⟩,⟨⟨⟨20663942006324,165513326310337652⟩,⟨3659450029063296,294644487424⟩,⟨1091246592,27106565345280⟩,⟨66929790976,0⟩⟩,⟨⟨20508705597912,4300252908480⟩,⟨31853725248,294642510528⟩,⟨1091246592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20622598637214,165200574795430482⟩,⟨3672489122006040,295694353360⟩,⟨1101086700,27350993628000⟩,⟨67900346500,0⟩⟩,⟨⟨20468226651852,4284256445280⟩,⟨31907707020,295692369420⟩,⟨1101086700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5371-R)⟩
def p858:CachedProfile:=⟨⟨24656,184,5375⟩,⟨⟨⟨20680483864320,165638436619488000⟩,⟨3662174909030400,294863880192⟩,⟨1092059136,27126748938240⟩,⟨66979627008,0⟩⟩,⟨⟨20524900784640,4306659840000⟩,⟨31901184000,294861901824⟩,⟨1092059136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20639134053050,165325671248037950⟩,⟨3675228810925800,295914938480⟩,⟨1101908100,27371397204000⟩,⟨67950999500,0⟩⟩,⟨⟨20484416684820,4290651453600⟩,⟨31955334900,295912953060⟩,⟨1101908100,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5375-R)⟩
def p859:CachedProfile:=⟨⟨25888,132,5079⟩,⟨⟨⟨21292524968840,179658199946274920⟩,⟨2724018133034880,209381018880⟩,⟨531083520,13818793190400⟩,⟨23367674880,0⟩⟩,⟨⟨21161215701360,4028102078400⟩,⟨20434645440,209379677760⟩,⟨531083520,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21248037930210,179300610353629830⟩,⟨2739251689672680,210551948880⟩,⟨538099380,14001345867600⟩,⟨23855739180,0⟩⟩,⟨⟨21117501649140,4012257459600⟩,⟨20508464340,210550600260⟩,⟨538099380,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26020 133 (5079-R)⟩
def p860:CachedProfile:=⟨⟨29656,176,5971⟩,⟨⟨⟨32954715165884,318384587875627292⟩,⟨5612473269587712,376275367424⟩,⟨1109932032,33111492378624⟩,⟨65116012544,0⟩⟩,⟨⟨32741440086024,6382642077504⟩,⟨37655705472,376273265280⟩,⟨1109932032,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨32860741208460,317521382066411436⟩,⟨5629239916706448,377399462304⟩,⟨1119573144,33399106031808⟩,⟨66054815496,0⟩⟩,⟨⟨32649174028776,6348484676160⟩,⟨37666994760,377397353880⟩,⟨1119573144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29832 177 (5971-R)⟩
def p861:CachedProfile:=⟨⟨24832,192,5237⟩,⟨⟨⟨20399626537146,164919948406928766⟩,⟨3778667688844800,302006486016⟩,⟨1158561792,28991850283008⟩,⟨74147954688,0⟩⟩,⟨⟨20255706112500,4118661022464⟩,⟨31600979712,302004474624⟩,⟨1158561792,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20357945693316,164600786497179396⟩,⟨3791096604684720,302999865184⟩,⟨1168426632,29238708039168⟩,⟨75168779992,0⟩⟩,⟨⟨20214847088760,4102948452864⟩,⟨31644383448,302997847176⟩,⟨1168426632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25024 193 (5237-R)⟩
def p862:CachedProfile:=⟨⟨5156,46,1608⟩,⟨⟨⟨282118803384,459850157084880⟩,⟨12018698257680,4620842048⟩,⟨20427864,106265748528⟩,⟨313227248,0⟩⟩,⟨⟨277941729972,80753933664⟩,⟨714087072,4620694020⟩,⟨20427864,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨280109071944,456867907078440⟩,⟨12203644752000,4691952096⟩,⟨21193146,110246745492⟩,⟨332025954,0⟩⟩,⟨⟨276009223152,79752964824⟩,⟨720566964,4691801790⟩,⟨21193146,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5202 47 (1608-R)⟩
def p863:CachedProfile:=⟨⟨122667,291,34706⟩,⟨⟨⟨3357402602474880,130490601253987125912⟩,⟨916171736695180272,14902202342448⟩,⟨17634140802,2168258684732316⟩,⟨1710511657794,0⟩⟩,⟨⟨3315589262594016,888647818428216⟩,⟨2103128833932,14902182142974⟩,⟨17634140802,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨3355988536344026,130440094313364019646⟩,⟨918975747194815200,14947811646592⟩,⟨17748895296,2182368667805568⟩,⟨1727559142144,0⟩⟩,⟨⟨3314222158719516,887982222182616⟩,⟨2108775426384,14947791385296⟩,⟨17748895296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 122958 292 (34706-R)⟩
def p864:CachedProfile:=⟨⟨4790,41,1610⟩,⟨⟨⟨246537345474,370149469398522⟩,⟨9250487860986,3829636980⟩,⟨16248546,78496725726⟩,⟨222063462,0⟩⟩,⟨⟨242345906892,75181278060⟩,⟨638052660,3829504878⟩,⟨16248546,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨244750015614,367727176462782⟩,⟨9417280158972,3898691160⟩,⟨16944984,81861217704⟩,⟨237229776,0⟩⟩,⟨⟨240635986752,74250537600⟩,⟨645523200,3898556676⟩,⟨16944984,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4831 42 (1610-R)⟩
def p865:CachedProfile:=⟨⟨3150,27,836⟩,⟨⟨⟨53636250654,54195047912682⟩,⟨1368821565594,861745068⟩,⟨3661038,11631117726⟩,⟨32949342,0⟩⟩,⟨⟨53045956404,13338291384⟩,⟨113356584,861699870⟩,⟨3661038,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨52855876290,53463659802966⟩,⟨1400860045872,881916896⟩,⟨3885504,12344246208⟩,⟨36264704,0⟩⟩,⟨⟨52288431636,12989799900⟩,⟨114483600,881870640⟩,⟨3885504,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3177 28 (836-R)⟩
def p866:CachedProfile:=⟨⟨7943,58,1846⟩,⟨⟨⟨741020622242,1903983514506830⟩,⟨41149041793908,10286238520⟩,⟨37279848,298276063848⟩,⟨720743728,0⟩⟩,⟨⟨734697015096,163679433372⟩,⟨1186527576,10286024268⟩,⟨37279848,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨735800982770,1891387523635190⟩,⟨41586536785710,10395605300⟩,⟨38325810,306644805810⟩,⟨753740930,0⟩⟩,⟨⟨729599493840,161558912340⟩,⟨1191348060,10395388770⟩,⟨38325810,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8001 59 (1846-R)⟩
def p867:CachedProfile:=⟨⟨1375,8,274⟩,⟨⟨⟨3262359650,1461794373050⟩,⟨25254728400,36528800⟩,⟨105600,146044800⟩,⟨281600,0⟩⟩,⟨⟨3240953100,625254300⟩,⟨3616800,36524400⟩,⟨105600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 18=>⟨⟨⟨3036555230,1365061556462⟩,⟨26551403478,38405052⟩,⟨124902,172739466⟩,⟨374706,0⟩⟩,⟨⟨3019001616,545942016⟩,⟨3552768,38400426⟩,⟨124902,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1383 9 (274-R)⟩
def p868:CachedProfile:=⟨⟨16690,126,3204⟩,⟨⟨⟨5602776367160,30588271382457920⟩,⟨685180615986720,81492894000⟩,⟨305295480,5133848791680⟩,⟨12822410160,0⟩⟩,⟨⟨5569767277320,1036082862720⟩,⟨7763227920,81492086340⟩,⟨305295480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨5576874143904,30453277638154152⟩,⟨687601746771912,81780862600⟩,⟨308805834,5192878904544⟩,⟨13072780306,0⟩⟩,⟨⟨5544294889092,1027049643840⟩,⟨7756618980,81780052086⟩,⟨308805834,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 16816 127 (3204-R)⟩
def p869:CachedProfile:=⟨⟨18255,136,3499⟩,⟨⟨⟨7317598459500,43695208069621500⟩,⟨966001670424000,105053200000⟩,⟨388416000,7143358656000⟩,⟨17608192000,0⟩⟩,⟨⟨7274619219000,1351352289000⟩,⟨9993144000,105052248000⟩,⟨388416000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨7286623732374,43518631107000882⟩,⟨969212125153692,105402347400⟩,⟨392572404,7219799081964⟩,⟨17927473116,0⟩⟩,⟨⟨7244157255972,1340561553660⟩,⟨9986239620,105401392236⟩,⟨392572404,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 18391 137 (3499-R)⟩
def p870:CachedProfile:=⟨⟨7858,61,1583⟩,⟨⟨⟨615953177136,1579766152898736⟩,⟨36357906945888,9182758464⟩,⟨35364384,280050556896⟩,⟨719075808,0⟩⟩,⟨⟨611958761568,119140024608⟩,⟨917734752,9182565216⟩,⟨35364384,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨610162697770,1565637703282630⟩,⟨36627308763960,9250804240⟩,⟨36210480,286750791120⟩,⟨748349920,0⟩⟩,⟨⟨606272867340,117042661620⟩,⟨916358760,9250609560⟩,⟨36210480,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 7919 62 (1583-R)⟩
def p871:CachedProfile:=⟨⟨6263,43,1239⟩,⟨⟨⟨305439710280,624364767461160⟩,⟨12722615030880,4035257600⟩,⟨13756560,86748867360⟩,⟨197177360,0⟩⟩,⟨⟨303520521360,58129716960⟩,⟨396380880,4035150960⟩,⟨13756560,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨301779702614,617236032359882⟩,⟨12871497787104,4082481920⟩,⟨14241216,89805108096⟩,⟨208871168,0⟩⟩,⟨⟨299924474052,56823996600⟩,⟨396488400,4082374032⟩,⟨14241216,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 6306 44 (1239-R)⟩
def p872:CachedProfile:=⟨⟨1523,9,377⟩,⟨⟨⟨5596592022,2741178486186⟩,⟨47922844536,62569584⟩,⟨183708,281440656⟩,⟨551124,0⟩⟩,⟨⟨5541709068,1309915152⟩,⟨7695324,62562780⟩,⟨183708,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨5354374872,2630070933336⟩,⟨51133951440,66762960⟩,⟨217800,333669600⟩,⟨726000,0⟩⟩,⟨⟨5305693668,1207883952⟩,⟨7884360,66755700⟩,⟨217800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1532 10 (377-R)⟩
def p873:CachedProfile:=⟨⟨52720,202,13711⟩,⟨⟨⟨243317203668784,4100266188887122672⟩,⟨46545765101345664,1759037667328⟩,⟨3357026688,177660566382336⟩,⟨226039796992,0⟩⟩,⟨⟨240738012599904,59697677327424⟩,⟨227862341184,1759032127680⟩,⟨3357026688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨243003257633920,4095358165461421696⟩,⟨46721607829059072,1765683060736⟩,⟨3386390784,179214573070848⟩,⟨229145776384,0⟩⟩,⟨⟨240433081764096,59558435735040⟩,⟨228456264960,1765677500160⟩,⟨3386390784,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 52922 203 (13711-R)⟩
def p874:CachedProfile:=⟨⟨43018,250,11427⟩,⟨⟨⟨135832860440236,1868521310775827212⟩,⟨32092269786276000,1483422968000⟩,⟨4285500000,185425014000000⟩,⟨357125000000,0⟩⟩,⟨⟨134339645219016,33901626159648⟩,⟨195881634000,1483417254000⟩,⟨4285500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨135700958876406,1866841525107812682⟩,⟨32192444052780264,1488053407632⟩,⟨4316072508,186747825276144⟩,⟨361111399836,0⟩⟩,⟨⟨134211658611756,33842318712048⟩,⟨196321114836,1488047675796⟩,⟨4316072508,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 43268 251 (11427-R)⟩
def p875:CachedProfile:=⟨⟨24334,159,4761⟩,⟨⟨⟨17681226784130,140461686317880902⟩,⟨2725389786391308,222546907992⟩,⟨722328732,17691997632876⟩,⟨38283422796,0⟩⟩,⟨⟨17573052682596,3331814434956⟩,⟨21628975428,222545393676⟩,⟨722328732,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨17641836804240,140163484066757712⟩,⟨2736771312337920,223476295680⟩,⟨729907200,17877617049600⟩,⟨38928384000,0⟩⟩,⟨⟨17534341874016,3317834320416⟩,⟨21673681920,223474775040⟩,⟨729907200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24493 160 (4761-R)⟩
def p876:CachedProfile:=⟨⟨24656,184,5359⟩,⟨⟨⟨20614331894480,165138028642714640⟩,⟨3651275389585920,293986309120⟩,⟨1088808960,27046014566400⟩,⟨66780282880,0⟩⟩,⟨⟨20460132407520,4281060729600⟩,⟨31711560960,293984336640⟩,⟨1088808960,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20573007823050,164825318573859150⟩,⟨3664270055673000,295032598000⟩,⟨1098622500,27289782900000⟩,⟨67748387500,0⟩⟩,⟨⟨20419668899700,4265100036000⟩,⟨31765036500,295030618500⟩,⟨1098622500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5359-R)⟩
def p877:CachedProfile:=⟨⟨24656,184,5365⟩,⟨⟨⟨20639134053050,165325671248037950⟩,⟨3655362709245120,294315398272⟩,⟨1090027776,27076289955840⟩,⟨66855036928,0⟩⟩,⟨⟨20484416684820,4290651453600⟩,⟨31782603360,294313423584⟩,⟨1090027776,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20597800338180,165012940479312900⟩,⟨3668379588759600,295363475680⟩,⟨1099854600,27320388264000⟩,⟨67824367000,0⟩⟩,⟨⟨20443945462200,4274672875200⟩,⟨31836331800,295361493960⟩,⟨1099854600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5365-R)⟩
def p878:CachedProfile:=⟨⟨24656,184,5373⟩,⟨⟨⟨20672212612914,165575880770796918⟩,⟨3660812469038016,294754183808⟩,⟨1091652864,27116657141760⟩,⟨66954708992,0⟩⟩,⟨⟨20516802933348,4303455778080⟩,⟨31877450208,294752206176⟩,⟨1091652864,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20630866023324,165263122330195068⟩,⟨3673858966457040,295804645920⟩,⟨1101497400,27361195416000⟩,⟨67925673000,0⟩⟩,⟨⟨20476321410888,4287453353280⟩,⟨31931516520,295802661240⟩,⟨1101497400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5373-R)⟩
def p879:CachedProfile:=⟨⟨24656,184,5377⟩,⟨⟨⟨20688755760782,165700993857442754⟩,⟨3663537349040448,294973576576⟩,⟨1092465408,27136840734720⟩,⟨67004545024,0⟩⟩,⟨⟨20532999151980,4309865094240⟩,⟨31924926624,294971597472⟩,⟨1092465408,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20647402726632,165388221549989064⟩,⟨3676598655412320,296025231040⟩,⟨1102318800,27381598992000⟩,⟨67976326000,0⟩⟩,⟨⟨20492512473840,4293850746240⟩,⟨31979162160,296023244880⟩,⟨1102318800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5377-R)⟩
def p880:CachedProfile:=⟨⟨24348,181,5143⟩,⟨⟨⟨19251367577496,152542056989756856⟩,⟨3361227407358768,274064274784⟩,⟨1011135504,24802142777616⟩,⟨61005175408,0⟩⟩,⟨⟨19115054113488,3893575297008⟩,⟨28730772912,274062412656⟩,⟨1011135504,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19211304727526,152241432239222666⟩,⟨3373227243573096,275042714128⟩,⟨1020351696,25028206751184⟩,⟨61901336224,0⟩⟩,⟨⟨19075783828428,3878450225028⟩,⟨28777281624,275040845352⟩,⟨1020351696,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24529 182 (5143-R)⟩
def p881:CachedProfile:=⟨⟨1166,8,283⟩,⟨⟨⟨2465136756,926647735476⟩,⟨18796374144,32026112⟩,⟨109056,128031744⟩,⟨290816,0⟩⟩,⟨⟨2441724648,566140368⟩,⟨3857856,32021568⟩,⟨109056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨2361316776,890020303536⟩,⟨20326564440,34633872⟩,⟨132678,155763972⟩,⟨398034,0⟩⟩,⟨⟨2340478140,523059264⟩,⟨4009824,34628958⟩,⟨132678,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1174 9 (283-R)⟩
def p882:CachedProfile:=⟨⟨14993,138,4728⟩,⟨⟨⟨7025323851310,33268264812018550⟩,⟨896505277004604,118499471160⟩,⟨540354456,8176103273736⟩,⟨24856304976,0⟩⟩,⟨⟨6919468751976,2029858027632⟩,⟨18513013536,118498165956⟩,⟨540354456,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨7008239139330,33194748807882090⟩,⟨901092115156662,119105766780⟩,⟨547054794,8277486088014⟩,⟨25346872122,0⟩⟩,⟨⟨6903053639196,2021281474212⟩,⟨18568377828,119104454898⟩,⟨547054794,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 15131 139 (4728-R)⟩
def p883:CachedProfile:=⟨⟨616,4,146⟩,⟨⟨⟨355480104,70685593272⟩,⟨1357193376,4379424⟩,⟨14112,8749440⟩,⟨18816,0⟩⟩,⟨⟨352164372,79838640⟩,⟨515088,4378248⟩,⟨14112,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 12=>⟨⟨⟨324190080,64807973640⟩,⟨1557905400,5027400⟩,⟨20250,12555000⟩,⟨33750,0⟩⟩,⟨⟨321598620,67294800⟩,⟨542700,5026050⟩,⟨20250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 620 5 (146-R)⟩
def p884:CachedProfile:=⟨⟨8297,63,1705⟩,⟨⟨⟨740306783590,2002300869693850⟩,⟨45071765572680,10783052784⟩,⟨40626684,339639078240⟩,⟨853160364,0⟩⟩,⟨⟨735318874620,145901896800⟩,⟨1099499940,10782837828⟩,⟨40626684,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨733829311764,1985662057250772⟩,⟨45411427408896,10864318464⟩,⟨41582592,347630469120⟩,⟨887095296,0⟩⟩,⟨⟨728962779672,143516387520⟩,⟨1098690048,10864101888⟩,⟨41582592,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8360 64 (1705-R)⟩
def p885:CachedProfile:=⟨⟨5435,38,1225⟩,⟨⟨⟨229595144658,404325281776134⟩,⟨8373590803512,3060086192⟩,⟨10622064,58134556272⟩,⟨134546144,0⟩⟩,⟨⟨227741958612,49317750300⟩,⟨342421800,3059993016⟩,⟨10622064,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨226766636220,399631557939612⟩,⟨8495804072808,3104751312⟩,⟨11060712,60535276776⟩,⟨143789256,0⟩⟩,⟨⟨224975946216,48197383416⟩,⟨343449288,3104656776⟩,⟨11060712,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5473 39 (1225-R)⟩
def p886:CachedProfile:=⟨⟨3835,28,860⟩,⟨⟨⟨80303091918,99849511725894⟩,⟨2158797484872,1117743312⟩,⟨4050144,15645706272⟩,⟨37801344,0⟩⟩,⟨⟨79659644232,17162381880⟩,⟨124397280,1117695096⟩,⟨4050144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨78896178130,98199508196482⟩,⟨2199537213258,1138838932⟩,⟨4273962,16510315206⟩,⟨41314966,0⟩⟩,⟨⟨78283422756,16608474036⟩,⟨124681788,1138789806⟩,⟨4273962,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3863 29 (860-R)⟩
def p887:CachedProfile:=⟨⟨50324,354,10688⟩,⟨⟨⟨170822529708936,2795557815189293616⟩,⟨58308804675722160,2301159730464⟩,⟨8037016344,407299914281232⟩,⟨948367928592,0⟩⟩,⟨⟨169600406100636,34737954322176⟩,⟨242654323968,2301152162652⟩,⟨8037016344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨170582830532800,2791845071482024600⟩,⟨58396932035358000,2304637706000⟩,⟨8071901250,409067811547500⟩,⟨955174981250,0⟩⟩,⟨⟨169365500161200,34647013056600⟩,⟨242702743500,2304630126750⟩,⟨8071901250,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 50678 355 (10688-R)⟩
def p888:CachedProfile:=⟨⟨3030,20,647⟩,⟨⟨⟨37541062872,36961771104504⟩,⟨723463021440,474439680⟩,⟨1555200,4743360000⟩,⟨10368000,0⟩⟩,⟨⟨37265851440,7672384800⟩,⟨50310720,474413760⟩,⟨1555200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨36611317272,36094177267344⟩,⟨742049609112,486630144⟩,⟨1674918,5108499900⟩,⟨11724426,0⟩⟩,⟨⟨36354620580,7321024800⟩,⟨50407056,486603558⟩,⟨1674918,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3050 21 (647-R)⟩
def p889:CachedProfile:=⟨⟨3384,22,951⟩,⟨⟨⟨70596674792,76087504681160⟩,⟨1458046468032,856190720⟩,⟨2764608,9416254848⟩,⟨20273792,0⟩⟩,⟨⟨69729200016,18501773472⟩,⟨119506464,856148832⟩,⟨2764608,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨69351695192,74850536736560⟩,⟨1500299760648,881004880⟩,⟨2974038,10129573428⟩,⟨22800958,0⟩⟩,⟨⟨68524410396,17923025952⟩,⟨121030416,880961778⟩,⟨2974038,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3406 23 (951-R)⟩
def p890:CachedProfile:=⟨⟨1270,8,298⟩,⟨⟨⟨3066108656,1257506579576⟩,⟨23449445760,36702848⟩,⟨114816,146734848⟩,⟨306176,0⟩⟩,⟨⟨3038792016,683234136⟩,⟨4276896,36698064⟩,⟨114816,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨2899906676,1193276886836⟩,⟨25056723600,39219264⟩,⟨138024,176394672⟩,⟨414072,0⟩⟩,⟨⟨2876435496,616292496⟩,⟨4340088,39214152⟩,⟨138024,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1278 9 (298-R)⟩
def p891:CachedProfile:=⟨⟨3475,22,720⟩,⟨⟨⟨54792733870,61957801889746⟩,⟨1163996292228,665759864⟩,⟨2093784,7321962648⟩,⟨15354416,0⟩⟩,⟨⟨54413924796,10892175840⟩,⟨68523840,665728140⟩,⟨2093784,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨53577326890,60652231390846⟩,⟨1191585262332,681541336⟩,⟨2240844,7836231468⟩,⟨17179804,0⟩⟩,⟨⟨53221489476,10443370860⟩,⟨68686740,681508860⟩,⟨2240844,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3497 23 (720-R)⟩
def p892:CachedProfile:=⟨⟨24656,184,5363⟩,⟨⟨⟨20630866023324,165263122330195068⟩,⟨3654000269341056,294205701888⟩,⟨1089621504,27066198159360⟩,⟨66830118912,0⟩⟩,⟨⟨20476321410888,4287453353280⟩,⟨31758913728,294203727936⟩,⟨1089621504,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20589535524134,164950398466569818⟩,⟨3667009744379640,295253183120⟩,⟨1099443900,27310186476000⟩,⟨67799040500,0⟩⟩,⟨⟨20435852760828,4271480736480⟩,⟨31812557820,295251202140⟩,⟨1099443900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5363-R)⟩
def p893:CachedProfile:=⟨⟨24640,172,5237⟩,⟨⟨⟨20067573542202,160782916084627806⟩,⟨3327944884113888,268255495872⟩,⟨929765952,23069352801024⟩,⟨53306581248,0⟩⟩,⟨⟨19923655338468,4083768274032⟩,⟨28309210992,268253694000⟩,⟨929765952,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20026526629252,160471652422277956⟩,⟨3340902888757872,269300009888⟩,⟨938812872,23293824980064⟩,⟨54138208952,0⟩⟩,⟨⟨19883430241368,4068188819232⟩,⟨28365172728,269298201000⟩,⟨938812872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24812 173 (5237-R)⟩
def p894:CachedProfile:=⟨⟨25947,131,5079⟩,⟨⟨⟨21384628254280,180857786940481960⟩,⟨2715446853636960,208257973120⟩,⟨523067280,13640548527840⟩,⟨22840604560,0⟩⟩,⟨⟨21253318397520,4037080937760⟩,⟨20279837520,208256642160⟩,⟨523067280,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21339959909970,180497835920828790⟩,⟨2730789203107680,209434642560⟩,⟨530038080,13822333050240⟩,⟨23321675520,0⟩⟩,⟨⟨21209423040780,4021201000440⟩,⟨20354265360,209433304080⟩,⟨530038080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26078 132 (5079-R)⟩
def p895:CachedProfile:=⟨⟨24646,162,5079⟩,⟨⟨⟨19414799935880,155793676475254760⟩,⟨3038929687350720,244998483840⟩,⟨799917120,19844343912960⟩,⟨43195524480,0⟩⟩,⟨⟨19283502982320,3840474879360⟩,⟨25078883040,244996837920⟩,⟨799917120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19374009206370,155483065028397990⟩,⟨3051669341536920,246025562640⟩,⟨808228980,20050544535840⟩,⟨43913774580,0⟩⟩,⟨⟨19243485214980,3825368295840⟩,⟨25134433740,246023909820⟩,⟨808228980,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24808 163 (5079-R)⟩
def p896:CachedProfile:=⟨⟨24836,139,5079⟩,⟨⟨⟨19668210158040,158947535815692120⟩,⟨2642699784551760,211629812960⟩,⟨588904080,14707879398000⟩,⟨27285889040,0⟩⟩,⟨⟨19536911507760,3866327802000⟩,⟨21518300880,211628400720⟩,⟨588904080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19626920589510,158630715882704130⟩,⟨2656472337464400,212732738400⟩,⟨596232000,14890894200000⟩,⟨27824160000,0⟩⟩,⟨⟨19496394904740,3851119525500⟩,⟨21587857200,212731318800⟩,⟨596232000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24975 140 (5079-R)⟩
def p897:CachedProfile:=⟨⟨24756,182,5111⟩,⟨⟨⟨19743793347240,159254733098934792⟩,⟨3471713378288064,278430437376⟩,⟨1015979328,25336492481664⟩,⟨61636079232,0⟩⟩,⟨⟨19610001076176,3909395395296⟩,⟨28531155744,278428576608⟩,⟨1015979328,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19702565720050,158939196198202102⟩,⟨3483959998035816,279412621824⟩,⟨1025165268,25565571453384⟩,⟨62535081348,0⟩⟩,⟨⟨19569556187196,3894113887656⟩,⟨28575781596,279410754492⟩,⟨1025165268,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24938 183 (5111-R)⟩
def p898:CachedProfile:=⟨⟨13191,97,2535⟩,⟨⟨⟨2768470461368,11942643060624344⟩,⟨260617721015328,39226868288⟩,⟨143167344,1902407667072⟩,⟨4629077456,0⟩⟩,⟨⟨2752106158032,512552177280⟩,⟨3741538320,39226376304⟩,⟨143167344,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2752294450230,11876031073890282⟩,⟨261850886374896,39412484384⟩,⟨145327728,1931114849664⟩,⟨4747372448,0⟩⟩,⟨⟨2736199003356,506907594336⟩,⟨3738481656,39411990072⟩,⟨145327728,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13288 98 (2535-R)⟩
def p899:CachedProfile:=⟨⟨2042,15,409⟩,⟨⟨⟨10758880930,7169207549110⟩,⟨156163272300,151855800⟩,⟨553500,1138549500⟩,⟨2767500,0⟩⟩,⟨⟨10688608980,2069629980⟩,⟨15092100,151843500⟩,⟨553500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨10369206540,6921580422636⟩,⟨160885194624,156448512⟩,⟨608256,1251182592⟩,⟨3244032,0⟩⟩,⟨⟨10305791496,1930535640⟩,⟨15016320,156435840⟩,⟨608256,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2057 16 (409-R)⟩
def p900:CachedProfile:=⟨⟨12968,96,2712⟩,⟨⟨⟨2878203338416,12153121634204416⟩,⟨266709461621760,40831995648⟩,⟨150018048,1959835779072⟩,⟨4800577536,0⟩⟩,⟨⟨2858178490080,576722507904⟩,⟨4238009856,40831474752⟩,⟨150018048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨2862328646296,12089572036544056⟩,⟨268096993356456,41044427128⟩,⟨152369346,1990553136144⟩,⟨4926608854,0⟩⟩,⟨⟨2842611555228,570784606368⟩,⟨4238066964,41043903522⟩,⟨152369346,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 13064 97 (2712-R)⟩
def p901:CachedProfile:=⟨⟨5321,40,1062⟩,⟨⟨⟨189348105954,328913260872462⟩,⟨7332772568400,2735736800⟩,⟨10204800,54707932800⟩,⟨136064000,0⟩⟩,⟨⟨188137810296,36312390396⟩,⟨270937440,2735651760⟩,⟨10204800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨186699373070,324531400340210⟩,⟨7417095676518,2767199060⟩,⟨10580214,56720527254⟩,⟨144596258,0⟩⟩,⟨⟨185536004796,35361756432⟩,⟨270440592,2767113042⟩,⟨10580214,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5361 41 (1062-R)⟩
def p902:CachedProfile:=⟨⟨2826,19,498⟩,⟨⟨⟨24864135074,23051559471038⟩,⟨460493364606,323757188⟩,⟨1080834,3074972730⟩,⟨6845282,0⟩⟩,⟨⟨24737541768,4241929140⟩,⟨28329228,323738226⟩,⟨1080834,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨24081091364,22353138501188⟩,⟨470157077280,330552640⟩,⟨1161600,3304752000⟩,⟨7744000,0⟩⟩,⟨⟨23965425528,3990488040⟩,⟨28052640,330533280⟩,⟨1161600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2845 20 (498-R)⟩
def p903:CachedProfile:=⟨⟨1136,6,277⟩,⟨⟨⟨2284692682,835045423726⟩,⟨13057617744,22871616⟩,⟨60048,68574816⟩,⟨120096,0⟩⟩,⟨⟨2262727068,527645112⟩,⟨2772216,22868280⟩,⟨60048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨2150778232,789075152776⟩,⟨14411583648,25243792⟩,⟨77322,88301724⟩,⟨180418,0⟩⟩,⟨⟨2132124168,472143912⟩,⟨2894052,25240110⟩,⟨77322,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1142 7 (277-R)⟩
def p904:CachedProfile:=⟨⟨1236,8,249⟩,⟨⟨⟨2401417750,967356222250⟩,⟨18576408000,29872000⟩,⟨96000,119424000⟩,⟨256000,0⟩⟩,⟨⟨2385295500,464634000⟩,⟨2988000,29868000⟩,⟨96000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨2238696486,904736928186⟩,⟨19560553272,31455216⟩,⟨113724,141472656⟩,⟨341172,0⟩⟩,⟨⟨2225410668,406952208⟩,⟨2944188,31451004⟩,⟨113724,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1244 9 (249-R)⟩
def p905:CachedProfile:=⟨⟨25988,196,5087⟩,⟨⟨⟨21589496374176,183355419352720416⟩,⟨4102351354160640,313351277568⟩,⟨1172763648,30707643359232⟩,⟨76620558336,0⟩⟩,⟨⟨21457564854720,4066268788224⟩,⟨30438003456,313349283072⟩,⟨1172763648,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨21544483446746,182991100597188446⟩,⟨4115177663973960,314331003056⟩,⟨1182432612,30960815512608⟩,⟨77646408188,0⟩⟩,⟨⟨21413327354580,4050299166624⟩,⟨30473149092,314329002324⟩,⟨1182432612,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 26184 197 (5087-R)⟩
def p906:CachedProfile:=⟨⟨45207,250,10158⟩,⟨⟨⟨131196799219874,1919165379105094430⟩,⟨31488214135852500,1385413307000⟩,⟨3809625000,173174123625000⟩,⟨317468750000,0⟩⟩,⟨⟨130147619575272,28145643964524⟩,⟨154792683000,1385408227500⟩,⟨3809625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨131057351318334,1917244809695760090⟩,⟨31583047317683130,1389585775308⟩,⟨3836382894,174390457212558⟩,⟨320977368798,0⟩⟩,⟨⟨130011265288452,28090258246584⟩,⟨155106030312,1389580680510⟩,⟨3836382894,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45457 251 (10158-R)⟩
def p907:CachedProfile:=⟨⟨4946,17,1168⟩,⟨⟨⟨180787456206,287753960225046⟩,⟨2937273716790,1183715372⟩,⟨2027046,10060229298⟩,⟨11486594,0⟩⟩,⟨⟨179181074856,40658642976⟩,⟨139269984,1183675626⟩,⟨2027046,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨179106127586,285244701419786⟩,⟨3083447618820,1242624168⟩,⟨2253096,11182115448⟩,⟨13518576,0⟩⟩,⟨⟨177540446076,39965708916⟩,⟨144949176,1242582444⟩,⟨2253096,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 4963 18 (1168-R)⟩
def p908:CachedProfile:=⟨⟨24434,175,5237⟩,⟨⟨⟨19752264788526,156887213973896466⟩,⟨3330812891164500,270701411400⟩,⟨962482500,23685731842500⟩,⟨56144812500,0⟩⟩,⟨⟨19608348711420,4050356821524⟩,⟨28802976300,270699578100⟩,⟨962482500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨19699689414350,156492246389601650⟩,⟨3341532104090400,271572593600⟩,⟨971097600,23897740838400⟩,⟨56971059200,0⟩⟩,⟨⟨19556841080700,4030274991600⟩,⟨28823942400,271570754400⟩,⟨971097600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24609 176 (5237-R)⟩
def p909:CachedProfile:=⟨⟨24656,184,5361⟩,⟨⟨⟨20622598637214,165200574795430482⟩,⟨3652637829454656,294096005504⟩,⟨1089215232,27056106362880⟩,⟨66805200896,0⟩⟩,⟨⟨20468226651852,4284256445280⟩,⟨31735232928,294094032288⟩,⟨1089215232,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20581271352504,164887857831761112⟩,⟨3665639900017440,295142890560⟩,⟨1099033200,27299984688000⟩,⟨67773714000,0⟩⟩,⟨⟨20427760573392,4268289790080⟩,⟨31788792720,295140910320⟩,⟨1099033200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5361-R)⟩
def p910:CachedProfile:=⟨⟨24656,184,5367⟩,⟨⟨⟨20647402726632,165388221549989064⟩,⟨3656725149166848,294425094656⟩,⟨1090434048,27086381752320⟩,⟨66879954944,0⟩⟩,⟨⟨20492512473840,4293850746240⟩,⟨31806301824,294423119232⟩,⟨1090434048,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20606065794882,165075483871018374⟩,⟨3669749433157320,295473768240⟩,⟨1100265300,27330590052000⟩,⟨67849693500,0⟩⟩,⟨⟨20452038677700,4277866206240⟩,⟨31860114660,295471785780⟩,⟨1100265300,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5367-R)⟩
def p911:CachedProfile:=⟨⟨24562,174,5237⟩,⟨⟨⟨19949223572154,159316928287451262⟩,⟨3346049577000240,270543538080⟩,⟨951514128,23536653470208⟩,⟨55187819424,0⟩⟩,⟨⟨19805306164596,4071259552896⟩,⟨28638387864,270541715256⟩,⟨951514128,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19908402604164,159008463427643652⟩,⟨3358854895410000,271578916000⟩,⟨960645000,23762514720000⟩,⟨56037625000,0⟩⟩,⟨⟨19765307010936,4055727818496⟩,⟨28693093800,271577086200⟩,⟨960645000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24736 175 (5237-R)⟩
def p912:CachedProfile:=⟨⟨42268,250,10475⟩,⟨⟨⟨119381051103588,1622534697620872164⟩,⟨28407789219636000,1336276656000⟩,⟨3928500000,167031963000000⟩,⟨327375000000,0⟩⟩,⟨⟨118230674618952,27994556998800⟩,⟨164604150000,1336271418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨119256136280638,1620951414168205714⟩,⟨28494194574092184,1340341100384⟩,⟨3956210796,168210170624328⟩,⟨331002969932,0⟩⟩,⟨⟨118109049483012,27941134832520⟩,⟨164947195140,1340335846452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42518 251 (10475-R)⟩
def p913:CachedProfile:=⟨⟨75039,665,19155⟩,⟨⟨⟨693864566388028,16757273506316849308⟩,⟨438044549930959440,11572584785440⟩,⟨50827572600,3847850556110400⟩,⟨11266778593000,0⟩⟩,⟨⟨686833060953480,166669856752320⟩,⟨1464063388200,11572559307960⟩,⟨50827572600,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨693465683537478,16748314900666082298⟩,⟨438474245898046896,11583936851616⟩,⟨50953939056,3857417002295424⟩,⟨11311774470432,0⟩⟩,⟨⟨686445181675260,166495884418080⟩,⟨1464734479320,11583911349144⟩,⟨50953939056,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 75704 666 (19155-R)⟩
def p914:CachedProfile:=⟨⟨872,6,249⟩,⟨⟨⟨1235707750,342933504250⟩,⟨6942438000,15816000⟩,⟨54000,47412000⟩,⟨108000,0⟩⟩,⟨⟨1219768500,327933000⟩,⟨2241000,15813000⟩,⟨54000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨1174929736,327349013416⟩,⟨7742911680,17640112⟩,⟨70266,61693548⟩,⟨163954,0⟩⟩,⟨⟨1160972136,299654376⟩,⟨2389044,17636766⟩,⟨70266,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 878 7 (249-R)⟩
def p915:CachedProfile:=⟨⟨2255,18,735⟩,⟨⟨⟨24817885408,17593457394784⟩,⟨410793904512,361458432⟩,⟨1430784,3252172032⟩,⟨8584704,0⟩⟩,⟨⟨24416933952,7377612480⟩,⟨58423680,361431936⟩,⟨1430784,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨24427673358,17342611086834⟩,⟨427722613956,376355496⟩,⟨1572516,3574328868⟩,⟨9959268,0⟩⟩,⟨⟨24042769212,7178361300⟩,⟨60003900,376327908⟩,⟨1572516,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 2273 19 (735-R)⟩
def p916:CachedProfile:=⟨⟨3555,30,1250⟩,⟨⟨⟨106281244530,117790848915750⟩,⟨2894626975500,1614840840⟩,⟨6755400,24218109000⟩,⟨67554000,0⟩⟩,⟨⟨104317587360,33636262500⟩,⟨281475000,1614765780⟩,⟨6755400,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨105277144910,116791033764050⟩,⟨2967200136330,1655330188⟩,⟨7155606,25652847510⟩,⟨73941262,0⟩⟩,⟨⟨103360085340,33100448400⟩,⟨286224240,1655253246⟩,⟨7155606,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3585 31 (1250-R)⟩
def p917:CachedProfile:=⟨⟨3231,25,895⟩,⟨⟨⟨60607392384,62531023965312⟩,⟨1425087014400,875392000⟩,⟨3360000,10940160000⟩,⟨28000000,0⟩⟩,⟨⟨59883839232,15666309120⟩,⟨120288000,875347200⟩,⟨3360000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 11=>⟨⟨⟨59776716120,61739856027840⟩,⟨1463892150240,899230800⟩,⟨3589560,11687607360⟩,⟨31109520,0⟩⟩,⟨⟨59079364440,15283794240⟩,⟨122045040,899184780⟩,⟨3589560,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3256 26 (895-R)⟩
def p918:CachedProfile:=⟨⟨10382,77,2211⟩,⟨⟨⟨1506095024420,5086096466608724⟩,⟨111795669140232,21378387184⟩,⟨78689688,823015446792⟩,⟨2019701992,0⟩⟩,⟨⟨1495235345352,306912995928⟩,⟨2259518184,21378046536⟩,⟨78689688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 13=>⟨⟨⟨1496613394626,5055784930776666⟩,⟨112581974383164,21528755352⟩,⟨80272296,839567943864⟩,⟨2087079696,0⟩⟩,⟨⟨1485943578348,303315309108⟩,⟨2262032136,21528412308⟩,⟨80272296,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10459 78 (2211-R)⟩
def p919:CachedProfile:=⟨⟨4971,38,992⟩,⟨⟨⟨154414341966,250621532331426⟩,⟨5680943884260,2268417144⟩,⟨8603352,43094190168⟩,⟨108975792,0⟩⟩,⟨⟨153427218540,29604873024⟩,⟨224592768,2268341676⟩,⟨8603352,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨152102270386,247047378606886⟩,⟨5748234388182,2295288996⟩,⟨8934354,44752179186⟩,⟨116146602,0⟩⟩,⟨⟨151156064928,28775562948⟩,⟨224046108,2295212634⟩,⟨8934354,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 5009 39 (992-R)⟩
def p920:CachedProfile:=⟨⟨8880,71,1634⟩,⟨⟨⟨807930446370,2352525698152890⟩,⟨55806936695190,12469850700⟩,⟨49452210,442646731710⟩,⟨1170368970,0⟩⟩,⟨⟨803535798540,143480412540⟩,⟨1138097340,12469618530⟩,⟨49452210,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨800643110734,2332199086664182⟩,⟨56108342330352,12537203040⟩,⟨50419584,451305696384⟩,⟨1210070016,0⟩⟩,⟨⟨796359939192,141033030120⟩,⟨1134440640,12536969616⟩,⟨50419584,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8951 72 (1634-R)⟩
def p921:CachedProfile:=⟨⟨10542,79,2015⟩,⟨⟨⟨1405603521504,4847785680078432⟩,⟨107799116652864,20299789440⟩,⟨75491136,801791355456⟩,⟨1987933248,0⟩⟩,⟨⟨1397375284032,258870306240⟩,⟨1925501760,20299470912⟩,⟨75491136,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨1395279527642,4813777896077150⟩,⟨108405554537280,20413993600⟩,⟨76876800,816508492800⟩,⟨2050048000,0⟩⟩,⟨⟨1387220991156,255286483452⟩,⟨1922880960,20413673280⟩,⟨76876800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 10621 80 (2015-R)⟩
def p922:CachedProfile:=⟨⟨8909,66,1693⟩,⟨⟨⟨843121046614,2457856132805458⟩,⟨54037563875064,12042185232⟩,⟨44274384,397362596400⟩,⟨974036448,0⟩⟩,⟨⟨838235213508,154438676700⟩,⟨1135705032,12041961624⟩,⟨44274384,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨835756509840,2437340164373520⟩,⟨54402937958880,12123612480⟩,⟨45249120,406110852000⟩,⟨1010563680,0⟩⟩,⟨⟨830990364960,151895772000⟩,⟨1133929440,12123387360⟩,⟨45249120,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 8975 67 (1693-R)⟩
def p923:CachedProfile:=⟨⟨24179,182,4651⟩,⟨⟨⟨17068714238892,134984504272220940⟩,⟨3014806029358032,247513753760⟩,⟨924557088,22523135220768⟩,⟨56089796672,0⟩⟩,⟨⟨16967856445896,3162513643032⟩,⟨23627005584,247512060432⟩,⟨924557088,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 14=>⟨⟨⟨17014331083254,134574053937015162⟩,⟨3022247970759780,248124744360⟩,⟨931931892,22702792821012⟩,⟨56847845412,0⟩⟩,⟨⟨16914379905996,3143505339396⟩,⟨23614033788,248123046852⟩,⟨931931892,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24361 183 (4651-R)⟩
def p924:CachedProfile:=⟨⟨11043,79,2272⟩,⟨⟨⟨1745883899112,6281638327863696⟩,⟨133278320734056,23967166624⟩,⟨85114758,946646338476⟩,⟨2241355294,0⟩⟩,⟨⟨1734100148868,344621131392⟩,⟨2447857344,23966807490⟩,⟨85114758,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨1733595394062,6239658914988546⟩,⟨134074690888320,24110382080⟩,⟨86707200,964357478400⟩,⟨2312192000,0⟩⟩,⟨⟨1722042804468,340086691992⟩,⟨2446226880,24110020800⟩,⟨86707200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 11122 80 (2272-R)⟩
def p925:CachedProfile:=⟨⟨14781,106,3195⟩,⟨⟨⟨4413363511100,21195174414388556⟩,⟨450495839816304,60523009952⟩,⟨215461536,3207575886432⟩,⟨7612974272,0⟩⟩,⟨⟨4380643505496,912086592840⟩,⟨6494335920,60522332400⟩,⟨215461536,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨4391128966670,21094234786164806⟩,⟨452611450502058,60807245284⟩,⟨218515614,3253041945618⟩,⟨7793723566,0⟩⟩,⟨⟨4358866711176,903543836760⟩,⟨6494202360,60806564550⟩,⟨218515614,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 14887 107 (3195-R)⟩
def p926:CachedProfile:=⟨⟨1585,10,327⟩,⟨⟨⟨5186404552,2675385894664⟩,⟨50079282720,62805440⟩,⟨196800,313896000⟩,⟨656000,0⟩⟩,⟨⟨5150285520,1026439920⟩,⟨6435360,62798880⟩,⟨196800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 15=>⟨⟨⟨4934211502,2551508003254⟩,⟨52567359042,65926564⟩,⟨227238,362444610⟩,⟨833206,0⟩⟩,⟨⟨4902744360,934567920⟩,⟨6445296,65919678⟩,⟨227238,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 1595 11 (327-R)⟩
def p927:CachedProfile:=⟨⟨3384,18,728⟩,⟨⟨⟨52575637464,57709353033360⟩,⟨911327623920,535797504⟩,⟨1417176,4821232752⟩,⟨8503056,0⟩⟩,⟨⟨52184319012,10832893344⟩,⟨57316896,535771260⟩,⟨1417176,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 16=>⟨⟨⟨51339553592,56424547264016⟩,⟨940841425896,553151104⟩,⟨1544358,5253905916⟩,⟨9780934,0⟩⟩,⟨⟨50973251268,10362274272⟩,⟨57872784,553124010⟩,⟨1544358,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 3402 19 (728-R)⟩
def p928:CachedProfile:=⟨⟨45268,250,10222⟩,⟨⟨⟨132430387412296,1939201875377500072⟩,⟨31771685002896000,1396011988000⟩,⟨3833625000,174498942750000⟩,⟨319468750000,0⟩⟩,⟨⟨131361262800936,28539651084648⟩,⟨156749259000,1396006876500⟩,⟨3833625000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨132290410976416,1937272935446261392⟩,⟨31867568489245944,1400225013712⟩,⟨3860575278,175725665504004⟩,⟨323001464926,0⟩⟩,⟨⟨131224419092676,28483841464848⟩,⟨157068504936,1400219886786⟩,⟨3860575278,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 45518 251 (10222-R)⟩
def p929:CachedProfile:=⟨⟨24592,152,5111⟩,⟨⟨⟨19448159230440,155582828606282184⟩,⟨2854517751505152,230726398464⟩,⟨708645888,17534733852672⟩,⟨35904724992,0⟩⟩,⟨⟨19314368942832,3878983064448⟩,⟨23828217984,230724844416⟩,⟨708645888,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19407509917250,155274474736085894⟩,⟨2867676688423368,231790023216⟩,⟨716596308,17731459045152⟩,⟨36546411708,0⟩⟩,⟨⟨19274502363972,3863820436128⟩,⟨23891227236,231788462004⟩,⟨716596308,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24744 153 (5111-R)⟩
def p930:CachedProfile:=⟨⟨24883,147,5237⟩,⟨⟨⟨20409065371242,165038060086821774⟩,⟨2894429920924584,231279154848⟩,⟨679127652,16998565129560⟩,⟨33277254948,0⟩⟩,⟨⟨20265144883740,4119648553080⟩,⟨24194500092,231277614876⟩,⟨679127652,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20367366507492,164718672683274084⟩,⟨2908556406536256,232407937792⟩,⟨687084672,17197729340160⟩,⟨33896177152,0⟩⟩,⟨⟨20224267840200,4103932216080⟩,⟨24266159328,232406390304⟩,⟨687084672,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25030 148 (5237-R)⟩
def p931:CachedProfile:=⟨⟨24914,145,5237⟩,⟨⟨⟨20454718302126,165609731893349466⟩,⟨2861669420772300,228396809160⟩,⟨660773700,16558328148300⟩,⟨31937395500,0⟩⟩,⟨⟨20310797510820,4124421617724⟩,⟨23865323220,228395290140⟩,⟨660773700,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20412932281196,165289253078315996⟩,⟨2875904016109680,229532914208⟩,⟨668640288,16755456976992⟩,⟨32540494016,0⟩⟩,⟨⟨20269833310680,4108687071624⟩,⟨23938238256,229531387632⟩,⟨668640288,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25059 146 (5237-R)⟩
def p932:CachedProfile:=⟨⟨29723,174,5971⟩,⟨⟨⟨33093831890644,320461895851621972⟩,⟨5572900934013168,372810030816⟩,⟨1084849632,32433749447904⟩,⟨62921278656,0⟩⟩,⟨⟨32880556034424,6396549014184⟩,⟨37227799728,372807952560⟩,⟨1084849632,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨33034859852434,319918900941459622⟩,⟨5595543628313100,374324766200⟩,⟨1095517500,32752686697500⟩,⟨63905187500,0⟩⟩,⟨⟨32822652508404,6375143360124⟩,⟨37316456100,374322679500⟩,⟨1095517500,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 29897 175 (5971-R)⟩
def p933:CachedProfile:=⟨⟨24656,184,5357⟩,⟨⟨⟨20606065794882,165075483871018374⟩,⟨3649912949734848,293876612736⟩,⟨1088402688,27035922769920⟩,⟨66755364864,0⟩⟩,⟨⟨20452038677700,4277866206240⟩,⟨31687897824,293874640992⟩,⟨1088402688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20564744935532,164762780691836684⟩,⟨3662900211346320,294922305440⟩,⟨1098211800,27279581112000⟩,⟨67723061000,0⟩⟩,⟨⟨20411577739560,4261911474240⟩,⟨31741289160,294920326680⟩,⟨1098211800,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24840 185 (5357-R)⟩
def p934:CachedProfile:=⟨⟨24439,179,5079⟩,⟨⟨⟨19128556363080,152256726931032360⟩,⟨3306593498905440,268634951680⟩,⟨976609680,24042177102240⟩,⟨58271044240,0⟩⟩,⟨⟨18997261339920,3811061374560⟩,⟨27710617680,268633133040⟩,⟨976609680,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19088329105170,151953078098874390⟩,⟨3318520573087200,269603942400⟩,⟨985608000,24263697744000⟩,⟨59136480000,0⟩⟩,⟨⟨18957807040380,3796070489640⟩,⟨27755816400,269602117200⟩,⟨985608000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24618 180 (5079-R)⟩
def p935:CachedProfile:=⟨⟨24714,170,5237⟩,⟨⟨⟨20180029463226,162180055641399966⟩,⟨3308364844246800,265905603360⟩,⟨908269200,22601370772800⟩,⟨51468588000,0⟩⟩,⟨⟨20036110505220,4095618641424⟩,⟨27980034120,265903822440⟩,⟨908269200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20138767857796,161866124618956996⟩,⟨3321472469118480,266959120608⟩,⟨917231688,22824393324192⟩,⟨52282206216,0⟩⟩,⟨⟨19995670717080,4079993977824⟩,⟨28037251656,266957332632⟩,⟨917231688,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24884 171 (5237-R)⟩
def p936:CachedProfile:=⟨⟨24784,168,5237⟩,⟨⟨⟨20286537027642,163507021092411966⟩,⟨3287335697013312,263495369088⟩,⟨887023872,22133019654144⟩,⟨49673336832,0⟩⟩,⟨⟨20142617357268,4106810655072⟩,⟨27650857248,263493609120⟩,⟨887023872,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20245072085892,163190556683568516⟩,⟨3300589771807536,264557753824⟩,⟨895901448,22354532930496⟩,⟨50469114904,0⟩⟩,⟨⟨20101974234168,4091143294272⟩,⟨27709330584,264555986760⟩,⟨895901448,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24952 169 (5237-R)⟩
def p937:CachedProfile:=⟨⟨24850,166,5143⟩,⟨⟨⟨19996087019080,161766541615774120⟩,⟨3206292750335808,256341980800⟩,⟨850488384,21275817414144⟩,⟨47060357248,0⟩⟩,⟨⟨19859768544816,3970878536832⟩,⟨26349769632,256340272992⟩,⟨850488384,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19954576425250,161447984052327910⟩,⟨3219337042387896,257384875600⟩,⟨859092756,21491064384096⟩,⟨47822830084,0⟩⟩,⟨⟨19819050525636,3955453170912⟩,⟨26405527644,257383160844⟩,⟨859092756,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25016 167 (5143-R)⟩
def p938:CachedProfile:=⟨⟨24912,164,5143⟩,⟨⟨⟨20088851857480,162928224369845800⟩,⟨3182875745761152,253860926720⟩,⟨830118144,20816042578944⟩,⟨45379791872,0⟩⟩,⟨⟨19952532765936,3980402549952⟩,⟨26032302528,253859239488⟩,⟨830118144,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20047160927650,162607408443707590⟩,⟨3196058144031720,254912341200⟩,⟨838638900,21029709056400⟩,⟨46125139500,0⟩⟩,⟨⟨19911634411956,3964940186832⟩,⟨26089293780,254910646980⟩,⟨838638900,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 25076 165 (5143-R)⟩
def p939:CachedProfile:=⟨⟨24609,175,5396⟩,⟨⟨⟨20677380812760,165178948853292864⟩,⟨3480904819198800,280901976600⟩,⟨991698750,24578261820000⟩,⟨57849093750,0⟩⟩,⟨⟨20519969838312,4330589413248⟩,⟨30578322600,280900087650⟩,⟨991698750,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20636163842520,164868179004405624⟩,⟨3494309031455616,281983678592⟩,⟨1001206272,24813896245248⟩,⟨58737434624,0⟩⟩,⟨⟨20479625358252,4314554660928⟩,⟨30639187392,281981782368⟩,⟨1001206272,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24784 176 (5396-R)⟩
def p940:CachedProfile:=⟨⟨24544,160,5396⟩,⟨⟨⟨20549175725400,163592808907397184⟩,⟨3162029287656960,255995685120⟩,⟨828979200,20479102156800⟩,⟨44212224000,0⟩⟩,⟨⟨20391765614472,4316610751488⟩,⟨27957323520,255993958080⟩,⟨828979200,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨20508196303960,163284978039159544⟩,⟨3175896384006696,257118363992⟩,⟨837818562,20697469755648⟩,⟨44962929494,0⟩⟩,⟨⟨20351658681612,4300627757568⟩,⟨28027893012,257116629378⟩,⟨837818562,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24704 161 (5396-R)⟩
def p941:CachedProfile:=⟨⟨42018,250,10792⟩,⟨⟨⟨121984633720656,1643698767054162432⟩,⟨28924248252816000,1368617158000⟩,⟨4047375000,171074446500000⟩,⟨337281250000,0⟩⟩,⟨⟨120726690143256,29539766826048⟩,⟨174717084000,1368611761500⟩,⟨4047375000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨121859979892976,1642138140878749352⟩,⟨29013038643598824,1372818494392⟩,⟨4076038698,172286003687064⟩,⟨341028571066,0⟩⟩,⟨⟨120605528157996,29485050900048⟩,⟨175091032836,1372813081326⟩,⟨4076038698,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 42268 251 (10792-R)⟩
def p942:CachedProfile:=⟨⟨41268,250,10475⟩,⟨⟨⟨114098800479588,1511555100150328164⟩,⟨27087247515636000,1304848656000⟩,⟨3928500000,163103463000000⟩,⟨327375000000,0⟩⟩,⟨⟨112948444946952,27336140398800⟩,⟨164604150000,1304843418000⟩,⟨3928500000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨113978927896638,1510077754950021714⟩,⟨27169636285436184,1308817508384⟩,⟨3956210796,164253959828328⟩,⟨331002969932,0⟩⟩,⟨⟨112831862031012,27283974692520⟩,⟨164947195140,1308812254452⟩,⟨3956210796,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 41518 251 (10475-R)⟩
def p943:CachedProfile:=⟨⟨24837,139,5079⟩,⟨⟨⟨19669732705160,158966548805606120⟩,⟨2642911412952480,211638286400⟩,⟨588904080,14708468302080⟩,⟨27285889040,0⟩⟩,⟨⟨19538434044720,3866482609920⟩,⟨21518300880,211636874160⟩,⟨588904080,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19628440139490,158649691444864230⟩,⟨2656685068783200,212741256000⟩,⟨596232000,14891490432000⟩,⟨27824160000,0⟩⟩,⟨⟨19497914444580,3851273724480⟩,⟨21587857200,212739836400⟩,⟨596232000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24976 140 (5079-R)⟩
def p944:CachedProfile:=⟨⟨24761,140,5079⟩,⟨⟨⟨19555710835160,157544795316632120⟩,⟨2645962529044800,212520784000⟩,⟨597408000,14876056608000⟩,⟨27879040000,0⟩⟩,⟨⟨19424412936720,3854872015920⟩,⟨21673108800,212519361600⟩,⟨597408000,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩,fun R=>match R with
 | 10=>⟨⟨⟨19514642721990,157230736728860730⟩,⟨2659616383757580,213617453400⟩,⟨604780020,15059627278020⟩,⟨28424660940,0⟩⟩,⟨⟨19384117787580,3839708800980⟩,⟨21742056180,213616023660⟩,⟨604780020,0⟩,⟨0,0⟩⟩,by rfl,by rfl⟩
 | R=>parts 24901 141 (5079-R)⟩
end ProximityPrize.SubmissionLower.Z0
end
