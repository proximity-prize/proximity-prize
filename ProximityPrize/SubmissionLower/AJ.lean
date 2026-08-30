import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.C1
namespace ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def agreements:ℕ:=182278
def errors:ℕ:=n-agreements
def gap:ℕ:=agreements-w
structure Profile where
 multiplicity:ℕ
 seedCap:ℕ
 slopeCap:ℕ
 deriving DecidableEq
def profileA:Profile:=⟨34,20000,10⟩
def profileB:Profile:=⟨68,900,21⟩
def profileC:Profile:=⟨37,42000,9⟩
namespace Profile
def weightedCap (P:Profile):ℕ:=P.multiplicity*agreements
def totalCap (P:Profile):ℕ:=P.seedCap
def yCap (P:Profile):ℕ:=(P.weightedCap-1)/w
def characteristicCap (P:Profile):ℕ:=
 (2*P.slopeCap-1)*P.weightedCap
def coefficients (P:Profile):ℕ:=
 coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P:Profile):ℕ:=
 localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P:Profile):ℕ:=n*P.localRank
def nullity (P:Profile):ℕ:=P.coefficients-P.totalRank
end Profile
theorem coefficientCount_eq_sum_range_of_weighted_cutoff
   (D w L s t:ℕ) (ht:t ≤ L+1) (hD:D ≤ w*t):
   coefficientCount D w L s=
     ∑ i∈Finset.range t,
       ∑ j∈Finset.range (s+1),
         (L+1-i-j)*(D-w*i-(w-1)*j):=by
 have hsplit:L+1=t+(L+1-t):=by omega
 unfold coefficientCount
 rw [hsplit,Finset.sum_range_add]
 have htail:
     (∑ x∈Finset.range (L+1-t),
       ∑ j∈Finset.range (s+1),
         (t+(L+1-t)-(t+x)-j)*
           (D-w*(t+x)-(w-1)*j))=0:=by
   apply Finset.sum_eq_zero
   intro i hi
   apply Finset.sum_eq_zero
   intro j hj
   have hti:t ≤ t+i:=by omega
   have hzero:D-w*(t+i)=0:=
     Nat.sub_eq_zero_of_le (hD.trans (Nat.mul_le_mul_left w hti))
   simp [hzero]
 rw [htail,add_zero]
theorem base_values:
   errors=79866∧gap=51207:=by
 norm_num [errors,gap,n,agreements,w]
theorem profileA_coefficients_exact:
   profileA.coefficients=26510739472987:=by
 change coefficientCount (34*182278) 131071 20000 10=26510739472987
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (34*182278) 131071 20000 10 48 (by norm_num) (by norm_num)]
 decide
theorem profileA_localRank_exact:profileA.localRank=101130370:=by
 change localRankBound 34 20000 10=101130370
 decide
theorem profileA_values:
   profileA.weightedCap=6197452∧profileA.yCap=47∧
     profileA.localRank=101130370∧
     profileA.coefficients=26510739472987∧
     profileA.nullity=19759707:=by
 refine ⟨by norm_num [Profile.weightedCap,profileA,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileA,agreements,w],
   profileA_localRank_exact,profileA_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileA_coefficients_exact,
   profileA_localRank_exact]
 norm_num [n]
theorem profileB_coefficients_exact:
   profileB.coefficients=8952917932750:=by
 change coefficientCount (68*182278) 131071 900 21=8952917932750
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (68*182278) 131071 900 21 95 (by norm_num) (by norm_num)]
 decide
theorem profileB_localRank_exact:profileB.localRank=34148169:=by
 change localRankBound 68 900 21=34148169
 decide
theorem profileB_values:
   profileB.weightedCap=12394904∧profileB.yCap=94∧
     profileB.localRank=34148169∧
     profileB.coefficients=8952917932750∧
     profileB.nullity=1180318414:=by
 refine ⟨by norm_num [Profile.weightedCap,profileB,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileB,agreements,w],
   profileB_localRank_exact,profileB_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileB_coefficients_exact,
   profileB_localRank_exact]
 norm_num [n]
theorem profileC_coefficients_exact:
   profileC.coefficients=62185590423245:=by
 change coefficientCount (37*182278) 131071 42000 9=62185590423245
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (37*182278) 131071 42000 9 52 (by norm_num) (by norm_num)]
 decide
theorem profileC_localRank_exact:profileC.localRank=237219085:=by
 change localRankBound 37 42000 9=237219085
 decide
theorem profileC_values:
   profileC.weightedCap=6744286∧profileC.yCap=51∧
     profileC.localRank=237219085∧
     profileC.coefficients=62185590423245∧
     profileC.nullity=30605005:=by
 refine ⟨by norm_num [Profile.weightedCap,profileC,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileC,agreements,w],
   profileC_localRank_exact,profileC_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileC_coefficients_exact,
   profileC_localRank_exact]
 norm_num [n]
theorem interpolation_gates:
     profileA.totalRank < profileA.coefficients∧
     profileB.totalRank < profileB.coefficients∧
     profileC.totalRank < profileC.coefficients:=by
 simp only [Profile.totalRank]
 rw [profileA_coefficients_exact,profileA_localRank_exact,
   profileB_coefficients_exact,profileB_localRank_exact,
   profileC_coefficients_exact,profileC_localRank_exact]
 norm_num [n]
theorem characteristic_gates:
   profileA.characteristicCap < prime∧
     (2*profileA.slopeCap-1)*profileA.seedCap < prime∧
     profileA.slopeCap < prime∧
   profileB.characteristicCap < prime∧
     (2*profileB.slopeCap-1)*profileB.seedCap < prime∧
     profileB.slopeCap < prime∧
   profileC.characteristicCap < prime∧
     (2*profileC.slopeCap-1)*profileC.seedCap < prime∧
     profileC.slopeCap < prime:=by
 norm_num [Profile.characteristicCap,Profile.weightedCap,profileA,profileB,
   profileC,agreements,prime]
theorem meet_caps:
   (min profileA.multiplicity profileB.multiplicity,
       min profileA.seedCap profileB.seedCap,
       min profileA.slopeCap profileB.slopeCap)=(34,900,10)∧
     (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
       min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
       min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap)=
         (34,900,9):=by
 norm_num [profileA,profileB,profileC]
theorem middle_support_gates:
   profileA.weightedCap+profileA.slopeCap ≤ w*(profileA.yCap+1)∧
     profileB.weightedCap+profileB.slopeCap ≤ w*(profileB.yCap+1)∧
     profileC.weightedCap+profileC.slopeCap ≤ w*(profileC.yCap+1):=by
 norm_num [Profile.weightedCap,Profile.yCap,profileA,profileB,profileC,
   agreements,w]
end ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
