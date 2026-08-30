import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactInterpolation
namespace ProximityPrize.SubmissionLower.ContactStackedParameters6656Research
open ContactInterpolation ContactRankKernel
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def agreements:ℕ:=182807
def errors:ℕ:=n-agreements
def gap:ℕ:=agreements-w
structure Profile where
  multiplicity:ℕ
  seedCap:ℕ
  slopeCap:ℕ
  deriving DecidableEq
def profileA:Profile:=⟨25,5263,7⟩
def profileB:Profile:=⟨47,598,14⟩
def profileC:Profile:=⟨27,579299,6⟩
namespace Profile
def weightedCap (P:Profile):ℕ:=P.multiplicity*agreements
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
          (L+1-i)*(D-w*i-(w-1)*j):=by
  have hsplit:L+1=t+(L+1-t):=by omega
  unfold coefficientCount
  rw [hsplit,Finset.sum_range_add]
  have htail:
      (∑ x∈Finset.range (L+1-t),
        ∑ j∈Finset.range (s+1),
          (t+(L+1-t)-(t+x))*
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
    errors=79337∧gap=51736:=by
  norm_num [errors,gap,n,agreements,w]
theorem profileA_coefficients_exact:
    profileA.coefficients=2811431653128:=by
  change coefficientCount (25*182807) 131071 5263 7=2811431653128
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (25*182807) 131071 5263 7 35 (by norm_num) (by norm_num)]
  decide
theorem profileA_localRank_exact:profileA.localRank=10724760:=by
  change localRankBound 25 5263 7=10724760
  decide
theorem profileA_values:
    profileA.weightedCap=4570175∧profileA.yCap=34∧
      profileA.localRank=10724760∧
      profileA.coefficients=2811431653128∧
      profileA.nullity=167688:=by
  refine ⟨by norm_num [Profile.weightedCap,profileA,agreements],
    by norm_num [Profile.yCap,Profile.weightedCap,profileA,agreements,w],
    profileA_localRank_exact,profileA_coefficients_exact,?_⟩
  rw [Profile.nullity,Profile.totalRank,profileA_coefficients_exact,
    profileA_localRank_exact]
  norm_num [n]
theorem profileB_coefficients_exact:
    profileB.coefficients=1997482954410:=by
  change coefficientCount (47*182807) 131071 598 14=1997482954410
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (47*182807) 131071 598 14 66 (by norm_num) (by norm_num)]
  decide
theorem profileB_localRank_exact:profileB.localRank=7619680:=by
  change localRankBound 47 598 14=7619680
  decide
theorem profileB_values:
    profileB.weightedCap=8591929∧profileB.yCap=65∧
      profileB.localRank=7619680∧
      profileB.coefficients=1997482954410∧
      profileB.nullity=29560490:=by
  refine ⟨by norm_num [Profile.weightedCap,profileB,agreements],
    by norm_num [Profile.yCap,Profile.weightedCap,profileB,agreements,w],
    profileB_localRank_exact,profileB_coefficients_exact,?_⟩
  rw [Profile.nullity,Profile.totalRank,profileB_coefficients_exact,
    profileB_localRank_exact]
  norm_num [n]
theorem profileC_coefficients_exact:
    profileC.coefficients=329531914715570:=by
  change coefficientCount (27*182807) 131071 579299 6=329531914715570
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    (27*182807) 131071 579299 6 38 (by norm_num) (by norm_num)]
  decide
theorem profileC_localRank_exact:profileC.localRank=1257064494:=by
  change localRankBound 27 579299 6=1257064494
  decide
theorem profileC_values:
    profileC.weightedCap=4935789∧profileC.yCap=37∧
      profileC.localRank=1257064494∧
      profileC.coefficients=329531914715570∧
      profileC.nullity=434:=by
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
        min profileA.slopeCap profileB.slopeCap)=(25,598,7)∧
      (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
        min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
        min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap)=
          (25,598,6):=by
  norm_num [profileA,profileB,profileC]
end ProximityPrize.SubmissionLower.ContactStackedParameters6656Research
