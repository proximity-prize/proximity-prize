import ProximityPrize.SubmissionLower.BCHKSParameters6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSSubfieldListBudgetAudit6401
def q6401 : Nat := 2130706433
def extensionDegree6401 : Nat := 6
def squaredInterleaving6401 : Nat := 2 * 8
def packedExtensionDegree6401 : Nat :=
  extensionDegree6401 * squaredInterleaving6401
def n6401 : Nat := 262144
def k6401 : Nat := 131072
def a6401 : Nat := 185354
def r1AgreementThreshold6401 : Nat := 196608
def r2AgreementThreshold6401 : Nat := 174763
def smallestApplicableFrobeniusTerms6401 : Nat := 2
def fullCodeTheoremExponent6401 : Nat :=
  (smallestApplicableFrobeniusTerms6401 - 1) * k6401
def fullCodeTheoremListBound6401 : Nat :=
  q6401 ^ fullCodeTheoremExponent6401
def exactFieldNumerator6401 : Nat := 274980728111395087
def currentConservativeMCANumerator6401 : Nat := 274980700000000000
def illustrativeListReserve6401 : Nat := 10000000000000000
def maxMCAWithIllustrativeListReserve6401 : Nat :=
  exactFieldNumerator6401 - illustrativeListReserve6401
theorem subfield_fullCode_parameters_exact6401 :
    packedExtensionDegree6401 = 96 ∧
      r1AgreementThreshold6401 = 196608 ∧
      a6401 < r1AgreementThreshold6401 ∧
      r2AgreementThreshold6401 = 174763 ∧
      r2AgreementThreshold6401 ≤ a6401 ∧
      smallestApplicableFrobeniusTerms6401 = 2 ∧
      fullCodeTheoremExponent6401 = 131072 := by
  norm_num [packedExtensionDegree6401, extensionDegree6401,
    squaredInterleaving6401, r1AgreementThreshold6401,
    r2AgreementThreshold6401, a6401,
    smallestApplicableFrobeniusTerms6401,
    fullCodeTheoremExponent6401, k6401]
theorem fullCode_subfield_bound_does_not_fit6401 :
    q6401 ^ 2 = 4539909903627583489 ∧
      exactFieldNumerator6401 < q6401 ^ 2 ∧
      q6401 ^ 2 ≤ fullCodeTheoremListBound6401 ∧
      exactFieldNumerator6401 < fullCodeTheoremListBound6401 := by
  have hbase : 1 ≤ q6401 := by norm_num [q6401]
  have hexp : 2 ≤ fullCodeTheoremExponent6401 := by
    norm_num [fullCodeTheoremExponent6401,
      smallestApplicableFrobeniusTerms6401, k6401]
  have hpow : q6401 ^ 2 ≤ q6401 ^ fullCodeTheoremExponent6401 :=
    Nat.pow_le_pow_right hbase hexp
  constructor
  · norm_num [q6401]
  constructor
  · norm_num [q6401, exactFieldNumerator6401]
  constructor
  · simpa [fullCodeTheoremListBound6401] using hpow
  · exact (by norm_num [q6401, exactFieldNumerator6401] :
        exactFieldNumerator6401 < q6401 ^ 2) |>.trans_le
      (by simpa [fullCodeTheoremListBound6401] using hpow)
theorem field_budget_split_exact6401 :
    exactFieldNumerator6401 - currentConservativeMCANumerator6401 =
        28111395087 ∧
      maxMCAWithIllustrativeListReserve6401 = 264980728111395087 ∧
      currentConservativeMCANumerator6401 -
          maxMCAWithIllustrativeListReserve6401 = 9999971888604913 ∧
      maxMCAWithIllustrativeListReserve6401 +
          illustrativeListReserve6401 = exactFieldNumerator6401 := by
  norm_num [exactFieldNumerator6401,
    currentConservativeMCANumerator6401,
    maxMCAWithIllustrativeListReserve6401,
    illustrativeListReserve6401]
end BCHKSSubfieldListBudgetAudit6401
end ProximityPrize.SubmissionLower
