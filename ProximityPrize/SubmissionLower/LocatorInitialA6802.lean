import ProximityPrize.SubmissionLower.LocatorFixedBridge6802

namespace ProximityPrize.SubmissionLower.LocatorInitialA6802

open ProximityPrize.Benchmark RCN095 RCN260 LocatorFactorAggregate
open LocatorGenericHelperFactorSwitch6802 LocatorPhase6802Oracle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem initialAHelperCap_le_potential (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    (helperPair 130000 132 29 (middle p) p.all (total p)).regularCountCap ≤
      initialAPotential.eval p := by
  have haz : 262142 * total p + 1 ≤ 34078460001 := by omega
  have hry : p.all ≤ middle p := by simp [middle]
  have hyt : middle p ≤ total p := by simp [middle, total]
  simp only [helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, RCN294.dot, Potential.eval, initialAPotential]
  rw [max_eq_right haz]
  by_cases hay : 34602745 ≤ 1 + 262142 * middle p
  · rw [max_eq_left hay]
    have hylo : 132 ≤ middle p := by omega
    by_cases har : 7471047 ≤ 131071 * (2 * p.all - 1)
    · rw [max_eq_left har]
      have hrlo : 29 ≤ p.all := by omega
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have hq : p.all * 2 - 1 ≤ 63 := by omega
      have htpart :
          2267742732156 * (total p * (p.all * 2 - 1)) +
              996432412614 * (middle p * total p) + 94141 * total p ≤
            291336221699455 * total p := by
        have hc : 2267742732156 * (p.all * 2 - 1) +
              996432412614 * middle p + 94141 ≤ 291336221699455 := by
          nlinarith
        nlinarith [Nat.mul_le_mul_left (total p) hc]
      have hypart :
          2233382993790000 * (middle p * (p.all * 2 - 1)) +
              20773185952864313 * middle p ≤
            161476314561634313 * middle p := by
        have hc : 2233382993790000 * (p.all * 2 - 1) +
              20773185952864313 ≤ 161476314561634313 := by omega
        nlinarith [Nat.mul_le_mul_left (middle p) hc]
      have hstatic :
          4466765987580000 * (middle p * p.all) ≤
            20773185952864313 * middle p +
              568822985056828470 * p.all := by
        have hpY : (0 : ℤ) ≤
            (149 - (middle p : ℤ)) *
              (4466765987580000 * (p.all : ℤ) -
                20773185952864313) := by
          apply mul_nonneg <;> omega
        have hpR : (0 : ℤ) ≤
            (32 - (p.all : ℤ)) *
              (4466765987580000 * 149 - 568822985056828470) := by
          apply mul_nonneg <;> omega
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (show 4466765987580000 * p.all * middle p ≤
              20773185952864313 * middle p +
                568822985056828470 * p.all from
          (by exact_mod_cast (show
          (4466765987580000 : ℤ) * p.all * middle p ≤
            20773185952864313 * middle p +
              568822985056828470 * p.all by nlinarith [hpY, hpR])))
      ring_nf
      omega
    · rw [max_eq_right (Nat.le_of_not_ge har)]
      have hrhi : p.all ≤ 28 := by omega
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have htcross :
          996432412614 * (middle p * total p) +
              13606456487077 * total p ≤
            162074885966563 * total p := by
        have hc : 996432412614 * middle p + 13606456487077 ≤
            162074885966563 := by omega
        nlinarith [Nat.mul_le_mul_left (total p) hc]
      have hstatic :
          4466765987580000 * (middle p * p.all) ≤
            34173483915604313 * middle p +
              568822985056828470 * p.all := by
        by_cases hrs : p.all ≤ 7
        · have hc : 4466765987580000 * p.all ≤
              34173483915604313 := by omega
          nlinarith [Nat.mul_le_mul_left (middle p) hc]
        · have hr8 : 8 ≤ p.all := by omega
          have hpY : (0 : ℤ) ≤
              (149 - (middle p : ℤ)) *
                (4466765987580000 * (p.all : ℤ) -
                  34173483915604313) := by
            apply mul_nonneg <;> omega
          have hpR : (0 : ℤ) ≤
              (28 - (p.all : ℤ)) *
                (4466765987580000 * 149 - 568822985056828470) := by
            apply mul_nonneg <;> omega
          simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            (show 4466765987580000 * p.all * middle p ≤
                34173483915604313 * middle p +
                  568822985056828470 * p.all from
            (by exact_mod_cast (show
            (4466765987580000 : ℤ) * p.all * middle p ≤
              34173483915604313 * middle p +
                568822985056828470 * p.all by nlinarith [hpY, hpR])))
      ring_nf
      omega
  · rw [max_eq_right (Nat.le_of_not_ge hay)]
    have hyhi : middle p ≤ 131 := by omega
    by_cases har : 7471047 ≤ 131071 * (2 * p.all - 1)
    · rw [max_eq_left har]
      have hrlo : 29 ≤ p.all := by omega
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      have hq : p.all * 2 - 1 ≤ 63 := by omega
      have htpart :
          2267742732156 * (total p * (p.all * 2 - 1)) +
              16939351108579 * total p ≤
            159807143234407 * total p := by
        have hc : 2267742732156 * (p.all * 2 - 1) +
              16939351108579 ≤ 159807143234407 := by omega
        nlinarith [Nat.mul_le_mul_left (total p) hc]
      have hypart :
          2233382993790000 * ((p.all * 2 - 1) * middle p) +
              20773185952864313 * middle p ≤
            161476314561634313 * middle p := by
        have hc : 2233382993790000 * (p.all * 2 - 1) +
              20773185952864313 ≤ 161476314561634313 := by omega
        nlinarith [Nat.mul_le_mul_left (middle p) hc]
      have hcover :
          20790125303731530 * p.all ≤
            16939351108579 * total p +
              20773185952864313 * middle p := by
        nlinarith
      ring_nf
      omega
    · rw [max_eq_right (Nat.le_of_not_ge har)]
      have hrhi : p.all ≤ 28 := by omega
      norm_num
      apply (Nat.div_le_iff_le_mul (by decide)).2
      ring_nf
      omega

end ProximityPrize.SubmissionLower.LocatorInitialA6802
