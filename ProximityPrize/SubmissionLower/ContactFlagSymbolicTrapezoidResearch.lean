import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps6543Research

/-! .





 -/

namespace ProximityPrize.SubmissionLower.ContactFlagSymbolicTrapezoidResearch

open ContactFlagBezout6543Research

/-- .
 -/
theorem flagMixed_projection_decomposition
    (p q r : FlagDegree) :
    flagMixed p q r =
      r.zOnly * flagMixed p q unitZFlag +
      r.yz * flagMixed p q unitYZFlag +
      r.all * flagMixed p q unitAllFlag := by
  cases p
  cases q
  cases r
  simp [flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
  ring

/-- .
 -/
theorem trapezoid_budget_mono
    (n mCap totalG totalT m : ℕ)
    (hn : n ≤ totalG) (hm : m ≤ mCap) :
    m * totalG + n * totalT - m * n ≤
      mCap * totalG + n * totalT - mCap * n := by
  let delta := totalG - n
  have hsplit : totalG = n + delta := by
    dsimp only [delta]
    omega
  have hdecomp (a : ℕ) :
      a * totalG = a * n + a * delta := by
    rw [hsplit, Nat.mul_add]
  have hdelta : m * delta ≤ mCap * delta :=
    Nat.mul_le_mul_right delta hm
  rw [hdecomp m, hdecomp mCap]
  omega

/-- . -/
theorem u_flag_trapezoid_budget
    (p q : FlagDegree) (m : ℕ) (hm : m ≤ q.all) :
    m * (p.zOnly + p.yz + p.all) +
          p.all * (q.zOnly + q.yz + q.all) - m * p.all ≤
      flagMixed p q unitYZFlag := by
  calc
    m * (p.zOnly + p.yz + p.all) +
          p.all * (q.zOnly + q.yz + q.all) - m * p.all ≤
        q.all * (p.zOnly + p.yz + p.all) +
          p.all * (q.zOnly + q.yz + q.all) - q.all * p.all :=
      trapezoid_budget_mono p.all q.all
        (p.zOnly + p.yz + p.all) (q.zOnly + q.yz + q.all) m
        (by omega) hm
    _ = flagMixed p q unitYZFlag := by
      have hsum :
          q.all * (p.zOnly + p.yz + p.all) +
              p.all * (q.zOnly + q.yz + q.all) =
            q.all * p.all + flagMixed p q unitYZFlag := by
        simp [flagMixed, unitYZFlag]
        ring
      rw [hsum, Nat.add_sub_cancel_left]

/-- . -/
theorem v_flag_trapezoid_budget
    (p q : FlagDegree) (m : ℕ) (hm : m ≤ q.yz + q.all) :
    m * (p.zOnly + p.yz + p.all) +
          (p.yz + p.all) * (q.zOnly + q.yz + q.all) -
            m * (p.yz + p.all) ≤
      flagMixed p q unitAllFlag := by
  calc
    m * (p.zOnly + p.yz + p.all) +
          (p.yz + p.all) * (q.zOnly + q.yz + q.all) -
            m * (p.yz + p.all) ≤
        (q.yz + q.all) * (p.zOnly + p.yz + p.all) +
          (p.yz + p.all) * (q.zOnly + q.yz + q.all) -
            (q.yz + q.all) * (p.yz + p.all) :=
      trapezoid_budget_mono (p.yz + p.all) (q.yz + q.all)
        (p.zOnly + p.yz + p.all) (q.zOnly + q.yz + q.all) m
        (by omega) hm
    _ = flagMixed p q unitAllFlag := by
      have hsum :
          (q.yz + q.all) * (p.zOnly + p.yz + p.all) +
              (p.yz + p.all) * (q.zOnly + q.yz + q.all) =
            (q.yz + q.all) * (p.yz + p.all) +
              flagMixed p q unitAllFlag := by
        simp [flagMixed, unitAllFlag]
        ring
      rw [hsum, Nat.add_sub_cancel_left]

/-- . -/
theorem z_flag_trapezoid_budget
    (p q : FlagDegree) (m : ℕ) (hm : m ≤ q.all) :
    m * (p.yz + p.all) + p.all * (q.yz + q.all) - m * p.all ≤
      flagMixed p q unitZFlag := by
  calc
    m * (p.yz + p.all) + p.all * (q.yz + q.all) - m * p.all ≤
        q.all * (p.yz + p.all) + p.all * (q.yz + q.all) -
          q.all * p.all :=
      trapezoid_budget_mono p.all q.all (p.yz + p.all)
        (q.yz + q.all) m (by omega) hm
    _ = flagMixed p q unitZFlag := by
      have hsum :
          q.all * (p.yz + p.all) + p.all * (q.yz + q.all) =
            q.all * p.all + flagMixed p q unitZFlag := by
        simp [flagMixed, unitZFlag]
        ring
      rw [hsum, Nat.add_sub_cancel_left]

end ProximityPrize.SubmissionLower.ContactFlagSymbolicTrapezoidResearch
