import ProximityPrize.SubmissionLower.BCHKSSparseCofactorAudit6400
import ProximityPrize.SubmissionLower.BCHKSCofactorLocalBridge6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSCofactorRetuneAudit6400

open BCHKSLocalValuation6400

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
Independent arithmetic and interface audit for the margin-one `j = 0`
retune.  The useful point of the first lemma is that it consumes the two
inequalities produced directly by the algebraic cofactor bridge; no
subtraction side conditions and no prior assumption `w <= total` are needed.
-/

/-- Direct margin-one finish from the summed cofactor root count and the
weighted support decomposition. -/
theorem marginOne_weight_le_degree_mul_agreement_direct
    (e w total rootMass d : Nat)
    (hroot : bchksCofactorMultiplicity6400 * 185364 <=
      rootMass + e * total)
    (hdegree : rootMass + e * w <= bchksCofactorXCap6400)
    (htotal : total <= d * 185364) :
    w <= d * 185364 - 1 := by
  have hmargin := bchksCofactor_exactMargin6400
  by_contra hnot
  have hdw : d * 185364 <= w := by omega
  have htw : total <= w := htotal.trans hdw
  have hetw : e * total <= e * w := Nat.mul_le_mul_left e htw
  omega

/-- A concrete coefficient on the `X = 0` fibre bounds local total order by
its outer index.  This is the exact nonverticality interface needed for the
claim `nu_i <= deg_Y R`. -/
theorem localOrder_le_of_nonvertical_coefficient
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A)) (d : Nat)
    (hwitness : ∃ t, t <= d ∧ (S.coeff t).coeff 0 ≠ 0) :
    localOrder S <= d := by
  obtain ⟨t, ht, hcoeff⟩ := hwitness
  have hdiag : (diagonalize S).coeff t ≠ 0 := by
    intro hzero
    have hz := congrArg (fun P : Polynomial A => P.coeff t) hzero
    rw [diagonalize_coeff_coeff] at hz
    exact hcoeff (by simpa using hz)
  exact (Polynomial.natTrailingDegree_le_of_ne_zero hdiag).trans ht

/-- Equivalently, it suffices that the shifted factor have no vertical
`X`-component.  Irreducibility of a positive-`Y` factor should establish
this after proving that bivariate translation preserves irreducibility. -/
theorem localOrder_le_natDegree_of_not_vertical
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A))
    (hvertical : ¬ (Polynomial.C (Polynomial.X : Polynomial A) ∣ S)) :
    localOrder S <= S.natDegree := by
  have hex : ∃ t, ¬ ((Polynomial.X : Polynomial A) ∣ S.coeff t) := by
    by_contra hnot
    push Not at hnot
    exact hvertical ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hnot)
  obtain ⟨t, ht⟩ := hex
  have hcoeff0 : (S.coeff t).coeff 0 ≠ 0 := by
    simpa only [Polynomial.X_dvd_iff] using ht
  have hcoeff : S.coeff t ≠ 0 := by
    intro hz
    exact hcoeff0 (by simp [hz])
  apply localOrder_le_of_nonvertical_coefficient S S.natDegree
  exact ⟨t, Polynomial.le_natDegree_of_ne_zero hcoeff, hcoeff0⟩

/-- The characteristic condition needed by Gao's rectangular theorem is
uniformly valid throughout the claimed degree range. -/
theorem bchksCofactor_gaoCharacteristic_of_degree_le25
    (d w : Nat) (hd : 1 <= d) (hd25 : d <= 25)
    (hw : w <= d * 185364 - 1) :
    (2 * d - 1) * w < 2130706433 := by
  interval_cases d <;> norm_num at hw ⊢ <;> omega

/-- Once a sparse rank-drop minor with the advertised column count exists,
all degrees through 25 fit both the root-count and characteristic ledgers. -/
theorem bchksCofactor_sparse_budget_of_degree_le25
    (d w C : Nat) (hd : 1 <= d) (hd25 : d <= 25)
    (hw : w <= d * 185364 - 1)
    (hC : C + 131071 * d * (d + 1) + 1 = (2 * d + 1) * w) :
    bchksCofactorRadicalCover6400 +
          C * (bchksCofactorZCap6400 - 1) <
        bchksWeightedNumerator6400 /\
      (2 * d - 1) * w < 2130706433 := by
  have hcolumns := bchksCofactor_columns_le_of_degree_le25
    d w C hd hd25 hw hC
  constructor
  · have hmul : C * (bchksCofactorZCap6400 - 1) <=
        bchksCofactorColumnCap6400 *
          (bchksCofactorZCap6400 - 1) :=
      Nat.mul_le_mul_right (bchksCofactorZCap6400 - 1) hcolumns
    have hledger := bchksCofactor_coverLedger6400
    have hbudget := bchksCofactor_fieldBudget6400.1
    omega
  · exact bchksCofactor_gaoCharacteristic_of_degree_le25 d w hd hd25 hw

def bchksCofactorDegree26Weight6400 : Nat := 4819463
def bchksCofactorDegree26Columns6400 : Nat := 163419696
def bchksCofactorDegree26MinorCover6400 : Nat := 276011850995229888
def bchksCofactorDegree26TotalCover6400 : Nat := 276297663934428078
def bchksCofactorDegree26Overshoot6400 : Nat := 1318663934428078

/-- Exact first miss of this particular ambient-triangle determinant
ledger.  It is a budget miss, not a mathematical obstruction at degree 26. -/
lemma bchksCofactor_degree26_exact_miss6400 :
    bchksCofactorDegree26Weight6400 = 26 * 185364 - 1 /\
      bchksCofactorDegree26Columns6400 +
          131071 * 26 * (26 + 1) + 1 =
        (2 * 26 + 1) * bchksCofactorDegree26Weight6400 /\
      bchksCofactorDegree26MinorCover6400 =
        bchksCofactorDegree26Columns6400 *
          (bchksCofactorZCap6400 - 1) /\
      bchksCofactorDegree26TotalCover6400 =
        bchksCofactorRadicalCover6400 +
          bchksCofactorDegree26MinorCover6400 /\
      bchksCofactorDegree26TotalCover6400 =
        bchksWeightedNumerator6400 + bchksCofactorDegree26Overshoot6400 := by
  norm_num [bchksCofactorDegree26Weight6400,
    bchksCofactorDegree26Columns6400,
    bchksCofactorDegree26MinorCover6400,
    bchksCofactorDegree26TotalCover6400,
    bchksCofactorDegree26Overshoot6400,
    bchksCofactorZCap6400, bchksCofactorRadicalCover6400,
    bchksWeightedNumerator6400]

end BCHKSCofactorRetuneAudit6400
end ProximityPrize.SubmissionLower
