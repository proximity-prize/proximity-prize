import ProximityPrize.SubmissionLower.BCHKSSparseRuppertAudit6400

namespace ProximityPrize.SubmissionLower

/-!
Margin-one cofactor refinement of the sparse Ruppert/Gao lane.

Outside the global radical, a challenge has one owning factor `R^e` and the
full cofactor `Q / R^e` is nonzero at its polynomial root.  Dividing all `e`
copies, rather than one copy, is essential.  If `total` is the sum of local
orders of `R` on an exact `a`-coordinate agreement row, root counting for the
cofactor gives `w < total`.  Since every nonzero identity slice has local
order at most `degY R`, this yields `w <= d*a-1` with no exponent loss.

The exact margin-one interpolant below then pays for sparse rank-drop minors
through `Y` degree 25.  As in `BCHKSSparseRuppertAudit6400`, the matrix
specialization theorem itself is kept explicit as the remaining algebraic
implementation task; this file compiles the cofactor and numerical ledgers.
-/

def bchksCofactorMultiplicity6400 : ℕ := 59826
def bchksCofactorXCap6400 : ℕ := 11089586663
def bchksCofactorYCap6400 : ℕ := 84608
def bchksCofactorZCap6400 : ℕ := 1688975429

def bchksCofactorVariableCount6400 : ℕ :=
  792346826125058079051840
def bchksCofactorConstraintCount6400 : ℕ :=
  792346826125056371326976
def bchksCofactorSlack6400 : ℕ := 1707724864

def bchksCofactorProduct6400 : ℕ := 142899144036796
def bchksCofactorBaseCover6400 : ℕ := 14651124598
def bchksCofactorRadicalCover6400 : ℕ := 285812939198190

def bchksCofactorDegreeCap6400 : ℕ := 25
def bchksCofactorWeightCap6400 : ℕ := 4634099
def bchksCofactorLatticePoints6400 : ℕ := 77888525
def bchksCofactorColumnCap6400 : ℕ := 151142898
def bchksCofactorMinorCover6400 : ℕ := 255276640838710344
def bchksCofactorTotalCover6400 : ℕ := 255562453777908534

def bchksCofactorSplitDegreeCap6400 : ℕ := 26
def bchksCofactorSplitWeightCap6400 : ℕ := 4765170
def bchksCofactorSplitColumnCap6400 : ℕ := 160542167
def bchksCofactorSplitMinorCover6400 : ℕ := 271151775220872476
def bchksCofactorSplitTotalCover6400 : ℕ := 271437588160070666

lemma bchksCofactor_exactMargin6400 :
    bchksCofactorXCap6400 + 1 =
      bchksCofactorMultiplicity6400 * 185364 := by
  norm_num [bchksCofactorXCap6400, bchksCofactorMultiplicity6400]

lemma bchksCofactor_variableFormula6400 :
    6 * bchksCofactorVariableCount6400 =
      bchksCofactorYCap6400 *
        (6 * bchksCofactorXCap6400 * bchksCofactorZCap6400 -
          3 * (bchksCofactorXCap6400 +
            131071 * bchksCofactorZCap6400) *
              (bchksCofactorYCap6400 - 1) +
          131071 * (bchksCofactorYCap6400 - 1) *
            (2 * bchksCofactorYCap6400 - 1)) := by
  norm_num [bchksCofactorVariableCount6400, bchksCofactorYCap6400,
    bchksCofactorXCap6400, bchksCofactorZCap6400]

lemma bchksCofactor_constraintFormula6400 :
    6 * bchksCofactorConstraintCount6400 =
      262144 * bchksCofactorMultiplicity6400 *
        (6 * bchksCofactorMultiplicity6400 * bchksCofactorZCap6400 -
          3 * (bchksCofactorMultiplicity6400 + bchksCofactorZCap6400) *
            (bchksCofactorMultiplicity6400 - 1) +
          (bchksCofactorMultiplicity6400 - 1) *
            (2 * bchksCofactorMultiplicity6400 - 1)) := by
  norm_num [bchksCofactorConstraintCount6400,
    bchksCofactorMultiplicity6400, bchksCofactorZCap6400]

lemma bchksCofactor_interpolationFeasible6400 :
    bchksCofactorConstraintCount6400 + bchksCofactorSlack6400 =
      bchksCofactorVariableCount6400 := by
  norm_num [bchksCofactorConstraintCount6400, bchksCofactorSlack6400,
    bchksCofactorVariableCount6400]

/-- Division-free arithmetic heart of the full-cofactor argument.  The
subtracted quantities are known to be in range from factor-support
additivity. -/
theorem marginOne_cofactor_forces_weight_lt
    (m a e DX w total : ℕ)
    (he : 1 ≤ e) (hDX : DX + 1 = m * a)
    (hsupport : e * w ≤ DX)
    (hrootCount : m * a - e * total ≤ DX - e * w) :
    w < total := by
  by_contra hnot
  have htotal : total ≤ w := by omega
  have hetotal : e * total ≤ e * w := Nat.mul_le_mul_left e htotal
  have hetotalDX : e * total ≤ DX := hetotal.trans hsupport
  omega

/-- Local order at most `d` on an exact `a=185364` row turns the cofactor
inequality into the universal sparse support cap. -/
theorem marginOne_cofactor_weight_le_degree_mul_agreement
    (e w total d : ℕ) (he : 1 ≤ e)
    (hsupport : e * w ≤ bchksCofactorXCap6400)
    (hrootCount :
      bchksCofactorMultiplicity6400 * 185364 - e * total ≤
        bchksCofactorXCap6400 - e * w)
    (htotal : total ≤ d * 185364) :
    w ≤ d * 185364 - 1 := by
  have hlt := marginOne_cofactor_forces_weight_lt
    bchksCofactorMultiplicity6400 185364 e
      bchksCofactorXCap6400 w total he
      (by norm_num [bchksCofactorXCap6400,
        bchksCofactorMultiplicity6400])
      hsupport hrootCount
  omega

/-- In a local-order profile, every coordinate which is not at full order
`d` spends at least one unit of the total deficiency. -/
theorem card_le_fullMultiplicity_card_add_deficiency
    {I : Type*} [DecidableEq I] (S : Finset I) (nu : I → ℕ) (d : ℕ)
    (hnu : ∀ i ∈ S, nu i ≤ d) :
    S.card ≤ (S.filter fun i => nu i = d).card +
      ∑ i ∈ S, (d - nu i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hnui : nu i ≤ d := hnu i (by simp)
      have hnuS : ∀ j ∈ S, nu j ≤ d := by
        intro j hj
        exact hnu j (Finset.mem_insert_of_mem hj)
      have hih := ih hnuS
      have hiFilter : i ∉ S.filter fun j => nu j = d := by simp [hi]
      by_cases hfull : nu i = d
      · have hfilter :
            (insert i S).filter (fun j => nu j = d) =
              insert i (S.filter fun j => nu j = d) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hji | hjS, hjd⟩
              · exact Or.inl hji
              · exact Or.inr ⟨hjS, hjd⟩
            · rintro (hji | ⟨hjS, hjd⟩)
              · subst j
                exact ⟨Or.inl rfl, hfull⟩
              · exact ⟨Or.inr hjS, hjd⟩
        rw [Finset.card_insert_of_notMem hi, hfilter,
          Finset.card_insert_of_notMem hiFilter, Finset.sum_insert hi]
        simp [hfull]
        omega
      · have hdef : 1 ≤ d - nu i := by omega
        have hfilter :
            (insert i S).filter (fun j => nu j = d) =
              S.filter fun j => nu j = d := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hji | hjS, hjd⟩
              · subst j
                exact (hfull hjd).elim
              · exact ⟨hjS, hjd⟩
            · rintro ⟨hjS, hjd⟩
              exact ⟨Or.inr hjS, hjd⟩
        rw [Finset.card_insert_of_notMem hi, hfilter, Finset.sum_insert hi]
        omega

/-- At the Johnson-boundary constants, either an exact agreement row exposes
at least `k+1` full-multiplicity coordinates, or its order deficiency is at
least `a-k=54293`. -/
theorem bchksCofactor_fullMultiplicity_or_deficiency6400
    (full deficiency : ℕ)
    (hprofile : 185364 ≤ full + deficiency) :
    131072 ≤ full ∨ 54293 ≤ deficiency := by
  omega

lemma bchksCofactor_triangleColumns6400 :
    bchksCofactorWeightCap6400 =
        bchksCofactorDegreeCap6400 * 185364 - 1 ∧
      bchksCofactorLatticePoints6400 =
        (bchksCofactorDegreeCap6400 + 1) *
            (bchksCofactorWeightCap6400 + 1) -
          131071 * bchksCofactorDegreeCap6400 *
            (bchksCofactorDegreeCap6400 + 1) / 2 ∧
      bchksCofactorColumnCap6400 =
        2 * bchksCofactorLatticePoints6400 -
          (bchksCofactorWeightCap6400 + 1) -
          2 * (bchksCofactorDegreeCap6400 + 1) ∧
      bchksCofactorColumnCap6400 =
        (2 * bchksCofactorDegreeCap6400 + 1) *
            bchksCofactorWeightCap6400 -
          131071 * bchksCofactorDegreeCap6400 *
            (bchksCofactorDegreeCap6400 + 1) - 1 := by
  norm_num [bchksCofactorWeightCap6400, bchksCofactorDegreeCap6400,
    bchksCofactorLatticePoints6400, bchksCofactorColumnCap6400]

lemma bchksCofactor_gaoCharacteristic6400 :
    (2 * bchksCofactorDegreeCap6400 - 1) *
        bchksCofactorWeightCap6400 < 2130706433 := by
  norm_num [bchksCofactorDegreeCap6400, bchksCofactorWeightCap6400]

/-- The degree-25 endpoint dominates the exact `w<=d*a-1` column count at
every lower positive degree. -/
theorem bchksCofactor_columns_le_of_degree_le25
    (d w C : ℕ) (hd : 1 ≤ d) (hd25 : d ≤ 25)
    (hw : w ≤ d * 185364 - 1)
    (hC : C + 131071 * d * (d + 1) + 1 = (2 * d + 1) * w) :
    C ≤ bchksCofactorColumnCap6400 := by
  dsimp [bchksCofactorColumnCap6400]
  interval_cases d <;> norm_num at hC hw ⊢ <;> omega

/-- In the non-alignment branch, the deficiency of at least `a-k` sharpens
the degree-26 weight and sparse-column caps enough to fit. -/
lemma bchksCofactor_degree26_splitColumns6400 :
    bchksCofactorSplitWeightCap6400 =
        bchksCofactorSplitDegreeCap6400 * 185364 - 54293 - 1 ∧
      bchksCofactorSplitColumnCap6400 =
        (2 * bchksCofactorSplitDegreeCap6400 + 1) *
            bchksCofactorSplitWeightCap6400 -
          131071 * bchksCofactorSplitDegreeCap6400 *
            (bchksCofactorSplitDegreeCap6400 + 1) - 1 := by
  norm_num [bchksCofactorSplitWeightCap6400,
    bchksCofactorSplitDegreeCap6400, bchksCofactorSplitColumnCap6400]

lemma bchksCofactor_degree26_splitCover6400 :
    bchksCofactorSplitMinorCover6400 =
        bchksCofactorSplitColumnCap6400 *
          (bchksCofactorZCap6400 - 1) ∧
      bchksCofactorSplitTotalCover6400 =
        bchksCofactorRadicalCover6400 +
          bchksCofactorSplitMinorCover6400 := by
  norm_num [bchksCofactorSplitMinorCover6400,
    bchksCofactorSplitColumnCap6400, bchksCofactorZCap6400,
    bchksCofactorSplitTotalCover6400, bchksCofactorRadicalCover6400]

lemma bchksCofactor_degree26_splitFieldBudget6400 :
    bchksCofactorSplitTotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksCofactorSplitTotalCover6400 =
        3541411839929334 ∧
      2 ^ (128 : ℕ) *
          (bchksCofactorSplitTotalCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksCofactorSplitTotalCover6400, bchksWeightedNumerator6400,
    bchksListBound6400]

lemma bchksCofactor_degree26_gaoCharacteristic6400 :
    (2 * bchksCofactorSplitDegreeCap6400 - 1) *
        bchksCofactorSplitWeightCap6400 < 2130706433 := by
  norm_num [bchksCofactorSplitDegreeCap6400,
    bchksCofactorSplitWeightCap6400]

lemma bchksCofactor_coverLedger6400 :
    bchksCofactorProduct6400 =
        (bchksCofactorYCap6400 - 1) *
          (bchksCofactorZCap6400 - 1) ∧
      bchksCofactorBaseCover6400 =
        (bchksCofactorYCap6400 - 1) * bchksStableFiberCap6400 +
          (262144 * (bchksCofactorZCap6400 - 1) +
              bchksStableChargeGap6400 - 1) /
            bchksStableChargeGap6400 ∧
      bchksCofactorRadicalCover6400 =
        2 * bchksCofactorProduct6400 + bchksCofactorBaseCover6400 ∧
      bchksCofactorMinorCover6400 =
        bchksCofactorColumnCap6400 * (bchksCofactorZCap6400 - 1) ∧
      bchksCofactorTotalCover6400 =
        bchksCofactorRadicalCover6400 + bchksCofactorMinorCover6400 := by
  norm_num [bchksCofactorProduct6400, bchksCofactorYCap6400,
    bchksCofactorZCap6400, bchksCofactorBaseCover6400,
    bchksStableFiberCap6400, bchksStableChargeGap6400,
    bchksCofactorRadicalCover6400, bchksCofactorMinorCover6400,
    bchksCofactorColumnCap6400, bchksCofactorTotalCover6400]

lemma bchksCofactor_fieldBudget6400 :
    bchksCofactorTotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksCofactorTotalCover6400 =
        19416546222091466 ∧
      2 ^ (128 : ℕ) *
          (bchksCofactorTotalCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksCofactorTotalCover6400, bchksWeightedNumerator6400,
    bchksListBound6400]

/-- Degree 26 is the first numerical miss for this exact cofactor/sparse
point. -/
lemma bchksCofactor_degree26_noGo6400 :
    bchksWeightedNumerator6400 < 276297663934428078 := by
  norm_num [bchksWeightedNumerator6400]

end ProximityPrize.SubmissionLower
