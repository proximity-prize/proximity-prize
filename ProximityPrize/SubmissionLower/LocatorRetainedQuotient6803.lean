import ProximityPrize.SubmissionLower.PackedLegacyCore2

/-!
# Quotient boxes after retaining a divisor of the selected gcd

The coupled 68.03 ledger remembers the aggregate flag of the factors which
survive the initial A-source split.  Their squarefree product divides the
selected gcd, so all three of its cumulative weights can be subtracted from
both coprime quotients.  For the contact coordinate the amount retained is
`w * middle p - p.all`, obtained from the residual-YS and slope weights.
-/

namespace ProximityPrize.SubmissionLower.LocatorRetainedQuotient6803

open RCN081 RCN095 RCN100 RCN130 RCN156 RCN180 RCN234

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

/-- The cumulative `Y,S` weight represented by a residual flag. -/
def middle (p : FlagDegree) : ℕ := p.yz + p.all

/-- The cumulative total weight represented by a residual flag. -/
def total (p : FlagDegree) : ℕ := p.zOnly + p.yz + p.all

/-- Contact weight forced by a cumulative residual flag. -/
def retainedContact (w : ℕ) (p : FlagDegree) : ℕ :=
  w * middle p - p.all

/-- A nonzero retained divisor supplies lower bounds for the three weights
of every nonzero multiple. -/
theorem retained_weight_lowers
    (w : ℕ) (hw : 1 ≤ w)
    (P H : MvPolynomial (Fin 4) K)
    (hP : P ≠ 0) (hH : H ≠ 0) (hPH : P ∣ H) :
    retainedContact w (originalCumulativeFlag P) ≤
        wt (contactWeights w) H ∧
      total (originalCumulativeFlag P) ≤ wt residualTotalWeights H ∧
      (originalCumulativeFlag P).all ≤ wt residualSWeights H := by
  have hcontactP := residualYS_mul_le_contact_add_slope P w hw
  have hcontactPH := weightedTotalDegree_le_of_dvd
    (contactWeights w) P H hPH hH
  have htotalPH := weightedTotalDegree_le_of_dvd
    residualTotalWeights P H hPH hH
  have hslopePH := weightedTotalDegree_le_of_dvd
    residualSWeights P H hPH hH
  have hc := originalCumulativeFlag_cumulative P
  constructor
  · unfold retainedContact middle
    rw [hc.2.1, hc.1]
    simp only [wt] at hcontactP hcontactPH
    simp only [wt]
    omega
  constructor
  · unfold total
    rw [hc.2.2]
    simpa only [wt] using htotalPH
  · rw [hc.1]
    simpa only [wt] using hslopePH

/-- If `Q = H * R` and a remembered product `P` divides `H`, the quotient
`R` lies in the parent box with the remembered flag subtracted. -/
theorem quotient_mem_box_of_retained_divisor
    (Q H R P : MvPolynomial (Fin 4) K)
    (D w L s : ℕ)
    (hQ : Q ≠ 0) (hH : H ≠ 0) (hR : R ≠ 0) (hP : P ≠ 0)
    (hbox : Q ∈ RCN100.globalCoefficientBox K D w L s)
    (heq : Q = H * R) (hPH : P ∣ H) (hw : 1 ≤ w) :
    R ∈ RCN100.globalCoefficientBox K
      (D - retainedContact w (originalCumulativeFlag P)) w
      (L - total (originalCumulativeFlag P))
      (s - (originalCumulativeFlag P).all) := by
  have hlower := retained_weight_lowers w hw P H hP hH hPH
  exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    Q H R D w L s
      (retainedContact w (originalCumulativeFlag P))
      (total (originalCumulativeFlag P))
      (originalCumulativeFlag P).all
      hQ hH hR hbox heq hlower.1 hlower.2.1 hlower.2.2

/-- The ordinary separated degree caps extracted from the retained quotient
box.  The caller supplies the elementary division inequality converting the
contact cutoff into its desired middle cap. -/
theorem quotient_degree_caps_of_retained_divisor
    (Q H R P : MvPolynomial (Fin 4) K)
    (D w L s y : ℕ)
    (hQ : Q ≠ 0) (hH : H ≠ 0) (hR : R ≠ 0) (hP : P ≠ 0)
    (hbox : Q ∈ RCN100.globalCoefficientBox K D w L s)
    (heq : Q = H * R) (hPH : P ∣ H) (hw : 1 ≤ w)
    (hy :
      (D - retainedContact w (originalCumulativeFlag P) - 1) / w ≤
        y - middle (originalCumulativeFlag P)) :
    R.degreeOf (1 : Fin 4) ≤ y - middle (originalCumulativeFlag P) ∧
      R.degreeOf (2 : Fin 4) ≤ s - (originalCumulativeFlag P).all ∧
      R.degreeOf (3 : Fin 4) ≤ L - total (originalCumulativeFlag P) := by
  have hretained := quotient_mem_box_of_retained_divisor
    Q H R P D w L s hQ hH hR hP hbox heq hPH hw
  have hordinary := RCN101.flag_box_to_ordinary K
    (D - retainedContact w (originalCumulativeFlag P)) w
    (L - total (originalCumulativeFlag P))
    (s - (originalCumulativeFlag P).all) R hretained
  exact degree_bounds_of_mem_box R
    (D - retainedContact w (originalCumulativeFlag P)) w
    (L - total (originalCumulativeFlag P))
    (s - (originalCumulativeFlag P).all) hw hordinary
    |> fun h ↦ ⟨h.1.trans hy, h.2⟩

end

end ProximityPrize.SubmissionLower.LocatorRetainedQuotient6803
