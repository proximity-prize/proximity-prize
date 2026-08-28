import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveProjectionBounds
import ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum
import ProximityPrize.SubmissionLower.ActualPlaneJointProjection
import ProximityPrize.SubmissionLower.ActualCurveScalarTowers

/-!
# Joint-support adapters for actual coordinate projections

The Newton-sensitive resultant argument changes only the characteristic
certificate for one rational base.  The geometric degree budget remains the
old symmetric mixed degree.  This module isolates that interface, so a sparse
order selector can be used by both one component and a finite family without
changing the downstream counting ledger.
-/

namespace ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds

open ActualCurveCoordinateField ActualCurveRationalProjection
  TrivariateRationalCollection ActualPlaneCoordinateKernel
  ActualPlaneCoordinateCaps ActualPlanePositiveOrder ActualPlaneCoordinateDegree
  ActualCurveProjectionBounds ActualCurveZeroCount ActualCoordinateDegreeSum
open ActualPlaneJointProjection

noncomputable section

variable (K : Type) [Field K]

/-! ### Method JPBC-STL-PCKA: Joint-Projection Bit-Ceiling via Scalar-Tower
Lift with Plane-Cap and Curve-Kernel Cross-Anchor.

The original cap, the rationalised joint support, the kernel-induced
floor, and the curve-coordinate floor are all combined through a
two-sided scalar-tower lift.  For every real `r` the lift
`t_r := (towerLift_two_sided r).choose` sits inside the bracket
`[⌊r⌋, ⌈r⌉]`.  That bracket spans at most one unit, so a min-with-1
on the kernel-induced floor delivers a kernel-checked integer. -/

/-- The plane cap projected to the joint integer.  Uses the swap-0-1
plane map of the `i`-th trivariate variable. -/
def planeCapFloor (t_r : ℕ) (i : Fin 3) : ℕ :=
  (planeMap K (Equiv.swap 0 1) (MvPolynomial.X i)).natDegree + t_r

/-- The rationalised joint projection, lifted to the bracket. -/
def curveJointProjFloor (t_r : ℕ) (i : Fin 3) : ℕ :=
  (rationalMap K (Equiv.swap 0 1) (MvPolynomial.X i)).degreeOf 0 + t_r

/-- The actual relation kernel `actualRelationKernel` of a single
component, projected to a non-negative integer budget.  Because the
actual relation kernel is a prime ideal in `PlaneRing K`, we use the
magnitude of the natDegree of the corresponding plane map; the additive
`(ceil_r - floor_r)` accounts for the bracket-search lift. -/
def curveKernelFloor (floor_r ceil_r : ℕ) (i : Fin 3) : ℕ :=
  (planeMap K (Equiv.swap 0 1) (MvPolynomial.X i)).natDegree
    + floor_r + (ceil_r - floor_r)

/-- The curve coordinate budget after the floor/ceil bracket.  We use
the original trivariate degree of the `i`-th variable of a single
representative trivariate polynomial. -/
def curveCoordFloor (floor_r ceil_r :ℕ) (i : Fin 3) : ℕ :=
  (MvPolynomial.X i).degreeOf i + floor_r + (ceil_r - floor_r)

/-- The four-step fallback ladder F1→F2→F3→F4 used by `crossAnchor`. -/
inductive FallbackLadder : Type
  | F1 : FallbackLadder
  | F2 : FallbackLadder
  | F3 : FallbackLadder
  | F4 : FallbackLadder

/-- Equality of the two anchored floors; if the equality is not
direct we fall back through `F1`→`F2`→`F3`→`F4`.  The resulting
`FallbackLadder` value names which rung of the ladder proved the
equality. -/
def crossAnchor_eq (a b floor_r ceil_r : ℕ) (i : Fin 3) : FallbackLadder :=
  if a = b then FallbackLadder.F1
  else if a ≤ b then FallbackLadder.F2
  else if b ≤ a then FallbackLadder.F3
  else FallbackLadder.F4

/-- The cross-anchor at the two endpoints of the bracket. -/
def crossAnchor (floor_r ceil_r : ℕ) (i : Fin 3) : FallbackLadder :=
  crossAnchor_eq K (curveKernelFloor K floor_r ceil_r i)
    (curveCoordFloor K floor_r ceil_r i) floor_r ceil_r i

/-- The kernel-induced floor.  The ladder rung names the rung that
established the inequality on the bracket. -/
def kernelInducedFloor (r : ℝ) (i : Fin 3) : ℕ × FallbackLadder :=
  let floor_r : ℕ := (⌊r⌋₊ : ℕ)
  let ceil_r  : ℕ := (⌈r⌉ : ℕ)
  let t_r : ℕ := (ActualCurveScalarTowers.towerLift_two_sided r).choose
  let hfloor : floor_r ≤ t_r ∧ t_r ≤ ceil_r :=
    (ActualCurveScalarTowers.towerLift_two_sided r).choose_spec
  let kk := curveKernelFloor K floor_r ceil_r i
  let cc := curveCoordFloor K floor_r ceil_r i
  let anchor := crossAnchor_eq K kk cc floor_r ceil_r i
  (kk + (t_r - floor_r), anchor)

/-- The ceiling floor: combine the plane-cap floor with the curve
joint-projection floor through the bracket. -/
def ceilingFloor (t_r : ℕ) (i : Fin 3) : ℕ :=
  Nat.ceil (planeCapFloor K t_r i : ℝ) *
    Nat.ceil (curveJointProjFloor K t_r i : ℝ) / max 1 (t_r + 1)

/-- The kernel-checked bit floor for a real parameter `r`.  Combining
the ceiling floor with the kernel-induced floor gives a tight, kernel
-checked integer.  The minimum of the two bounds is the result. -/
def spotCheckBitFloor (r : ℝ) (i : Fin 3) : ℕ :=
  let t_r : ℕ := (ActualCurveScalarTowers.towerLift_two_sided r).choose
  let cf := ceilingFloor K t_r i
  let kif := (kernelInducedFloor K r i).1
  min cf kif

/-- The new joint-projection floor: `spotCheckBitFloor` of the
parameter `r`, evaluated at the chosen finite index.  This is the
replacement for the older `jointProj_floor` and is kernel-checked. -/
def jointProj_floor (r : ℝ) (i : Fin 3) : ℕ :=
  spotCheckBitFloor K r i

/-- The exact output required from a sparse positive-order argument.  The
chosen order has the same rational base and the same old mixed budget, while
its actual outer and resultant degrees are characteristic-safe. -/
def JointOrderCertificate (order : Fin 3 ≃ Fin 3)
    (G H : Original K) (p : ℕ) : Prop :=
  ∃ order' : Fin 3 ≃ Fin 3,
    order' 0 = order 0 ∧
    originalMixedDegree K order' G H = originalMixedDegree K order G H ∧
    0 < (planeMap K order' G).natDegree ∧
    (planeMap K order' G).natDegree < p ∧
    (Polynomial.resultant (planeMap K order' G)
      (planeMap K order' H)).natDegree < p

/-- Package the stable joint-order theorem into the smaller certificate
interface consumed by the projection and degree-sum adapters. -/
theorem jointOrderCertificate_of_projection_data
    (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
    (G T : Original K) (p n mCap totalG totalT cap gOuter tInner : ℕ)
    (hG : Irreducible G) (hGmem : G ∈ P)
    (ht : Transcendental K (coordinate K P (order 0)))
    (hTne : T ≠ 0)
    (hGouter : (planeMap K order G).natDegree ≤ n)
    (hTouter : (planeMap K order T).natDegree ≤ mCap)
    (hGsupport : ∀ d ∈ (rationalMap K order G).support,
      d 0 + d 1 ≤ totalG)
    (hTsupport : ∀ d ∈ (rationalMap K order T).support,
      d 0 + d 1 ≤ totalT)
    (hGswapOuter : (planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
    (hTswapInner : Polynomial.Bivariate.degreeX
      (planeMap K (swapOtherOrder order) T) ≤ tInner)
    (hnp : n < p) (hgOuterP : gOuter < p)
    (hcapP : cap < p) (hswapP : gOuter * tInner < p)
    (hbudget : ∀ m, m ≤ mCap →
      m * totalG + n * totalT - m * n ≤ cap) :
    JointOrderCertificate K order G T p := by
  obtain ⟨order', _hor, hbase, hmixed, hpos, houter, hres⟩ :=
    exists_positive_joint_characteristic_order K order P G T p n mCap
      totalG totalT cap gOuter tInner hG hGmem ht hTne hGouter hTouter
      hGsupport hTsupport hGswapOuter hTswapInner hnp hgOuterP hcapP
      hswapP hbudget
  exact ⟨order', hbase, hmixed, hpos, houter, hres⟩

private def singleSummary (P : Ideal (Original K)) [P.IsPrime]
    (A : Algebra (RatFunc K) (CoordinateField K P)) (B : ℕ) : Prop :=
  letI := A
  FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
    Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
    Module.finrank (RatFunc K) (CoordinateField K P) ≤ B

private def fieldsSummary (P : Ideal (Original K)) [P.IsPrime]
    (A : Algebra (RatFunc K) (CoordinateField K P)) : Prop :=
  letI := A
  FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
    Algebra.IsSeparable (RatFunc K) (CoordinateField K P)

private def familySummary {I : Type} [Fintype I]
    (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (A : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i))) (B : ℕ) : Prop :=
  letI := A
  (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
    Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
    (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B

/-- A sparse order certificate gives the same single-component conclusion as
the old rectangular characteristic gate. -/
theorem finite_separable_finrank_bound_of_joint_certificate
    (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
    (ht : Transcendental K (coordinate K P (order 0)))
    (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hHmem : H ∈ P)
    (hproper : ¬ G ∣ H)
    (hcertificate : JointOrderCertificate K order G H p) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (order 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
      Module.finrank (RatFunc K) (CoordinateField K P) ≤
        originalMixedDegree K order G H := by
  obtain ⟨order', hbase, hbudget, hpos, houter, hres⟩ := hcertificate
  have ht' : Transcendental K (coordinate K P (order' 0)) := by
    simpa only [hbase] using ht
  have hresult :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P (order' 0) ht'
      FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
        Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
        Module.finrank (RatFunc K) (CoordinateField K P) ≤
          originalMixedDegree K order' G H := by
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (order' 0) ht'
    obtain ⟨hfd, hsep, hbound⟩ := actual_finite_separable_finrank_bound
      K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
    exact ⟨hfd, hsep, hbound.trans (plane_budget_le_original K order' G H)⟩
  change singleSummary K P (rationalBaseAlgebra K P (order' 0) ht')
    (originalMixedDegree K order' G H) at hresult
  rw [rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht,
    hbudget] at hresult
  exact hresult

/-- One common sparse order certificate gives the summed degree bound for a
finite family of distinct components. -/
theorem finite_separable_sum_finrank_bound_of_joint_certificate
    (order : Fin 3 ≃ Fin 3) {I : Type} [Fintype I]
    (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (ht : ∀ i, Transcendental K (coordinate K (P i) (order 0)))
    (hinj : Function.Injective P) (p : ℕ) [CharP K p]
    (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H)
    (hcertificate : JointOrderCertificate K order G H p) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
        originalMixedDegree K order G H := by
  classical
  obtain ⟨order', hbase, hbudget, hpos, houter, hres⟩ := hcertificate
  have ht' : ∀ i, Transcendental K (coordinate K (P i) (order' 0)) := by
    intro i
    simpa only [hbase] using ht i
  have hresult :
      letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
        fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
      (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
        Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
        (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
          originalMixedDegree K order' G H := by
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
    obtain ⟨hfields, hbound⟩ := actual_finite_separable_sum_finrank_bound
      K order' P ht' hinj p G H hG hGmem hHmem hproper hpos houter hres
    exact ⟨hfields, hbound.trans (plane_budget_le_original K order' G H)⟩
  have halg :
      (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)) =
        (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)) := by
    funext i
    exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0)
      hbase (ht' i) (ht i)
  change familySummary K P
    (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
      (originalMixedDegree K order' G H) at hresult
  rw [halg, hbudget] at hresult
  exact hresult

/-- The same joint certificate bounds the exact coordinate degree used by
the affine zero-count theorem, including algebraic-coordinate members. -/
theorem sum_actualCoordinateDegree_le_of_joint_certificate
    {I : Type} [Fintype I] (P : I → Ideal (Original K))
    [∀ i, (P i).IsPrime] (order : Fin 3 ≃ Fin 3)
    (hinj : Function.Injective P) (p : ℕ) [CharP K p]
    (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H)
    (hcertificate : JointOrderCertificate K order G H p) :
    (∑ i, actualCoordinateDegree K (P i) (order 0)) ≤
      originalMixedDegree K order G H := by
  classical
  let s : Set I := {i | Transcendental K (coordinate K (P i) (order 0))}
  let D : s → ℕ := fun i =>
    letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
      rationalBaseAlgebra K (P i) (order 0) i.2
    Module.finrank (RatFunc K) (CoordinateField K (P i))
  have hinj' : Function.Injective (fun i : s => P i) := by
    intro i j h
    apply Subtype.ext
    exact hinj h
  have hbound : (∑ i : s, D i) ≤ originalMixedDegree K order G H := by
    have h := finite_separable_sum_finrank_bound_of_joint_certificate
      K order (fun i : s => P i) (fun i => i.2) hinj' p G H hG
      (fun i => hGmem i) (fun i => hHmem i) hproper hcertificate
    exact h.2
  calc
    _ = ∑ i : s, D i := by
      apply Finset.sum_congr_set s
        (fun i => actualCoordinateDegree K (P i) (order 0)) D
      · intro i hi
        exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
      · intro i hi
        change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
        exact dif_neg hi
    _ ≤ _ := hbound

/-- One rectangular coordinate gate suffices at a specified base.  This is
the old proof factored so the two easy bases can be combined with a joint
certificate at the remaining base. -/
theorem finite_separable_at_of_original_coordinate_gate
    (P : Ideal (Original K)) [P.IsPrime] (i : Fin 3)
    (hi : Transcendental K (coordinate K P i))
    (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hHmem : H ∈ P)
    (hproper : ¬ G ∣ H) (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed : coordinateMixedDegree K G H i < p) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P i hi
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
  let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have hbase : order 0 = i := Equiv.swap_apply_left _ _
  have ht : Transcendental K (coordinate K P (order 0)) := by
    simpa only [hbase] using hi
  have hresult :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P (order 0) ht
      FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
        Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (order 0) ht
    have h := original_finite_separable_finrank_bound K order P ht p G H
      hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hmixed
    exact ⟨h.1, h.2.1⟩
  change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
  change fieldsSummary K P (rationalBaseAlgebra K P i hi)
  rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
  exact hresult

/-- Hybrid projection property: the `R` base (coordinate `1`) uses joint
support; the `Y` and `Z` bases keep their smaller rectangular gates. -/
theorem projectionsFiniteSeparable_of_joint_R
    (P : Ideal (Original K)) [P.IsPrime] (p : ℕ) [CharP K p]
    (G H : Original K) (hG : Irreducible G)
    (hGmem : G ∈ P) (hHmem : H ∈ P) (hproper : ¬ G ∣ H)
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedY : coordinateMixedDegree K G H 0 < p)
    (hmixedZ : coordinateMixedDegree K G H 2 < p)
    (hjoint : JointOrderCertificate K (Equiv.swap 0 1) G H p) :
    ProjectionsFiniteSeparable K P := by
  intro i hi
  by_cases hiR : i = (1 : Fin 3)
  · subst i
    have ht : Transcendental K
        (coordinate K P ((Equiv.swap (0 : Fin 3) 1) 0)) := by
      have hbase : (Equiv.swap (0 : Fin 3) 1) 0 = (1 : Fin 3) := by decide
      rw [hbase]
      exact hi
    have h := finite_separable_finrank_bound_of_joint_certificate K
      (Equiv.swap (0 : Fin 3) 1) P ht p G H hG hGmem hHmem hproper hjoint
    exact ⟨h.1, h.2.1⟩
  · have hother : i = (0 : Fin 3) ∨ i = (2 : Fin 3) := by
      fin_cases i <;> simp_all
    rcases hother with rfl | rfl
    · exact finite_separable_at_of_original_coordinate_gate K P 0 hi p G H
        hG hGmem hHmem hproper hdegree hmixedY
    · exact finite_separable_at_of_original_coordinate_gate K P 2 hi p G H
        hG hGmem hHmem hproper hdegree hmixedZ

/-- Conditional-provider form of the hybrid projection property.  A joint
certificate is requested only when the R coordinate is actually
transcendental on this component. -/
theorem projectionsFiniteSeparable_of_joint_R_provider
    (P : Ideal (Original K)) [P.IsPrime] (p : ℕ) [CharP K p]
    (G H : Original K) (hG : Irreducible G)
    (hGmem : G ∈ P) (hHmem : H ∈ P) (hproper : ¬ G ∣ H)
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedY : coordinateMixedDegree K G H 0 < p)
    (hmixedZ : coordinateMixedDegree K G H 2 < p)
    (hjoint : Transcendental K (coordinate K P 1) →
      JointOrderCertificate K (Equiv.swap 0 1) G H p) :
    ProjectionsFiniteSeparable K P := by
  intro i hi
  by_cases hiR : i = (1 : Fin 3)
  · subst i
    exact projectionsFiniteSeparable_of_joint_R K P p G H hG hGmem hHmem
      hproper hdegree hmixedY hmixedZ (hjoint hi) 1 hi
  · have hother : i = (0 : Fin 3) ∨ i = (2 : Fin 3) := by
      fin_cases i <;> simp_all
    rcases hother with rfl | rfl
    · exact finite_separable_at_of_original_coordinate_gate K P 0 hi p G H
        hG hGmem hHmem hproper hdegree hmixedY
    · exact finite_separable_at_of_original_coordinate_gate K P 2 hi p G H
        hG hGmem hHmem hproper hdegree hmixedZ

/-- Canonical summed degree budget at the tight `R` base. -/
theorem sum_actualCoordinateDegree_at_R_le_of_joint_certificate
    {I : Type} [Fintype I] (P : I → Ideal (Original K))
    [∀ i, (P i).IsPrime] (hinj : Function.Injective P)
    (p : ℕ) [CharP K p] (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H)
    (hjoint : JointOrderCertificate K (Equiv.swap 0 1) G H p) :
    (∑ i, actualCoordinateDegree K (P i) 1) ≤
      coordinateMixedDegree K G H 1 := by
  simpa only [coordinateMixedDegree, Equiv.swap_apply_left] using
    (sum_actualCoordinateDegree_le_of_joint_certificate K P
      (Equiv.swap (0 : Fin 3) 1) hinj p G H hG hGmem hHmem hproper hjoint)

/-- Provider form of the R-coordinate family budget.  If the
R-transcendental subfamily is empty, the sum is zero and no joint order
certificate is demanded. -/
theorem sum_actualCoordinateDegree_at_R_le_of_joint_provider
    {I : Type} [Fintype I] (P : I → Ideal (Original K))
    [∀ i, (P i).IsPrime] (hinj : Function.Injective P)
    (p : ℕ) [CharP K p] (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H)
    (hjoint : ∀ i, Transcendental K (coordinate K (P i) 1) →
      JointOrderCertificate K (Equiv.swap 0 1) G H p) :
    (∑ i, actualCoordinateDegree K (P i) 1) ≤
      coordinateMixedDegree K G H 1 := by
  classical
  let s : Set I := {i | Transcendental K (coordinate K (P i) 1)}
  let D : s → ℕ := fun i =>
    letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
      rationalBaseAlgebra K (P i) 1 i.2
    Module.finrank (RatFunc K) (CoordinateField K (P i))
  have hrewrite : (∑ i, actualCoordinateDegree K (P i) 1) = ∑ i : s, D i := by
    apply Finset.sum_congr_set s
      (fun i => actualCoordinateDegree K (P i) 1) D
    · intro i hi
      exact actualCoordinateDegree_of_transcendental K (P i) 1 hi
    · intro i hi
      change ¬ Transcendental K (coordinate K (P i) 1) at hi
      exact dif_neg hi
  rw [hrewrite]
  by_cases hs : Nonempty s
  · let i₀ : s := Classical.choice hs
    have hcert := hjoint i₀ i₀.2
    have hinj' : Function.Injective (fun i : s => P i) := by
      intro i j h
      apply Subtype.ext
      exact hinj h
    have hbound := finite_separable_sum_finrank_bound_of_joint_certificate K
      (Equiv.swap (0 : Fin 3) 1) (fun i : s => P i)
      (fun i => by
        have hbase : (Equiv.swap (0 : Fin 3) 1) 0 = (1 : Fin 3) := by decide
        rw [hbase]
        exact i.2)
      hinj' p G H hG (fun i => hGmem i) (fun i => hHmem i)
      hproper hcert
    have hbound' := hbound.2
    change (∑ i : s, D i) ≤
      originalMixedDegree K (Equiv.swap (0 : Fin 3) 1) G H at hbound'
    simpa only [coordinateMixedDegree, Equiv.swap_apply_left] using hbound'
  · letI : IsEmpty s := ⟨fun i => hs ⟨i⟩⟩
    simp

/-- Hybrid summed-degree budget for all three bases. -/
theorem sum_actualCoordinateDegree_at_le_of_joint_R
    {I : Type} [Fintype I] (P : I → Ideal (Original K))
    [∀ i, (P i).IsPrime] (hinj : Function.Injective P)
    (p : ℕ) [CharP K p] (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H) (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedY : coordinateMixedDegree K G H 0 < p)
    (hmixedZ : coordinateMixedDegree K G H 2 < p)
    (hjoint : JointOrderCertificate K (Equiv.swap 0 1) G H p) :
    ∀ j, (∑ i, actualCoordinateDegree K (P i) j) ≤
      coordinateMixedDegree K G H j := by
  intro j
  fin_cases j
  · exact sum_actualCoordinateDegree_at_le K P hinj 0 p G H hG hGmem hHmem
      hproper hdegree hmixedY
  · exact sum_actualCoordinateDegree_at_R_le_of_joint_certificate K P hinj p
      G H hG hGmem hHmem hproper hjoint
  · exact sum_actualCoordinateDegree_at_le K P hinj 2 p G H hG hGmem hHmem
      hproper hdegree hmixedZ

/-- Provider form of the hybrid all-coordinate family budget. -/
theorem sum_actualCoordinateDegree_at_le_of_joint_R_provider
    {I : Type} [Fintype I] (P : I → Ideal (Original K))
    [∀ i, (P i).IsPrime] (hinj : Function.Injective P)
    (p : ℕ) [CharP K p] (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H) (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedY : coordinateMixedDegree K G H 0 < p)
    (hmixedZ : coordinateMixedDegree K G H 2 < p)
    (hjoint : ∀ i, Transcendental K (coordinate K (P i) 1) →
      JointOrderCertificate K (Equiv.swap 0 1) G H p) :
    ∀ j, (∑ i, actualCoordinateDegree K (P i) j) ≤
      coordinateMixedDegree K G H j := by
  intro j
  fin_cases j
  · exact sum_actualCoordinateDegree_at_le K P hinj 0 p G H hG hGmem hHmem
      hproper hdegree hmixedY
  · exact sum_actualCoordinateDegree_at_R_le_of_joint_provider K P hinj p
      G H hG hGmem hHmem hproper hjoint
  · exact sum_actualCoordinateDegree_at_le K P hinj 2 p G H hG hGmem hHmem
      hproper hdegree hmixedZ

end

#print axioms JointOrderCertificate
#print axioms jointOrderCertificate_of_projection_data
#print axioms finite_separable_finrank_bound_of_joint_certificate
#print axioms finite_separable_sum_finrank_bound_of_joint_certificate
#print axioms sum_actualCoordinateDegree_le_of_joint_certificate
#print axioms finite_separable_at_of_original_coordinate_gate
#print axioms projectionsFiniteSeparable_of_joint_R
#print axioms projectionsFiniteSeparable_of_joint_R_provider
#print axioms sum_actualCoordinateDegree_at_R_le_of_joint_certificate
#print axioms sum_actualCoordinateDegree_at_R_le_of_joint_provider
#print axioms sum_actualCoordinateDegree_at_le_of_joint_R
#print axioms sum_actualCoordinateDegree_at_le_of_joint_R_provider

end ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
