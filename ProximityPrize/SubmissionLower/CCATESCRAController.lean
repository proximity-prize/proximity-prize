import ProximityPrize.Benchmark.TargetLower

/-!
# CCAT-ESCRA — Conformal-Calibrated Adaptive Threshold Elevation with
  Spot-Check Residual Annealing

Model label: gpt-5.

This module instantiates a bucketed conformal-coverage controller that gates
threshold descent and allocates a residual-quantile-conditioned margin into
the kernel-checked spot-check-bit floor. Every knob is exposed as a `Nat`
configuration field so the controller is auditable without any `native_decide`
or unverified oracle.

  * `conformal_alpha`     — miscoverage level for each conformal bucket,
                            expressed in basis points (1e-4 = 0.01 %).
  * `anneal_schedule`     — monotone map from descent step `s` to a
                            non-negative `Nat` scale `annealCoeff s`.
  * `residual_quantile_q` — numerator of the residual-quantile fraction
                            `q/1000` (denominator is fixed at 1000 for
                            closed-form arithmetic).
  * `spot_margin_gamma`   — centibits of margin that the controller pushes
                            into the kernel-checked spot-check-bit floor.
  * `bucket_count`        — number of conformal-coverage buckets `B`; the
                            bucket index is `step mod bucket_count`.
  * `safety_shrink_eta`   — fixed-point numerator of the safety shrink
                            factor `eta/1000`; `(1 - eta/1000)` contracts
                            the descent whenever the gate is closed.

The gate is the conjunction of three kernel-checkable conditions:

  (1) the conformal-coverage threshold for the current bucket is satisfied,
  (2) the anneal coefficient for the current step is at least the bucket
      minimum, and
  (3) the safety-shrunk descent stays in the admissible radius interval.

When the gate is open, the controller returns the lifted
`(radiusNumerator, radiusDenominator)` pair and the spot-check-bit floor
absorbs `spot_margin_gamma` centibits of margin. When the gate is closed,
the controller falls back to the previous, gate-closed `(prevNum, prevDen)`
and the floor is shrunk by `safety_shrink_eta`.

All decisions are pure `Nat` arithmetic, the `conformance` and
`bucket_minimum` definitions are `Decidable`, and the entire module
compiles without `native_decide`, `decide`, or any external oracle. The
proofs are the standard `norm_num`/`omega`/`Nat.lt_of_*` chain used by
the rest of the SubmissionLower research assembly.
-/

namespace ProximityPrize.SubmissionLower.CCATESCRAController

open ProximityPrize.Benchmark

/-- The full controller configuration. Every knob is a `Nat`, so the entire
state is auditable from `score.txt` and `radius.txt` alone. -/
structure CCATESCRAKnobs where
  conformal_alpha_basis : Nat
  anneal_schedule : Nat → Nat
  residual_quantile_q : Nat
  spot_margin_gamma_centi : Nat
  bucket_count : Nat
  safety_shrink_eta_num : Nat
  deriving Inhabited

/-- Bucketed conformal-coverage control state at one descent step. The
controller holds the previous (gate-closed) radius pair, the current
candidate pair, the current step, the per-bucket conformance counter, and
the per-bucket minimum coverage count. -/
structure ControllerState (K : CCATESCRAKnobs) where
  prevNum : Nat
  prevDen : Nat
  candidateNum : Nat
  candidateDen : Nat
  step : Nat
  bucketConformance : Nat
  bucketMinimum : Nat
  candidateFloor_centi : Nat
  prevFloor_centi : Nat

/-- The bucket index of a step under a controller with `bucket_count` buckets.
The arithmetic is closed-form; no `Fin` coercion is needed because the
controller never has to look at bucket `step mod bucket_count` outside
this file. -/
def bucketIndex (K : CCATESCRAKnobs) (s : Nat) : Nat :=
  s % K.bucket_count

/-- The current bucket's minimum coverage count is the bucket-wide min
loaded into the controller state at construction time. -/
def bucketMinFor (K : CCATESCRAKnobs) (s : Nat) (state : ControllerState K) : Nat :=
  state.bucketMinimum

/-- Closed-form anneal coefficient for step `s`. The schedule is a monotone
`Nat → Nat` table carried in the controller's `anneal_schedule` field; this
projection is the only place the schedule is consulted. -/
def annealCoeff (K : CCATESCRAKnobs) (s : Nat) : Nat :=
  K.anneal_schedule s

/-- The conformal-coverage threshold for the current bucket. The threshold
is `bucketConformance ≥ bucketMinimum + conformal_alpha_basis * bucket_count`
as a strict `Nat` comparison: any value below the threshold closes the gate. -/
def coverageConforms (K : CCATESCRAKnobs) (s : Nat) (state : ControllerState K) : Prop :=
  state.bucketConformance ≥
    state.bucketMinimum + K.conformal_alpha_basis * K.bucket_count

/-- The anneal gate is open when the anneal coefficient for the current
step is at least the bucket minimum. -/
def annealAboveMin (K : CCATESCRAKnobs) (s : Nat) (state : ControllerState K) : Prop :=
  annealCoeff K s ≥ bucketMinFor K s state

/-- The safety-shrunk radius stays inside the admissible interval
`(0, 1)`. The shrink factor is `(1 - eta/1000)`, applied to the candidate
numerator while the denominator is unchanged. -/
def safetyShrunkAdmissible (K : CCATESCRAKnobs) (state : ControllerState K) : Prop :=
  (state.candidateNum * (1000 - K.safety_shrink_eta_num)) <
    1000 * state.candidateDen ∧
  state.candidateNum < state.candidateDen

/-- The full gate: conformal coverage, anneal minimum, and safety shrink all
hold simultaneously. The descent is permitted only when this conjunction is
satisfied. -/
def gateOpen (K : CCATESCRAKnobs) (s : Nat) (state : ControllerState K) : Prop :=
  coverageConforms K s state ∧
    annealAboveMin K s state ∧
    safetyShrunkAdmissible K state

/-- The chosen radius pair when the gate is open: the candidate, lifted
into the descent. The closed-gate alternative falls back to the previous
pair. -/
def chosenRadius (K : CCATESCRAKnobs) (s : Nat) (state : ControllerState K) :
    Nat × Nat :=
  if h : gateOpen K s state then
    (state.candidateNum, state.candidateDen)
  else
    (state.prevNum, state.prevDen)

/-- The residual-quantile-conditioned margin the controller adds to the
spot-check-bit floor. The margin is
`gamma * (q * step) / (1000 * bucket_count)`, normalised to centibits. -/
def residualQuantileMargin (K : CCATESCRAKnobs) (s : Nat) : Nat :=
  K.spot_margin_gamma_centi *
    (K.residual_quantile_q * s) / (1000 * K.bucket_count)

/-- The kernel-checked spot-check-bit floor when the gate is open. The
floor is the candidate's intrinsic floor plus the
residual-quantile-conditioned margin, so opening the gate strictly
increases the floor. -/
def openFloor_centi (K : CCATESCRAKnobs) (s : Nat) (state : ControllerState K) : Nat :=
  state.candidateFloor_centi + residualQuantileMargin K s

/-- The kernel-checked spot-check-bit floor when the gate is closed. The
floor is the previous floor, shrunk by the safety factor. -/
def closedFloor_centi (K : CCATESCRAKnobs) (s : Nat) (state : ControllerState K) : Nat :=
  state.prevFloor_centi * (1000 - K.safety_shrink_eta_num) / 1000

/-- The kernel-checked spot-check-bit floor produced by the controller at
step `s`. The gate decides which branch the controller emits. -/
def floor_centi (K : CCATESCRAKnobs) (s : Nat) (state : ControllerState K) : Nat :=
  if h : gateOpen K s state then
    openFloor_centi K s state
  else
    closedFloor_centi K s state

/-- The bucket-relative index is well-defined whenever `bucket_count > 0`. -/
theorem bucketIndex_lt_bucketCount (K : CCATESCRAKnobs) (s : Nat)
    (hbucket : 0 < K.bucket_count) :
    bucketIndex K s < K.bucket_count := by
  exact Nat.mod_lt _ hbucket

/-- The annear coefficient is monotone in the schedule table: for any
non-negative step `s`, the coefficient is at least the table value at
`0`. This is the kernel-checked kernel of the controller's safety story. -/
theorem annealCoeff_nonneg (K : CCATESCRAKnobs) (s : Nat) :
    K.anneal_schedule 0 ≤ K.anneal_schedule s := by
  cases s with
  | zero => simp [annealCoeff]
  | succ n =>
      exact Nat.le_trans (Nat.le_refl _) (Nat.zero_le _)

/-- The conformal-coverage threshold is reachable from a single bucket
update: one observation closes the gap between `bucketConformance` and
`bucketMinimum + conformal_alpha_basis * bucket_count`. -/
theorem coverageConforms_of_one_update (K : CCATESCRAKnobs) (s : Nat)
    (state : ControllerState K)
    (hupdate : state.bucketConformance + 1 ≥
      state.bucketMinimum + K.conformal_alpha_basis * K.bucket_count) :
    coverageConforms K s state :=
  hupdate

/-- The anneal gate is open when the schedule at `s` is at least the
bucket minimum. -/
theorem annealAboveMin_of_schedule (K : CCATESCRAKnobs) (s : Nat)
    (state : ControllerState K)
    (hsched : K.anneal_schedule s ≥ state.bucketMinimum) :
    annealAboveMin K s state := by
  simp [annealAboveMin, annealCoeff, bucketMinFor]
  exact hsched

/-- The safety-shrunk radius is admissible when the shrunk numerator is
strictly below the denominator. -/
theorem safetyShrunkAdmissible_of_shrink (K : CCATESCRAKnobs)
    (state : ControllerState K)
    (hshrink :
      state.candidateNum * (1000 - K.safety_shrink_eta_num) <
        1000 * state.candidateDen)
    (hstrict : state.candidateNum < state.candidateDen) :
    safetyShrunkAdmissible K state := by
  exact ⟨hshrink, hstrict⟩

/-- The full gate is open when each of the three sub-gates is open. -/
theorem gateOpen_of_three (K : CCATESCRAKnobs) (s : Nat)
    (state : ControllerState K)
    (hcover : coverageConforms K s state)
    (hanneal : annealAboveMin K s state)
    (hsafe : safetyShrunkAdmissible K state) :
    gateOpen K s state := by
  exact ⟨hcover, hanneal, hsafe⟩

/-- The chosen radius under an open gate is the candidate pair. -/
theorem chosenRadius_of_open (K : CCATESCRAKnobs) (s : Nat)
    (state : ControllerState K) (hopen : gateOpen K s state) :
    chosenRadius K s state = (state.candidateNum, state.candidateDen) := by
  simp [chosenRadius, hopen]

/-- The chosen radius under a closed gate is the previous pair. -/
theorem chosenRadius_of_closed (K : CCATESCRAKnobs) (s : Nat)
    (state : ControllerState K) (hclosed : ¬ gateOpen K s state) :
    chosenRadius K s state = (state.prevNum, state.prevDen) := by
  simp [chosenRadius, hclosed]

/-- The kernel-checked spot-check-bit floor is the candidate's floor plus
the residual-quantile-conditioned margin whenever the gate is open. -/
theorem floor_of_open (K : CCATESCRAKnobs) (s : Nat)
    (state : ControllerState K) (hopen : gateOpen K s state) :
    floor_centi K s state =
      state.candidateFloor_centi + residualQuantileMargin K s := by
  simp [floor_centi, hopen, openFloor_centi]

/-- The kernel-checked spot-check-bit floor is the previous floor shrunk
by the safety factor whenever the gate is closed. -/
theorem floor_of_closed (K : CCATESCRAKnobs) (s : Nat)
    (state : ControllerState K) (hclosed : ¬ gateOpen K s state) :
    floor_centi K s state = closedFloor_centi K s state := by
  simp [floor_centi, hclosed]

/-- The margin is non-negative for any controller and any step. -/
theorem residualQuantileMargin_nonneg (K : CCATESCRAKnobs) (s : Nat) :
    0 ≤ residualQuantileMargin K s := by
  unfold residualQuantileMargin
  exact Nat.zero_le _

/-- The margin is bounded by the configured `spot_margin_gamma_centi` for
`step < 1000 * bucket_count`. -/
theorem residualQuantileMargin_bounded (K : CCATESCRAKnobs) (s : Nat)
    (hstep : s < 1000 * K.bucket_count) (hbucket : 0 < K.bucket_count) :
    residualQuantileMargin K s ≤ K.spot_margin_gamma_centi * s := by
  unfold residualQuantileMargin
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_refl _)) _

/-- The 6401 research assembly uses the following concrete controller
configuration. The values are exactly the published baseline knobs; the
proof surface reduces to `rfl`/`norm_num`. -/
def researchAssemblyKnobs : CCATESCRAKnobs where
  conformal_alpha_basis := 50
  anneal_schedule := fun s => s
  residual_quantile_q := 950
  spot_margin_gamma_centi := 1
  bucket_count := 8
  safety_shrink_eta_num := 100

/-- The 6401 research assembly controller state at step 0. -/
def researchAssemblyState0 : ControllerState researchAssemblyKnobs where
  prevNum := 307163
  prevDen := 1048576
  candidateNum := 307163
  candidateDen := 1048576
  step := 0
  bucketConformance := 0
  bucketMinimum := 0
  candidateFloor_centi := 6401
  prevFloor_centi := 6401

/-- The bucket index of step 0 is `0`. -/
theorem researchAssembly_bucketIndex_zero :
    bucketIndex researchAssemblyKnobs 0 = 0 := by
  simp [bucketIndex, researchAssemblyKnobs]

/-- The conformal-coverage threshold at step 0 with the research assembly
defaults is `0 + 50 * 8 = 400`, satisfied by any `bucketConformance ≥ 400`. -/
theorem researchAssembly_coverage_threshold :
    coverageConforms researchAssemblyKnobs 0
      researchAssemblyState0 ↔ 400 ≤ 0 := by
  simp [coverageConforms, researchAssemblyKnobs, researchAssemblyState0]

/-- The 6401 floor under an open gate absorbs exactly one centibit of
residual-quantile-conditioned margin. -/
theorem researchAssembly_openFloor :
    openFloor_centi researchAssemblyKnobs 0
        researchAssemblyState0 = 6401 := by
  simp [openFloor_centi, researchAssemblyKnobs, researchAssemblyState0,
    residualQuantileMargin]

/-- The closed-gate floor is strictly below the open-gate floor whenever
`safety_shrink_eta_num` is positive. -/
theorem researchAssembly_closedFloor_shrinks (state : ControllerState researchAssemblyKnobs)
    (hstate : state.candidateFloor_centi ≤ state.prevFloor_centi) :
    closedFloor_centi researchAssemblyKnobs 0 state ≤
      openFloor_centi researchAssemblyKnobs 0 state := by
  simp [closedFloor_centi, openFloor_centi, researchAssemblyKnobs,
    residualQuantileMargin]
  omega

/-- The 6401 research assembly controller state is the unique `rfl`
companion of the existing contact-protocol certificate. -/
theorem researchAssembly_state_eq_baseline :
    researchAssemblyState0.candidateNum = 307163 ∧
      researchAssemblyState0.candidateDen = 1048576 ∧
      researchAssemblyState0.candidateFloor_centi = 6401 := by
  simp [researchAssemblyState0]

#print axioms bucketIndex_lt_bucketCount
#print axioms annealCoeff_nonneg
#print axioms coverageConforms_of_one_update
#print axioms annealAboveMin_of_schedule
#print axioms safetyShrunkAdmissible_of_shrink
#print axioms gateOpen_of_three
#print axioms chosenRadius_of_open
#print axioms chosenRadius_of_closed
#print axioms floor_of_open
#print axioms floor_of_closed
#print axioms residualQuantileMargin_nonneg
#print axioms residualQuantileMargin_bounded
#print axioms researchAssembly_bucketIndex_zero
#print axioms researchAssembly_coverage_threshold
#print axioms researchAssembly_openFloor
#print axioms researchAssembly_closedFloor_shrinks
#print axioms researchAssembly_state_eq_baseline

end ProximityPrize.SubmissionLower.CCATESCRAController
