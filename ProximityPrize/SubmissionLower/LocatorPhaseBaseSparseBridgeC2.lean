import ProximityPrize.SubmissionLower.LocatorPhaseBaseC2

/-!
# Sparse base-candidate bridge

The carrier objective is coordinatewise discretely convex.  Consequently a
split of the total `R` coordinate is bounded by one of the two positive
endpoints, and (away from the two hybrid-boundary layers) the same is true of
the `V` coordinate.  This reduces the finite receipt from every carrier to

* the aggregate carrier itself; and
* `r = 1` or `r = R - 1`, with
  `v ∈ {0, 1, 2, V - 2, V - 1, V}`.

The definitions below deliberately separate the generic convexity argument
from the concrete arithmetic proof of the four shape fields.  Only boundary carrier rows remain in the benchmark box (at most 13 for one `(R,V)`).
-/

namespace ProximityPrize.SubmissionLower.LocatorPhaseBaseSparseBridgeC2

open LocatorPhase6802Oracle LocatorPhaseBaseC2 LocatorArbitraryPowerAvoidance
open LocatorOrdinaryZConvexC2

set_option autoImplicit false
set_option maxRecDepth 100000

def forwardDiff (f : ℕ → ℕ) (n : ℕ) : ℕ := f (n + 1) - f n

/-- The two positive endpoints of an `R` split, together with the unsplit
aggregate carrier. -/
def RBoundary (R r : ℕ) : Prop := r = R ∨ r = 1 ∨ r + 1 = R

/-- The only `V` values left after applying convexity on the shifted interior
`v ≥ 2`, `V-v ≥ 2`. -/
def VBoundary (V v : ℕ) : Prop := v ≤ 2 ∨ V ≤ v + 2

/-- Monotonicity restricted to the finite prefix `0, ..., N`. -/
def StepMonotone (f : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n, n < N → f n ≤ f (n + 1)

/-- Midpoint convexity restricted to the finite prefix `0, ..., N`. -/
def StepConvex (f : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n, n + 2 ≤ N → 2 * f (n + 1) ≤ f n + f (n + 2)

theorem forwardDiff_mono_bounded (f : ℕ → ℕ) (N n : ℕ)
    (hm : StepMonotone f N) (hc : StepConvex f N)
    (hn : n + 2 ≤ N) :
    forwardDiff f n ≤ forwardDiff f (n + 1) := by
  have h₀ := hm n (by omega)
  have h₁ := hm (n + 1) (by omega)
  have h₂ := hc n hn
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem move_one_right_bounded (f g : ℕ → ℕ) (N : ℕ)
    (hf : StepMonotone f N) (hg : StepMonotone g N)
    (a b : ℕ) (ha : a < N) (hb : b < N)
    (hcross : forwardDiff f a ≤ forwardDiff g b) :
    f (a + 1) + g b ≤ f a + g (b + 1) := by
  have hfa := hf a ha
  have hgb := hg b hb
  unfold forwardDiff at hcross
  omega

theorem transfer_all_right_bounded
    (f g : ℕ → ℕ) (N : ℕ)
    (hf : StepMonotone f N) (hg : StepMonotone g N)
    (hcf : StepConvex f N) (hcg : StepConvex g N) :
    ∀ a b, a + 1 + b ≤ N → forwardDiff f a ≤ forwardDiff g b →
      f (a + 1) + g b ≤ f 0 + g (a + 1 + b) := by
  intro a
  induction a with
  | zero =>
      intro b hbound hcross
      simpa only [Nat.zero_add, Nat.add_comm] using
        move_one_right_bounded f g N hf hg 0 b (by omega) (by omega) hcross
  | succ a ih =>
      intro b hbound hcross
      have hdf : forwardDiff f a ≤ forwardDiff f (a + 1) :=
        forwardDiff_mono_bounded f N a hf hcf (by omega)
      have hdg : forwardDiff g b ≤ forwardDiff g (b + 1) :=
        forwardDiff_mono_bounded g N b hg hcg (by omega)
      have hcross' : forwardDiff f a ≤ forwardDiff g (b + 1) :=
        hdf.trans (hcross.trans hdg)
      calc
        f (a + 1 + 1) + g b ≤ f (a + 1) + g (b + 1) :=
          move_one_right_bounded f g N hf hg (a + 1) b
            (by omega) (by omega) hcross
        _ ≤ f 0 + g (a + 1 + (b + 1)) := ih (b + 1) (by omega) hcross'
        _ = f 0 + g (a + 1 + 1 + b) := by
          rw [show a + 1 + (b + 1) = a + 1 + 1 + b by omega]

/-- Finite-prefix version of `two_discreteConvex_endpoint`. -/
theorem two_discreteConvex_endpoint_bounded
    (f g : ℕ → ℕ) (N : ℕ)
    (hf : StepMonotone f N) (hg : StepMonotone g N)
    (hcf : StepConvex f N) (hcg : StepConvex g N)
    (a b : ℕ) (hbound : a + b ≤ N) :
    f a + g b ≤ max (f (a + b) + g 0) (f 0 + g (a + b)) := by
  rcases a with _ | a
  · simpa only [Nat.zero_add] using
      (le_max_right (f b + g 0) (f 0 + g b))
  rcases b with _ | b
  · simpa only [Nat.add_zero] using
      (le_max_left (f (a + 1) + g 0) (f 0 + g (a + 1)))
  have hdf (n : ℕ) (hn : n + 2 ≤ N) :
      forwardDiff f n ≤ forwardDiff f (n + 1) :=
    forwardDiff_mono_bounded f N n hf hcf hn
  have hdg (n : ℕ) (hn : n + 2 ≤ N) :
      forwardDiff g n ≤ forwardDiff g (n + 1) :=
    forwardDiff_mono_bounded g N n hg hcg hn
  by_cases hcross : forwardDiff f a ≤ forwardDiff g (b + 1)
  · have h := transfer_all_right_bounded f g N hf hg hcf hcg
      a (b + 1) (by omega) hcross
    exact h.trans (le_max_right _ _)
  · have hcross' : forwardDiff g b ≤ forwardDiff f (a + 1) :=
      (hdg b (by omega)).trans
        ((Nat.lt_of_not_ge hcross).le.trans (hdf a (by omega)))
    have h := transfer_all_right_bounded g f N hg hf hcg hcf
      b (a + 1) (by omega) hcross'
    have h' : f (a + 1) + g (b + 1) ≤
        f ((a + 1) + (b + 1)) + g 0 := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    exact h'.trans (le_max_left _ _)

/-- Coordinate-shape facts used by the sparse bridge.  The shifts avoid the
padding/hybrid branch boundaries at `r = 1` and `v = 0,1`.  The zero-cost
function is abstract on purpose: the concrete proof uses a total closed-form
model, avoiding the out-of-range default of a finite receipt array. -/
structure CoordinateShape (zero : ℕ → ℕ → ℕ) : Prop where
  rawMonoR : ∀ v z n, n + 2 ≤ 29 → n + 2 + v ≤ 132 →
    rawCost (n + 1) v z ≤ rawCost (n + 2) v z
  rawConvexR : ∀ v z n, n + 3 ≤ 29 → n + 3 + v ≤ 132 →
    2 * rawCost (n + 2) v z ≤ rawCost (n + 1) v z + rawCost (n + 3) v z
  zeroMonoR : ∀ v n, n + 2 ≤ 29 → n + 2 + v ≤ 132 →
    zero (n + 1) v ≤ zero (n + 2) v
  zeroConvexR : ∀ v n, n + 3 ≤ 29 → n + 3 + v ≤ 132 →
    2 * zero (n + 2) v ≤ zero (n + 1) v + zero (n + 3) v
  rawMonoV2 : ∀ r z n, 1 ≤ r → r ≤ 29 → r + (n + 3) ≤ 132 →
    rawCost r (n + 2) z ≤ rawCost r (n + 3) z
  rawConvexV2 : ∀ r z n, 1 ≤ r → r ≤ 29 → r + (n + 4) ≤ 132 →
    2 * rawCost r (n + 3) z ≤ rawCost r (n + 2) z + rawCost r (n + 4) z
  zeroMonoV2 : ∀ r n, 1 ≤ r → r ≤ 29 → r + (n + 3) ≤ 132 →
    zero r (n + 2) ≤ zero r (n + 3)
  zeroConvexV2 : ∀ r n, 1 ≤ r → r ≤ 29 → r + (n + 4) ≤ 132 →
    2 * zero r (n + 3) ≤ zero r (n + 2) + zero r (n + 4)

/-- Only boundary carriers need a numerical `CandidateRowCheck`. -/
def SparseCandidateChecks (rows : ℕ → ℕ → BaseRow) : Prop :=
  ∀ R V r v,
    1 ≤ r → r ≤ R → v ≤ V → R ≤ 29 → R + V ≤ 132 →
    (r < R ∨ v = V) → RBoundary R r → VBoundary V v →
      CandidateRowCheck rows R V r v

/-- Convexity in the positive `R` split. -/
theorem splitR_le_endpoints (zero : ℕ → ℕ → ℕ)
    (shape : CoordinateShape zero) (a b v w z : ℕ)
    (hR : a + b + 2 ≤ 29)
    (hraw : a + b + 2 + v ≤ 132)
    (hzero : a + b + 2 + w ≤ 132) :
    rawCost (a + 1) v z + zero (b + 1) w ≤
      max
        (rawCost (a + b + 1) v z + zero 1 w)
        (rawCost 1 v z + zero (a + b + 1) w) := by
  apply two_discreteConvex_endpoint_bounded
    (fun n => rawCost (n + 1) v z)
    (fun n => zero (n + 1) w)
    (a + b)
  · intro n hn
    exact shape.rawMonoR v z n (by omega) (by omega)
  · intro n hn
    exact shape.zeroMonoR w n (by omega) (by omega)
  · intro n hn
    exact shape.rawConvexR v z n (by omega) (by omega)
  · intro n hn
    exact shape.zeroConvexR w n (by omega) (by omega)
  · omega

/-- Convexity on the interior `V` split, shifted past `v = 0,1`. -/
theorem splitV_le_endpoints (zero : ℕ → ℕ → ℕ)
    (shape : CoordinateShape zero) (r s a b z : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hr28 : r ≤ 29) (hs28 : s ≤ 29)
    (hraw : r + (a + b + 4) ≤ 132)
    (hzero : s + (a + b + 4) ≤ 132) :
    rawCost r (a + 2) z + zero s (b + 2) ≤
      max
        (rawCost r (a + b + 2) z + zero s 2)
        (rawCost r 2 z + zero s (a + b + 2)) := by
  apply two_discreteConvex_endpoint_bounded
    (fun n => rawCost r (n + 2) z)
    (fun n => zero s (n + 2))
    (a + b)
  · intro n hn
    exact shape.rawMonoV2 r z n hr hr28 (by omega)
  · intro n hn
    exact shape.zeroMonoV2 s n hs hs28 (by omega)
  · intro n hn
    exact shape.rawConvexV2 r z n hr hr28 (by omega)
  · intro n hn
    exact shape.zeroConvexV2 s n hs hs28 (by omega)
  · omega

/-- Pointwise Bellman inequality reconstructed from the sparse carrier set. -/
theorem candidate_le_of_sparse (rows : ℕ → ℕ → BaseRow)
    (zero : ℕ → ℕ → ℕ) (shape : CoordinateShape zero)
    (zero_eq : ∀ r v, r ≤ 29 → r + v ≤ 132 →
      zero r v = baseZeroCap rows r v)
    (checks : SparseCandidateChecks rows)
    (R V r v z : ℕ)
    (hr : 1 ≤ r) (hrR : r ≤ R) (hvV : v ≤ V)
    (hR28 : R ≤ 29) (hRV : R + V ≤ 132)
    (hcandidate : r < R ∨ v = V) :
    rawCost r v z + baseZeroCap rows (R - r) (V - v) ≤
      LocatorPhaseBaseC2.baseTableCap rows (rawFlag R V z) := by
  have sparseSound (r₀ v₀ : ℕ)
      (hr₀ : 1 ≤ r₀) (hr₀R : r₀ ≤ R) (hv₀V : v₀ ≤ V)
      (hc₀ : r₀ < R ∨ v₀ = V)
      (hRb : RBoundary R r₀) (hVb : VBoundary V v₀) :
      rawCost r₀ v₀ z + zero (R - r₀) (V - v₀) ≤
        LocatorPhaseBaseC2.baseTableCap rows (rawFlag R V z) := by
    rw [zero_eq (R - r₀) (V - v₀) (by omega) (by omega)]
    exact candidateRowCheck_sound rows R V r₀ v₀ z hr₀
      (checks R V r₀ v₀ hr₀ hr₀R hv₀V hR28 hRV hc₀ hRb hVb)

  rw [← zero_eq (R - r) (V - v) (by omega) (by omega)]
  by_cases hself : r = R
  · have hvself : v = V := by rcases hcandidate with hlt | heq <;> omega
    subst r
    subst v
    simpa using sparseSound R V hr (le_rfl) (le_rfl) (Or.inr rfl)
      (Or.inl rfl) (Or.inr (by omega))
  · have hrlt : r < R := lt_of_le_of_ne hrR hself
    obtain ⟨a, haSucc⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    have ha : r = a + 1 := by omega
    obtain ⟨b, hbSucc⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.sub_pos_of_lt hrlt))
    have hb : R - r = b + 1 := by omega
    have hRsum : R = a + b + 2 := by omega

    have endpointV (r₀ s₀ : ℕ)
        (hr₀ : 1 ≤ r₀) (hs₀ : 1 ≤ s₀)
        (hsum : r₀ + s₀ = R)
        (hRb : RBoundary R r₀) :
        rawCost r₀ v z + zero s₀ (V - v) ≤
          LocatorPhaseBaseC2.baseTableCap rows (rawFlag R V z) := by
      have hr₀R : r₀ ≤ R := by omega
      have hr₀lt : r₀ < R := by omega
      by_cases hvLow : v ≤ 2
      · simpa [show R - r₀ = s₀ by omega] using
          sparseSound r₀ v hr₀ hr₀R hvV (Or.inl hr₀lt) hRb (Or.inl hvLow)
      by_cases hwLow : V - v ≤ 2
      · have hnear : V ≤ v + 2 := by omega
        simpa [show R - r₀ = s₀ by omega] using
          sparseSound r₀ v hr₀ hr₀R hvV (Or.inl hr₀lt) hRb (Or.inr hnear)
      · obtain ⟨c, hcAdd⟩ := Nat.exists_eq_add_of_le (show 2 ≤ v by omega)
        have hc : v = c + 2 := by omega
        obtain ⟨d, hdAdd⟩ :=
          Nat.exists_eq_add_of_le (show 2 ≤ V - v by omega)
        have hd : V - v = d + 2 := by omega
        have hVsum : V = c + d + 4 := by omega
        have hleft :
            rawCost r₀ (c + d + 2) z + zero s₀ 2 ≤
              LocatorPhaseBaseC2.baseTableCap rows (rawFlag R V z) := by
          have hv' : c + d + 2 ≤ V := by omega
          have hnear : V ≤ (c + d + 2) + 2 := by omega
          simpa [show R - r₀ = s₀ by omega, show V - (c + d + 2) = 2 by omega]
            using sparseSound r₀ (c + d + 2) hr₀ hr₀R hv'
              (Or.inl hr₀lt) hRb (Or.inr hnear)
        have hright :
            rawCost r₀ 2 z + zero s₀ (c + d + 2) ≤
              LocatorPhaseBaseC2.baseTableCap rows (rawFlag R V z) := by
          have hv' : 2 ≤ V := by omega
          simpa [show R - r₀ = s₀ by omega, show V - 2 = c + d + 2 by omega]
            using sparseSound r₀ 2 hr₀ hr₀R hv'
              (Or.inl hr₀lt) hRb (Or.inl (by omega))
        have hsplit := splitV_le_endpoints zero shape r₀ s₀ c d z
          hr₀ hs₀ (by omega) (by omega) (by omega) (by omega)
        rw [← hc, ← hd] at hsplit
        exact hsplit.trans (max_le hleft hright)

    have hleft :
        rawCost (a + b + 1) v z + zero 1 (V - v) ≤
          LocatorPhaseBaseC2.baseTableCap rows (rawFlag R V z) := by
      apply endpointV (a + b + 1) 1 (by omega) (by omega) (by omega)
      exact Or.inr (Or.inr (by omega))
    have hright :
        rawCost 1 v z + zero (a + b + 1) (V - v) ≤
          LocatorPhaseBaseC2.baseTableCap rows (rawFlag R V z) := by
      apply endpointV 1 (a + b + 1) (by omega) (by omega) (by omega)
      exact Or.inr (Or.inl rfl)
    have hsplit := splitR_le_endpoints zero shape a b v (V - v) z
      (by omega) (by omega) (by omega)
    rw [← ha, ← hb] at hsplit
    exact hsplit.trans (max_le hleft hright)

/-- Sparse coordinate checks imply the complete Bellman table condition. -/
theorem baseCandidatesSound_of_sparse (rows : ℕ → ℕ → BaseRow)
    (zero : ℕ → ℕ → ℕ) (shape : CoordinateShape zero)
    (zero_eq : ∀ r v, r ≤ 29 → r + v ≤ 132 →
      zero r v = baseZeroCap rows r v)
    (checks : SparseCandidateChecks rows) :
    BaseCandidatesSound rows := by
  intro R V r v z hr hrR hvV hR28 hRV hcandidate _hz
  exact candidate_le_of_sparse rows zero shape zero_eq checks R V r v z
    hr hrR hvV hR28 hRV hcandidate

end ProximityPrize.SubmissionLower.LocatorPhaseBaseSparseBridgeC2
