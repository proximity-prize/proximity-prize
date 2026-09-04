import ProximityPrize.SubmissionLower.PackedLocatorTail1

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Concrete. -/
section PackedLocator_LocatorPhase6800Concrete

/-!
# Executable interpretation of the compact 6800 receipts

The generated threshold and prefix rows are distributed by global row index
modulo eight.  This module gives constant-time strided lookups and defines the
small finite predicates checked by the receipt shards.  In particular, the
ordinary base cap is forced to zero away from the actual narrow state box.
This is essential at raw slope zero: `baseRowIndex 0 _` is not a meaningful
table index, while a slope-zero subfamily is necessarily empty.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Concrete

open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle LocatorPhase6800Audit
open LocatorPhase6800ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## Zero-safe base cap -/

def NarrowState (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ p.all ≤ 29 ∧ middle p ≤ 135 ∧ total p ≤ 6677

instance (p : FlagDegree) : Decidable (NarrowState p) := by
  unfold NarrowState
  infer_instance

def checkedBaseCap (p : FlagDegree) : ℕ :=
  if NarrowState p then LocatorPhase6800BaseDirectData.cap p else 0

@[simp] theorem checkedBaseCap_of_narrow {p : FlagDegree}
    (hp : NarrowState p) :
    checkedBaseCap p = LocatorPhase6800BaseDirectData.cap p := by
  simp only [checkedBaseCap, if_pos hp]

@[simp] theorem checkedBaseCap_of_not_narrow {p : FlagDegree}
    (hp : ¬ NarrowState p) : checkedBaseCap p = 0 := by
  simp only [checkedBaseCap, if_neg hp]

@[simp] theorem checkedBaseCap_zero (v z : ℕ) :
    checkedBaseCap (rawFlag 0 v z) = 0 := by
  apply checkedBaseCap_of_not_narrow
  simp [NarrowState]

theorem checkedBaseCap_eq_zero_of_all_eq_zero {p : FlagDegree}
    (hp : p.all = 0) : checkedBaseCap p = 0 := by
  apply checkedBaseCap_of_not_narrow
  intro hnarrow
  rcases hnarrow with ⟨hpos, _, _, _⟩
  omega

theorem checkedBaseCap_sound : StateLocalBaseOracleSound checkedBaseCap := by
  intro ι _ s p hpositive hslope hmiddle htotal
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi⟩ := hs
    have hiSum : (p i).all ≤ ∑ j ∈ s, (p j).all := by
      exact Finset.single_le_sum
        (f := fun j ↦ (p j).all) (fun _ _ ↦ Nat.zero_le _) hi
    have haggPositive : 1 ≤ (sumFlag s p).all := by
      rw [sumFlag_all]
      exact (hpositive i hi).trans hiSum
    have hnarrow : NarrowState (sumFlag s p) :=
      ⟨haggPositive, hslope, hmiddle, htotal⟩
    rw [checkedBaseCap_of_narrow hnarrow]
    exact LocatorPhase6800BaseSparseChecked.stateLocalSound s p hpositive
      hslope hmiddle htotal
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [checkedBaseCap, NarrowState, sumFlag]

/-! ## Executable threshold recurrence -/

def fastApply (previous : FlagDegree → ℕ) (q : Potential)
    (threshold : ℕ → ℕ → ℕ) (pref : FlagDegree → ℕ)
    (p : FlagDegree) : ℕ :=
  if threshold p.all p.yz ≤ p.zOnly then
    min (previous p) (q.eval p + parentDefect pref p)
  else previous p

def fastAfterR : FlagDegree → ℕ :=
  fastApply checkedBaseCap r1200Potential rThreshold rPrefix

def fastAfterC : FlagDegree → ℕ :=
  fastApply fastAfterR sourceCPotential cThreshold cPrefix

def fastAfterF500 : FlagDegree → ℕ :=
  fastApply fastAfterC split500Potential f500Threshold f500Prefix

def fastAfterS1200 : FlagDegree → ℕ :=
  fastApply fastAfterF500 split1200Potential s1200Threshold s1200Prefix

def fastAfterS390 : FlagDegree → ℕ :=
  fastApply fastAfterS1200 split390Potential s390Threshold s390Prefix

/-- The exact numerical obligations for one positive raw-slope layer.  Each
state checks all four terminal inequalities, the narrow maximum, and the
correlated initial-A complement. -/
def PhaseStateRCheck (R : ℕ) : Prop :=
  ∀ V ∈ List.range (136 - R),
    ∀ z ∈ List.range (6678 - (R + V)),
      let p := rawFlag R V z
      (rThreshold R V ≤ z ∨
        checkedBaseCap p ≤ r1200Potential.eval p + rPrefix p) ∧
      (cThreshold R V ≤ z ∨
        fastAfterR p ≤ sourceCPotential.eval p + cPrefix p) ∧
      (f500Threshold R V ≤ z ∨
        fastAfterC p ≤ split500Potential.eval p + f500Prefix p) ∧
      (s1200Threshold R V ≤ z ∨
        fastAfterF500 p ≤ split1200Potential.eval p + s1200Prefix p) ∧
      (s390Threshold R V ≤ z ∨
        fastAfterS1200 p ≤ split390Potential.eval p + s390Prefix p) ∧
      fastAfterS390 p ≤ certifiedNarrowMaximum ∧
      fastAfterS390 p + initialAComplement p ≤ certifiedJointMaximum

instance (R : ℕ) : Decidable (PhaseStateRCheck R) := by
  unfold PhaseStateRCheck
  infer_instance

def PhaseStateChecks : Prop :=
  ∀ R ∈ List.range 30, 1 ≤ R → PhaseStateRCheck R

instance : Decidable PhaseStateChecks := by
  unfold PhaseStateChecks
  infer_instance

/-! ## Semantic extraction from the finite predicates -/

theorem threshold_indexed_at (h : ThresholdsIndexed)
    (R V : ℕ) (hR : 1 ≤ R) (hR28 : R ≤ 29) (hRV : R + V ≤ 135) :
    let q := lookupThreshold R V
    q.r = R ∧ q.v = V ∧ ThresholdSufficient q := by
  apply h R
  · exact List.mem_range.mpr (by omega)
  · exact hR
  · exact List.mem_range.mpr (by omega)

theorem prefix_indexed_at (h : PrefixesIndexed)
    (R V : ℕ) (hR : 1 ≤ R) (hR27 : R ≤ 28)
    (hRV : R + 1 + V ≤ 135) :
    let q := lookupPrefix R V
    q.afterR = R ∧ q.v = V ∧ q.ExpectedShape := by
  apply h R
  · exact List.mem_range.mpr (by omega)
  · exact hR
  · exact List.mem_range.mpr (by omega)

private theorem routeable_of_threshold_field
    (hindex : ThresholdsIndexed) (s : SourceNumbers)
    (field : ThresholdReceipt → ℕ)
    (hfield : ∀ q, ThresholdSufficient q →
      SourceThresholdSufficient s q.r q.v (field q))
    (hsourceCap : 6677 ≤ s.totalCap)
    (p : FlagDegree) (hp : NarrowState p) :
    field (lookupThreshold p.all p.yz) ≤ p.zOnly → s.Routeable p := by
  rcases hp with ⟨hr, hr28, hy, ht⟩
  have hry : p.all + p.yz ≤ 135 := by
    simpa only [middle, Nat.add_comm] using hy
  have hrow := threshold_indexed_at hindex p.all p.yz hr hr28 hry
  have hsufficient :
      SourceThresholdSufficient s p.all p.yz
        (field (lookupThreshold p.all p.yz)) := by
    have hs := hfield (lookupThreshold p.all p.yz) hrow.2.2
    rw [hrow.1, hrow.2.1] at hs
    exact hs
  intro hthreshold
  rcases hsufficient with hout | hroute
  · have hz : p.zOnly ≤ 6677 - (p.all + p.yz) := by
      simp only [total] at ht
      omega
    omega
  · have hcap : p.all + p.yz + p.zOnly ≤ s.totalCap := by
      simpa only [total, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        ht.trans hsourceCap
    have hmono := routeable_raw_mono_z s hthreshold hcap hroute
    simpa only [rawFlag] using hmono

theorem routeableR_of_cutoff (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) :
    rThreshold p.all p.yz ≤ p.zOnly → sourceR1200.Routeable p := by
  exact routeable_of_threshold_field h sourceR1200 ThresholdReceipt.r1200
    (fun q hq ↦ hq.2.2.2.1) (by decide) p hp

theorem routeableC_of_cutoff (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) :
    cThreshold p.all p.yz ≤ p.zOnly → sourceC.Routeable p := by
  exact routeable_of_threshold_field h sourceC ThresholdReceipt.sourceC
    (fun q hq ↦ hq.2.2.2.2.1) (by decide) p hp

theorem routeableF500_of_cutoff (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) :
    f500Threshold p.all p.yz ≤ p.zOnly → sourceSplit500.Routeable p := by
  exact routeable_of_threshold_field h sourceSplit500 ThresholdReceipt.split500
    (fun q hq ↦ hq.2.2.2.2.2.1) (by decide) p hp

theorem routeableS1200_of_cutoff (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) :
    s1200Threshold p.all p.yz ≤ p.zOnly → sourceSplit1200.Routeable p := by
  exact routeable_of_threshold_field h sourceSplit1200 ThresholdReceipt.split1200
    (fun q hq ↦ hq.2.2.2.2.2.2.1) (by decide) p hp

theorem routeableS390_of_cutoff (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) :
    s390Threshold p.all p.yz ≤ p.zOnly → sourceSplit390.Routeable p := by
  exact routeable_of_threshold_field h sourceSplit390 ThresholdReceipt.split390
    (fun q hq ↦ hq.2.2.2.2.2.2.2) (by decide) p hp

def afterR : FlagDegree → ℕ :=
  applyPhase checkedBaseCap r1200Potential sourceR1200.Routeable rPrefix

def afterC : FlagDegree → ℕ :=
  applyPhase afterR sourceCPotential sourceC.Routeable cPrefix

def afterF500 : FlagDegree → ℕ :=
  applyPhase afterC split500Potential sourceSplit500.Routeable f500Prefix

def afterS1200 : FlagDegree → ℕ :=
  applyPhase afterF500 split1200Potential sourceSplit1200.Routeable s1200Prefix

def afterS390 : FlagDegree → ℕ :=
  applyPhase afterS1200 split390Potential sourceSplit390.Routeable s390Prefix

private theorem applyPhase_eq_zero
    (previous : FlagDegree → ℕ) (q : Potential) (s : SourceNumbers)
    (pref : FlagDegree → ℕ) (p : FlagDegree)
    (hzero : previous p = 0) :
    applyPhase previous q s.Routeable pref p = 0 := by
  unfold applyPhase
  split <;> simp [hzero]

theorem afterR_eq_zero_of_not_narrow {p : FlagDegree} (hp : ¬ NarrowState p) :
    afterR p = 0 := by
  exact applyPhase_eq_zero checkedBaseCap r1200Potential sourceR1200 rPrefix p
    (checkedBaseCap_of_not_narrow hp)

theorem afterC_eq_zero_of_not_narrow {p : FlagDegree} (hp : ¬ NarrowState p) :
    afterC p = 0 := by
  exact applyPhase_eq_zero afterR sourceCPotential sourceC cPrefix p
    (afterR_eq_zero_of_not_narrow hp)

theorem afterF500_eq_zero_of_not_narrow {p : FlagDegree} (hp : ¬ NarrowState p) :
    afterF500 p = 0 := by
  exact applyPhase_eq_zero afterC split500Potential sourceSplit500 f500Prefix p
    (afterC_eq_zero_of_not_narrow hp)

theorem afterS1200_eq_zero_of_not_narrow {p : FlagDegree} (hp : ¬ NarrowState p) :
    afterS1200 p = 0 := by
  exact applyPhase_eq_zero afterF500 split1200Potential sourceSplit1200 s1200Prefix p
    (afterF500_eq_zero_of_not_narrow hp)

theorem afterS390_eq_zero_of_not_narrow {p : FlagDegree} (hp : ¬ NarrowState p) :
    afterS390 p = 0 := by
  exact applyPhase_eq_zero afterS1200 split390Potential sourceSplit390 s390Prefix p
    (afterS1200_eq_zero_of_not_narrow hp)

theorem applyPhase_le_fastApply
    (previous fastPrevious : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (threshold : ℕ → ℕ → ℕ) (pref : FlagDegree → ℕ)
    (p : FlagDegree) (hprevious : previous p ≤ fastPrevious p)
    (hroute : threshold p.all p.yz ≤ p.zOnly → routeable p) :
    applyPhase previous q routeable pref p ≤
      fastApply fastPrevious q threshold pref p := by
  unfold applyPhase fastApply
  by_cases ht : threshold p.all p.yz ≤ p.zOnly
  · rw [if_pos ht, if_pos (hroute ht)]
    exact min_le_min hprevious le_rfl
  · rw [if_neg ht]
    split
    · exact (min_le_left _ _).trans hprevious
    · exact hprevious

theorem afterR_le_fast (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) : afterR p ≤ fastAfterR p := by
  exact applyPhase_le_fastApply checkedBaseCap checkedBaseCap
    r1200Potential sourceR1200.Routeable rThreshold rPrefix p le_rfl
    (routeableR_of_cutoff h p hp)

theorem afterC_le_fast (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) : afterC p ≤ fastAfterC p := by
  exact applyPhase_le_fastApply afterR fastAfterR sourceCPotential
    sourceC.Routeable cThreshold cPrefix p (afterR_le_fast h p hp)
    (routeableC_of_cutoff h p hp)

theorem afterF500_le_fast (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) : afterF500 p ≤ fastAfterF500 p := by
  exact applyPhase_le_fastApply afterC fastAfterC split500Potential
    sourceSplit500.Routeable f500Threshold f500Prefix p
    (afterC_le_fast h p hp) (routeableF500_of_cutoff h p hp)

theorem afterS1200_le_fast (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) : afterS1200 p ≤ fastAfterS1200 p := by
  exact applyPhase_le_fastApply afterF500 fastAfterF500 split1200Potential
    sourceSplit1200.Routeable s1200Threshold s1200Prefix p
    (afterF500_le_fast h p hp) (routeableS1200_of_cutoff h p hp)

theorem afterS390_le_fast (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) : afterS390 p ≤ fastAfterS390 p := by
  exact applyPhase_le_fastApply afterS1200 fastAfterS1200 split390Potential
    sourceSplit390.Routeable s390Threshold s390Prefix p
    (afterS1200_le_fast h p hp) (routeableS390_of_cutoff h p hp)

theorem phase_state_checked_at (h : PhaseStateChecks) (p : FlagDegree)
    (hp : NarrowState p) :
    (rThreshold p.all p.yz ≤ p.zOnly ∨
        checkedBaseCap p ≤ r1200Potential.eval p + rPrefix p) ∧
    (cThreshold p.all p.yz ≤ p.zOnly ∨
        fastAfterR p ≤ sourceCPotential.eval p + cPrefix p) ∧
    (f500Threshold p.all p.yz ≤ p.zOnly ∨
        fastAfterC p ≤ split500Potential.eval p + f500Prefix p) ∧
    (s1200Threshold p.all p.yz ≤ p.zOnly ∨
        fastAfterF500 p ≤ split1200Potential.eval p + s1200Prefix p) ∧
    (s390Threshold p.all p.yz ≤ p.zOnly ∨
        fastAfterS1200 p ≤ split390Potential.eval p + s390Prefix p) ∧
    fastAfterS390 p ≤ certifiedNarrowMaximum ∧
    fastAfterS390 p + initialAComplement p ≤ certifiedJointMaximum := by
  rcases hp with ⟨hr, hr28, hy, ht⟩
  have hry : p.all + p.yz ≤ 135 := by
    simpa only [middle, Nat.add_comm] using hy
  have hrz : p.all + p.yz + p.zOnly ≤ 6677 := by
    simpa only [total, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
  have hR := h p.all (List.mem_range.mpr (by omega)) hr
  have hV : p.yz ∈ List.range (136 - p.all) :=
    List.mem_range.mpr (by omega)
  have hZ : p.zOnly ∈ List.range (6678 - (p.all + p.yz)) :=
    List.mem_range.mpr (by omega)
  simpa only [rawFlag] using hR p.yz hV p.zOnly hZ

theorem r_terminal (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks) :
    ∀ p, ¬ sourceR1200.Routeable p →
      checkedBaseCap p ≤ r1200Potential.eval p + rPrefix p := by
  intro p hn
  by_cases hp : NarrowState p
  · have hs := (phase_state_checked_at hstate p hp).1
    exact hs.resolve_left (fun hz ↦ hn (routeableR_of_cutoff hindex p hp hz))
  · rw [checkedBaseCap_of_not_narrow hp]
    exact Nat.zero_le _

theorem c_terminal (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks) :
    ∀ p, ¬ sourceC.Routeable p →
      afterR p ≤ sourceCPotential.eval p + cPrefix p := by
  intro p hn
  by_cases hp : NarrowState p
  · have hs := (phase_state_checked_at hstate p hp).2.1
    exact (afterR_le_fast hindex p hp).trans
      (hs.resolve_left (fun hz ↦ hn (routeableC_of_cutoff hindex p hp hz)))
  · rw [afterR_eq_zero_of_not_narrow hp]
    exact Nat.zero_le _

theorem f500_terminal (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks) :
    ∀ p, ¬ sourceSplit500.Routeable p →
      afterC p ≤ split500Potential.eval p + f500Prefix p := by
  intro p hn
  by_cases hp : NarrowState p
  · have hs := (phase_state_checked_at hstate p hp).2.2.1
    exact (afterC_le_fast hindex p hp).trans
      (hs.resolve_left
        (fun hz ↦ hn (routeableF500_of_cutoff hindex p hp hz)))
  · rw [afterC_eq_zero_of_not_narrow hp]
    exact Nat.zero_le _

theorem s1200_terminal (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks) :
    ∀ p, ¬ sourceSplit1200.Routeable p →
      afterF500 p ≤ split1200Potential.eval p + s1200Prefix p := by
  intro p hn
  by_cases hp : NarrowState p
  · have hs := (phase_state_checked_at hstate p hp).2.2.2.1
    exact (afterF500_le_fast hindex p hp).trans
      (hs.resolve_left
        (fun hz ↦ hn (routeableS1200_of_cutoff hindex p hp hz)))
  · rw [afterF500_eq_zero_of_not_narrow hp]
    exact Nat.zero_le _

theorem s390_terminal (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks) :
    ∀ p, ¬ sourceSplit390.Routeable p →
      afterS1200 p ≤ split390Potential.eval p + s390Prefix p := by
  intro p hn
  by_cases hp : NarrowState p
  · have hs := (phase_state_checked_at hstate p hp).2.2.2.2.1
    exact (afterS1200_le_fast hindex p hp).trans
      (hs.resolve_left
        (fun hz ↦ hn (routeableS390_of_cutoff hindex p hp hz)))
  · rw [afterS1200_eq_zero_of_not_narrow hp]
    exact Nat.zero_le _

/-! ## From adjacent prefix checks to global raw monotonicity -/

structure CoreGridSound (core : FlagDegree → ℕ) : Prop where
  top : ∀ p, PrefixValid p → core p ≤ prefixSentinel
  stepR : ∀ r v z, 1 ≤ r → PrefixValid (rawFlag (r + 1) v z) →
    core (rawFlag r v z) ≤ core (rawFlag (r + 1) v z)
  stepV : ∀ r v z, PrefixValid (rawFlag r (v + 1) z) →
    core (rawFlag r v z) ≤ core (rawFlag r (v + 1) z)
  stepZ : ∀ r v z, PrefixValid (rawFlag r v (z + 1)) →
    core (rawFlag r v z) ≤ core (rawFlag r v (z + 1))

private theorem core_mono_add_r
    {core : FlagDegree → ℕ} (h : CoreGridSound core)
    (r v z d : ℕ) (hr : 1 ≤ r)
    (hvalid : PrefixValid (rawFlag (r + d) v z)) :
    core (rawFlag r v z) ≤ core (rawFlag (r + d) v z) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : PrefixValid (rawFlag (r + d) v z) := by
        simp only [PrefixValid, rawFlag] at hvalid ⊢
        omega
      calc
        core (rawFlag r v z) ≤ core (rawFlag (r + d) v z) := ih hprev
        _ ≤ core (rawFlag ((r + d) + 1) v z) :=
          h.stepR (r + d) v z (by omega) (by
            simpa only [Nat.add_assoc] using hvalid)
        _ = core (rawFlag (r + d.succ) v z) := by
          congr 2 <;> omega

private theorem core_mono_add_v
    {core : FlagDegree → ℕ} (h : CoreGridSound core)
    (r v z d : ℕ) (hvalid : PrefixValid (rawFlag r (v + d) z)) :
    core (rawFlag r v z) ≤ core (rawFlag r (v + d) z) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : PrefixValid (rawFlag r (v + d) z) := by
        simp only [PrefixValid, rawFlag] at hvalid ⊢
        omega
      calc
        core (rawFlag r v z) ≤ core (rawFlag r (v + d) z) := ih hprev
        _ ≤ core (rawFlag r ((v + d) + 1) z) :=
          h.stepV r (v + d) z (by
            simpa only [Nat.add_assoc] using hvalid)
        _ = core (rawFlag r (v + d.succ) z) := by
          congr 2 <;> omega

private theorem core_mono_add_z
    {core : FlagDegree → ℕ} (h : CoreGridSound core)
    (r v z d : ℕ) (hvalid : PrefixValid (rawFlag r v (z + d))) :
    core (rawFlag r v z) ≤ core (rawFlag r v (z + d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : PrefixValid (rawFlag r v (z + d)) := by
        simp only [PrefixValid, rawFlag] at hvalid ⊢
        omega
      calc
        core (rawFlag r v z) ≤ core (rawFlag r v (z + d)) := ih hprev
        _ ≤ core (rawFlag r v ((z + d) + 1)) :=
          h.stepZ r v (z + d) (by
            simpa only [Nat.add_assoc] using hvalid)
        _ = core (rawFlag r v (z + d.succ)) := by
          congr 2 <;> omega

private theorem core_mono_of_grid
    {core : FlagDegree → ℕ} (h : CoreGridSound core)
    {p₁ p₂ : FlagDegree} (hp₁ : PrefixValid p₁) (hp₂ : PrefixValid p₂)
    (hbelow : RawBelow p₁ p₂) : core p₁ ≤ core p₂ := by
  rcases p₁ with ⟨z₁, v₁, r₁⟩
  rcases p₂ with ⟨z₂, v₂, r₂⟩
  change r₁ ≤ r₂ ∧ v₁ ≤ v₂ ∧ z₁ ≤ z₂ at hbelow
  rcases hbelow with ⟨hr, hv, hz⟩
  have hr₁ : 1 ≤ r₁ := by
    simpa [PrefixValid] using hp₁.1
  obtain ⟨dr, hdr⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨dv, hdv⟩ := Nat.exists_eq_add_of_le hv
  obtain ⟨dz, hdz⟩ := Nat.exists_eq_add_of_le hz
  have hR : core (rawFlag r₁ v₁ z₁) ≤ core (rawFlag r₂ v₁ z₁) := by
    have hvalid : PrefixValid (rawFlag (r₁ + dr) v₁ z₁) := by
      simp only [PrefixValid, rawFlag] at hp₂ ⊢
      omega
    simpa only [hdr] using core_mono_add_r h r₁ v₁ z₁ dr hr₁ hvalid
  have hV : core (rawFlag r₂ v₁ z₁) ≤ core (rawFlag r₂ v₂ z₁) := by
    have hvalid : PrefixValid (rawFlag r₂ (v₁ + dv) z₁) := by
      simp only [PrefixValid, rawFlag] at hp₂ ⊢
      omega
    simpa only [hdv] using core_mono_add_v h r₂ v₁ z₁ dv hvalid
  have hZ : core (rawFlag r₂ v₂ z₁) ≤ core (rawFlag r₂ v₂ z₂) := by
    have hvalid : PrefixValid (rawFlag r₂ v₂ (z₁ + dz)) := by
      simpa only [hdz, PrefixValid, rawFlag] using hp₂
    simpa only [hdz] using core_mono_add_z h r₂ v₂ z₁ dz hvalid
  exact hR.trans (hV.trans hZ)

theorem satPrefix_mono
    {core : FlagDegree → ℕ} (h : CoreGridSound core) :
    ∀ {p₁ p₂}, RawBelow p₁ p₂ → satPrefix core p₁ ≤ satPrefix core p₂ := by
  intro p₁ p₂ hbelow
  by_cases hp₁zero : p₁.all = 0
  · simp [satPrefix, hp₁zero]
  have hp₁pos : 1 ≤ p₁.all := Nat.one_le_iff_ne_zero.mpr hp₁zero
  have hp₂zero : p₂.all ≠ 0 := by
    intro hp₂zero
    exact hp₁zero (Nat.eq_zero_of_le_zero (hp₂zero ▸ hbelow.1))
  by_cases hp₂valid : PrefixValid p₂
  · have hp₁valid : PrefixValid p₁ := by
      unfold PrefixValid at hp₂valid ⊢
      unfold RawBelow at hbelow
      omega
    simp only [satPrefix, if_neg hp₁zero, if_neg hp₂zero,
      if_pos hp₁valid, if_pos hp₂valid]
    exact core_mono_of_grid h hp₁valid hp₂valid hbelow
  · by_cases hp₁valid : PrefixValid p₁
    · simp only [satPrefix, if_neg hp₁zero, if_neg hp₂zero,
        if_pos hp₁valid, if_neg hp₂valid]
      exact h.top p₁ hp₁valid
    · simp [satPrefix, hp₁zero, hp₂zero, hp₁valid, hp₂valid]

private theorem core_check_at (h : PrefixCoreChecks)
    (R V : ℕ) (hR : 1 ≤ R) (hR27 : R ≤ 28)
    (hRV : R + 1 + V ≤ 135) :
    rPrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
    f500PrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
    s1200PrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
    s390PrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
    (∀ b ∈ List.range 23, cPrefixAt R V b ≤ prefixSentinel) ∧
    (R + 1 ≤ 28 ∧ R + 1 + 1 + V ≤ 135 →
      rPrefixCore (rawFlag R V 0) ≤ rPrefixCore (rawFlag (R + 1) V 0) ∧
      f500PrefixCore (rawFlag R V 0) ≤
        f500PrefixCore (rawFlag (R + 1) V 0) ∧
      s1200PrefixCore (rawFlag R V 0) ≤
        s1200PrefixCore (rawFlag (R + 1) V 0) ∧
      s390PrefixCore (rawFlag R V 0) ≤
        s390PrefixCore (rawFlag (R + 1) V 0) ∧
      ∀ b ∈ List.range 23, cPrefixAt R V b ≤ cPrefixAt (R + 1) V b) ∧
    (R + 1 + (V + 1) ≤ 135 →
      rPrefixCore (rawFlag R V 0) ≤ rPrefixCore (rawFlag R (V + 1) 0) ∧
      f500PrefixCore (rawFlag R V 0) ≤
        f500PrefixCore (rawFlag R (V + 1) 0) ∧
      s1200PrefixCore (rawFlag R V 0) ≤
        s1200PrefixCore (rawFlag R (V + 1) 0) ∧
      s390PrefixCore (rawFlag R V 0) ≤
        s390PrefixCore (rawFlag R (V + 1) 0) ∧
      ∀ b ∈ List.range 23, cPrefixAt R V b ≤ cPrefixAt R (V + 1) b) ∧
    (∀ b ∈ List.range 22, cPrefixAt R V b ≤ cPrefixAt R V (b + 1)) := by
  exact h R (List.mem_range.mpr (by omega)) hR V
    (List.mem_range.mpr (by omega))

private theorem cPrefixAt_mono_bucket (h : PrefixCoreChecks)
    (R V b₁ b₂ : ℕ) (hR : 1 ≤ R) (hR27 : R ≤ 28)
    (hRV : R + 1 + V ≤ 135)
    (hb : b₁ ≤ b₂) (hb₂ : b₂ ≤ 22) :
    cPrefixAt R V b₁ ≤ cPrefixAt R V b₂ := by
  have hsteps := (core_check_at h R V hR hR27 hRV).2.2.2.2.2.2.2
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
  induction d with
  | zero => rfl
  | succ d ih =>
      have hprev : b₁ + d ≤ 22 := by omega
      exact (ih (by omega) hprev).trans
        (hsteps (b₁ + d) (List.mem_range.mpr (by omega)))

theorem cBucket_mono {z₁ z₂ : ℕ} (hz : z₁ ≤ z₂) :
    cBucket z₁ ≤ cBucket z₂ := by
  unfold cBucket
  by_cases h₁ : z₁ ≤ 64
  · rw [if_pos h₁]
    exact Nat.zero_le _
  · have h₂ : ¬ z₂ ≤ 64 := by omega
    rw [if_neg h₁, if_neg h₂]
    exact Nat.div_le_div_right
      (Nat.add_le_add_right (Nat.sub_le_sub_right hz 64) 303)

theorem rCoreGridSound (h : PrefixCoreChecks) : CoreGridSound rPrefixCore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hr, hr27, hrv, _⟩
    simpa [rPrefixCore, rawFlag] using
      (core_check_at h p.all p.yz hr hr27 hrv).1
  · intro r v z hr hvalid
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.1
    have hstep := hrow ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega⟩
    simpa only [rPrefixCore, rawFlag] using hstep.1
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.2.1
    have hstep := hrow (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)
    simpa only [rPrefixCore, rawFlag] using hstep.1
  · intro r v z _
    rfl

theorem f500CoreGridSound (h : PrefixCoreChecks) :
    CoreGridSound f500PrefixCore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hr, hr27, hrv, _⟩
    simpa [f500PrefixCore, rawFlag] using
      (core_check_at h p.all p.yz hr hr27 hrv).2.1
  · intro r v z hr hvalid
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.1
    have hstep := hrow ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega⟩
    simpa only [f500PrefixCore, rawFlag] using hstep.2.1
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.2.1
    have hstep := hrow (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)
    simpa only [f500PrefixCore, rawFlag] using hstep.2.1
  · intro r v z _
    rfl

theorem s1200CoreGridSound (h : PrefixCoreChecks) :
    CoreGridSound s1200PrefixCore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hr, hr27, hrv, _⟩
    simpa [s1200PrefixCore, rawFlag] using
      (core_check_at h p.all p.yz hr hr27 hrv).2.2.1
  · intro r v z hr hvalid
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.1
    have hstep := hrow ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega⟩
    simpa only [s1200PrefixCore, rawFlag] using hstep.2.2.1
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.2.1
    have hstep := hrow (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)
    simpa only [s1200PrefixCore, rawFlag] using hstep.2.2.1
  · intro r v z _
    rfl

theorem s390CoreGridSound (h : PrefixCoreChecks) :
    CoreGridSound s390PrefixCore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hr, hr27, hrv, _⟩
    simpa [s390PrefixCore, rawFlag] using
      (core_check_at h p.all p.yz hr hr27 hrv).2.2.2.1
  · intro r v z hr hvalid
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.1
    have hstep := hrow ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega⟩
    simpa only [s390PrefixCore, rawFlag] using hstep.2.2.2.1
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.2.1
    have hstep := hrow (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)
    simpa only [s390PrefixCore, rawFlag] using hstep.2.2.2.1
  · intro r v z _
    rfl

theorem cCoreGridSound (h : PrefixCoreChecks) : CoreGridSound cPrefixCore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hr, hr27, hrv, htotal⟩
    have hb : cBucket p.zOnly ∈ List.range 23 :=
      List.mem_range.mpr (Nat.lt_succ_iff.mpr
        (cBucket_le_22 p.zOnly (by omega)))
    simpa [cPrefixCore, rawFlag] using
      (core_check_at h p.all p.yz hr hr27 hrv).2.2.2.2.1 _ hb
  · intro r v z hr hvalid
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrv : r + 1 + v ≤ 135 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hnext : r + 1 + 1 + v ≤ 135 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hb20 : cBucket z ≤ 22 := by
      apply cBucket_le_22
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hstep := (core_check_at h r v hr hr27 hrv).2.2.2.2.2.1 ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, hnext⟩
    simpa only [cPrefixCore, rawFlag] using
      hstep.2.2.2.2 (cBucket z) (List.mem_range.mpr (by omega))
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrv : r + 1 + v ≤ 135 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hnext : r + 1 + (v + 1) ≤ 135 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hb20 : cBucket z ≤ 22 := by
      apply cBucket_le_22
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hstep := (core_check_at h r v hr hr27 hrv).2.2.2.2.2.2.1 hnext
    simpa only [cPrefixCore, rawFlag] using
      hstep.2.2.2.2 (cBucket z) (List.mem_range.mpr (by omega))
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrv : r + 1 + v ≤ 135 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hz20 : cBucket (z + 1) ≤ 22 := by
      apply cBucket_le_22
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    exact cPrefixAt_mono_bucket h r v (cBucket z) (cBucket (z + 1))
      hr hr27 hrv (cBucket_mono (by omega)) hz20

theorem rPrefix_mono (h : PrefixCoreChecks) :
    ∀ {p₁ p₂}, RawBelow p₁ p₂ → rPrefix p₁ ≤ rPrefix p₂ :=
  satPrefix_mono (rCoreGridSound h)

theorem cPrefix_mono (h : PrefixCoreChecks) :
    ∀ {p₁ p₂}, RawBelow p₁ p₂ → cPrefix p₁ ≤ cPrefix p₂ :=
  satPrefix_mono (cCoreGridSound h)

theorem f500Prefix_mono (h : PrefixCoreChecks) :
    ∀ {p₁ p₂}, RawBelow p₁ p₂ → f500Prefix p₁ ≤ f500Prefix p₂ :=
  satPrefix_mono (f500CoreGridSound h)

theorem s1200Prefix_mono (h : PrefixCoreChecks) :
    ∀ {p₁ p₂}, RawBelow p₁ p₂ → s1200Prefix p₁ ≤ s1200Prefix p₂ :=
  satPrefix_mono (s1200CoreGridSound h)

theorem s390Prefix_mono (h : PrefixCoreChecks) :
    ∀ {p₁ p₂}, RawBelow p₁ p₂ → s390Prefix p₁ ≤ s390Prefix p₂ :=
  satPrefix_mono (s390CoreGridSound h)

theorem rRows (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (hcore : PrefixCoreChecks) :
    PrefixTableSound checkedBaseCap r1200Potential
      sourceR1200.Routeable rPrefix :=
  ⟨r_terminal hindex hstate, rPrefix_mono hcore⟩

theorem cRows (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (hcore : PrefixCoreChecks) :
    PrefixTableSound afterR sourceCPotential sourceC.Routeable cPrefix :=
  ⟨c_terminal hindex hstate, cPrefix_mono hcore⟩

theorem f500Rows (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (hcore : PrefixCoreChecks) :
    PrefixTableSound afterC split500Potential
      sourceSplit500.Routeable f500Prefix :=
  ⟨f500_terminal hindex hstate, f500Prefix_mono hcore⟩

theorem s1200Rows (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (hcore : PrefixCoreChecks) :
    PrefixTableSound afterF500 split1200Potential
      sourceSplit1200.Routeable s1200Prefix :=
  ⟨s1200_terminal hindex hstate, s1200Prefix_mono hcore⟩

theorem s390Rows (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (hcore : PrefixCoreChecks) :
    PrefixTableSound afterS1200 split390Potential
      sourceSplit390.Routeable s390Prefix :=
  ⟨s390_terminal hindex hstate, s390Prefix_mono hcore⟩

theorem narrow_le (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (p : FlagDegree) (hslope : p.all ≤ 29) (hmiddle : middle p ≤ 135)
    (htotal : total p ≤ 6677) :
    afterS390 p ≤ certifiedNarrowMaximum := by
  by_cases hpzero : p.all = 0
  · have hnarrow : ¬ NarrowState p := by
      intro hp
      rcases hp with ⟨hpos, _, _, _⟩
      omega
    rw [afterS390_eq_zero_of_not_narrow hnarrow]
    exact Nat.zero_le _
  · have hp : NarrowState p :=
      ⟨Nat.one_le_iff_ne_zero.mpr hpzero, hslope, hmiddle, htotal⟩
    exact (afterS390_le_fast hindex p hp).trans
      (phase_state_checked_at hstate p hp).2.2.2.2.2.1

theorem initialAComplement_le_certifiedJoint (p : FlagDegree)
    (hslope : p.all ≤ 29) (hmiddle : middle p ≤ 135) :
    initialAComplement p ≤ certifiedJointMaximum := by
  have hcore : initialAComplementCore p ≤ 1720089382497312 := by
    simp only [initialAComplementCore, initialAPotential, Potential.eval,
      rawFlag_total, rawFlag_middle, rawFlag_all, Nat.min_def]
    split_ifs <;> omega
  have h1 := ChainGroupMaj.chainMaj_mono_y 6677 p.all
    (hmiddle.trans (by norm_num : (135 : ℕ) ≤ 153))
  have h2 := ChainGroupMaj.chainMaj_mono_y 6677 (33 - p.all) (Nat.sub_le 153 p.yz)
  have h3 := ChainGroupMaj.chainMaj_pair_le p.all (Finset.mem_range.mpr (by omega))
  have h4 := ChainGroupMaj.residMaj6802_le p.all (Finset.mem_range.mpr (by omega))
  unfold initialAComplement certifiedJointMaximum
  omega

theorem joint_le (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (p : FlagDegree) (hslope : p.all ≤ 29) (hmiddle : middle p ≤ 135)
    (htotal : total p ≤ 6677) :
    afterS390 p + initialAComplement p ≤ certifiedJointMaximum := by
  by_cases hpzero : p.all = 0
  · have hnarrow : ¬ NarrowState p := by
      intro hp
      rcases hp with ⟨hpos, _, _, _⟩
      omega
    rw [afterS390_eq_zero_of_not_narrow hnarrow, Nat.zero_add]
    exact initialAComplement_le_certifiedJoint p hslope hmiddle
  · have hp : NarrowState p :=
      ⟨Nat.one_le_iff_ne_zero.mpr hpzero, hslope, hmiddle, htotal⟩
    exact (Nat.add_le_add_right (afterS390_le_fast hindex p hp) _).trans
      (phase_state_checked_at hstate p hp).2.2.2.2.2.2

end ProximityPrize.SubmissionLower.LocatorPhase6800Concrete
end PackedLocator_LocatorPhase6800Concrete

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier190 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunsBridge. -/
section PackedLocator_LocatorPhase6800PhaseRunsBridge

/-! Definitional bridge from the sparse affine-run checker to the public
`PhaseStateRCheck`.  It contains no generated data and no computation. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunsBridge

open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open LocatorPhase6800Audit
open LocatorPhase6800Concrete LocatorPhase6800BaseDirectData
open LocatorPhase6800PhaseRuns

set_option autoImplicit false
set_option maxRecDepth 100000

theorem baseAt_rowContext_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 29)
    (hV : V < 136 - R) (hz : z < 6678 - (R + V)) :
    baseAt (rowContext R V) z = checkedBaseCap (rawFlag R V z) := by
  have hnarrow : NarrowState (rawFlag R V z) := by
    simp only [NarrowState, rawFlag_all, rawFlag_middle, rawFlag_total]
    omega
  rw [checkedBaseCap_of_narrow hnarrow]
  rfl

theorem parentCharge0_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 0 z =
      r1200Potential.eval (rawFlag R V z) +
        parentDefect rPrefix (rawFlag R V z) := by
  rfl

theorem parentCharge1_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 1 z =
      sourceCPotential.eval (rawFlag R V z) +
        parentDefect cPrefix (rawFlag R V z) := by
  rfl

theorem parentCharge2_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 2 z =
      split500Potential.eval (rawFlag R V z) +
        parentDefect f500Prefix (rawFlag R V z) := by
  rfl

theorem parentCharge3_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 3 z =
      split1200Potential.eval (rawFlag R V z) +
        parentDefect s1200Prefix (rawFlag R V z) := by
  rfl

theorem parentCharge4_eq (R V z : ℕ) :
    parentCharge (rowContext R V) 4 z =
      split390Potential.eval (rawFlag R V z) +
        parentDefect s390Prefix (rawFlag R V z) := by
  rfl

theorem hereCharge0_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 0 z =
      r1200Potential.eval (rawFlag R V z) + rPrefix (rawFlag R V z) := by
  rfl

theorem hereCharge1_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 1 z =
      sourceCPotential.eval (rawFlag R V z) + cPrefix (rawFlag R V z) := by
  rfl

theorem hereCharge2_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 2 z =
      split500Potential.eval (rawFlag R V z) + f500Prefix (rawFlag R V z) := by
  rfl

theorem hereCharge3_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 3 z =
      split1200Potential.eval (rawFlag R V z) + s1200Prefix (rawFlag R V z) := by
  rfl

theorem hereCharge4_eq (R V z : ℕ) :
    hereCharge (rowContext R V) 4 z =
      split390Potential.eval (rawFlag R V z) + s390Prefix (rawFlag R V z) := by
  rfl

theorem capBefore0_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 29)
    (hV : V < 136 - R) (hz : z < 6678 - (R + V)) :
    capBefore (rowContext R V) 0 z = checkedBaseCap (rawFlag R V z) :=
  baseAt_rowContext_eq R V z hR hR28 hV hz

theorem capBefore1_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 29)
    (hV : V < 136 - R) (hz : z < 6678 - (R + V)) :
    capBefore (rowContext R V) 1 z = fastAfterR (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 0 ≤ z then
    min (baseAt (rowContext R V) z) (parentCharge (rowContext R V) 0 z)
    else baseAt (rowContext R V) z) = fastAfterR (rawFlag R V z)
  rw [baseAt_rowContext_eq R V z hR hR28 hV hz, parentCharge0_eq]
  rfl

theorem capBefore2_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 29)
    (hV : V < 136 - R) (hz : z < 6678 - (R + V)) :
    capBefore (rowContext R V) 2 z = fastAfterC (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 1 ≤ z then
    min (capBefore (rowContext R V) 1 z) (parentCharge (rowContext R V) 1 z)
    else capBefore (rowContext R V) 1 z) = fastAfterC (rawFlag R V z)
  rw [capBefore1_eq R V z hR hR28 hV hz, parentCharge1_eq]
  rfl

theorem capBefore3_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 29)
    (hV : V < 136 - R) (hz : z < 6678 - (R + V)) :
    capBefore (rowContext R V) 3 z = fastAfterF500 (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 2 ≤ z then
    min (capBefore (rowContext R V) 2 z) (parentCharge (rowContext R V) 2 z)
    else capBefore (rowContext R V) 2 z) = fastAfterF500 (rawFlag R V z)
  rw [capBefore2_eq R V z hR hR28 hV hz, parentCharge2_eq]
  rfl

theorem capBefore4_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 29)
    (hV : V < 136 - R) (hz : z < 6678 - (R + V)) :
    capBefore (rowContext R V) 4 z = fastAfterS1200 (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 3 ≤ z then
    min (capBefore (rowContext R V) 3 z) (parentCharge (rowContext R V) 3 z)
    else capBefore (rowContext R V) 3 z) = fastAfterS1200 (rawFlag R V z)
  rw [capBefore3_eq R V z hR hR28 hV hz, parentCharge3_eq]
  rfl

theorem capBefore5_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 29)
    (hV : V < 136 - R) (hz : z < 6678 - (R + V)) :
    capBefore (rowContext R V) 5 z = fastAfterS390 (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 4 ≤ z then
    min (capBefore (rowContext R V) 4 z) (parentCharge (rowContext R V) 4 z)
    else capBefore (rowContext R V) 4 z) = fastAfterS390 (rawFlag R V z)
  rw [capBefore4_eq R V z hR hR28 hV hz, parentCharge4_eq]
  rfl

theorem sparseRV_to_public (R V : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 29) (hV : V < 136 - R)
    (h : SparsePhaseStateRVCheck (rowContext R V))
    (z : ℕ) (hz : z < 6678 - (R + V)) :
    let p := rawFlag R V z
    (rThreshold R V ≤ z ∨
      checkedBaseCap p ≤ r1200Potential.eval p + rPrefix p) ∧
    (cThreshold R V ≤ z ∨
      fastAfterR p ≤ sourceCPotential.eval p + cPrefix p) ∧
    (f500Threshold R V ≤ z ∨
      fastAfterC p ≤ split500Potential.eval p + f500Prefix p) ∧
    (s1200Threshold R V ≤ z ∨
      fastAfterF500 p ≤ split1200Potential.eval p + s1200Prefix p) ∧
    (s390Threshold R V ≤ z ∨
      fastAfterS1200 p ≤ split390Potential.eval p + s390Prefix p) ∧
    fastAfterS390 p ≤ certifiedNarrowMaximum ∧
    fastAfterS390 p + initialAComplement p ≤ certifiedJointMaximum := by
  have hs := h z hz
  dsimp only
  rw [← capBefore0_eq R V z hR hR28 hV hz,
    ← capBefore1_eq R V z hR hR28 hV hz,
    ← capBefore2_eq R V z hR hR28 hV hz,
    ← capBefore3_eq R V z hR hR28 hV hz,
    ← capBefore4_eq R V z hR hR28 hV hz,
    ← capBefore5_eq R V z hR hR28 hV hz,
    ← hereCharge0_eq R V z, ← hereCharge1_eq R V z,
    ← hereCharge2_eq R V z, ← hereCharge3_eq R V z,
    ← hereCharge4_eq R V z]
  exact hs

theorem sparseLayer_to_public (R : ℕ) (hR : 1 ≤ R) (hR28 : R ≤ 29)
    (h : ∀ V ∈ List.range (136 - R),
      SparsePhaseStateRVCheck (rowContext R V)) : PhaseStateRCheck R := by
  intro V hV z hz
  exact sparseRV_to_public R V hR hR28 (List.mem_range.mp hV)
    (h V hV) z (List.mem_range.mp hz)

end ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunsBridge
end PackedLocator_LocatorPhase6800PhaseRunsBridge

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier191 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800FastChannelCount. -/
section PackedLocator_LocatorPhase6800FastChannelCount

namespace ProximityPrize.SubmissionLower.ThresholdFastProof

open scoped BigOperators
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000

theorem term_eq (B x : ℕ) :
    (x + 1) * (B + x) - (x + 1) * x / 2 =
      (x + 1) * B + (x + 1).choose 2 := by
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  have hdvd : 2 ∣ (x + 1) * x := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (even_iff_two_dvd.mp (Nat.even_mul_succ_self x))
  have hhalf := Nat.div_mul_cancel hdvd
  rw [Nat.mul_add]
  omega

theorem kernelSumRange_succ_all : ∀ n : ℕ,
    kernelSumRange (fun x => x + 1) n = (n + 1).choose 2
  | 0 => by decide
  | n + 1 => by
      rw [LocatorLowQuotient.kernelSumRange_succ, kernelSumRange_succ_all]
      simpa [Nat.choose_one_right, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using (Nat.choose_succ_succ (n + 1) 1).symm

theorem kernelSumRange_succ (U : ℕ) :
    kernelSumRange (fun x => x + 1) (U + 1) = (U + 2).choose 2 := by
  simpa only [Nat.add_assoc] using kernelSumRange_succ_all (U + 1)

theorem kernelSumRange_choose_two_all : ∀ n : ℕ,
    kernelSumRange (fun x => (x + 1).choose 2) n = (n + 1).choose 3
  | 0 => by decide
  | n + 1 => by
      rw [LocatorLowQuotient.kernelSumRange_succ, kernelSumRange_choose_two_all]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.choose_succ_succ (n + 1) 2).symm

theorem kernelSumRange_choose_two (U : ℕ) :
    kernelSumRange (fun x => (x + 1).choose 2) (U + 1) =
      (U + 2).choose 3 := by
  simpa only [Nat.add_assoc] using kernelSumRange_choose_two_all (U + 1)

theorem kernelSumRange_uncapped (B U : ℕ) :
    kernelSumRange (fun x =>
      (x + 1) * (B + x) - (x + 1) * x / 2) (U + 1) =
      B * (U + 2).choose 2 + (U + 2).choose 3 := by
  rw [kernelSumRange_eq]
  simp_rw [term_eq]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [← kernelSumRange_eq, kernelSumRange_succ]
  rw [← kernelSumRange_eq, kernelSumRange_choose_two]
  simp only [Nat.mul_comm]

def cappedTerm (B S x : ℕ) : ℕ :=
  let M := min S x
  (M + 1) * (B + x) - (M + 1) * M / 2

theorem min_sub_min_eq (T YS x : ℕ) (hx : x ≤ min T YS) :
    min (T - (min T YS - x)) (YS - (min T YS - x)) = x := by
  rcases le_total T YS with h | h
  · simp only [Nat.min_eq_left h] at hx ⊢
    omega
  · simp only [Nat.min_eq_right h] at hx ⊢
    omega

theorem channelCount_eq_cappedKernel (T YS S : ℕ) :
    channelCount T YS S =
      kernelSumRange
        (cappedTerm (T + 1 - min T YS) S) (min T YS + 1) := by
  unfold channelCount
  rw [kernelSumRange_eq, ← Finset.sum_range_reflect]
  rw [kernelSumRange_eq]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hx' : x ≤ min T YS := by
    have := Finset.mem_range.mp hx
    omega
  have hU : min T YS ≤ T := Nat.min_le_left _ _
  simp only [Nat.add_sub_cancel, cappedTerm]
  rw [min_sub_min_eq T YS x hx']
  have harg : T + 1 - (min T YS - x) =
      (T + 1 - min T YS) + x := by omega
  rw [harg]

def fastChannelCount (T YS S : ℕ) : ℕ :=
  let U := min T YS
  let B := T + 1 - U
  let k := min S U
  let n := U - k
  let C := (S + 1) * (B + S + 1) - (S + 1) * S / 2
  B * (k + 2).choose 2 + (k + 2).choose 3 +
    n * C + (S + 1) * (n * (n - 1) / 2)

theorem tail_term_eq (B S t : ℕ) :
    cappedTerm B S (S + 1 + t) =
      ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
        (S + 1) * t := by
  unfold cappedTerm
  rw [Nat.min_eq_left (by omega)]
  change (S + 1) * (B + (S + 1 + t)) - (S + 1) * S / 2 =
    ((S + 1) * (B + S + 1) - (S + 1) * S / 2) + (S + 1) * t
  rw [show B + (S + 1 + t) = (B + S + 1) + t by omega,
    Nat.mul_add]
  have hS : S ≤ B + S + 1 := by omega
  have hq : (S + 1) * S / 2 ≤ (S + 1) * (B + S + 1) :=
    (Nat.div_le_self ((S + 1) * S) 2).trans
      (Nat.mul_le_mul_left (S + 1) hS)
  exact Nat.sub_add_comm
    (n := (S + 1) * (B + S + 1)) (m := (S + 1) * t)
    (k := (S + 1) * S / 2) hq

theorem kernelSumRange_capped_prefix (B S k : ℕ) (hk : k ≤ S) :
    kernelSumRange (cappedTerm B S) (k + 1) =
      B * (k + 2).choose 2 + (k + 2).choose 3 := by
  calc
    kernelSumRange (cappedTerm B S) (k + 1) =
        kernelSumRange (fun x =>
          (x + 1) * (B + x) - (x + 1) * x / 2) (k + 1) := by
      rw [kernelSumRange_eq, kernelSumRange_eq]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxk : x ≤ k := by
        have := Finset.mem_range.mp hx
        omega
      simp only [cappedTerm, Nat.min_eq_right (hxk.trans hk)]
    _ = B * (k + 2).choose 2 + (k + 2).choose 3 :=
      kernelSumRange_uncapped B k

theorem sum_Ico_capped_tail (B S U : ℕ) (hSU : S < U) :
    (∑ x ∈ Finset.Ico (S + 1) (U + 1), cappedTerm B S x) =
      (U - S) *
          ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
        (S + 1) * ((U - S) * (U - S - 1) / 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hsub : U + 1 - (S + 1) = U - S := by omega
  rw [hsub]
  simp_rw [tail_term_eq]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
    Finset.sum_range_id]

theorem kernelSumRange_capped_closed (B S U : ℕ) :
    kernelSumRange (cappedTerm B S) (U + 1) =
      let k := min S U
      let n := U - k
      B * (k + 2).choose 2 + (k + 2).choose 3 +
        n * ((S + 1) * (B + S + 1) - (S + 1) * S / 2) +
          (S + 1) * (n * (n - 1) / 2) := by
  by_cases hSU : S < U
  · simp only [Nat.min_eq_left hSU.le]
    rw [kernelSumRange_eq]
    rw [← Finset.sum_range_add_sum_Ico (cappedTerm B S)
      (show S + 1 ≤ U + 1 by omega)]
    rw [← kernelSumRange_eq, kernelSumRange_capped_prefix B S S le_rfl,
      sum_Ico_capped_tail B S U hSU]
    simp only [Nat.add_assoc]
  · have hUS : U ≤ S := Nat.le_of_not_gt hSU
    simp only [Nat.min_eq_right hUS, Nat.sub_self, zero_mul,
      Nat.zero_sub, Nat.add_zero]
    exact kernelSumRange_capped_prefix B S U hUS

theorem channelCount_eq_fast (T YS S : ℕ) :
    channelCount T YS S = fastChannelCount T YS S := by
  rw [channelCount_eq_cappedKernel]
  rw [kernelSumRange_capped_closed]
  rfl

/-! ## Constant-time executable form -/

theorem choose_three_right (n : ℕ) :
    n.choose 3 = n * (n - 1) * (n - 2) / 6 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp [Nat.descFactorial, Nat.factorial]
  congr 1
  ring

def evalChooseTwo (n : ℕ) : ℕ := n * (n - 1) / 2
def evalChooseThree (n : ℕ) : ℕ := n * (n - 1) * (n - 2) / 6

/-- A constant-time executable version of `channelCount`. -/
def evalChannelCount (T YS S : ℕ) : ℕ :=
  let U := min T YS
  let B := T + 1 - U
  let k := min S U
  let n := U - k
  let C := (S + 1) * (B + S + 1) - (S + 1) * S / 2
  B * evalChooseTwo (k + 2) + evalChooseThree (k + 2) +
    n * C + (S + 1) * (n * (n - 1) / 2)

theorem fastChannelCount_eq_eval (T YS S : ℕ) :
    fastChannelCount T YS S = evalChannelCount T YS S := by
  simp only [fastChannelCount, evalChannelCount, evalChooseTwo,
    evalChooseThree, Nat.choose_two_right, choose_three_right]

theorem channelCount_eq_eval (T YS S : ℕ) :
    channelCount T YS S = evalChannelCount T YS S :=
  (channelCount_eq_fast T YS S).trans (fastChannelCount_eq_eval T YS S)

open LocatorArbitraryPowerAvoidance LocatorPhase6800Oracle
open RCN095 LocatorFactorAggregate LocatorPhase6800ReceiptCellCore

/-- Executable power-band budget with the expensive range sum replaced by
the proved constant-time channel-count formula. -/
def evalPowerBandBudget
    (delta dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      delta * evalChannelCount T YS S +
        evalPowerBandBudget delta dT dY dS
          (T - dT) (YS - dY) (S - dS) fuel

theorem evalPowerBandBudget_eq
    (delta dT dY dS T YS S fuel : ℕ) :
    evalPowerBandBudget delta dT dY dS T YS S fuel =
      powerBandBudget delta dT dY dS T YS S fuel := by
  induction fuel generalizing T YS S with
  | zero => rfl
  | succ fuel ih =>
      simp only [evalPowerBandBudget, powerBandBudget]
      rw [← channelCount_eq_eval, ih]

def evalBand (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  evalPowerBandBudget 50293 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem evalBand_eq (s : SourceNumbers) (p : FlagDegree) :
    evalBand s p = s.band p := by
  unfold evalBand SourceNumbers.band
  exact evalPowerBandBudget_eq _ _ _ _ _ _ _ _

/-- Executable thin budget (lever S1): the same recursion with the constant-time
channel count; `thinTop` is already a single division. -/
def evalPowerBandBudgetThin
    (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      delta * evalChannelCount T (min YS (thinTop w Dh S)) S +
        evalPowerBandBudgetThin w (Dh - delta - dc) delta dc dT dY dS
          (T - dT) (YS - dY) (S - dS) fuel

theorem evalPowerBandBudgetThin_eq
    (w Dh delta dc dT dY dS T YS S fuel : ℕ) :
    evalPowerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel =
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel := by
  induction fuel generalizing Dh T YS S with
  | zero => rfl
  | succ fuel ih =>
      simp only [evalPowerBandBudgetThin, powerBandBudgetThin]
      rw [← channelCount_eq_eval, ih]

def evalBandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  evalPowerBandBudgetThin 131071 (s.contactCap p) 50293 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem evalBandThin_eq (s : SourceNumbers) (p : FlagDegree) :
    evalBandThin s p = s.bandThin p := by
  unfold evalBandThin SourceNumbers.bandThin
  exact evalPowerBandBudgetThin_eq _ _ _ _ _ _ _ _ _ _ _

def FastRouteable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (evalBand s p < s.gap ∨ evalBandThin s p < s.gap)

instance (s : SourceNumbers) (p : FlagDegree) :
    Decidable (FastRouteable s p) := by
  unfold FastRouteable
  infer_instance

theorem fastRouteable_iff (s : SourceNumbers) (p : FlagDegree) :
    FastRouteable s p ↔ s.Routeable p := by
  unfold FastRouteable SourceNumbers.Routeable
  rw [evalBand_eq, evalBandThin_eq]

def FastSourceThresholdSufficient
    (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  6677 - (r + v) < threshold ∨ FastRouteable s (rawFlag r v threshold)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (FastSourceThresholdSufficient s r v threshold) := by
  unfold FastSourceThresholdSufficient
  infer_instance

def FastThresholdSufficient (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 135 ∧
    FastSourceThresholdSufficient sourceR1200 q.r q.v q.r1200 ∧
    FastSourceThresholdSufficient LocatorPhase6800Oracle.sourceC
      q.r q.v q.sourceC ∧
    FastSourceThresholdSufficient sourceSplit500 q.r q.v q.split500 ∧
    FastSourceThresholdSufficient sourceSplit1200 q.r q.v q.split1200 ∧
    FastSourceThresholdSufficient sourceSplit390 q.r q.v q.split390

instance (q : ThresholdReceipt) : Decidable (FastThresholdSufficient q) := by
  unfold FastThresholdSufficient
  infer_instance

theorem fastSourceThresholdSufficient_sound
    (s : SourceNumbers) (r v threshold : ℕ) :
    FastSourceThresholdSufficient s r v threshold →
      SourceThresholdSufficient s r v threshold := by
  intro h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((fastRouteable_iff s _).mp h)

theorem fastThresholdSufficient_sound (q : ThresholdReceipt) :
    FastThresholdSufficient q → ThresholdSufficient q := by
  intro h
  rcases h with ⟨hr1, hr28, hrv, hR, hC, hF, hT, hS⟩
  exact ⟨hr1, hr28, hrv,
    fastSourceThresholdSufficient_sound _ _ _ _ hR,
    fastSourceThresholdSufficient_sound _ _ _ _ hC,
    fastSourceThresholdSufficient_sound _ _ _ _ hF,
    fastSourceThresholdSufficient_sound _ _ _ _ hT,
    fastSourceThresholdSufficient_sound _ _ _ _ hS⟩

/-! ## Whole-row executable interfaces -/

def FastThresholdAtOf
    (row : ℕ → ThresholdReceipt) (R V : ℕ) : Prop :=
  let q := row V
  q.r = R ∧ q.v = V ∧ FastThresholdSufficient q

instance (row : ℕ → ThresholdReceipt) (R V : ℕ) :
    Decidable (FastThresholdAtOf row R V) := by
  unfold FastThresholdAtOf
  infer_instance

theorem fastThresholdAtOf_sound
    (row : ℕ → ThresholdReceipt) (R V : ℕ) :
    FastThresholdAtOf row R V → ThresholdAtOf row R V := by
  intro h
  rcases h with ⟨hr, hv, hs⟩
  exact ⟨hr, hv, fastThresholdSufficient_sound _ hs⟩

def FastThresholdRIndexedOf
    (row : ℕ → ThresholdReceipt) (R count : ℕ) : Prop :=
  ∀ V ∈ List.range count, FastThresholdAtOf row R V

instance (row : ℕ → ThresholdReceipt) (R count : ℕ) :
    Decidable (FastThresholdRIndexedOf row R count) := by
  unfold FastThresholdRIndexedOf
  infer_instance

def PrefixCoreRIndexedOf
    (row nextRow : ℕ → PrefixReceipt) (R count : ℕ) : Prop :=
  ∀ V ∈ List.range count, PrefixCoreAtOf row nextRow R V

instance (row nextRow : ℕ → PrefixReceipt) (R count : ℕ) :
    Decidable (PrefixCoreRIndexedOf row nextRow R count) := by
  unfold PrefixCoreRIndexedOf
  infer_instance

end ProximityPrize.SubmissionLower.ThresholdFastProof
end PackedLocator_LocatorPhase6800FastChannelCount

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier193 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorResidual. -/
section PackedLocator_LocatorResidual
namespace ProximityPrize.SubmissionLower.LocatorResidual
open scoped Classical
open LocatorArithmetic LocatorDerivativeChain RCN174 RCN319 RCN260 RCN318 RCN238 RCN243 RCN052 RCN303
  RCN259 RCN180 RCN156 RCN234 RCN081
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

/-- Residual bound: regular pairs `(Q, T)`, the derivative-chain pairs
`(∂_R^j F, F)` for the positive-slope factors `F` of `Q`, and the slope-free
tails, all with linear characteristic gates only. -/
theorem residual_count_lt
    (Q T:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0) (hrel:IsRelPrime Q T)
    (hbox:Q ∈ globalCoefficientBox K weightedB w LB sB)
    (hTcaps:T.degreeOf 1 ≤ yT ∧ T.degreeOf 2 ≤ sT ∧ T.degreeOf 3 ≤ LCap)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hQsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma Q=0)
    (hTsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma T=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements)) :
    seeds.card < residualStage.regularCountCap +
      ChainAmort.capSum (fun t=>(chainStageAt t).regularCountCap) sB +
      2 * tailSingular.countCap + 1:=by
  have hclamp:∀ t:ℕ,1 ≤ max 1 (min t sB) ∧ max 1 (min t sB) ≤ sB:=by
    intro t; simp only [sB]; omega
  have hQgap : ∀ t:ℕ, 0 < (chainStageAt t).gap := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQY : ∀ t:ℕ, (weightedB - 1) / w ≤ (chainStageAt t).leftY := by
    intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; norm_num [weightedB]
  have hQR : ∀ t:ℕ, t ≤ sB → t ≤ (chainStageAt t).leftR := by
    intro t ht
    simp only [chainStageAt, sB] at ht ⊢
    omega
  have hQZ : ∀ t:ℕ, LB ≤ (chainStageAt t).leftZ := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQY' : ∀ t:ℕ, (weightedB - 1) / w ≤ (chainStageAt t).rightY := by
    intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; norm_num [weightedB]
  have hQR' : ∀ t:ℕ, sB ≤ (chainStageAt t).rightR := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQZ' : ∀ t:ℕ, LB ≤ (chainStageAt t).rightZ := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQlR : ∀ t:ℕ, 1 ≤ (chainStageAt t).leftR := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQlYS : ∀ t:ℕ, (chainStageAt t).leftY < 2130706433 := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQlRS : ∀ t:ℕ, (chainStageAt t).leftR < 2130706433 := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQlZS : ∀ t:ℕ, (chainStageAt t).leftZ < 2130706433 := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQmY : ∀ t:ℕ, (chainStageAt t).mixedCost.y < 2130706433 := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQmR : ∀ t:ℕ, (chainStageAt t).mixedCost.r < 2130706433 := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQmZ : ∀ t:ℕ, (chainStageAt t).mixedCost.z < 2130706433 := by intro t; simp only [chainStageAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have h:=residual_chain_count_le residualStage chainStageAt tailSingular Q T hQ hrel
    weightedB w LB sB 2130706433
    (by norm_num [sB]) (by norm_num [sB, prime]) (by norm_num [w]) (by norm_num)
    hbox
    (by norm_num [residualStage, UnequalParameters.gap, agreements, w])
    (by norm_num [residualStage, weightedB, w, yB]) (by norm_num [residualStage, sB])
    (by norm_num [residualStage, LB])
    (by simpa [residualStage, yT] using hTcaps.1) (by simpa [residualStage, sT] using hTcaps.2.1)
    (by simpa [residualStage, LCap] using hTcaps.2.2)
    (by norm_num [residualStage, sB]) (by norm_num [residualStage, yB])
    (by norm_num [residualStage, sB])
    (by norm_num [residualStage, LB])
    (by norm_num [residualStage, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT])
    (by norm_num [residualStage, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT])
    (by norm_num [residualStage, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT])
    chainStageAt_mono
    hQgap hQY hQR hQZ hQY' hQR' hQZ' hQlR hQlYS hQlRS hQlZS hQmY hQmR hQmZ
    tailSingular_le_chainStageAt_one
    rfl rfl rfl rfl
    (by norm_num [tailSingular, w])
    (by norm_num [tailSingular, TightParameters.kappa, weightedB, w])
    (by norm_num [tailSingular, TightParameters.algebraicCap, TightParameters.kappa, LB])
    (by norm_num [tailSingular, TightParameters.implicitYCap, TightParameters.kappa, weightedB, w])
    (by norm_num [tailSingular, TightParameters.algebraicCap, TightParameters.kappa, LB])
    (by norm_num [tailSingular, TightParameters.implicitYCap, TightParameters.algebraicCap,
      TightParameters.kappa, weightedB, w, LB])
    (by norm_num [tailSingular, w, agreements]) (by norm_num [tailSingular, n, agreements])
    selected seeds nodes x u0 u1 hinj
    (by simpa [residualStage] using hnodes) (fun (_:ℕ)=>by rw [hnodes]; rfl)
    (by simpa [tailSingular] using hnodes)
    (by norm_num [residualStage, w]) (by norm_num [residualStage, w])
    (by norm_num [residualStage, w, agreements]) (by norm_num [residualStage, n, agreements])
    (fun (_:ℕ)=>by norm_num [chainStageAt, w]) (fun (_:ℕ)=>by norm_num [chainStageAt, w])
    (fun (_:ℕ)=>by norm_num [chainStageAt, w, agreements])
    (fun (_:ℕ)=>by norm_num [chainStageAt, n, agreements])
    (by simpa [residualStage] using hdegree) (fun (_:ℕ)=>by simpa [chainStageAt] using hdegree)
    (by simpa [tailSingular] using hdegree)
    (by simpa [residualStage] using hagreement)
    (fun (_:ℕ)=>by simpa [chainStageAt] using hagreement)
    (by simpa [tailSingular] using hagreement)
    (by simpa [residualStage, UnequalParameters.errors] using hno)
    (fun (_:ℕ)=>by simpa [chainStageAt, UnequalParameters.errors] using hno)
    (by simpa [tailSingular, TightParameters.errors] using hno)
    hQsolution hTsolution
  omega

theorem residual_count_lt_slope (d:ℕ) (hd:d ≤ sB)
    (Q T:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0) (hrel:IsRelPrime Q T)
    (hbox:Q ∈ globalCoefficientBox K weightedB w LB (max 1 (sB - d)))
    (hTcaps:T.degreeOf 1 ≤ yT ∧ T.degreeOf 2 ≤ sT ∧ T.degreeOf 3 ≤ LCap)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hQsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma Q=0)
    (hTsolution:∀ gamma ∈ seeds,specialization K (selected gamma) gamma T=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements)) :
    seeds.card < (residualStageD d).regularCountCap +
      ChainAmort.capSum (fun t=>(chainStageAtD d t).regularCountCap) (max 1 (sB - d)) +
      2 * tailSingular.countCap + 1:=by
  have hsB:sB=33:=rfl
  have hQgap : ∀ t:ℕ, 0 < (chainStageAtD d t).gap := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQY : ∀ t:ℕ, (weightedB - 1) / w ≤ (chainStageAtD d t).leftY := by
    intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; norm_num [weightedB]
  have hQR : ∀ t:ℕ, t ≤ max 1 (sB - d) → t ≤ (chainStageAtD d t).leftR := by
    intro t ht
    simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, sB] at ht ⊢
    omega
  have hQZ : ∀ t:ℕ, LB ≤ (chainStageAtD d t).leftZ := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQY' : ∀ t:ℕ, (weightedB - 1) / w ≤ (chainStageAtD d t).rightY := by
    intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; norm_num [weightedB]
  have hQR' : ∀ t:ℕ, max 1 (sB - d) ≤ (chainStageAtD d t).rightR := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQZ' : ∀ t:ℕ, LB ≤ (chainStageAtD d t).rightZ := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQlR : ∀ t:ℕ, 1 ≤ (chainStageAtD d t).leftR := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQlYS : ∀ t:ℕ, (chainStageAtD d t).leftY < 2130706433 := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQlRS : ∀ t:ℕ, (chainStageAtD d t).leftR < 2130706433 := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQlZS : ∀ t:ℕ, (chainStageAtD d t).leftZ < 2130706433 := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQmY : ∀ t:ℕ, (chainStageAtD d t).mixedCost.y < 2130706433 := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQmR : ∀ t:ℕ, (chainStageAtD d t).mixedCost.r < 2130706433 := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have hQmZ : ∀ t:ℕ, (chainStageAtD d t).mixedCost.z < 2130706433 := by intro t; simp only [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.gap, UnequalParameters.mixedCost, n, w, agreements, yB, sB, LB]; omega
  have h:=residual_chain_count_le (residualStageD d) (chainStageAtD d) tailSingular Q T hQ hrel
    weightedB w LB (max 1 (sB - d)) 2130706433
    (le_max_left 1 _) (by simp only [sB]; omega) (by norm_num [w]) (by norm_num)
    hbox
    (by norm_num [residualStageD, UnequalParameters.gap, agreements, w])
    (by norm_num [residualStageD, weightedB, w, yB]) (by simp only [residualStageD]; omega)
    (by norm_num [residualStageD, LB])
    (by simpa [residualStageD, yT] using hTcaps.1) (by simpa [residualStageD, sT] using hTcaps.2.1)
    (by simpa [residualStageD, LCap] using hTcaps.2.2)
    (by simp only [residualStageD]; omega) (by norm_num [residualStageD, yB])
    (by simp only [residualStageD]; omega)
    (by norm_num [residualStageD, LB])
    (by simp only [residualStageD, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT]; omega)
    (by simp only [residualStageD, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT]; omega)
    (by simp only [residualStageD, UnequalParameters.mixedCost, LCap, LB, yB, yT, sB, sT]; omega)
    (chainStageAtD_mono d)
    hQgap hQY hQR hQZ hQY' hQR' hQZ' hQlR hQlYS hQlRS hQlZS hQmY hQmR hQmZ
    (tailSingular_le_chainStageAtD_one d (Finset.mem_range.mpr (by omega)))
    rfl rfl rfl rfl
    (by norm_num [tailSingular, w])
    (by norm_num [tailSingular, TightParameters.kappa, weightedB, w])
    (by norm_num [tailSingular, TightParameters.algebraicCap, TightParameters.kappa, LB])
    (by norm_num [tailSingular, TightParameters.implicitYCap, TightParameters.kappa, weightedB, w])
    (by norm_num [tailSingular, TightParameters.algebraicCap, TightParameters.kappa, LB])
    (by norm_num [tailSingular, TightParameters.implicitYCap, TightParameters.algebraicCap,
      TightParameters.kappa, weightedB, w, LB])
    (by norm_num [tailSingular, w, agreements]) (by norm_num [tailSingular, n, agreements])
    selected seeds nodes x u0 u1 hinj
    (by simpa [residualStageD] using hnodes) (fun (_:ℕ)=>by rw [hnodes]; rfl)
    (by simpa [tailSingular] using hnodes)
    (by norm_num [residualStageD, w]) (by norm_num [residualStageD, w])
    (by norm_num [residualStageD, w, agreements]) (by norm_num [residualStageD, n, agreements])
    (fun (_:ℕ)=>by norm_num [chainStageAtD, ChainGroupMaj.chainGroupAt, w]) (fun (_:ℕ)=>by norm_num [chainStageAtD, ChainGroupMaj.chainGroupAt, w])
    (fun (_:ℕ)=>by norm_num [chainStageAtD, ChainGroupMaj.chainGroupAt, w, agreements])
    (fun (_:ℕ)=>by norm_num [chainStageAtD, ChainGroupMaj.chainGroupAt, n, agreements])
    (by simpa [residualStageD] using hdegree) (fun (_:ℕ)=>by simpa [chainStageAtD, ChainGroupMaj.chainGroupAt, w] using hdegree)
    (by simpa [tailSingular] using hdegree)
    (by simpa [residualStageD] using hagreement)
    (fun (_:ℕ)=>by simpa [chainStageAtD, ChainGroupMaj.chainGroupAt, agreements] using hagreement)
    (by simpa [tailSingular] using hagreement)
    (by simpa [residualStageD, UnequalParameters.errors] using hno)
    (fun (_:ℕ)=>by simpa [chainStageAtD, ChainGroupMaj.chainGroupAt, UnequalParameters.errors, w, n, agreements] using hno)
    (by simpa [tailSingular, TightParameters.errors] using hno)
    hQsolution hTsolution
  omega

theorem gcd_residual_count_lt
    [GCDMonoid (MvPolynomial (Fin 4) K)]
    (QA QB:MvPolynomial (Fin 4) K) (hQA:QA ≠ 0) (hQB:QB ≠ 0)
    (hboxA:QA ∈ RCN100.globalCoefficientBox K weightedTCap w LCap sT)
    (hboxB:QB ∈ RCN100.globalCoefficientBox K weightedB w LB sB)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hA:∀ gamma ∈ seeds,specialization K (selected gamma) gamma QA=0)
    (hB:∀ gamma ∈ seeds,specialization K (selected gamma) gamma QB=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements)) :
    (LocatorCover.residual
      (fun gamma=> (specialization K (selected gamma) gamma).toRingHom)
      seeds QA QB).card < residualStage.regularCountCap +
        ChainAmort.capSum (fun t=>(chainStageAt t).regularCountCap) sB +
        2 * tailSingular.countCap + 1:=by
  classical
  let phi:=fun gamma=> (specialization K (selected gamma) gamma).toRingHom
  let Delta:=LocatorCover.residual phi seeds QA QB
  let H:=gcd12 QA QB
  let Q:=quotientB QA QB
  let T:=quotientA QA QB
  have hH:H ≠ 0:=gcd_ne_zero_of_left hQA
  have hQeq:QB=H * Q:=b_eq_gcd12_mul_quotientB QA QB
  have hTeq:QA=H * T:=a_eq_gcd12_mul_quotientA QA QB
  have hQ:Q ≠ 0:=by
    intro hz
    exact hQB (by rw [hQeq,hz,mul_zero])
  have hT:T ≠ 0:=by
    intro hz
    exact hQA (by rw [hTeq,hz,mul_zero])
  have hQflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QB H Q weightedB w LB sB 0 0 0 hQB hH hQ hboxB hQeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hTflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QA H T weightedTCap w LCap sT 0 0 0 hQA hH hT hboxA hTeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hQbox:Q ∈ globalCoefficientBox K weightedB w LB sB:=
    RCN101.flag_box_to_ordinary K
      weightedB w LB sB Q (by simpa only [Nat.sub_zero] using hQflag)
  have hTbox:T ∈ globalCoefficientBox K weightedTCap w LCap sT:=
    RCN101.flag_box_to_ordinary K
      weightedTCap w LCap sT T (by simpa only [Nat.sub_zero] using hTflag)
  have hTcaps:=RCN081.degree_bounds_of_mem_box
    T weightedTCap w LCap sT (by decide) hTbox
  rw [show (weightedTCap - 1) / w=yT by decide] at hTcaps
  have hsub:Delta ⊆ seeds:=by
    intro gamma hg
    have hm:gamma ∈ seeds ∧ (phi gamma) (gcd12 QA QB) ≠ 0:=by
      simpa only [Delta,LocatorCover.residual,Finset.mem_filter] using hg
    exact hm.1
  have hsol (gamma:K) (hg:gamma ∈ Delta) :
      specialization K (selected gamma) gamma T=0 ∧
      specialization K (selected gamma) gamma Q=0:=
    LocatorCover.residual_vanish phi seeds QA QB hA hB gamma hg
  exact residual_count_lt Q T hQ
    (firstQuotients_isRelPrime hQA).symm hQbox hTcaps selected Delta
    nodes x u0 u1 hinj hnodes
    (fun gamma hg=> hdegree gamma (hsub hg))
    (fun gamma hg=> (hsol gamma hg).2) (fun gamma hg=> (hsol gamma hg).1)
    (fun gamma hg=> hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono selected seeds Delta w (n - agreements) hsub hno)
theorem gcd_residual_count_lt_slope (d:ℕ)
    [GCDMonoid (MvPolynomial (Fin 4) K)]
    (QA QB:MvPolynomial (Fin 4) K) (hQA:QA ≠ 0) (hQB:QB ≠ 0)
    (hboxA:QA ∈ RCN100.globalCoefficientBox K weightedTCap w LCap sT)
    (hboxB:QB ∈ RCN100.globalCoefficientBox K weightedB w LB sB)
    (selected:K → Polynomial K) (seeds:Finset K)
    (nodes:Finset I) (x u0 u1:I → K)
    (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
    (hdegree:∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hA:∀ gamma ∈ seeds,specialization K (selected gamma) gamma QA=0)
    (hB:∀ gamma ∈ seeds,specialization K (selected gamma) gamma QB=0)
    (hagreement:∀ gamma ∈ seeds,agreements ≤
      (nodes.filter (fun i=> (selected gamma).eval (x i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected seeds w (n - agreements))
    (hd:d ≤ wt residualSWeights (gcd12 QA QB))
    (hgcdS:wt residualSWeights (gcd12 QA QB) ≤ sB) :
    (LocatorCover.residual
      (fun gamma=> (specialization K (selected gamma) gamma).toRingHom)
      seeds QA QB).card < ChainGroupMaj.residMaj6802 d + 1:=by
  classical
  let phi:=fun gamma=> (specialization K (selected gamma) gamma).toRingHom
  let Delta:=LocatorCover.residual phi seeds QA QB
  let H:=gcd12 QA QB
  let Q:=quotientB QA QB
  let T:=quotientA QA QB
  have hH:H ≠ 0:=gcd_ne_zero_of_left hQA
  have hQeq:QB=H * Q:=b_eq_gcd12_mul_quotientB QA QB
  have hTeq:QA=H * T:=a_eq_gcd12_mul_quotientA QA QB
  have hQ:Q ≠ 0:=by
    intro hz
    exact hQB (by rw [hQeq,hz,mul_zero])
  have hT:T ≠ 0:=by
    intro hz
    exact hQA (by rw [hTeq,hz,mul_zero])
  have hdsB:d ≤ sB:=hd.trans hgcdS
  have hQflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QB H Q weightedB w LB sB 0 0 d hQB hH hQ hboxB hQeq
    (Nat.zero_le _) (Nat.zero_le _) hd
  have hTflag:=quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    QA H T weightedTCap w LCap sT 0 0 0 hQA hH hT hboxA hTeq
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hQbox0:Q ∈ globalCoefficientBox K weightedB w LB (sB - d):=
    RCN101.flag_box_to_ordinary K
      weightedB w LB (sB - d) Q (by simpa only [Nat.sub_zero] using hQflag)
  have hQbox:Q ∈ globalCoefficientBox K weightedB w LB (max 1 (sB - d)):=
    mem_box_of_R_degree_le Q weightedB w LB (sB - d) (max 1 (sB - d)) hQbox0
      ((degreeOf_R_le_of_mem_box Q weightedB w LB (sB - d) hQbox0).trans (Nat.le_max_right _ _))
  have hTbox:T ∈ globalCoefficientBox K weightedTCap w LCap sT:=
    RCN101.flag_box_to_ordinary K
      weightedTCap w LCap sT T (by simpa only [Nat.sub_zero] using hTflag)
  have hTcaps:=RCN081.degree_bounds_of_mem_box
    T weightedTCap w LCap sT (by decide) hTbox
  rw [show (weightedTCap - 1) / w=yT by decide] at hTcaps
  have hsub:Delta ⊆ seeds:=by
    intro gamma hg
    have hm:gamma ∈ seeds ∧ (phi gamma) (gcd12 QA QB) ≠ 0:=by
      simpa only [Delta,LocatorCover.residual,Finset.mem_filter] using hg
    exact hm.1
  have hsol (gamma:K) (hg:gamma ∈ Delta) :
      specialization K (selected gamma) gamma T=0 ∧
      specialization K (selected gamma) gamma Q=0:=
    LocatorCover.residual_vanish phi seeds QA QB hA hB gamma hg
  have h:=residual_count_lt_slope d hdsB Q T hQ
    (firstQuotients_isRelPrime hQA).symm hQbox hTcaps selected Delta
    nodes x u0 u1 hinj hnodes
    (fun gamma hg=> hdegree gamma (hsub hg))
    (fun gamma hg=> (hsol gamma hg).2) (fun gamma hg=> (hsol gamma hg).1)
    (fun gamma hg=> hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono selected seeds Delta w (n - agreements) hsub hno)
  have hmaj:=residual_le_residMaj d
  change Delta.card < ChainGroupMaj.residMaj6802 d + 1
  omega
end
end ProximityPrize.SubmissionLower.LocatorResidual
end PackedLocator_LocatorResidual

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier252 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalarParameters. -/
section PackedLocator_LocatorScalarParameters

/-! Small shared rows for the 6800 scalar-interpolation receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorScalarParameters

open scoped BigOperators
open ProximityPrize.Benchmark RCN279 RCN285

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

/-- One coefficient row for the retuned seedless interpolant. -/
def coefficientRow (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 30,
    min 1 (134 - i - j) * (17592211 - 131071 * i - 131070 * j)

/-- One local contact-rank row for the retuned seedless interpolant. -/
def rankRow (r : ℕ) : ℕ :=
  seedlessContactRankBound (min r 133) 133 29 (97 - r)

end ProximityPrize.SubmissionLower.LocatorScalarParameters
end PackedLocator_LocatorScalarParameters

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalarCoefficientA. -/
section PackedLocator_LocatorScalarCoefficientA

namespace ProximityPrize.SubmissionLower.LocatorScalarCoefficient

open scoped BigOperators
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 16, coefficientRow i) = 7060158480 := by decide

theorem chunk_16 :
    (∑ i ∈ Finset.range 16, coefficientRow (16 + i)) = 6053533200 := by decide

theorem chunk_32 :
    (∑ i ∈ Finset.range 16, coefficientRow (32 + i)) = 5046907920 := by decide

theorem chunk_48 :
    (∑ i ∈ Finset.range 16, coefficientRow (48 + i)) = 4040282640 := by decide

theorem chunk_64 :
    (∑ i ∈ Finset.range 16, coefficientRow (64 + i)) = 3033657360 := by decide

end ProximityPrize.SubmissionLower.LocatorScalarCoefficient
end PackedLocator_LocatorScalarCoefficientA

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalarCoefficientB. -/
section PackedLocator_LocatorScalarCoefficientB

namespace ProximityPrize.SubmissionLower.LocatorScalarCoefficient

open scoped BigOperators
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_80 :
    (∑ i ∈ Finset.range 16, coefficientRow (80 + i)) = 2027032080 := by decide

theorem chunk_96 :
    (∑ i ∈ Finset.range 16, coefficientRow (96 + i)) = 1026942504 := by decide

theorem chunk_112 :
    (∑ i ∈ Finset.range 16, coefficientRow (112 + i)) = 264607168 := by decide

theorem chunk_128 :
    (∑ i ∈ Finset.range 6, coefficientRow (128 + i)) = 7942648 := by decide

end ProximityPrize.SubmissionLower.LocatorScalarCoefficient
end PackedLocator_LocatorScalarCoefficientB

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalarCoefficient. -/
section PackedLocator_LocatorScalarCoefficient

/-! Assembly of the separately checked scalar coefficient-count chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorScalarCoefficient

open scoped BigOperators
open ProximityPrize.Benchmark RCN279
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 17592211 131071 133 29 = 28561064000 := by
  change (∑ i ∈ Finset.range 134, coefficientRow i) = _
  rw [Finset.sum_range_add coefficientRow 128 6,
    Finset.sum_range_add coefficientRow 112 16,
    Finset.sum_range_add coefficientRow 96 16,
    Finset.sum_range_add coefficientRow 80 16,
    Finset.sum_range_add coefficientRow 64 16,
    Finset.sum_range_add coefficientRow 48 16,
    Finset.sum_range_add coefficientRow 32 16,
    Finset.sum_range_add coefficientRow 16 16,
    chunk_0, chunk_16, chunk_32, chunk_48, chunk_64, chunk_80, chunk_96, chunk_112, chunk_128]

end ProximityPrize.SubmissionLower.LocatorScalarCoefficient
end PackedLocator_LocatorScalarCoefficient

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalarRankA. -/
section PackedLocator_LocatorScalarRankA

namespace ProximityPrize.SubmissionLower.LocatorScalarRank

open scoped BigOperators
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ r ∈ Finset.range 24, rankRow r) = 9000 := by decide

theorem chunk_24 :
    (∑ r ∈ Finset.range 24, rankRow (24 + r)) = 26280 := by decide

theorem chunk_48 :
    (∑ r ∈ Finset.range 24, rankRow (48 + r)) = 43120 := by decide

end ProximityPrize.SubmissionLower.LocatorScalarRank
end PackedLocator_LocatorScalarRankA

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalarRankB. -/
section PackedLocator_LocatorScalarRankB

namespace ProximityPrize.SubmissionLower.LocatorScalarRank

open scoped BigOperators
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_72 :
    (∑ r ∈ Finset.range 24, rankRow (72 + r)) = 30424 := by decide

theorem chunk_96 :
    (∑ r ∈ Finset.range 1, rankRow (96 + r)) = 126 := by decide

end ProximityPrize.SubmissionLower.LocatorScalarRank
end PackedLocator_LocatorScalarRankB

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalarRank. -/
section PackedLocator_LocatorScalarRank

/-! Assembly of the separately checked scalar local-rank chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorScalarRank

open scoped BigOperators
open ProximityPrize.Benchmark RCN279
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem localRankBound_exact :
    localRankBound 97 133 29 = 108950 := by
  change (∑ r ∈ Finset.range 97, rankRow r) = _
  rw [Finset.sum_range_add rankRow 96 1,
    Finset.sum_range_add rankRow 72 24,
    Finset.sum_range_add rankRow 48 24,
    Finset.sum_range_add rankRow 24 24,
    chunk_0, chunk_24, chunk_48, chunk_72, chunk_96]

end ProximityPrize.SubmissionLower.LocatorScalarRank
end PackedLocator_LocatorScalarRank

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_ScP : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_ScCA : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_ScCB : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_ScC : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_ScRA : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_ScRB : True := by trivial
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier6803_ScR : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalarArithmetic. -/
section PackedLocator_LocatorScalarArithmetic
namespace ProximityPrize.SubmissionLower.LocatorScalarArithmetic
open scoped BigOperators
open ProximityPrize.Benchmark RCN279
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80781
def agreements:ℕ:=n - errors
def gap:ℕ:=agreements - w
def prime:ℕ:=2130706433
def multiplicity:ℕ:=97
def yTotalCap:ℕ:=133
def slopeCap:ℕ:=29
def weightedCap:ℕ:=multiplicity * agreements
def listBudget:ℕ:=5224816755
def capY:ℕ:=1 + 2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap - 1)
def regularListNumerator:ℕ:=(n-w)*(capY*slopeCap + capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap - 1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator + singularListCap*gap
theorem coefficient_count_exact:
   coefficientCount weightedCap w yTotalCap slopeCap=28561064000:=by
  simpa [weightedCap,multiplicity,agreements,n,errors,w,yTotalCap,slopeCap]
    using LocatorScalarCoefficient.coefficientCount_exact
theorem local_rank_exact:
   localRankBound multiplicity yTotalCap slopeCap=108950:=by
  simpa [multiplicity,yTotalCap,slopeCap] using
    LocatorScalarRank.localRankBound_exact
theorem nullity_exact:
   coefficientCount weightedCap w yTotalCap slopeCap -
     n * localRankBound multiplicity yTotalCap slopeCap=475200:=by
  rw [coefficient_count_exact,local_rank_exact]
  decide
theorem interpolation_gate:
   n*localRankBound multiplicity yTotalCap slopeCap <
     coefficientCount weightedCap w yTotalCap slopeCap:=by
 rw [coefficient_count_exact,local_rank_exact]
 decide
theorem list_numerator_fits:listNumerator < listBudget*gap:=by decide
theorem exists_seedless_interpolant (received:IRSProfile.Index → IRSProfile.Field) :
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       RCN119.slopeDifference IRSProfile.Field ^ (multiplicity-r) ∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
 obtain ⟨theta,htheta,hzero⟩:=exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index=n by norm_num [IRSProfile.Index,n]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta, ?_⟩
 intro i r
 have hdiv:=all_blocks_divisible_of_kernel IRSProfile.Field
   weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received theta hzero i r
 rw [← translation_reconstruct_coeff IRSProfile.Field weightedCap w
   yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv
end
end ProximityPrize.SubmissionLower.LocatorScalarArithmetic
end PackedLocator_LocatorScalarArithmetic

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier260 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorScalar. -/
section PackedLocator_LocatorScalar
namespace ProximityPrize.SubmissionLower.LocatorScalar
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001 RCN281 RCN019 RCN018
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
private abbrev n:=LocatorScalarArithmetic.n
private abbrev w:=LocatorScalarArithmetic.w
private abbrev errors:=LocatorScalarArithmetic.errors
private abbrev agreements:=LocatorScalarArithmetic.agreements
private abbrev gap:=LocatorScalarArithmetic.gap
private abbrev prime:=LocatorScalarArithmetic.prime
private abbrev multiplicity:=LocatorScalarArithmetic.multiplicity
private abbrev yTotalCap:=LocatorScalarArithmetic.yTotalCap
private abbrev slopeCap:=LocatorScalarArithmetic.slopeCap
private abbrev weightedCap:=LocatorScalarArithmetic.weightedCap
private abbrev listBudget:=LocatorScalarArithmetic.listBudget
private abbrev capY:=LocatorScalarArithmetic.capY
private abbrev capR:=LocatorScalarArithmetic.capR
private abbrev regularListNumerator :=
 LocatorScalarArithmetic.regularListNumerator
private abbrev singularListCap:=LocatorScalarArithmetic.singularListCap
private abbrev listNumerator:=LocatorScalarArithmetic.listNumerator
private theorem list_numerator_fits:listNumerator < listBudget * gap :=
 LocatorScalarArithmetic.list_numerator_fits
private theorem w_pos:0 < w:=by decide
private theorem prime_pos:0 < prime:=by decide
private theorem w_lt_prime:w < prime:=by decide
private theorem w_lt_agreements:w < agreements:=by decide
private theorem agreements_le_n:agreements ≤ n:=by decide
private theorem yTotalCap_lt_prime:yTotalCap < prime:=by decide
private theorem slopeCap_lt_prime:slopeCap < prime:=by decide
private theorem slopeCap_pos:0 < slopeCap:=by decide
private theorem weightedCap_pos:0 < weightedCap:=by decide
private theorem gap_pos:0 < gap:=by decide
private theorem base_dimension_exact:IRSProfile.baseDimension = w + 1:=by
 norm_num [IRSProfile.baseDimension, w, LocatorScalarArithmetic.w]
private theorem index_card_exact:Fintype.card IRSProfile.Index = n:=by
 norm_num [IRSProfile.Index, n, LocatorScalarArithmetic.n]
section
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
private def agreementCap:Fin 3 → ℕ:=![capY, capR, 1]
private theorem seedless_degree_caps
   (Q:MvPolynomial (Fin 4) K)
   (hbox:Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap) :
   Q.degreeOf 1 ≤ yTotalCap ∧ Q.degreeOf 2 ≤ slopeCap ∧
     Q.degreeOf 3 = 0:=by
 refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
   MvPolynomial.degreeOf_le_iff.mpr ?_, ?_⟩
 · intro d hd
   exact (Nat.le_add_right (d 1) (d 2)).trans (hbox hd).1
 · intro d hd
   exact (hbox hd).2.1
 · apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.2.1.le
private theorem agreement_cap
   (phi:Polynomial K →+* GenericField K)
   (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ yTotalCap)
   (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 = 0) (x u:K) :
   ∀ j, (agreementPolynomial phi F w x u 0).degreeOf j ≤ agreementCap j:=by
 have hb:=agreementNumerator_degree_bounds F yTotalCap slopeCap 0
   slopeCap_pos hY hR hZ.le w
     (fun j => (j.factorial:K)⁻¹) x u 0
 intro j
 fin_cases j
 · exact (surfaceMap_degreeOf_le phi _ 0).trans
     (by simpa [agreementCap, capY, LocatorScalarArithmetic.capY]
       using hb.1)
 · exact (surfaceMap_degreeOf_le phi _ 1).trans
     (by simpa [agreementCap, capR, LocatorScalarArithmetic.capR]
       using hb.2.1)
 · exact (surfaceMap_degreeOf_le phi _ 2).trans
     (hb.2.2.trans (by simp [agreementCap]))
private theorem original_regular_seedless_bound
   [CharP K prime]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf 2)
   (hbox:F ∈ RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hY:F.degreeOf 1 ≤ yTotalCap)
   (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 = 0)
   (Gamma:Finset (Polynomial K))
   (hdegree:∀ S ∈ Gamma, S.natDegree ≤ w)
   (hsolutions:∀ S ∈ Gamma, specialization K S 0 F = 0)
   (hregular:∀ S ∈ Gamma,
     specialization K S 0 (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0)
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card = n)
   (hagreement:∀ S ∈ Gamma, agreements ≤
     (nodes.filter (fun i => S.eval (x i) = received i)).card) :
   Gamma.card * gap ≤
     (n - w) * (capY * F.degreeOf 2 + capR * F.degreeOf 1):=by
 classical
 letI:CharP (GenericField K) prime:=genericField_charP K prime
 have hsmall:F.degreeOf 2 < prime:=hR.trans_lt slopeCap_lt_prime
 have hcount (g:RCN281.GeometricFactor K F) :
     (RCN281.geometricPolynomials K F Gamma g).card * gap ≤
       (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0):=by
   obtain ⟨hgirred, hgdiv⟩ :=
     surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
   have hgate:=geometric_factor_regular_gate K (GenericField K) F hF
     prime hRpos hsmall g.1 hgirred
     (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
   have hproper:=RCN281.geometric_seedless_cut_proper
     K g.1 hgate.1
   have hgY:=(geometricFactor_degree_le K F hF.ne_zero g 0).trans hY
   have hgR:=(geometricFactor_degree_le K F hF.ne_zero g 1).trans hR
   have hgZ:g.1.degreeOf 2 = 0:=Nat.eq_zero_of_le_zero
     ((geometricFactor_degree_le K F hF.ne_zero g 2).trans_eq hZ)
   have hGdegree:∀ j:Fin 3, g.1.degreeOf j < prime:=by
     intro j
     fin_cases j
     · exact hgY.trans_lt yTotalCap_lt_prime
     · exact hgR.trans_lt slopeCap_lt_prime
     · simpa [hgZ] using prime_pos
   have hcutDegree:∀ j k:Fin 3, j ≠ k →
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf j *
           g.1.degreeOf k +
         g.1.degreeOf j *
           (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf k < prime:=by
     intro j k hjk
     have h0:=hGdegree 0
     have h1:=hGdegree 1
     have h2:=hGdegree 2
     fin_cases j <;> fin_cases k <;>
       simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne] at hjk ⊢ <;>
       omega
   have hsub:=RCN281.geometricPolynomials_subset K F Gamma g
   have hraw:=seedless_proper_cut_bound (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F g.1 hgirred hgdiv hproper
     (RCN281.geometricPolynomials K F Gamma g)
     nodes x received hinj prime w agreements
     w_pos w_lt_prime w_lt_agreements
     (by rw [hnodes]; exact agreements_le_n)
     hGdegree hcutDegree
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolutions S (hsub hS))
     (fun S hS => selectedPoint_regular_of_specialization K F
       (fun _:K => S) 0 (hregular S (hsub hS)))
     (fun S hS => (Finset.mem_filter.mp hS).2)
     (fun S hS => hagreement S (hsub hS)) agreementCap
     (fun i hi => agreement_cap K (polynomialEmbedding K) F hY hR hZ
       (x i) (received i))
   have hx0 :
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 0 = 0:=by
     simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne (by decide:(0:Fin 3) ≠ 2)]
   have hx1 :
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1 = 0:=by
     simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3) ≠ 2)]
   have hx2 :
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 2 = 1:=by
     simp [seedlessCut]
   have hm0:coordinateMixedDegree (GenericField K) g.1 seedlessCut 0 =
       g.1.degreeOf 1:=by
     rw [RCN001.coordinateMixedDegree_zero, hx1, hx2]
     omega
   have hm1:coordinateMixedDegree (GenericField K) g.1 seedlessCut 1 =
       g.1.degreeOf 0:=by
     rw [RCN001.coordinateMixedDegree_one, hx0, hx2]
     omega
   have hm2:coordinateMixedDegree (GenericField K) g.1 seedlessCut 2 = 0:=by
     rw [RCN001.coordinateMixedDegree_two, hx0, hx1]
     omega
   have hcost :
       (∑ i:Fin 3, agreementCap i *
         coordinateMixedDegree (GenericField K) g.1 seedlessCut i) =
       capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0:=by
     simp [Fin.sum_univ_succ, agreementCap, hm0, hm1, hm2]
   rw [hnodes, hcost] at hraw
   change (RCN281.geometricPolynomials K F Gamma g).card *
       (agreements - w) ≤
     (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0)
   exact hraw
 calc
   Gamma.card * gap ≤
       (∑ g:RCN281.GeometricFactor K F,
         (RCN281.geometricPolynomials K F Gamma g).card) * gap :=
     Nat.mul_le_mul_right _
       (RCN281.card_le_sum_geometricPolynomials
         K F hF.ne_zero Gamma hsolutions)
   _ = ∑ g:RCN281.GeometricFactor K F,
       (RCN281.geometricPolynomials K F Gamma g).card * gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:RCN281.GeometricFactor K F,
       (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0) :=
     Finset.sum_le_sum (fun g _ => hcount g)
   _ = (n - w) *
       (capY * (∑ g:RCN281.GeometricFactor K F,
         g.1.degreeOf 1) +
       capR * (∑ g:RCN281.GeometricFactor K F,
         g.1.degreeOf 0)):=by
     rw [← Finset.mul_sum, Finset.sum_add_distrib,
       ← Finset.mul_sum, ← Finset.mul_sum]
   _ ≤ (n - w) * (capY * F.degreeOf 2 + capR * F.degreeOf 1):=by
     apply Nat.mul_le_mul_left
     exact Nat.add_le_add
       (Nat.mul_le_mul_left capY (geometricFactor_sum_degree_le K F hF.ne_zero 1))
       (Nat.mul_le_mul_left capR (geometricFactor_sum_degree_le K F hF.ne_zero 0))
private theorem singular_seedless_card_le
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
   (hbox:Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S ∈ Gamma,
     specialization K S 0 (singularAuxiliary Q) = 0) :
   Gamma.card ≤ singularListCap:=by
 classical
 let phi:=polynomialEmbedding K
 let J:=singularAuxiliary Q
 have hcaps:=seedless_degree_caps K Q hbox
 have hJne:J ≠ 0:=singularAuxiliary_nonzero Q hQ prime
   (hcaps.2.1.trans_lt slopeCap_lt_prime)
 have hJR:J.degreeOf 2 = 0:=singularAuxiliary_R_degree Q hQ prime
   (hcaps.2.1.trans_lt slopeCap_lt_prime)
 have hQY:MvPolynomial.weightedTotalDegree
     RCN281.yWeights Q ≤ yTotalCap:=by
   apply (weightedTotalDegree_le_iff
     RCN281.yWeights Q yTotalCap).mpr
   intro d hd
   have hh:=(hbox hd).1
   rw [weight_fin4]
   simpa [RCN281.yWeights] using
     (Nat.le_add_right (d 1) (d 2)).trans hh
 have hQZ:MvPolynomial.weightedTotalDegree
     RCN281.zWeights Q ≤ 0:=by
   apply (weightedTotalDegree_le_iff
     RCN281.zWeights Q 0).mpr
   intro d hd
   have hh:=(hbox hd).2.2.1
   rw [weight_fin4]
   simpa [RCN281.zWeights, hh]
 have hJYw:=singularAuxiliary_weight_le
   RCN281.yWeights Q hQ slopeCap
   slopeCap_pos hcaps.2.1
 have hJZw:=singularAuxiliary_weight_le
   RCN281.zWeights Q hQ slopeCap
   slopeCap_pos hcaps.2.1
 have hJY:J.degreeOf 1 ≤ singularListCap :=
   (RCN281.degreeY_le_yWeight K J).trans
     (hJYw.trans (by
       simp only [singularListCap, LocatorScalarArithmetic.singularListCap]
       exact Nat.mul_le_mul_left _ hQY))
 have hJZ:J.degreeOf 3 = 0:=Nat.eq_zero_of_le_zero
   ((RCN281.degreeZ_le_zWeight K J).trans
     (hJZw.trans (by
       simpa only [Nat.mul_zero] using
         Nat.mul_le_mul_left (2 * slopeCap - 1) hQZ)))
 let A:MvPolynomial (Fin 3) (GenericField K):=surfaceMap phi J
 have hAne:A ≠ 0:=surfaceMap_ne_zero phi
   (polynomialEmbedding_injective K) J hJne
 have hAR:A.degreeOf 1 = 0:=Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 1).trans_eq hJR)
 have hAZ:A.degreeOf 2 = 0:=Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 2).trans_eq hJZ)
 let q:Polynomial (GenericField K) :=
   RCN281.yProjection (GenericField K) A
 have hq:q ≠ 0 :=
   RCN281.yProjection_nonzero A hAne hAR hAZ
 have hroots:∀ z ∈ Gamma.image phi, z ∈ q.roots:=by
   intro z hz
   obtain ⟨S, hS, rfl⟩:=Finset.mem_image.mp hz
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (phi S) = 0
   have hv:seedlessPoint phi S 0 = phi S:=by
     simp [seedlessPoint_value]
   change (RCN281.yProjection (GenericField K) A).eval
     (phi S) = 0
   rw [← hv, RCN281.yProjection_eval A hAR hAZ
     (seedlessPoint phi S)]
   rw [seedlessPoint_surface_evaluation, eval_polynomialPoint_eq_specialization,
     hsolutions S hS]
   simp
 have hcard:(Gamma.image phi).card = Gamma.card :=
   Finset.card_image_of_injective _ (polynomialEmbedding_injective K)
 rw [← hcard]
 calc
   (Gamma.image phi).card ≤ q.roots.toFinset.card:=by
     apply Finset.card_le_card
     intro z hz
     exact Multiset.mem_toFinset.mpr (hroots z hz)
   _ ≤ q.roots.card:=Multiset.toFinset_card_le _
   _ ≤ q.natDegree:=Polynomial.card_roots' q
   _ ≤ A.degreeOf 0:=RCN281.yProjection_natDegree_le A
   _ ≤ J.degreeOf 1:=surfaceMap_degreeOf_le phi J 0
   _ ≤ singularListCap:=hJY
theorem seedless_list_card_le
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q ≠ 0)
   (hbox:Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hlegacy:Q ∈ RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card = n)
   (hdegree:∀ S ∈ Gamma, S.natDegree ≤ w)
   (hsolutions:∀ S ∈ Gamma, specialization K S 0 Q = 0)
   (hagreement:∀ S ∈ Gamma, agreements ≤
     (nodes.filter (fun i => S.eval (x i) = received i)).card) :
   Gamma.card ≤ listBudget:=by
 classical
 have hcaps:=seedless_degree_caps K Q hbox
 have hsing:(singularPolynomials K Q Gamma).card ≤ singularListCap :=
   singular_seedless_card_le K Q hQ hbox (singularPolynomials K Q Gamma)
     (fun S hS => (Finset.mem_filter.mp hS).2)
 have hreg (F:↥(positiveRFactors Q)) :
     (regularPolynomials K Q Gamma F).card * gap ≤
       (n - w) * (capY * F.1.degreeOf 2 + capR * F.1.degreeOf 1):=by
   have hdata:=directFactor_data Q F.1 hQ weightedCap w yTotalCap slopeCap
     hlegacy F.2
   have hdivF:=(positiveRFactors_spec Q F.1 F.2).2.1
   have hFZ:F.1.degreeOf 3 = 0:=Nat.eq_zero_of_le_zero
     ((degreeOf_le_of_dvd 3 F.1 Q hdivF hQ).trans_eq hcaps.2.2)
   have hsub:regularPolynomials K Q Gamma F ⊆ Gamma:=Finset.filter_subset _ _
   exact original_regular_seedless_bound K F.1 hdata.1 hdata.2.1 hdata.2.2
     ((degreeOf_le_of_dvd 1 F.1 Q hdivF hQ).trans hcaps.1)
     ((degreeOf_le_of_dvd 2 F.1 Q hdivF hQ).trans hcaps.2.1)
     hFZ (regularPolynomials K Q Gamma F)
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => (Finset.mem_filter.mp hS).2.1)
     (fun S hS => (Finset.mem_filter.mp hS).2.2)
     nodes x received hinj hnodes (fun S hS => hagreement S (hsub hS))
 have hsumY:=sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 1
 have hsumR:=sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 2
 have hsumY':(∑ F:↥(positiveRFactors Q), F.1.degreeOf 1) ≤ Q.degreeOf 1:=by
   simpa only [Finset.sum_coe_sort, id_eq] using hsumY
 have hsumR':(∑ F:↥(positiveRFactors Q), F.1.degreeOf 2) ≤ Q.degreeOf 2:=by
   simpa only [Finset.sum_coe_sort, id_eq] using hsumR
 have hregularScaled :
     (∑ F:↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap ≤
       regularListNumerator:=by
   calc
     _ = ∑ F:↥(positiveRFactors Q),
         (regularPolynomials K Q Gamma F).card * gap:=by rw [Finset.sum_mul]
     _ ≤ ∑ F:↥(positiveRFactors Q),
         (n - w) * (capY * F.1.degreeOf 2 + capR * F.1.degreeOf 1) :=
       Finset.sum_le_sum (fun F _ => hreg F)
     _ = (n - w) * (capY * (∑ F:↥(positiveRFactors Q), F.1.degreeOf 2) +
         capR * (∑ F:↥(positiveRFactors Q), F.1.degreeOf 1)):=by
       rw [← Finset.mul_sum, Finset.sum_add_distrib,
         ← Finset.mul_sum, ← Finset.mul_sum]
     _ ≤ (n - w) * (capY * slopeCap + capR * yTotalCap):=by
       apply Nat.mul_le_mul_left
       exact Nat.add_le_add (Nat.mul_le_mul_left capY (hsumR'.trans hcaps.2.1))
         (Nat.mul_le_mul_left capR (hsumY'.trans hcaps.1))
     _ = regularListNumerator:=rfl
 have hcover:=seedless_solution_cover K Q hQ Gamma hsolutions
 have hscaled:=Nat.mul_le_mul_right gap hcover
 have htotal:Gamma.card * gap ≤ listNumerator:=by
   calc
     Gamma.card * gap ≤
         ((singularPolynomials K Q Gamma).card +
           ∑ F:↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap :=
       hscaled
     _ = (singularPolynomials K Q Gamma).card * gap +
         (∑ F:↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap:=by
       ring
     _ ≤ singularListCap * gap + regularListNumerator :=
       Nat.add_le_add (Nat.mul_le_mul_right gap hsing) hregularScaled
     _ = listNumerator:=by
       simp only [listNumerator, LocatorScalarArithmetic.listNumerator,
         regularListNumerator, singularListCap, gap]
       omega
 by_contra hnot
 have hlarge:listBudget < Gamma.card:=Nat.lt_of_not_ge hnot
 have hgap:0 < gap:=gap_pos
 have hmul:=Nat.mul_lt_mul_of_pos_right hlarge hgap
 have hcontra:listBudget * gap < listNumerator:=hmul.trans_le htotal
 exact (Nat.not_lt_of_ge hcontra.le) list_numerator_fits
end
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem exists_seedless_vanishing_interpolant
   (received:IRSProfile.Index → IRSProfile.Field) :
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧
     Q ∈ RCN279.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap ∧
     Q ∈ RCN174.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap ∧
     ∀ (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i ∈ support, P.eval (IRSProfile.domain i) = received i) →
       RCN319.specialization IRSProfile.Field P 0 Q = 0:=by
 classical
 obtain ⟨Q, hQ, hbox, hcontact⟩ :=
   LocatorScalarArithmetic.exists_seedless_interpolant received
 change Q ∈ RCN279.globalCoefficientBox IRSProfile.Field
   weightedCap w yTotalCap slopeCap at hbox
 have hlegacy:Q ∈ RCN174.globalCoefficientBox IRSProfile.Field
     weightedCap w yTotalCap slopeCap:=by
   intro d hd
   obtain ⟨hYR, hR, hZ, hweight⟩:=hbox hd
   exact ⟨by omega, hR, hweight⟩
 refine ⟨Q, hQ, hbox, hlegacy, ?_⟩
 intro P support hdegree hcard hvalues
 apply RCN319.specialization_eq_zero_of_contact_and_degree
   IRSProfile.Field Q P 0 IRSProfile.domain received (fun _ => 0)
     support multiplicity
 · intro i hi r
   exact hcontact i r
 · intro i hi
   simpa only [mul_zero, add_zero] using hvalues i hi
 · have hdeg:=RCN319.specialization_natDegree_lt
     IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
     weightedCap_pos
     hlegacy hdegree
   have hbound:weightedCap ≤ multiplicity * support.card:=by
     rw [weightedCap]
     exact Nat.mul_le_mul_left multiplicity hcard
   exact hdeg.trans_le hbound
theorem irs_scalar_finite_list_card_le
   (received:IRSProfile.Index → IRSProfile.Field)
   (L:Finset (IRSProfile.Index → IRSProfile.Field))
   (hcode:∀ c ∈ L, c ∈ IRSProfile.baseCode)
   (hclose:∀ c ∈ L, agreements ≤
     (Finset.univ.filter (fun i => c i = received i)).card) :
   L.card ≤ listBudget:=by
 classical
 let D:=↥L
 let codeword:D → IRSProfile.baseCode:=fun c => ⟨c.1, hcode c.1 c.2⟩
 let selected:D → Polynomial IRSProfile.Field:=fun c => ReedSolomon.toPolynomial (codeword c)
 let Gamma:Finset (Polynomial IRSProfile.Field):=Finset.univ.image selected
 have hselected:Function.Injective selected:=by
   intro c d h
   apply Subtype.ext
   funext i
   have hh:=congrArg (fun P:Polynomial IRSProfile.Field =>
     P.eval (IRSProfile.domain i)) h
   simpa only [selected, ReedSolomon.toPolynomial_eval_at_domain] using hh
 have hcard:Gamma.card = L.card:=by
   rw [show Gamma = Finset.univ.image selected by rfl,
     Finset.card_image_of_injective _ hselected, Finset.card_univ,
     Fintype.card_coe]
 obtain ⟨Q, hQ, hbox, hlegacy, hvanish⟩ :=
   exists_seedless_vanishing_interpolant received
 have hdegree:∀ P ∈ Gamma, P.natDegree ≤ w:=by
   intro P hP
   obtain ⟨c, hc, rfl⟩:=Finset.mem_image.mp hP
   have hp:=ReedSolomon.toPolynomial_mem_lt_deg (codeword c)
   have hdeg:(selected c).degree < ((w + 1:ℕ):WithBot ℕ):=by
     have hh:=Polynomial.mem_degreeLT.mp hp
     change (selected c).degree <
       ((IRSProfile.baseDimension:ℕ):WithBot ℕ) at hh
     rw [base_dimension_exact] at hh
     exact hh
   by_cases hz:selected c = 0
   · simp [hz]
   · rw [← Polynomial.natDegree_lt_iff_degree_lt hz] at hdeg
     omega
 have hsolution:∀ P ∈ Gamma, specialization IRSProfile.Field P 0 Q = 0:=by
   intro P hP
   obtain ⟨c, hc, rfl⟩:=Finset.mem_image.mp hP
   let A:=Finset.univ.filter (fun i => c.1 i = received i)
   apply hvanish (selected c) A (hdegree (selected c)
     (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩))
     (hclose c.1 c.2)
   intro i hi
   have hcval:=ReedSolomon.toPolynomial_eval_at_domain (c:=codeword c) (i:=i)
   exact hcval.trans (Finset.mem_filter.mp hi).2
 have hagreement:∀ P ∈ Gamma, agreements ≤
     (Finset.univ.filter (fun i => P.eval (IRSProfile.domain i) = received i)).card:=by
   intro P hP
   obtain ⟨c, hc, rfl⟩:=Finset.mem_image.mp hP
   have heq:Finset.univ.filter
       (fun i => (selected c).eval (IRSProfile.domain i) = received i) =
       Finset.univ.filter (fun i => c.1 i = received i):=by
     apply Finset.filter_congr
     intro i hi
     rw [ReedSolomon.toPolynomial_eval_at_domain]
   rw [heq]
   exact hclose c.1 c.2
 have hbound:=seedless_list_card_le IRSProfile.Field Q hQ hbox hlegacy Gamma
   (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain received
   IRSProfile.domain.injective.injOn
   (by simpa using index_card_exact) hdegree hsolution hagreement
 rwa [hcard] at hbound
end
end ProximityPrize.SubmissionLower.LocatorScalar
end PackedLocator_LocatorScalar

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier261 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorProtocol. -/
section PackedLocator_LocatorProtocol
namespace ProximityPrize.SubmissionLower.LocatorProtocol
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280
open scoped NNReal
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
def n:ℕ:=262144
def errors:ℕ:=80781
def agreements:ℕ:=n-errors
def listBudget:ℕ:=5224816755
def mcaBudget:ℕ:=274980722886578332
def radius:ℝ≥0:=LocatorArithmetic.radius
theorem sixteen_row_separation:
   15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field:=by
 rw [show Fintype.card IRSProfile.Field= (2130706433:ℕ) ^ 6 by
   norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize],
   Nat.choose_eq_descFactorial_div_factorial]
 norm_num [listBudget,Nat.descFactorial_succ,Nat.factorial_succ]
theorem squared_eight_lambda_new
   (delta:ℝ)
   (hcell:(delta:ℝ) * (Fintype.card IRSProfile.Index:ℝ) <
     ((errors + 1:ℕ):ℝ)) :
   Code.Lambda
     (((IRSProfile.baseCode ^⋈ (Fin 8)) ^⋈ (Fin 2) :
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin 8 → IRSProfile.Field)) :
       Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))
     delta ≤ (listBudget:ℕ∞):=by
 apply RCN280.squared_eight_lambda_le_of_interleaved_list
   IRSProfile.baseCode errors listBudget ?_ delta hcell
 intro received L hrows hclose
 have hclose':∀ v ∈ L,agreements ≤
     (Finset.univ.filter (fun i=> v i=received i)).card:=by
   intro v hv
   simpa [agreements,n,errors,IRSProfile.Index] using hclose v hv
 classical
 letI:DecidableEq (IRSProfile.Index → Fin 16 → IRSProfile.Field):=Classical.decEq _
 letI:DecidableEq (IRSProfile.Index → IRSProfile.Field):=Classical.decEq _
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩ :=
   Finset.exists_subset_card_eq (show listBudget + 1 ≤ L.card by omega)
 have hsepD:15 * D.card.choose 2 < Fintype.card IRSProfile.Field:=by
   rw [hDcard]
   exact sixteen_row_separation
 obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
 let projected:Finset (IRSProfile.Index → IRSProfile.Field) :=
   D.image (momentProjection (ι:=IRSProfile.Index) (r:=16) t)
 have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
 have hcode:∀ c ∈ projected,c ∈ IRSProfile.baseCode:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
 have hnear:∀ c ∈ projected,agreements ≤
     (Finset.univ.filter (fun i=> c i=momentProjection t received i)).card:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact (hclose' v (hDL hv)).trans
     (Finset.card_le_card (momentProjection_preserves_agreements t v received))
 have hbound:=LocatorScalar.irs_scalar_finite_list_card_le
   (momentProjection t received) projected hcode hnear
 change projected.card ≤ listBudget at hbound
 rw [hprojcard,hDcard] at hbound
 omega
theorem lambda_le:
   Code.Lambda
     ((IRSProfile.code ^⋈ (Fin 2) :
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (radius:ℝ) ≤ (listBudget:ℕ∞):=by
 rw [irs_squared_carrier_eq]
 apply squared_eight_lambda_new (radius:ℝ)
 norm_num [radius,LocatorArithmetic.radius,claimedRadius,
   LocatorArithmetic.radiusNumerator,
   LocatorArithmetic.radiusDenominator,
   errors,IRSProfile.Index]
theorem base_mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ) ≤
     ENNReal.ofReal ((mcaBudget:ℝ) / Fintype.card IRSProfile.Field):=by
 apply mcaError_affineLine_le_of_givenSetsBound
 apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
   (radius:ℝ) errors mcaBudget
 · intro A hA
   have hcomp:=
     (mul_one_sub_le_card_iff_sub_card_le_floor A
       (show (0:ℝ) ≤ (radius:ℝ) by positivity)).mp hA
   rw [show ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors by
     simpa only [radius,errors,LocatorArithmetic.errors] using
       LocatorArithmetic.radius_floor] at hcomp
   have hn:Fintype.card IRSProfile.Index=262144:=by
     norm_num [IRSProfile.Index]
   rw [hn]
   norm_num [errors,LocatorArithmetic.errors] at hcomp ⊢
   omega
 · exact halign
theorem mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
       (radius:ℝ) ≤
     (mcaBudget:ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
 calc
   _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ):=by
     rw [RCN284.irs_code_eq_base_interleaved]
     exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
       IRSProfile.interleaving radius
       (by norm_num [IRSProfile.interleaving])
       (by norm_num [radius,LocatorArithmetic.radius,
         claimedRadius,LocatorArithmetic.radiusNumerator,
         LocatorArithmetic.radiusDenominator])
       (by norm_num [radius,LocatorArithmetic.radius,
         claimedRadius,LocatorArithmetic.radiusNumerator,
         LocatorArithmetic.radiusDenominator])
   _ ≤ ENNReal.ofReal
       ((mcaBudget:ℝ) / Fintype.card IRSProfile.Field) :=
     base_mca_le_of_alignment halign
   _= (mcaBudget:ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
       ENNReal.ofReal_natCast]
theorem field_capacity_split:
   2 ^ (128:ℕ) * (mcaBudget + listBudget) ≤
     Fintype.card IRSProfile.Field:=by
 rw [RCN284.field_cardinality]
 norm_num [mcaBudget,listBudget]
theorem certifiedGammaError_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   certifiedGammaError IRSProfile.code radius ≤
     (1:ℝ≥0) / 2 ^ (128:ℕ):=by
 rw [← ENNReal.coe_le_coe,coe_certifiedGammaError]
 push_cast
 have hLambdaNat:=ENat.toNat_le_of_le_coe lambda_le
 have hList:
     ((Code.Lambda
       ((IRSProfile.code ^⋈ (Fin 2) :
         ModuleCode IRSProfile.Index IRSProfile.Field
           (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
         Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
           IRSProfile.Field))
       (radius:ℝ)).toNat:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) ≤
       (listBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) :=
   ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
 calc
   _ ≤ (mcaBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) +
       (listBudget:ENNReal) /
         (Fintype.card IRSProfile.Field:ENNReal) :=
     add_le_add (mca_le_of_alignment halign) hList
   _= ((mcaBudget + listBudget:ℕ):ENNReal) /
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [← ENNReal.add_div,Nat.cast_add]
   _ ≤ (1:ENNReal) / 2 ^ (128:ℕ):=by
     apply RCN284.nat_div_le_inv_pow
     · norm_num [mcaBudget,listBudget]
     · simpa only [Nat.mul_comm] using field_capacity_split
theorem protocolClaim6803_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
   ProtocolClaim 6803 10340095 33554432 where
 admissible:=LocatorArithmetic.radius_admissible
 reduction:=by
   change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
   simpa [reductionTarget,ProximityGap.prizeThreshold] using
     certifiedGammaError_le_of_alignment halign
 score:=by
   change (1 - LocatorArithmetic.radius) ^
     IRSProfile.repetitions ≤ claimedError 6803
   exact LocatorArithmetic.score_target_le
end
end ProximityPrize.SubmissionLower.LocatorProtocol
end PackedLocator_LocatorProtocol

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier262 : True := by trivial
end ProximityPrize.SubmissionLower
