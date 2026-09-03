import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseChecked
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptDirectCore

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
  1 ≤ p.all ∧ p.all ≤ 28 ∧ middle p ≤ 127 ∧ total p ≤ 5964

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

def fastAfterS390 : FlagDegree → ℕ :=
  fastApply fastAfterF500 split390Potential s390Threshold s390Prefix

/-- The exact numerical obligations for one positive raw-slope layer.  Each
state checks all four terminal inequalities, the narrow maximum, and the
correlated initial-A complement. -/
def PhaseStateRCheck (R : ℕ) : Prop :=
  ∀ V ∈ List.range (128 - R),
    ∀ z ∈ List.range (5965 - (R + V)),
      let p := rawFlag R V z
      (rThreshold R V ≤ z ∨
        checkedBaseCap p ≤ r1200Potential.eval p + rPrefix p) ∧
      (cThreshold R V ≤ z ∨
        fastAfterR p ≤ sourceCPotential.eval p + cPrefix p) ∧
      (f500Threshold R V ≤ z ∨
        fastAfterC p ≤ split500Potential.eval p + f500Prefix p) ∧
      (s390Threshold R V ≤ z ∨
        fastAfterF500 p ≤ split390Potential.eval p + s390Prefix p) ∧
      fastAfterS390 p ≤ certifiedNarrowMaximum ∧
      fastAfterS390 p + initialAComplement p ≤ certifiedJointMaximum

instance (R : ℕ) : Decidable (PhaseStateRCheck R) := by
  unfold PhaseStateRCheck
  infer_instance

def PhaseStateChecks : Prop :=
  ∀ R ∈ List.range 29, 1 ≤ R → PhaseStateRCheck R

instance : Decidable PhaseStateChecks := by
  unfold PhaseStateChecks
  infer_instance

/-! ## Semantic extraction from the finite predicates -/

theorem threshold_indexed_at (h : ThresholdsIndexed)
    (R V : ℕ) (hR : 1 ≤ R) (hR28 : R ≤ 28) (hRV : R + V ≤ 127) :
    let q := lookupThreshold R V
    q.r = R ∧ q.v = V ∧ ThresholdSufficient q := by
  apply h R
  · exact List.mem_range.mpr (by omega)
  · exact hR
  · exact List.mem_range.mpr (by omega)

theorem prefix_indexed_at (h : PrefixesIndexed)
    (R V : ℕ) (hR : 1 ≤ R) (hR27 : R ≤ 27)
    (hRV : R + 1 + V ≤ 127) :
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
    (hsourceCap : 5964 ≤ s.totalCap)
    (p : FlagDegree) (hp : NarrowState p) :
    field (lookupThreshold p.all p.yz) ≤ p.zOnly → s.Routeable p := by
  rcases hp with ⟨hr, hr28, hy, ht⟩
  have hry : p.all + p.yz ≤ 127 := by
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
  · have hz : p.zOnly ≤ 5964 - (p.all + p.yz) := by
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

theorem routeableS390_of_cutoff (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) :
    s390Threshold p.all p.yz ≤ p.zOnly → sourceSplit390.Routeable p := by
  exact routeable_of_threshold_field h sourceSplit390 ThresholdReceipt.split390
    (fun q hq ↦ hq.2.2.2.2.2.2) (by decide) p hp

def afterR : FlagDegree → ℕ :=
  applyPhase checkedBaseCap r1200Potential sourceR1200.Routeable rPrefix

def afterC : FlagDegree → ℕ :=
  applyPhase afterR sourceCPotential sourceC.Routeable cPrefix

def afterF500 : FlagDegree → ℕ :=
  applyPhase afterC split500Potential sourceSplit500.Routeable f500Prefix

def afterS390 : FlagDegree → ℕ :=
  applyPhase afterF500 split390Potential sourceSplit390.Routeable s390Prefix

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

theorem afterS390_eq_zero_of_not_narrow {p : FlagDegree} (hp : ¬ NarrowState p) :
    afterS390 p = 0 := by
  exact applyPhase_eq_zero afterF500 split390Potential sourceSplit390 s390Prefix p
    (afterF500_eq_zero_of_not_narrow hp)

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

theorem afterS390_le_fast (h : ThresholdsIndexed) (p : FlagDegree)
    (hp : NarrowState p) : afterS390 p ≤ fastAfterS390 p := by
  exact applyPhase_le_fastApply afterF500 fastAfterF500 split390Potential
    sourceSplit390.Routeable s390Threshold s390Prefix p
    (afterF500_le_fast h p hp) (routeableS390_of_cutoff h p hp)

theorem phase_state_checked_at (h : PhaseStateChecks) (p : FlagDegree)
    (hp : NarrowState p) :
    (rThreshold p.all p.yz ≤ p.zOnly ∨
        checkedBaseCap p ≤ r1200Potential.eval p + rPrefix p) ∧
    (cThreshold p.all p.yz ≤ p.zOnly ∨
        fastAfterR p ≤ sourceCPotential.eval p + cPrefix p) ∧
    (f500Threshold p.all p.yz ≤ p.zOnly ∨
        fastAfterC p ≤ split500Potential.eval p + f500Prefix p) ∧
    (s390Threshold p.all p.yz ≤ p.zOnly ∨
        fastAfterF500 p ≤ split390Potential.eval p + s390Prefix p) ∧
    fastAfterS390 p ≤ certifiedNarrowMaximum ∧
    fastAfterS390 p + initialAComplement p ≤ certifiedJointMaximum := by
  rcases hp with ⟨hr, hr28, hy, ht⟩
  have hry : p.all + p.yz ≤ 127 := by
    simpa only [middle, Nat.add_comm] using hy
  have hrz : p.all + p.yz + p.zOnly ≤ 5964 := by
    simpa only [total, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
  have hR := h p.all (List.mem_range.mpr (by omega)) hr
  have hV : p.yz ∈ List.range (128 - p.all) :=
    List.mem_range.mpr (by omega)
  have hZ : p.zOnly ∈ List.range (5965 - (p.all + p.yz)) :=
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

theorem s390_terminal (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks) :
    ∀ p, ¬ sourceSplit390.Routeable p →
      afterF500 p ≤ split390Potential.eval p + s390Prefix p := by
  intro p hn
  by_cases hp : NarrowState p
  · have hs := (phase_state_checked_at hstate p hp).2.2.2.1
    exact (afterF500_le_fast hindex p hp).trans
      (hs.resolve_left
        (fun hz ↦ hn (routeableS390_of_cutoff hindex p hp hz)))
  · rw [afterF500_eq_zero_of_not_narrow hp]
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
    (R V : ℕ) (hR : 1 ≤ R) (hR27 : R ≤ 27)
    (hRV : R + 1 + V ≤ 127) :
    rPrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
    f500PrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
    s390PrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
    (∀ b ∈ List.range 21, cPrefixAt R V b ≤ prefixSentinel) ∧
    (R + 1 ≤ 27 ∧ R + 1 + 1 + V ≤ 127 →
      rPrefixCore (rawFlag R V 0) ≤ rPrefixCore (rawFlag (R + 1) V 0) ∧
      f500PrefixCore (rawFlag R V 0) ≤
        f500PrefixCore (rawFlag (R + 1) V 0) ∧
      s390PrefixCore (rawFlag R V 0) ≤
        s390PrefixCore (rawFlag (R + 1) V 0) ∧
      ∀ b ∈ List.range 21, cPrefixAt R V b ≤ cPrefixAt (R + 1) V b) ∧
    (R + 1 + (V + 1) ≤ 127 →
      rPrefixCore (rawFlag R V 0) ≤ rPrefixCore (rawFlag R (V + 1) 0) ∧
      f500PrefixCore (rawFlag R V 0) ≤
        f500PrefixCore (rawFlag R (V + 1) 0) ∧
      s390PrefixCore (rawFlag R V 0) ≤
        s390PrefixCore (rawFlag R (V + 1) 0) ∧
      ∀ b ∈ List.range 21, cPrefixAt R V b ≤ cPrefixAt R (V + 1) b) ∧
    (∀ b ∈ List.range 20, cPrefixAt R V b ≤ cPrefixAt R V (b + 1)) := by
  exact h R (List.mem_range.mpr (by omega)) hR V
    (List.mem_range.mpr (by omega))

private theorem cPrefixAt_mono_bucket (h : PrefixCoreChecks)
    (R V b₁ b₂ : ℕ) (hR : 1 ≤ R) (hR27 : R ≤ 27)
    (hRV : R + 1 + V ≤ 127)
    (hb : b₁ ≤ b₂) (hb₂ : b₂ ≤ 20) :
    cPrefixAt R V b₁ ≤ cPrefixAt R V b₂ := by
  have hsteps := (core_check_at h R V hR hR27 hRV).2.2.2.2.2.2
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
  induction d with
  | zero => rfl
  | succ d ih =>
      have hprev : b₁ + d ≤ 20 := by omega
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
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.1
    have hstep := hrow ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega⟩
    simpa only [rPrefixCore, rawFlag] using hstep.1
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.1
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
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.1
    have hstep := hrow ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega⟩
    simpa only [f500PrefixCore, rawFlag] using hstep.2.1
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.1
    have hstep := hrow (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)
    simpa only [f500PrefixCore, rawFlag] using hstep.2.1
  · intro r v z _
    rfl

theorem s390CoreGridSound (h : PrefixCoreChecks) :
    CoreGridSound s390PrefixCore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hr, hr27, hrv, _⟩
    simpa [s390PrefixCore, rawFlag] using
      (core_check_at h p.all p.yz hr hr27 hrv).2.2.1
  · intro r v z hr hvalid
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.1
    have hstep := hrow ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega⟩
    simpa only [s390PrefixCore, rawFlag] using hstep.2.2.1
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := (core_check_at h r v hr hr27 (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)).2.2.2.2.2.1
    have hstep := hrow (by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega)
    simpa only [s390PrefixCore, rawFlag] using hstep.2.2.1
  · intro r v z _
    rfl

theorem cCoreGridSound (h : PrefixCoreChecks) : CoreGridSound cPrefixCore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hr, hr27, hrv, htotal⟩
    have hb : cBucket p.zOnly ∈ List.range 21 :=
      List.mem_range.mpr (Nat.lt_succ_iff.mpr
        (cBucket_le_20 p.zOnly (by omega)))
    simpa [cPrefixCore, rawFlag] using
      (core_check_at h p.all p.yz hr hr27 hrv).2.2.2.1 _ hb
  · intro r v z hr hvalid
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrv : r + 1 + v ≤ 127 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hnext : r + 1 + 1 + v ≤ 127 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hb20 : cBucket z ≤ 20 := by
      apply cBucket_le_20
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hstep := (core_check_at h r v hr hr27 hrv).2.2.2.2.1 ⟨by
      simp only [PrefixValid, rawFlag] at hvalid
      omega, hnext⟩
    simpa only [cPrefixCore, rawFlag] using
      hstep.2.2.2 (cBucket z) (List.mem_range.mpr (by omega))
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrv : r + 1 + v ≤ 127 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hnext : r + 1 + (v + 1) ≤ 127 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hb20 : cBucket z ≤ 20 := by
      apply cBucket_le_20
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hstep := (core_check_at h r v hr hr27 hrv).2.2.2.2.2.1 hnext
    simpa only [cPrefixCore, rawFlag] using
      hstep.2.2.2 (cBucket z) (List.mem_range.mpr (by omega))
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag_all, rawFlag] using hvalid.1
    have hr27 : r ≤ 27 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrv : r + 1 + v ≤ 127 := by
      simp only [PrefixValid, rawFlag_all, rawFlag] at hvalid
      omega
    have hz20 : cBucket (z + 1) ≤ 20 := by
      apply cBucket_le_20
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

theorem s390Rows (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (hcore : PrefixCoreChecks) :
    PrefixTableSound afterF500 split390Potential
      sourceSplit390.Routeable s390Prefix :=
  ⟨s390_terminal hindex hstate, s390Prefix_mono hcore⟩

theorem narrow_le (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (p : FlagDegree) (hslope : p.all ≤ 28) (hmiddle : middle p ≤ 127)
    (htotal : total p ≤ 5964) :
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
      (phase_state_checked_at hstate p hp).2.2.2.2.1

theorem initialAComplement_le_certifiedJoint (p : FlagDegree) :
    initialAComplement p ≤ certifiedJointMaximum := by
  simp only [initialAComplement, initialAPotential, Potential.eval,
    rawFlag_total, rawFlag_middle, rawFlag_all, certifiedJointMaximum,
    Nat.min_def]
  split_ifs <;> omega

theorem joint_le (hindex : ThresholdsIndexed) (hstate : PhaseStateChecks)
    (p : FlagDegree) (hslope : p.all ≤ 28) (hmiddle : middle p ≤ 127)
    (htotal : total p ≤ 5964) :
    afterS390 p + initialAComplement p ≤ certifiedJointMaximum := by
  by_cases hpzero : p.all = 0
  · have hnarrow : ¬ NarrowState p := by
      intro hp
      rcases hp with ⟨hpos, _, _, _⟩
      omega
    rw [afterS390_eq_zero_of_not_narrow hnarrow, Nat.zero_add]
    exact initialAComplement_le_certifiedJoint p
  · have hp : NarrowState p :=
      ⟨Nat.one_le_iff_ne_zero.mpr hpzero, hslope, hmiddle, htotal⟩
    exact (Nat.add_le_add_right (afterS390_le_fast hindex p hp) _).trans
      (phase_state_checked_at hstate p hp).2.2.2.2.2

end ProximityPrize.SubmissionLower.LocatorPhase6800Concrete
