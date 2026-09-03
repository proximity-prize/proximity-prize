import ProximityPrize.SubmissionLower.PackedLocatorTailPart02

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
end PackedLocator_LocatorPhase6800Concrete

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
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
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
      split390Potential.eval (rawFlag R V z) + s390Prefix (rawFlag R V z) := by
  rfl

theorem capBefore0_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 0 z = checkedBaseCap (rawFlag R V z) :=
  baseAt_rowContext_eq R V z hR hR28 hV hz

theorem capBefore1_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 1 z = fastAfterR (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 0 ≤ z then
    min (baseAt (rowContext R V) z) (parentCharge (rowContext R V) 0 z)
    else baseAt (rowContext R V) z) = fastAfterR (rawFlag R V z)
  rw [baseAt_rowContext_eq R V z hR hR28 hV hz, parentCharge0_eq]
  rfl

theorem capBefore2_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 2 z = fastAfterC (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 1 ≤ z then
    min (capBefore (rowContext R V) 1 z) (parentCharge (rowContext R V) 1 z)
    else capBefore (rowContext R V) 1 z) = fastAfterC (rawFlag R V z)
  rw [capBefore1_eq R V z hR hR28 hV hz, parentCharge1_eq]
  rfl

theorem capBefore3_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 3 z = fastAfterF500 (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 2 ≤ z then
    min (capBefore (rowContext R V) 2 z) (parentCharge (rowContext R V) 2 z)
    else capBefore (rowContext R V) 2 z) = fastAfterF500 (rawFlag R V z)
  rw [capBefore2_eq R V z hR hR28 hV hz, parentCharge2_eq]
  rfl

theorem capBefore4_eq (R V z : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (hV : V < 128 - R) (hz : z < 5965 - (R + V)) :
    capBefore (rowContext R V) 4 z = fastAfterS390 (rawFlag R V z) := by
  change (if thresholdAt (rowContext R V).threshold 3 ≤ z then
    min (capBefore (rowContext R V) 3 z) (parentCharge (rowContext R V) 3 z)
    else capBefore (rowContext R V) 3 z) = fastAfterS390 (rawFlag R V z)
  rw [capBefore3_eq R V z hR hR28 hV hz, parentCharge3_eq]
  rfl

theorem sparseRV_to_public (R V : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28) (hV : V < 128 - R)
    (h : SparsePhaseStateRVCheck (rowContext R V))
    (z : ℕ) (hz : z < 5965 - (R + V)) :
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
    fastAfterS390 p + initialAComplement p ≤ certifiedJointMaximum := by
  have hs := h z hz
  dsimp only
  rw [← capBefore0_eq R V z hR hR28 hV hz,
    ← capBefore1_eq R V z hR hR28 hV hz,
    ← capBefore2_eq R V z hR hR28 hV hz,
    ← capBefore3_eq R V z hR hR28 hV hz,
    ← capBefore4_eq R V z hR hR28 hV hz,
    ← hereCharge0_eq R V z, ← hereCharge1_eq R V z,
    ← hereCharge2_eq R V z, ← hereCharge3_eq R V z]
  exact hs

theorem sparseLayer_to_public (R : ℕ) (hR : 1 ≤ R) (hR28 : R ≤ 28)
    (h : ∀ V ∈ List.range (128 - R),
      SparsePhaseStateRVCheck (rowContext R V)) : PhaseStateRCheck R := by
  intro V hV z hz
  exact sparseRV_to_public R V hR hR28 (List.mem_range.mp hV)
    (h V hV) z (List.mem_range.mp hz)

end ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunsBridge
end PackedLocator_LocatorPhase6800PhaseRunsBridge

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked. -/
section PackedLocator_LocatorPhase6800PhaseRunChecked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked

open LocatorPhase6800Concrete LocatorPhase6800PhaseRunsBridge

set_option autoImplicit false
set_option maxRecDepth 100000

theorem states : PhaseStateChecks := by
  intro R hR hpos
  have hlt : R < 29 := List.mem_range.mp hR
  interval_cases R <;>
  first
    | exact sparseLayer_to_public 1 (by decide) (by decide)
        LocatorPhase6800PhaseRunData01.sparseStates
    | exact sparseLayer_to_public 2 (by decide) (by decide)
        LocatorPhase6800PhaseRunData02.sparseStates
    | exact sparseLayer_to_public 3 (by decide) (by decide)
        LocatorPhase6800PhaseRunData03.sparseStates
    | exact sparseLayer_to_public 4 (by decide) (by decide)
        LocatorPhase6800PhaseRunData04.sparseStates
    | exact sparseLayer_to_public 5 (by decide) (by decide)
        LocatorPhase6800PhaseRunData05.sparseStates
    | exact sparseLayer_to_public 6 (by decide) (by decide)
        LocatorPhase6800PhaseRunData06.sparseStates
    | exact sparseLayer_to_public 7 (by decide) (by decide)
        LocatorPhase6800PhaseRunData07.sparseStates
    | exact sparseLayer_to_public 8 (by decide) (by decide)
        LocatorPhase6800PhaseRunData08.sparseStates
    | exact sparseLayer_to_public 9 (by decide) (by decide)
        LocatorPhase6800PhaseRunData09.sparseStates
    | exact sparseLayer_to_public 10 (by decide) (by decide)
        LocatorPhase6800PhaseRunData10.sparseStates
    | exact sparseLayer_to_public 11 (by decide) (by decide)
        LocatorPhase6800PhaseRunData11.sparseStates
    | exact sparseLayer_to_public 12 (by decide) (by decide)
        LocatorPhase6800PhaseRunData12.sparseStates
    | exact sparseLayer_to_public 13 (by decide) (by decide)
        LocatorPhase6800PhaseRunData13.sparseStates
    | exact sparseLayer_to_public 14 (by decide) (by decide)
        LocatorPhase6800PhaseRunData14.sparseStates
    | exact sparseLayer_to_public 15 (by decide) (by decide)
        LocatorPhase6800PhaseRunData15.sparseStates
    | exact sparseLayer_to_public 16 (by decide) (by decide)
        LocatorPhase6800PhaseRunData16.sparseStates
    | exact sparseLayer_to_public 17 (by decide) (by decide)
        LocatorPhase6800PhaseRunData17.sparseStates
    | exact sparseLayer_to_public 18 (by decide) (by decide)
        LocatorPhase6800PhaseRunData18.sparseStates
    | exact sparseLayer_to_public 19 (by decide) (by decide)
        LocatorPhase6800PhaseRunData19.sparseStates
    | exact sparseLayer_to_public 20 (by decide) (by decide)
        LocatorPhase6800PhaseRunData20.sparseStates
    | exact sparseLayer_to_public 21 (by decide) (by decide)
        LocatorPhase6800PhaseRunData21.sparseStates
    | exact sparseLayer_to_public 22 (by decide) (by decide)
        LocatorPhase6800PhaseRunData22.sparseStates
    | exact sparseLayer_to_public 23 (by decide) (by decide)
        LocatorPhase6800PhaseRunData23.sparseStates
    | exact sparseLayer_to_public 24 (by decide) (by decide)
        LocatorPhase6800PhaseRunData24.sparseStates
    | exact sparseLayer_to_public 25 (by decide) (by decide)
        LocatorPhase6800PhaseRunData25.sparseStates
    | exact sparseLayer_to_public 26 (by decide) (by decide)
        LocatorPhase6800PhaseRunData26.sparseStates
    | exact sparseLayer_to_public 27 (by decide) (by decide)
        LocatorPhase6800PhaseRunData27.sparseStates
    | exact sparseLayer_to_public 28 (by decide) (by decide)
        LocatorPhase6800PhaseRunData28.sparseStates

end ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked

end PackedLocator_LocatorPhase6800PhaseRunChecked

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
  evalPowerBandBudget 50322 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem evalBand_eq (s : SourceNumbers) (p : FlagDegree) :
    evalBand s p = s.band p := by
  unfold evalBand SourceNumbers.band
  exact evalPowerBandBudget_eq _ _ _ _ _ _ _ _

def FastRouteable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ evalBand s p < s.gap

instance (s : SourceNumbers) (p : FlagDegree) :
    Decidable (FastRouteable s p) := by
  unfold FastRouteable
  infer_instance

theorem fastRouteable_iff (s : SourceNumbers) (p : FlagDegree) :
    FastRouteable s p ↔ s.Routeable p := by
  unfold FastRouteable SourceNumbers.Routeable
  rw [evalBand_eq]

def FastSourceThresholdSufficient
    (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  5964 - (r + v) < threshold ∨ FastRouteable s (rawFlag r v threshold)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (FastSourceThresholdSufficient s r v threshold) := by
  unfold FastSourceThresholdSufficient
  infer_instance

def FastThresholdSufficient (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 28 ∧ q.r + q.v ≤ 127 ∧
    FastSourceThresholdSufficient sourceR1200 q.r q.v q.r1200 ∧
    FastSourceThresholdSufficient LocatorPhase6800Oracle.sourceC
      q.r q.v q.sourceC ∧
    FastSourceThresholdSufficient sourceSplit500 q.r q.v q.split500 ∧
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
  rcases h with ⟨hr1, hr28, hrv, hR, hC, hF, hS⟩
  exact ⟨hr1, hr28, hrv,
    fastSourceThresholdSufficient_sound _ _ _ _ hR,
    fastSourceThresholdSufficient_sound _ _ _ _ hC,
    fastSourceThresholdSufficient_sound _ _ _ _ hF,
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

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR01Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR01Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR01Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData01.threshold 1 127 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 127,
    ThresholdAtOf LocatorPhase6800ReceiptRowData01.threshold 1 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR01Checked
end PackedLocator_LocatorPhase6800ThresholdR01Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR13Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR13Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR13Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData13.threshold 13 115 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 115,
    ThresholdAtOf LocatorPhase6800ReceiptRowData13.threshold 13 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR13Checked
end PackedLocator_LocatorPhase6800ThresholdR13Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR25Checked. -/
