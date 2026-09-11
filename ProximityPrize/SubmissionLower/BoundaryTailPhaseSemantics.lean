import ProximityPrize.SubmissionLower.BoundaryTailPhaseRuns
import ProximityPrize.SubmissionLower.BoundaryTailBaseOracle

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecks
open Lower80811.PhaseRows Lower80811.PhaseData
open Lower80811.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def phaseSource : ℕ → Lower80811.Oracle.SourceNumbers
  | 0 => Lower80811.SourceSound.Phase00.source
  | 1 => Lower80811.SourceSound.Phase01.source
  | 2 => Lower80811.SourceSound.Phase02.source
  | 3 => Lower80811.SourceSound.Phase03.source
  | 4 => Lower80811.SourceSound.Phase04.source
  | _ => Lower80811.SourceSound.Phase05.source

def ThresholdAt (R V : ℕ) : Prop :=
  ∀ j ∈ List.range 6, FastSourceThresholdSufficient (phaseSource j) R V
    (thresholdAt (rowContext R V).threshold j)
instance (R V : ℕ) : Decidable (ThresholdAt R V) := by
  unfold ThresholdAt; infer_instance

def PrefixAt (R V : ℕ) : Prop :=
  ∀ j ∈ List.range 6,
    (R+1 ≤ 31 → R+1+V ≤ 142 →
      cachedPrefixAt (lookup R V).prefixValues j ≤ cachedPrefixAt (lookup (R+1) V).prefixValues j) ∧
    (R+(V+1) ≤ 142 →
      cachedPrefixAt (lookup R V).prefixValues j ≤ cachedPrefixAt (lookup R (V+1)).prefixValues j)
instance (R V : ℕ) : Decidable (PrefixAt R V) := by
  unfold PrefixAt; infer_instance

def RunsAt (R V : ℕ) : Prop :=
  RowRunsValid (rowContext R V) (Lower80811.PhaseRunData.lookup R V)
instance (R V : ℕ) : Decidable (RunsAt R V) := by
  unfold RunsAt; infer_instance
end ProximityPrize.SubmissionLower.Lower80811.PhaseChecks

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseSemantics
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN095 RCN238 RCN266 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential rawFlag rawFlag_all rawFlag_middle rawFlag_total
  sumFlag)
open LocatorBatchPhase6800 (regularAggregateFlag)
open Lower80811.Oracle Lower80811.PhaseRows Lower80811.PhaseData Lower80811.PhaseChecks
open Lower80811.BatchPhase
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

noncomputable section

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

def PrefixReceiptSound : Prop := ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → PrefixAt R V
def ThresholdReceiptSound : Prop := ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → ThresholdAt R V
def RunReceiptSound : Prop := ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → RunsAt R V

def prefixValue (j r v : ℕ) : ℕ := cachedPrefixAt (lookup r v).prefixValues j

def phaseCap (j : ℕ) (p : FlagDegree) : ℕ := capBefore (rowContext p.all p.yz) j p.zOnly


theorem phaseCap_zero (j : ℕ) (p : FlagDegree) (hp : p.all = 0) : phaseCap j p = 0 := by
  have h := capBefore_le_sourceLine (rowContext p.all p.yz) j 0 p.zOnly (Nat.zero_le _) trivial
  have hb : sourceLine (rowContext p.all p.yz) 0 p.zOnly = 0 := by
    simp [sourceLine, baseAt, rowContext, hp, BoundaryTailBaseData.lookup,
      BoundaryTailBaseData.defaultRow, LocatorPhase6800Oracle.BaseRow.evalAt,
      LocatorPhase6800Oracle.evalBaseSegments]
  unfold phaseCap
  omega

theorem prefix_zero (j v : ℕ) : prefixValue j 0 v = 0 := by
  simp [prefixValue, lookup, defaults, cachedPrefixAt]

theorem prefix_r_mono (hc : PrefixReceiptSound) (j v r R : ℕ)
    (hj : j < 6) (hr : r ≤ R) (hR : R ≤ 31) (hRV : R+v ≤ 142) :
    prefixValue j r v ≤ prefixValue j R v := by
  by_cases hr0 : r = 0
  · subst r; rw [prefix_zero]; exact Nat.zero_le _
  have hr1 : 1 ≤ r := by omega
  induction R, hr using Nat.le_induction with
  | base => exact le_rfl
  | succ R hrR ih =>
      have hstep := hc R v (by omega) (by omega) (by omega) j (List.mem_range.mpr hj)
      exact (ih (by omega) (by omega)).trans (hstep.1 (by omega) (by omega))

theorem prefix_v_mono (hc : PrefixReceiptSound) (j r v V : ℕ)
    (hj : j < 6) (hv : v ≤ V) (hr : r ≤ 31) (hRV : r+V ≤ 142) :
    prefixValue j r v ≤ prefixValue j r V := by
  by_cases hr0 : r = 0
  · subst r; simp [prefix_zero]
  have hr1 : 1 ≤ r := by omega
  induction V, hv using Nat.le_induction with
  | base => exact le_rfl
  | succ V hvV ih =>
      have hstep := hc r V hr1 hr (by omega) j (List.mem_range.mpr hj)
      exact (ih (by omega)).trans (hstep.2 (by omega))

theorem prefix_mono (hc : PrefixReceiptSound) (j r v R V : ℕ)
    (hj : j < 6) (hr : r ≤ R) (hv : v ≤ V) (hR : R ≤ 31) (hRV : R+V ≤ 142) :
    prefixValue j r v ≤ prefixValue j R V :=
  (prefix_r_mono hc j v r R hj hr hR (by omega)).trans
    (prefix_v_mono hc j R v V hj hv hR hRV)

def phaseSound : ℕ → PhaseSourceSound
  | 0 => Lower80811.SourceSound.Phase00.sound
  | 1 => Lower80811.SourceSound.Phase01.sound
  | 2 => Lower80811.SourceSound.Phase02.sound
  | 3 => Lower80811.SourceSound.Phase03.sound
  | 4 => Lower80811.SourceSound.Phase04.sound
  | _ => Lower80811.SourceSound.Phase05.sound

noncomputable def phaseKernel (j : ℕ) (hj : j < 6) (u0 u1 : I → K) :
    PhaseKernelRealization (phaseSound j) u0 u1 := by
  interval_cases j <;> first
    | exact Lower80811.SourceSound.Phase00.kernel u0 u1
    | exact Lower80811.SourceSound.Phase01.kernel u0 u1
    | exact Lower80811.SourceSound.Phase02.kernel u0 u1
    | exact Lower80811.SourceSound.Phase03.kernel u0 u1
    | exact Lower80811.SourceSound.Phase04.kernel u0 u1
    | exact Lower80811.SourceSound.Phase05.kernel u0 u1

theorem source_eq (j : ℕ) (hj : j < 6) : (phaseSound j).source = phaseSource j := by
  interval_cases j <;> decide

theorem potential_eq (j : ℕ) (hj : j < 6) : (phaseSound j).potential = phasePotential j := by
  interval_cases j <;> decide

theorem source_total (j : ℕ) (hj : j < 6) : 7501 ≤ (phaseSource j).totalCap := by
  interval_cases j <;> decide

def phaseDefect (j : ℕ) (p : FlagDegree) : ℕ := prefixValue j (p.all-1) p.yz

theorem defect_sound (hpref : PrefixReceiptSound) (hth : ThresholdReceiptSound)
    (hruns : RunReceiptSound) (j : ℕ) (hj : j < 6) :
    PhaseDefectSound (phaseCap j) (phaseSound j).source (phaseSound j).potential (phaseDefect j) := by
  intro p q hR hY hT hstrict hnroute
  have hqr := hstrict.1.1
  have hqs := hstrict.2
  have hm : q.all+q.yz ≤ p.all+p.yz := Nat.add_le_add hstrict.1.1 hstrict.1.2.1
  have ht : q.all+q.yz+q.zOnly ≤ p.all+p.yz+p.zOnly :=
    Nat.add_le_add hm hstrict.1.2.2
  have hyP : p.all+p.yz ≤ 142 := by simpa [middle, Nat.add_comm] using hY
  have htP : p.all+p.yz+p.zOnly ≤ 7501 := by
    simpa [total, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hT
  by_cases hq0 : q.all = 0
  · rw [phaseCap_zero j q hq0]
    exact Nat.zero_le _
  have hqpos : 1 ≤ q.all := by omega
  have hcut := hth q.all q.yz hqpos (by omega) (by omega) j (List.mem_range.mpr hj)
  have hnot : ¬ thresholdAt (rowContext q.all q.yz).threshold j ≤ q.zOnly := by
    intro hle
    apply hnroute
    rw [source_eq j hj]
    have he : rawFlag q.all q.yz q.zOnly = q := by cases q; rfl
    rw [← he]
    exact Lower80811.ThresholdFast.sufficient_route _ _ _ _ _ (source_total j hj)
      (by omega) hle hcut
  have hrun := hruns q.all q.yz hqpos (by omega) (by omega) j (List.mem_range.mpr hj)
  have hterminal := phaseTerminal_of_runs (rowContext q.all q.yz) j
    (((Lower80811.PhaseRunData.lookup q.all q.yz)[j]?).getD []) hj hrun q.zOnly (by
      change q.zOnly < 7502-(q.all+q.yz)
      omega)
  have hsmall := hterminal.resolve_left hnot
  have hmono := prefix_mono hpref j q.all q.yz (p.all-1) p.yz hj
    (by omega) hstrict.1.2.1 (by omega) (by omega)
  have he : rawFlag q.all q.yz q.zOnly = q := by cases q; rfl
  change phaseCap j q ≤ (phasePotential j).eval (rawFlag q.all q.yz q.zOnly) +
    prefixValue j q.all q.yz at hsmall
  rw [he] at hsmall
  rw [potential_eq j hj]
  exact hsmall.trans (Nat.add_le_add_left hmono _)


theorem bound_step (hpref : PrefixReceiptSound) (hth : ThresholdReceiptSound)
    (hruns : RunReceiptSound) (j : ℕ) (hj : j < 6)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181333 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i) = u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80811)
    (hprevious : StateLocalRegularBoundOn H selected Gamma ambient (phaseCap j)) :
    StateLocalRegularBoundOn H selected Gamma ambient (phaseCap (j+1)) := by
  classical
  let actual : FlagDegree → ℕ := fun p =>
    if (phaseSound j).source.Routeable p then
      min (phaseCap j p) ((phaseSound j).potential.eval p+phaseDefect j p)
    else phaseCap j p
  have hnext : StateLocalRegularBoundOn H selected Gamma ambient actual := by
    apply stateLocalRegularBoundOn_onePhase (phaseSound j) u0 u1 (phaseKernel j hj u0 u1)
      H selected Gamma ambient
    · exact hdegree
    · exact hagreement
    · exact hno
    · exact hprevious
    · exact defect_sound hpref hth hruns j hj
    · intro p _ _ _
      rfl

  intro A hA hR hY hT
  let p := regularAggregateFlag H A
  have hprev := hprevious A hA hR hY hT
  by_cases hp0 : p.all = 0
  · have h0 := phaseCap_zero j p hp0
    have h1 := phaseCap_zero (j+1) p hp0
    change _ ≤ phaseCap (j+1) p
    change _ ≤ phaseCap j p at hprev
    omega
  have hr1 : 1 ≤ p.all := by omega
  have hyP : p.all+p.yz ≤ 142 := by simpa [p, middle, Nat.add_comm] using hY
  have htP : p.all+p.yz+p.zOnly ≤ 7501 := by
    simpa [p, total, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hT
  by_cases hcut : thresholdAt (rowContext p.all p.yz).threshold j ≤ p.zOnly
  · have hreceipt := hth p.all p.yz hr1 hR hyP j (List.mem_range.mpr hj)
    have hroute : (phaseSound j).source.Routeable p := by
      rw [source_eq j hj]
      have he : rawFlag p.all p.yz p.zOnly = p := by cases p; rfl
      rw [← he]
      exact Lower80811.ThresholdFast.sufficient_route _ _ _ _ _ (source_total j hj)
        htP hcut hreceipt
    have hb := hnext A hA hR hY hT
    change _ ≤ actual p at hb
    dsimp only [actual] at hb
    rw [if_pos hroute, potential_eq j hj] at hb
    change _ ≤ capBefore (rowContext p.all p.yz) (j+1) p.zOnly
    rw [capBefore, if_pos hcut]
    have he : rawFlag p.all p.yz p.zOnly = p := by cases p; rfl
    simpa only [phaseCap, parentCharge, rowContext, phaseDefect, prefixValue, he] using hb
  · change _ ≤ capBefore (rowContext p.all p.yz) (j+1) p.zOnly
    rw [capBefore, if_neg hcut]
    exact hprev

theorem bound_all (hpref : PrefixReceiptSound) (hth : ThresholdReceiptSound)
    (hruns : RunReceiptSound)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ g ∈ Gamma, (selected g).natDegree ≤ 131071)
    (hagreement : ∀ g ∈ Gamma, 181333 ≤ ((Finset.univ : Finset I).filter (fun i =>
      (selected g).eval (IRSProfile.domain i) = u0 i+g*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80811)
    (hbase : StateLocalRegularBoundOn H selected Gamma ambient (phaseCap 0))
    (j : ℕ) (hj : j ≤ 6) :
    StateLocalRegularBoundOn H selected Gamma ambient (phaseCap j) := by
  induction j with
  | zero => exact hbase
  | succ j ih =>
      exact bound_step hpref hth hruns j (by omega) u0 u1 H selected Gamma ambient
        hdegree hagreement hno (ih (by omega))

end

end ProximityPrize.SubmissionLower.Lower80811.PhaseSemantics
