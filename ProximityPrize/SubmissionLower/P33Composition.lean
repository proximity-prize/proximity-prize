/- P33Composition (Bome2017 tree): the composition combinator over `K6833Residual.TerminalData`.
   Ported from the lower-6833p version (68.32 Ready/ReachedTerminal):
   * residue `A` -> an explicit `A : Finset (RegularIndex T.primary)` (as in `terminal_count`,
     K6833TerminalCount.lean:170); count `(A.biUnion (regularFiber T.primary T.seeds T.selected)).card`;
   * per-factor jet charge = `K6833Residual.factor_jet_charge` (added to K6833TerminalCount, the `hcount` step of
     `multiple_count`); raw = `incumbent_raw_fiber` (K6833TerminalData.lean:104);
   * old rows = Bome's single-factor check `simpleMode` via `single_count` (K6833TerminalCount.lean:58);
   * caps 16/67/8870 (`validRow`), Profiles = Fin 6^3. -/
import ProximityPrize.SubmissionLower.P33Check
import ProximityPrize.SubmissionLower.P33Bridge
import ProximityPrize.SubmissionLower.K6833TerminalCount

set_option Elab.async false

namespace ProximityPrize
namespace SubmissionLower
namespace P33
open scoped Classical BigOperators
open RCN095 RCN130 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN313
open LocatorHybridCells LocatorFactorAggregate LocatorBatchProductRoute
open LocatorPhase6800Oracle (sumFlag_all sumFlag_middle sumFlag_total)
open K6833Residual Koala6831MovingPaid
set_option autoImplicit false

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]

/-! ## 0. Notation and small arithmetic facts -/

/-- Cumulative coordinates of a factor: (slope, middle, total) = (wt S, wt YS, wt Total). -/
noncomputable abbrev κr {H : MvPolynomial (Fin 4) K} (F : RegularIndex H) : ℕ := wt residualSWeights F.1
noncomputable abbrev κy {H : MvPolynomial (Fin 4) K} (F : RegularIndex H) : ℕ := wt residualYSWeights F.1
noncomputable abbrev κt {H : MvPolynomial (Fin 4) K} (F : RegularIndex H) : ℕ := wt residualTotalWeights F.1

theorem κ_of_flag {H : MvPolynomial (Fin 4) K} (F : RegularIndex H) :
    (originalCumulativeFlag F.1).all = κr F ∧ middle (originalCumulativeFlag F.1) = κy F ∧
      total (originalCumulativeFlag F.1) = κt F := by
  obtain ⟨h1, h2, h3⟩ := originalCumulativeFlag_cumulative F.1          -- K LowerFoundation:14084
  exact ⟨h1, by simpa [middle] using h2, by simpa [total] using h3⟩

/-- A flag is below an envelope iff its cumulative coordinates are (for a shaped envelope). -/
theorem below_env {H : MvPolynomial (Fin 4) K} (F : RegularIndex H) (e : Envelope)
    (hs : e.slope ≤ e.middle) (hm : e.middle ≤ e.total)
    (h1 : κr F ≤ e.slope) (h2 : κy F ≤ e.middle) (h3 : κt F ≤ e.total) :
    Below (originalCumulativeFlag F.1) e.flag := by
  obtain ⟨k1, k2, k3⟩ := κ_of_flag F
  refine ⟨?_, ?_, ?_⟩
  · simp only [Envelope.flag]; omega
  · rw [k2]; simp only [Envelope.flag, middle]; omega
  · rw [k3]; simp only [Envelope.flag, total]; omega

theorem caps_of (e : Envelope) (h : capsOK e = true) :
    e.slope ≤ e.middle ∧ e.middle ≤ e.total ∧ e.slope ≤ 16 ∧ e.middle ≤ 67 ∧ e.total ≤ 8870 :=
  of_decide_eq_true h

theorem slope_pos {H : MvPolynomial (Fin 4) K} (F : RegularIndex H) : 1 ≤ κr F := by
  have h := regularCumulativeFlag_positive H F                          -- K LowerFoundation:14195
  have h1 := (originalCumulativeFlag_cumulative F.1).1
  change 0 < (originalCumulativeFlag F.1).all at h
  show 1 ≤ wt residualSWeights F.1
  omega

theorem cumCharge_mono (a : ℕ × ℕ × ℕ) {r y t r' y' t' : ℕ} (hr : r ≤ r') (hy : y ≤ y') (ht : t ≤ t') :
    cumCharge a r y t ≤ cumCharge a r' y' t' := by
  unfold cumCharge
  have h1 := Nat.mul_le_mul_left a.1 ht
  have h2 := Nat.mul_le_mul_left (a.2.1 - a.1) hy
  have h3 := Nat.mul_le_mul_left (a.2.2 - a.2.1) hr
  omega

theorem cumCharge_sum {ι : Type} (a : ℕ × ℕ × ℕ) (s : Finset ι) (r y t : ι → ℕ) :
    (∑ i ∈ s, cumCharge a (r i) (y i) (t i)) = cumCharge a (∑ i ∈ s, r i) (∑ i ∈ s, y i) (∑ i ∈ s, t i) := by
  simp only [cumCharge, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- `linear_cost_cumulative` (K LowerFoundation:23547) in `cumCharge` form. -/
theorem linear_eq_cum (c0 c1 c2 : ℕ) (h01 : c0 ≤ c1) (h12 : c1 ≤ c2) (left : FlagDegree) :
    left.zOnly * c0 + left.yz * c1 + left.all * c2 = cumCharge (c0, c1, c2) left.all (middle left) (total left) := by
  rw [RCN131.linear_cost_cumulative c0 c1 c2 left h01 h12]
  simp only [cumCharge, middle, total]

/-- The raw axes are monotone (no gate needed): `rawChargeWithCorrections` is `flagMixed left · ·` plus a multiple,
monotone in `left` by `mixed_mono_first` (K LowerGeometry:724), and `unitZ ≤ unitYZ ≤ unitAll` cumulatively. -/
theorem raw_axes_mono (e : Envelope) :
    rawChargeWithCorrections TailCorrections.original (e.pad 0) unitZFlag ≤
        rawChargeWithCorrections TailCorrections.original (e.pad 0) unitYZFlag ∧
      rawChargeWithCorrections TailCorrections.original (e.pad 0) unitYZFlag ≤
        rawChargeWithCorrections TailCorrections.original (e.pad 0) unitAllFlag := by
  have hzy : Below unitZFlag unitYZFlag := by unfold Below; decide
  have hya : Below unitYZFlag unitAllFlag := by unfold Below; decide
  constructor
  · unfold rawChargeWithCorrections
    exact Nat.add_le_add (mixed_mono_first hzy _ _) (Nat.mul_le_mul_left _ (mixed_mono_first hzy _ _))
  · unfold rawChargeWithCorrections
    exact Nat.add_le_add (mixed_mono_first hya _ _) (Nat.mul_le_mul_left _ (mixed_mono_first hya _ _))

/-- The raw charge of a flag in `cumCharge` form (scaled by `terminalScale`). -/
theorem raw_eq_cum (e : Envelope) (left : FlagDegree) :
    rawChargeWithCorrections TailCorrections.original (e.pad 0) left * terminalScale =
      cumCharge (axes e none) left.all (middle left) (total left) := by
  obtain ⟨m01, m12⟩ := raw_axes_mono e
  rw [rawCharge_increments]                                             -- K FactorRouting:141 (make public)
  have h := linear_eq_cum _ _ _ (Nat.mul_le_mul_right terminalScale m01) (Nat.mul_le_mul_right terminalScale m12) left
  simp only [axes]
  rw [← h]
  ring

/-- The jet charge of a flag in `cumCharge` form, for a monotone route. -/
theorem jet_eq_cum (e : Envelope) (ids : Profiles)
    (hmono : jetMonotoneWithCorrections TailCorrections.original e (cellConfig ids) = true) (left : FlagDegree) :
    jetFlagCharge TailCorrections.original e (cellConfig ids) left =
      cumCharge (axes e (some ids)) left.all (middle left) (total left) := by
  have hc := of_decide_eq_true hmono
  rw [jetFlagCharge_eq]                                                -- K FactorRouting:123
  exact linear_eq_cum _ _ _ hc.1 hc.2 left

/-! ## 1. Per-factor charge at an arbitrary verified support (P1) -/

/-- The jet per-factor bound at a verified support (Bome2017's `hcount` step, `K6833Residual.factor_jet_charge`). -/
theorem jet_factor_card_mul_le {x : I ↪ K} (T : TerminalData x)
    (e : Envelope) (ids : Profiles) (hroute : routeOK e (some ids) = true) (hcapsE : capsOK e = true)
    (F : RegularIndex T.primary) (hbelow : Below (originalCumulativeFlag F.1) e.flag) :
    (regularFiber T.primary T.seeds T.selected F).card * terminalScale ≤
      jetFlagCharge TailCorrections.original e (cellConfig ids) (originalCumulativeFlag F.1) := by
  simp only [routeOK, Bool.and_eq_true, decide_eq_true_eq] at hroute
  obtain ⟨⟨hjg, _⟩, hsize⟩ := hroute
  obtain ⟨hs, hm, h1, h2, h3⟩ := caps_of e hcapsE
  exact factor_jet_charge T F e ids ⟨hsize.1, hsize.2.1⟩ ⟨hs, hm⟩ ⟨h1, h2, h3⟩ hbelow hjg

/-- **factor_charge_le** (P1 in `cumCharge` form): at a verified support `e` with route `ids`, a factor below `e`
has `|fiber| · terminalScale ≤ cumCharge (axes e ids) κ(F)`. -/
theorem factor_charge_le {x : I ↪ K} (T : TerminalData x)
    (e : Envelope) (ids : Option (Profiles)) (hroute : routeOK e ids = true)
    (hcapsE : capsOK e = true) (F : RegularIndex T.primary) (hbelow : Below (originalCumulativeFlag F.1) e.flag) :
    (regularFiber T.primary T.seeds T.selected F).card * terminalScale ≤ cumCharge (axes e ids) (κr F) (κy F) (κt F) := by
  obtain ⟨k1, k2, k3⟩ := κ_of_flag F
  obtain ⟨hs, hm, hR17, hY71, hT⟩ := caps_of e hcapsE
  cases ids with
  | none =>
    have hdata := residual_support_of_endpoint F.1 e ⟨hs, hm⟩ hbelow             -- K ShortCount:126
    have hraw := incumbent_raw_fiber T F e ⟨hR17, hY71, hT⟩ hroute hdata
    have h := raw_eq_cum e (originalCumulativeFlag F.1)
    rw [k1, k2, k3] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hraw
  | some ids =>
    have hmono : jetMonotoneWithCorrections TailCorrections.original e (cellConfig ids) = true := by
      have h := hroute
      simp only [routeOK, Bool.and_eq_true] at h
      exact h.1.2
    have h := jet_eq_cum e ids hmono (originalCumulativeFlag F.1)
    rw [k1, k2, k3] at h
    rw [← h]
    exact jet_factor_card_mul_le T e ids hroute hcapsE F hbelow

/-- A factor below a verified old-table support has fiber ≤ the stored price (`single_count`). -/
theorem fiber_le_old {x : I ↪ K} (T : TerminalData x) (e : Envelope) (ids : Option Profiles) (price : ℕ)
    (hca : capsOK e = true) (hsm : simpleMode e price ids = true)
    (F : RegularIndex T.primary) (hb : Below (originalCumulativeFlag F.1) e.flag) :
    (regularFiber T.primary T.seeds T.selected F).card ≤ price := by
  obtain ⟨hs, hm, h1, h2, h3⟩ := caps_of e hca
  exact single_count T F e price ids ⟨hs, hm⟩ ⟨h1, h2, h3⟩ hb hsm

/-! ## 2. The residue as a Finset sum -/

/-- `T.route.seeds ⊆ residue.biUnion fiber` (definitional: `PaidRoute.seeds`, K MovingPaidRoute:38), hence
`|seeds| ≤ Σ |fiber|` (`Finset.card_biUnion_le`, as at K ShortCount:200). -/
theorem seeds_le_sum {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary)) :
    (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤
      ∑ F ∈ A, (regularFiber T.primary T.seeds T.selected F).card :=
  Finset.card_biUnion_le

/-- The cumulative coordinates of the residue sum to those of the aggregate flag, which is below the cell. -/
theorem residue_sums {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (e : Envelope) (hshape : e.slope ≤ e.middle ∧ e.middle ≤ e.total)
    (hfit : Below (Koala6831MovingAdaptive.aggregateFlag T.primary A) e.flag) :
    (∑ F ∈ A, κr F) ≤ e.slope ∧ (∑ F ∈ A, κy F) ≤ e.middle ∧
      (∑ F ∈ A, κt F) ≤ e.total := by
  have hprod := Koala6831Moving.contactFlag_regularProduct T.primary A            -- K MovingPartition:40
  change Below (Koala6831Moving.contactFlag (regularProduct T.primary A)) e.flag at hfit
  rw [hprod] at hfit
  obtain ⟨h1, h2, h3⟩ := hfit
  simp only [sumFlag_all, sumFlag_middle, sumFlag_total, Koala6831Moving.contactFlag_all, Koala6831Moving.contactFlag_middle,
    Koala6831Moving.contactFlag_total] at h1 h2 h3
  simp only [Envelope.flag, middle, total] at h1 h2 h3
  show (∑ F ∈ A, wt residualSWeights F.1) ≤ e.slope ∧
    (∑ F ∈ A, wt residualYSWeights F.1) ≤ e.middle ∧
      (∑ F ∈ A, wt residualTotalWeights F.1) ≤ e.total
  refine ⟨h1, ?_, ?_⟩
  · have : e.middle - e.slope + e.slope = e.middle := Nat.sub_add_cancel hshape.1
    omega
  · have : e.total - e.middle + (e.middle - e.slope) + e.slope = e.total := by omega
    omega

/-- At most one factor has total ≥ T* = t/2 + 1 (two would sum to more than t). -/
theorem big_unique {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (t : ℕ) (hsum : (∑ F ∈ A, κt F) ≤ t)
    {F G : RegularIndex T.primary} (hF : F ∈ A) (hG : G ∈ A)
    (hFb : t / 2 + 1 ≤ κt F) (hGb : t / 2 + 1 ≤ κt G) : F = G := by
  by_contra hne
  have hpair : κt F + κt G ≤ ∑ H ∈ A, κt H := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (Finset.insert_subset hF (Finset.singleton_subset_iff.mpr hG))
  omega

/-- The small-factor charge: for `S ⊆ residue` whose members are all below `smallSupport c`,
`(Σ_S |fiber|) · scale ≤ cumCharge a (Σ_S κr) (Σ_S κy) (Σ_S κt)`. -/
theorem small_sum_charge {x : I ↪ K} (T : TerminalData x)
    (c : CertCell) (hroute : routeOK (smallSupport c) c.lam = true) (hcaps : capsOK (smallSupport c) = true)
    (S : Finset (RegularIndex T.primary))
    (hS : ∀ F ∈ S, Below (originalCumulativeFlag F.1) (smallSupport c).flag) :
    (∑ F ∈ S, (regularFiber T.primary T.seeds T.selected F).card) * terminalScale ≤
      cumCharge (axes (smallSupport c) c.lam) (∑ F ∈ S, κr F) (∑ F ∈ S, κy F) (∑ F ∈ S, κt F) := by
  rw [Finset.sum_mul, ← cumCharge_sum]
  exact Finset.sum_le_sum fun F hF => factor_charge_le T _ c.lam hroute hcaps F (hS F hF)

/-! ## 3. The big factor: `ub(Q)` bounds its fiber -/

/-- From a box row's `ub = some u`: the big factor's fiber is ≤ u.
Sources of the bound: a clip row (`clipOK`), the old index (`oldIndex_ok_all`), a window (`capOK_of`). -/
theorem fiber_le_ub {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (c : CertCell) (hclips : ∀ x ∈ c.clips, clipOK c x = true) (hcapsE : capsOK c.env = true)
    (hr14 : c.env.slope ≤ 14)
    (F : RegularIndex T.primary) (hF : F ∈ A)
    (hdataE : ResidualSupportData (c.env.paddedSupport 0) F.1)
    (j k : ℕ) (hj : j < 24) (hk : k < 24)
    (hr : κr F ≤ c.env.slope) (hyE : κy F ≤ c.env.middle) (htE : κt F ≤ c.env.total)
    (hyLo : bandLo (κr F) j ≤ κy F) (hyHi : κy F ≤ bandHi (κr F) j)
    (htLo : 300 * k < κt F) (htHi : κt F ≤ 300 * (k + 1))
    (u : ℕ) (hu : ub c (κr F) j k = some u) :
    (regularFiber T.primary T.seeds T.selected F).card ≤ u := by
  set rq := κr F with hrq
  have hrq1 : 1 ≤ rq := slope_pos F
  obtain ⟨hEs, hEm, _, hE71, _⟩ := caps_of c.env hcapsE
  -- the three individual bounds
  have hold : ∀ v, oldAt rq j k = v → v ≠ 0 → (regularFiber T.primary T.seeds T.selected F).card ≤ v := by
    intro v hv hv0
    have hslice := oldIndex_ok_all rq hrq1 (hr.trans hr14)
    simp only [oldSliceOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hslice
    rcases hslice j hj k hk with h0 | hrow
    · have hv' : v = 0 := by rw [← hv]; simpa only [oldAt] using h0
      exact absurd hv' hv0
    · have hrow' := hrow
      simp only [oldRowOK, Bool.and_eq_true] at hrow'
      obtain ⟨hca, hsm⟩ := hrow'
      have hcorner := caps_of _ hca
      have hb : Below (originalCumulativeFlag F.1) (⟨rq, bandHi rq j, 300 * (k + 1)⟩ : Envelope).flag :=
        below_env F _ hcorner.1 hcorner.2.1 le_rfl hyHi htHi
      have hfc := fiber_le_old T _ _ _ hca hsm F hb
      rw [← hv]
      simp only [oldAt]
      exact hfc
  have hclip : ∀ x ∈ c.clips, x.1 = rq → x.2.1 = j → x.2.2.1 = k →
      (regularFiber T.primary T.seeds T.selected F).card ≤ x.2.2.2.2.2 := by
    intro x hx h1 h2 h3
    have hc := hclips x hx
    simp only [clipOK, Bool.and_eq_true, decide_eq_true_eq, oldRowOK] at hc
    obtain ⟨hys, hca, hsm⟩ := hc
    have hcorner := caps_of _ hca
    have hb : Below (originalCumulativeFlag F.1)
        (⟨x.1, x.2.2.2.1, min (300 * (x.2.2.1 + 1)) c.env.total⟩ : Envelope).flag := by
      refine below_env F _ hcorner.1 hcorner.2.1 (by dsimp only; omega) ?_ ?_
      · rw [hys, h1, h2]; exact le_min hyHi hyE
      · rw [h3]; exact le_min htHi htE
    exact fiber_le_old T _ _ _ hca hsm F hb
  have hcap : ∀ W, capAt rq j k = some W → (regularFiber T.primary T.seeds T.selected F).card ≤ W.cap := by
    intro W hW
    have hok := of_decide_eq_true (capOK_of (by omega) hj (by omega) hW)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _, _⟩ := hok
    exact fiber_le_window T W (windows_count W (capAt_mem hW)) h5 h6 h7 h8 h9 h10 F c.env hdataE
      h1 (hyHi.trans h2) (htHi.trans h3) (by show W.low ≤ κt F; omega)
  -- unfold `ub` and combine (le_min for the two-source case)
  unfold ub at hu
  cases hfind : c.clips.find? (fun x => x.1 = rq ∧ x.2.1 = j ∧ x.2.2.1 = k) with
  | some x =>
    have hxmem := List.mem_of_find?_eq_some hfind
    have hxp : x.1 = rq ∧ x.2.1 = j ∧ x.2.2.1 = k := by
      have h := List.find?_some hfind
      exact of_decide_eq_true h
    have hx := hclip x hxmem hxp.1 hxp.2.1 hxp.2.2
    rw [hfind] at hu
    cases hW : capAt rq j k with
    | some W => simp only [hW, Option.map_some, Option.map, Option.some.injEq] at hu
                rw [← hu]; exact le_min hx (hcap W hW)
    | none => simp only [hW, Option.map_some, Option.map, Option.some.injEq] at hu
              rw [← hu]; exact hx
  | none =>
    rw [hfind] at hu
    by_cases h0 : oldAt rq j k = 0
    · cases hW : capAt rq j k with
      | some W => simp only [h0, hW, if_true, Option.map, Option.some.injEq] at hu
                  rw [← hu]; exact hcap W hW
      | none => simp [h0, hW] at hu
    · have ho := hold _ rfl h0
      cases hW : capAt rq j k with
      | some W => simp only [h0, hW, if_false, Option.map, Option.some.injEq] at hu
                  rw [← hu]; exact le_min ho (hcap W hW)
      | none => simp only [h0, hW, if_false, Option.map, Option.some.injEq] at hu
                rw [← hu]; exact ho

/-! ## 4. The combinator -/

/-- **composition_card_le** (PACKET5 §3.2). Steps:
1. the residue's coordinates sum below the cell (`residue_sums`); `|seeds| ≤ Σ |fiber|` (`seeds_le_sum`);
2. at most one factor has total ≥ T* (`big_unique`);
3. no big factor: every factor is below `smallSupport c`, and the "no big factor" row bounds the total;
4. one big factor F0: its box `(rq, j, k) = (κr F0, (κy F0 - κr F0)/3, (κt F0 - 1)/300)` is a row of the
   certificate; `ub` bounds `|fiber F0|` (`fiber_le_ub`); the others are small and their coordinates sum to at
   most `κ(E) − lo(Q)` (truncated subtraction is safe: `lo(Q) ≤ κ(F0) ≤ κ(E)`); if `r − rq = 0` there are none;
5. combine with `Nat.le_div_iff_mul_le`. -/
theorem composition_card_le {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (c : CertCell) (hc : certCheck c = true)
    (hshape : c.env.slope ≤ c.env.middle ∧ c.env.middle ≤ c.env.total)
    (hfit : Below (Koala6831MovingAdaptive.aggregateFlag T.primary A) c.env.flag) :
    (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤ c.bound := by
  obtain ⟨hrS, hcS, hcE, ⟨hr1, hr14, ht7200⟩, hclips, hnobig, hboxes⟩ := certCheck_parts hc
  obtain ⟨_, _, _, hE71, _⟩ := caps_of c.env hcE
  obtain ⟨hsR, hsY, hsT⟩ := residue_sums T A c.env hshape hfit
  have hseeds := seeds_le_sum T A
  set r := c.env.slope with hr_def
  set y := c.env.middle with hy_def
  set t := c.env.total with ht_def
  set a := axes (smallSupport c) c.lam with ha
  set res := A with hres
  let fiber := regularFiber T.primary T.seeds T.selected
  have hscale : 0 < terminalScale := by decide
  have hsmallS : (smallSupport c).slope ≤ (smallSupport c).middle ∧
      (smallSupport c).middle ≤ (smallSupport c).total := by
    simp only [smallSupport]; exact ⟨hshape.1, le_max_right _ _⟩
  -- each factor's coordinates are below the cell's
  have hκ (F : RegularIndex T.primary) (hF : F ∈ res) : κr F ≤ r ∧ κy F ≤ y ∧ κt F ≤ t :=
    ⟨(Finset.single_le_sum (fun _ _ => Nat.zero_le _) hF).trans hsR,
     (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hF).trans hsY,
     (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hF).trans hsT⟩
  -- a non-big factor is below the small support
  have hsmallBelow (F : RegularIndex T.primary) (hF : F ∈ res) (hnb : κt F ≤ t / 2) :
      Below (originalCumulativeFlag F.1) (smallSupport c).flag := by
    obtain ⟨h1, h2, _⟩ := hκ F hF
    exact below_env F _ hsmallS.1 hsmallS.2 h1 h2 (hnb.trans (le_max_left _ _))
  by_cases hbig : ∃ F ∈ res, t / 2 + 1 ≤ κt F
  · ------------------------------------------------------------------ one big factor
    obtain ⟨F0, hF0, hF0b⟩ := hbig
    obtain ⟨k1, k2, k3⟩ := hκ F0 hF0
    set rq := κr F0 with hrq
    have hrq1 : 1 ≤ rq := slope_pos F0
    have hyr : rq ≤ κy F0 := by
      obtain ⟨_, h2, _⟩ := κ_of_flag F0
      have : (originalCumulativeFlag F0.1).all ≤ middle (originalCumulativeFlag F0.1) := Nat.le_add_left _ _
      rw [(κ_of_flag F0).1, h2] at this; exact this
    set j := (κy F0 - rq) / 3 with hj_def
    set k := (κt F0 - 1) / 300 with hk_def
    have hj : j < 24 := by omega
    have hk : k < 24 := by omega
    have hyLo : bandLo rq j ≤ κy F0 := by simp only [bandLo]; omega
    have hyHi : κy F0 ≤ bandHi rq j := by
      simp only [bandHi]
      exact le_min (by omega) (k2.trans (hE71.trans (by norm_num)))
    have htLo : 300 * k < κt F0 := by omega
    have htHi : κt F0 ≤ 300 * (k + 1) := by omega
    -- the box row of (rq, j, k)
    have hrow := hboxes rq k1 hrq1 j hj k hk
    have hlot : max (300 * k) (t / 2 + 1) ≤ κt F0 := max_le htLo.le hF0b
    have hskip : ¬ (r < rq ∨ y < bandLo rq j ∨ t < max (300 * k) (t / 2 + 1) ∨ 300 * k + 300 < t / 2 + 1) := by
      omega
    unfold boxOK at hrow
    rw [if_neg hskip] at hrow
    -- `ub` is `some u` (a `none` makes the row `false`)
    cases hu : ub c rq j k with
    | none => rw [hu] at hrow; dsimp only at hrow; exact absurd hrow Bool.false_ne_true
    | some u =>
      rw [hu] at hrow
      dsimp only at hrow
      replace hrow := of_decide_eq_true hrow
      -- the big factor
      have hdataE := residual_support_of_endpoint F0.1 c.env hshape
        (below_env F0 c.env hshape.1 hshape.2 k1 k2 k3)
      have hF0u := fiber_le_ub T A c hclips hcE hr14 F0 hF0 hdataE j k hj hk k1 k2 k3 hyLo hyHi htLo htHi u hu
      -- the others: all small, and their coordinates sum below κ(E) − lo(Q)
      set others := res.erase F0 with hothers
      have hothSmall : ∀ G ∈ others, Below (originalCumulativeFlag G.1) (smallSupport c).flag := by
        intro G hG
        have hGres := Finset.mem_of_mem_erase hG
        have hne := Finset.ne_of_mem_erase hG
        have hnb : κt G ≤ t / 2 := by
          by_contra hcon
          exact hne (big_unique T A t hsT hGres hF0 (by omega) hF0b)
        exact hsmallBelow G hGres hnb
      have hsplit (f : RegularIndex T.primary → ℕ) : (∑ G ∈ res, f G) = f F0 + ∑ G ∈ others, f G :=
        (Finset.add_sum_erase res f hF0).symm
      have hoR : (∑ G ∈ others, κr G) ≤ r - rq := by have := hsplit κr; omega
      have hoY : (∑ G ∈ others, κy G) ≤ y - bandLo rq j := by have := hsplit κy; omega
      have hoT : (∑ G ∈ others, κt G) ≤ t - max (300 * k) (t / 2 + 1) := by have := hsplit κt; omega
      have hothCharge := small_sum_charge T c hrS hcS others hothSmall
      have hothBound : (∑ G ∈ others, (fiber G).card) ≤
          (if r - rq = 0 then 0 else cumCharge a (r - rq) (y - bandLo rq j) (t - max (300 * k) (t / 2 + 1)) /
            terminalScale) := by
        split_ifs with h0
        · -- no other factor: each has slope ≥ 1
          have hempty : others = ∅ := by
            by_contra hne
            obtain ⟨G, hG⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            have h1 := slope_pos G
            have h2 := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hG (f := κr)
            omega
          simp [hempty]
        · exact (Nat.le_div_iff_mul_le hscale).mpr
            (hothCharge.trans (cumCharge_mono a hoR hoY hoT))
      calc (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤ ∑ G ∈ res, (fiber G).card := hseeds
        _ = (fiber F0).card + ∑ G ∈ others, (fiber G).card := hsplit _
        _ ≤ u + _ := Nat.add_le_add hF0u hothBound
        _ ≤ c.bound := hrow
  · ------------------------------------------------------------------ no big factor
    push_neg at hbig
    have hall : ∀ F ∈ res, Below (originalCumulativeFlag F.1) (smallSupport c).flag :=
      fun F hF => hsmallBelow F hF (by have := hbig F hF; omega)
    have hcharge := small_sum_charge T c hrS hcS res hall
    have hsum : (∑ F ∈ res, (fiber F).card) ≤ cumCharge a r y t / terminalScale :=
      (Nat.le_div_iff_mul_le hscale).mpr (hcharge.trans (cumCharge_mono a hsR hsY hsT))
    exact hseeds.trans (hsum.trans hnobig)

end P33
end SubmissionLower
end ProximityPrize
