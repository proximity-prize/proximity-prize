/- P33RComposition: soundness of the refined composition certificate `certCheckR` (see `P33RCheck`).
   `composition_card_le_refined`: for an aggregate residue `A` below the envelope of an `RCell` (with exact slope,
   as in `row_count`), the fiber union has at most `c.bound` points.
   Facts used (all omega-level on the factor flags or existing lemmas of `P33Composition`):
   each factor has slope >= 1 (`slope_pos`), flags add (`residue_sums`), the largest-total factor F1 exists
   (`Finset.exists_max_image`), `Below` is monotone in the support, `factor_charge_le` holds at any verified support. -/
import ProximityPrize.SubmissionLower.P33RCheck
import ProximityPrize.SubmissionLower.P33Composition

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

theorem κ_chain {H : MvPolynomial (Fin 4) K} (F : RegularIndex H) : κr F ≤ κy F ∧ κy F ≤ κt F := by
  obtain ⟨k1, k2, k3⟩ := κ_of_flag F
  simp only [middle, total] at k2 k3
  omega

/-- The aggregate slope is the sum of the factors' slopes (exactness; `residue_sums` only gives `≤`). -/
theorem agg_all_eq {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary)) :
    (Koala6831MovingAdaptive.aggregateFlag T.primary A).all = ∑ F ∈ A, κr F := by
  have hprod := Koala6831Moving.contactFlag_regularProduct T.primary A
  change (Koala6831Moving.contactFlag (regularProduct T.primary A)).all = _
  rw [hprod]
  simp only [sumFlag_all, Koala6831Moving.contactFlag_all]

/-- `small_sum_charge` at an arbitrary verified support `e` with route `ids`. -/
theorem sum_charge_at {x : I ↪ K} (T : TerminalData x) (e : Envelope) (ids : Option Profiles)
    (hroute : routeOK e ids = true) (hcaps : capsOK e = true)
    (S : Finset (RegularIndex T.primary))
    (hS : ∀ F ∈ S, Below (originalCumulativeFlag F.1) e.flag) :
    (∑ F ∈ S, (regularFiber T.primary T.seeds T.selected F).card) * terminalScale ≤
      cumCharge (axes e ids) (∑ F ∈ S, κr F) (∑ F ∈ S, κy F) (∑ F ∈ S, κt F) := by
  rw [Finset.sum_mul, ← cumCharge_sum]
  exact Finset.sum_le_sum fun F hF => factor_charge_le T e ids hroute hcaps F (hS F hF)

/-- Table lookup: a nonzero entry is a valid route with the stored axes. -/
theorem supAt_valid {s yy kT : ℕ} (hs : s < 15) (hyy : yy < 68) (hkT : kT < 31)
    (h : (supAt s yy kT).1 ≠ 0) :
    capsOK ⟨s, yy, min (300 * kT) 8870⟩ = true ∧
      routeOK ⟨s, yy, min (300 * kT) 8870⟩ (idsOfCode (supAt s yy kT).1) = true ∧
      axes ⟨s, yy, min (300 * kT) 8870⟩ (idsOfCode (supAt s yy kT).1) =
        ((supAt s yy kT).2.1, (supAt s yy kT).2.2.1, (supAt s yy kT).2.2.2) := by
  have hok := supTab_ok_all s hs
  simp only [supSliceOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hok
  have := hok yy hyy kT hkT
  rcases this with h0 | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd (by simpa [supAt] using h0) h
  · exact ⟨h1, h2, h3⟩

/-- (refined certificate: `hclips` only for clips of the box slope) From a box row's `ub = some u`: the big factor's fiber is ≤ u.
Sources of the bound: a clip row (`clipOK`), the old index (`oldIndex_ok_all`), a window (`capOK_of`). -/
theorem fiber_le_ubR {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (c : CertCell) (hcapsE : capsOK c.env = true)
    (hr14 : c.env.slope ≤ 14)
    (F : RegularIndex T.primary) (hF : F ∈ A)
    (hclips : ∀ x ∈ c.clips, x.1 = κr F → clipOK c x = true)
    (hdataE : ResidualSupportData (c.env.paddedSupport 0) F.1)
    (j k : ℕ) (hj : j < 24) (hk : k < 30)
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
    rcases hslice j hj k (by omega) with h0 | hrow
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
    have hc := hclips x hx h1
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




theorem pcell_env (c : RCell) (rq d : ℕ) (hd : d = if rq < c.env.slope then 1 else 0) :
    (pcell c rq).env = ⟨rq, c.env.middle - d, c.env.total - d⟩ := by
  simp only [pcell, hd]

/-- The big factor `F` of an `RCell` box: its fiber is at most `ub` (any `d` with `κ F + d ≤ E`, `d = 1` iff
another factor exists). -/
theorem F1_fiber_le {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (c : RCell) (hr14 : c.env.slope ≤ 14) (hmt : c.env.middle ≤ c.env.total) (hclips : ∀ x ∈ c.clips, clipOKR c x = true)
    (F : RegularIndex T.primary) (hF : F ∈ A) (d : ℕ) (hd : d = if κr F < c.env.slope then 1 else 0)
    (hrC : κr F ≤ 14) (hyE : κy F + d ≤ c.env.middle) (htE : κt F + d ≤ c.env.total)
    (hcapY : c.env.middle ≤ 67) (hcapT : c.env.total ≤ 8870)
    (j k : ℕ) (hj : j < 24) (hk : k < 30)
    (hyLo : bandLo (κr F) j ≤ κy F) (hyHi : κy F ≤ bandHi (κr F) j)
    (htLo : 300 * k < κt F) (htHi : κt F ≤ 300 * (k + 1))
    (u : ℕ) (hu : ub (pcell c (κr F)) (κr F) j k = some u) :
    (regularFiber T.primary T.seeds T.selected F).card ≤ u := by
  have he := pcell_env c (κr F) d hd
  have hch := κ_chain F
  have hr1 := slope_pos F
  have hshape : (pcell c (κr F)).env.slope ≤ (pcell c (κr F)).env.middle ∧
      (pcell c (κr F)).env.middle ≤ (pcell c (κr F)).env.total := by
    rw [he]; exact ⟨by show κr F ≤ c.env.middle - d; omega, by show c.env.middle - d ≤ c.env.total - d; omega⟩
  have hcp : capsOK (pcell c (κr F)).env = true := by
    rw [he]; simp only [capsOK, decide_eq_true_eq]; omega
  have hdataE := residual_support_of_endpoint F.1 (pcell c (κr F)).env hshape
    (below_env F _ hshape.1 hshape.2
      (by rw [he] <;> exact le_rfl)
      (by rw [he]; show κy F ≤ c.env.middle - d; omega)
      (by rw [he]; show κt F ≤ c.env.total - d; omega))
  refine fiber_le_ubR T A (pcell c (κr F)) hcp (by rw [he]; show κr F ≤ 14; exact hrC) F hF ?_ hdataE j k hj hk
    (by rw [he] <;> exact le_rfl) (by rw [he]; show κy F ≤ c.env.middle - d; omega)
    (by rw [he]; show κt F ≤ c.env.total - d; omega) hyLo hyHi htLo htHi u hu
  intro x hx hx1
  have := hclips x hx
  simp only [clipOKR] at this
  rw [hx1] at this
  exact this

/-- **composition_card_le_refined**: the refined composition certificate (F35 §2). Splits on a factor `F1` of
largest total; `F1` is bounded by `ub` of its box, the other factors by the linear charge at the box-dependent support
`S'(Q)` read from `supTab`. `hs` is the exact slope of the aggregate (as in `row_count`), which makes `rq < r` equivalent
to "another factor exists". -/
theorem composition_card_le_refined {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (c : RCell) (hc : certCheckR c = true)
    (hshape : c.env.slope ≤ c.env.middle ∧ c.env.middle ≤ c.env.total)
    (hfit : Below (Koala6831MovingAdaptive.aggregateFlag T.primary A) c.env.flag)
    (hs : c.env.slope = (Koala6831MovingAdaptive.aggregateFlag T.primary A).all) :
    (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤ c.bound := by
  obtain ⟨hcE, ⟨hr1, hr14⟩, hclips, hboxes⟩ := certCheckR_parts hc
  obtain ⟨_, _, hR16, hE71, hT8870⟩ := caps_of c.env hcE
  obtain ⟨hsR, hsY, hsT⟩ := residue_sums T A c.env hshape hfit
  have hsRe : ∑ F ∈ A, κr F = c.env.slope := by rw [hs, agg_all_eq]
  have hseeds := seeds_le_sum T A
  rcases A.eq_empty_or_nonempty with hA | hne
  · subst hA; simp
  obtain ⟨F1, hF1, hmax⟩ := Finset.exists_max_image A κt hne
  set r := c.env.slope with hr_def
  set y := c.env.middle with hy_def
  set t := c.env.total with ht_def
  let fiber := regularFiber T.primary T.seeds T.selected
  have hscale : 0 < terminalScale := by decide
  have hsplit (f : RegularIndex T.primary → ℕ) : (∑ G ∈ A, f G) = f F1 + ∑ G ∈ A.erase F1, f G :=
    (Finset.add_sum_erase A f hF1).symm
  have hκ1 := κ_chain F1
  have hrq1 : 1 ≤ κr F1 := slope_pos F1
  have hrqr : κr F1 ≤ r := by have := hsplit κr; omega
  have hyF1 : κy F1 ≤ y := by have := hsplit κy; omega
  have htF1 : κt F1 ≤ t := by have := hsplit κt; omega
  -- the box of F1
  set rq := κr F1 with hrq
  set j := (κy F1 - rq) / 3 with hj_def
  set k := (κt F1 - 1) / 300 with hk_def
  have hj : j < 24 := by omega
  have hk : k < 30 := by omega
  have hyLo : bandLo rq j ≤ κy F1 := by simp only [bandLo]; omega
  have hyHi : κy F1 ≤ bandHi rq j := by simp only [bandHi]; omega
  have htLo : 300 * k < κt F1 := by omega
  have htHi : κt F1 ≤ 300 * (k + 1) := by omega
  have hrow := hboxes rq hrqr hrq1 j hj k hk
  have hlot : max (300 * k + 1) (bandLo rq j) ≤ κt F1 := max_le (by omega) (hyLo.trans hκ1.2)
  rcases Nat.lt_or_ge rq r with hlt | hge
  · ------------------------------------------------------------------ rq < r: another factor exists
    obtain ⟨G0, hG0⟩ : (A.erase F1).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have := hsplit κr
      rw [hcon] at this
      simp at this
      omega
    have hG0A := Finset.mem_of_mem_erase hG0
    have hG0ne := Finset.ne_of_mem_erase hG0
    have hG0pos : 1 ≤ κr G0 := slope_pos G0
    have hG0chain := κ_chain G0
    have hG0le (f : RegularIndex T.primary → ℕ) (hf : ∀ G, 0 ≤ f G) : f G0 ≤ ∑ G ∈ A.erase F1, f G :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hG0
    have hy1 : κy F1 + 1 ≤ y := by
      have h1 := hsplit κy; have h2 := hG0le κy (fun _ => Nat.zero_le _); omega
    have ht1 : κt F1 + 1 ≤ t := by
      have h1 := hsplit κt; have h2 := hG0le κt (fun _ => Nat.zero_le _); omega
    have hnotskip : ¬ (y ≤ bandLo rq j ∨ t ≤ max (300 * k + 1) (bandLo rq j)) := by omega
    unfold boxR at hrow
    rw [if_pos hlt, if_neg hnotskip] at hrow
    dsimp only at hrow
    -- the support S'
    set loy := bandLo rq j with hloy
    set lot := max (300 * k + 1) loy with hlot_def
    set rr := r - rq with hrr
    set tt := min (300 * (k + 1)) (t - lot) with htt
    set yy := min (y - loy) tt with hyy
    set kT := (tt + 299) / 300 with hkT
    have hent : (supAt (min rr yy) yy kT).1 ≠ 0 := by
      intro h0; rw [if_pos h0] at hrow; exact absurd hrow Bool.false_ne_true
    rw [if_neg hent] at hrow
    -- ub is some u
    cases hu : ub (pcell c rq) rq j k with
    | none => rw [hu] at hrow; exact absurd hrow Bool.false_ne_true
    | some u =>
      rw [hu] at hrow
      replace hrow := of_decide_eq_true hrow
      -- F1
      have hF1u : (fiber F1).card ≤ u :=
        F1_fiber_le T A c hr14 hshape.2 hclips F1 hF1 1 (by rw [if_pos hlt]) (by omega) (by omega) (by omega)
          hE71 hT8870 j k hj hk hyLo hyHi htLo htHi u hu
      -- the others
      set others := A.erase F1 with hothers
      have hoR : ∑ G ∈ others, κr G ≤ rr := by have := hsplit κr; omega
      have hoY : ∑ G ∈ others, κy G ≤ y - loy := by have := hsplit κy; omega
      have hoT : ∑ G ∈ others, κt G ≤ t - lot := by have := hsplit κt; omega
      have hGt (G) (hG : G ∈ others) : κt G ≤ tt := by
        have h1 : κt G ≤ κt F1 := hmax G (Finset.mem_of_mem_erase hG)
        have h2 : κt G ≤ ∑ H ∈ others, κt H := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hG
        simp only [htt]; omega
      have hGy (G) (hG : G ∈ others) : κy G ≤ yy := by
        have h2 : κy G ≤ ∑ H ∈ others, κy H := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hG
        have := hGt G hG; have := (κ_chain G).2
        simp only [hyy]; omega
      have hGr (G) (hG : G ∈ others) : κr G ≤ min rr yy := by
        have h2 : κr G ≤ ∑ H ∈ others, κr H := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hG
        have := hGy G hG; have := (κ_chain G).1
        omega
      have hyyT : yy ≤ tt := min_le_right _ _
      have httT : tt ≤ min (300 * kT) 8870 := by
        simp only [htt, hkT]; omega
      obtain ⟨hcap', hroute', haxes'⟩ := supAt_valid (s := min rr yy) (yy := yy) (kT := kT)
        (by omega) (by omega) (by simp only [hkT, htt]; omega) hent
      have hbelow : ∀ G ∈ others, Below (originalCumulativeFlag G.1)
          (⟨min rr yy, yy, min (300 * kT) 8870⟩ : Envelope).flag := fun G hG =>
        below_env G _ (min_le_right _ _) (hyyT.trans httT) (hGr G hG) (hGy G hG) ((hGt G hG).trans httT)
      have hcharge := sum_charge_at T _ _ hroute' hcap' others hbelow
      rw [haxes'] at hcharge
      -- aggregate of the others
      have hcardO : others.card ≤ rr := by
        have h1 : others.card ≤ ∑ G ∈ others, κr G := by
          have := Finset.card_nsmul_le_sum others κr 1 (fun G _ => slope_pos G)
          simpa using this
        omega
      have hoT' : ∑ G ∈ others, κt G ≤ rr * tt := by
        have h1 : ∑ G ∈ others, κt G ≤ others.card * tt := by
          have := Finset.sum_le_card_nsmul others κt tt hGt
          simpa using this
        have h2 : others.card * tt ≤ rr * tt := Nat.mul_le_mul_right _ hcardO
        omega
      have hoT'' : ∑ G ∈ others, κt G ≤ min (t - lot) (rr * tt) := le_min hoT hoT'
      have hothBound : (∑ G ∈ others, (fiber G).card) ≤
          cumCharge ((supAt (min rr yy) yy kT).2.1, (supAt (min rr yy) yy kT).2.2.1, (supAt (min rr yy) yy kT).2.2.2)
            rr (y - loy) (min (t - lot) (rr * tt)) / terminalScale :=
        (Nat.le_div_iff_mul_le hscale).mpr (hcharge.trans (cumCharge_mono _ hoR hoY hoT''))
      calc (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤ ∑ G ∈ A, (fiber G).card := hseeds
        _ = (fiber F1).card + ∑ G ∈ others, (fiber G).card := hsplit _
        _ ≤ u + _ := Nat.add_le_add hF1u hothBound
        _ ≤ c.bound := hrow
  · ------------------------------------------------------------------ rq = r: F1 is the only factor
    have hrqr' : rq = r := le_antisymm hrqr hge
    have hnotskip : ¬ (y < bandLo rq j ∨ t < max (300 * k + 1) (bandLo rq j)) := by omega
    unfold boxR at hrow
    rw [if_neg (by omega : ¬ rq < r), if_neg hnotskip] at hrow
    have hothEmpty : A.erase F1 = ∅ := by
      by_contra hcon
      obtain ⟨G, hG⟩ := Finset.nonempty_iff_ne_empty.mpr hcon
      have h1 := slope_pos G
      have h2 : κr G ≤ ∑ H ∈ A.erase F1, κr H := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hG
      have := hsplit κr
      omega
    cases hu : ub (pcell c rq) rq j k with
    | none => rw [hu] at hrow; exact absurd hrow Bool.false_ne_true
    | some u =>
      rw [hu] at hrow
      replace hrow := of_decide_eq_true hrow
      have hF1u : (fiber F1).card ≤ u :=
        F1_fiber_le T A c hr14 hshape.2 hclips F1 hF1 0 (by rw [if_neg (by omega)]) (by omega) (by omega) (by omega)
          hE71 hT8870 j k hj hk hyLo hyHi htLo htHi u hu
      calc (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤ ∑ G ∈ A, (fiber G).card := hseeds
        _ = (fiber F1).card + ∑ G ∈ A.erase F1, (fiber G).card := hsplit _
        _ ≤ u + 0 := by rw [hothEmpty]; simpa using hF1u
        _ ≤ c.bound := by omega

end P33
end SubmissionLower
end ProximityPrize
