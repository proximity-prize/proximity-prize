/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.LabelTable

/-!
# Three reserved cosets and three flats sharing a row

A label is `v = (y, z)` with `y ∈ 𝔽₂^11` and `z ∈ 𝔽₂^4`.  A member of the family is

`S = {z ∈ Q} ∪ F₀ ∪ F₁ ∪ F₂`,   `F_t = {z ∈ H_t, r · y = ρ_t(z), m_t · y = ν_t(z)}`,

with the row `(Q, H₀, H₁, H₂)` from `LabelTable`, one common functional `r ≠ 0`, three
distinct functionals `m_t` vanishing at a pivot `pv r` of `r`, affine `ρ_t` with
`ρ_s ≠ ρ_t` on `H_s ∩ H_t`, and affine `ν_t`.  Each `F_t` is a coset of the kernel of a
surjection `V → 𝔽₂^3`, so a flat of size `2^12`; `S` has `3 · 2^11 + 3 · 2^12 = 18432`
points, and avoids the label `0`.

Its locator is `V_S = ∏_{q ∈ Q} (L_W - L_W(q)) · F₀ F₁ F₂`.  The three flat locators
give `X^12288` plus terms of degree at most `10240`, and the cubic in `L_W` differs
from `L_W^3` in degree at most `4096`, so `V_S = L_W^3 X^12288 + C_S` with
`deg C_S ≤ 16384`: every member shares the top `L_W^3 X^12288`.
-/

namespace ProximityPrize.SubmissionBinaryUpper.LabelFamily

set_option linter.constructorNameAsVariable false

attribute [local irreducible] SubspacePoly.nodeN FlatPoly.P SubspacePoly.L

open Polynomial
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly
open ProximityPrize.SubmissionBinaryUpper.FlatPoly
open ProximityPrize.SubmissionBinaryUpper.LabelSpace
open ProximityPrize.SubmissionBinaryUpper.LabelTable

/-! ## Linear forms on the low part -/

def ydot (f y : Yv) : ZMod 2 := ∑ i, f i * y i

theorem ydot_add (f y y' : Yv) : ydot f (y + y') = ydot f y + ydot f y' := by
  simp only [ydot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ydot_smul (f : Yv) (c : ZMod 2) (y : Yv) : ydot f (c • y) = c * ydot f y := by
  simp only [ydot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ydot_zero (f : Yv) : ydot f 0 = 0 := by simp [ydot]

theorem ydot_single (f : Yv) (i : Fin 11) : ydot f (Pi.single i 1) = f i := by
  simp [ydot, Pi.single_apply]

theorem zmod2_eq_one {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl

/-- A pivot of a functional: a coordinate where it is `1` (when it is nonzero). -/
noncomputable def pv (r : Yv) : Fin 11 := if h : ∃ i, r i ≠ 0 then Classical.choose h else 0

theorem pv_spec {r : Yv} (hr : r ≠ 0) : r (pv r) = 1 := by
  have h : ∃ i, r i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hr (funext hc)
  rw [pv, dif_pos h]
  exact zmod2_eq_one (Classical.choose_spec h)

/-! ## Parameters -/

abbrev NZ10 := {m : Fin 10 → ZMod 2 // m ≠ 0}
abbrev NZ11 := {r : Yv // r ≠ 0}

/-- Row, `ρ`-data `(j, a, e)`, the row `r`, the reduced `m_t`, the `ν`-slopes and two free
constants. -/
abbrev Param :=
  Fin 420 × (Fin 8 × ZMod 2 × ZMod 2) × NZ11 × (Fin 3 ↪ NZ10) × (Fin 3 → Fin 8) × (ZMod 2 × ZMod 2)

def row (p : Param) : QRow := qrow p.1
def jr (p : Param) : Fin 8 := p.2.1.1
def aa (p : Param) : ZMod 2 := p.2.1.2.1
def ee (p : Param) : ZMod 2 := p.2.1.2.2
def rr (p : Param) : Yv := p.2.2.1.val
def mr (p : Param) (t : Fin 3) : Fin 10 → ZMod 2 := (p.2.2.2.1 t).val
noncomputable def mm (p : Param) (t : Fin 3) : Yv := Fin.insertNth (pv (rr p)) 0 (mr p t)
def jn (p : Param) (t : Fin 3) : Fin 8 := p.2.2.2.2.1 t
def e0 (p : Param) : ZMod 2 := p.2.2.2.2.2.1
def e1 (p : Param) : ZMod 2 := p.2.2.2.2.2.2

theorem rr_ne (p : Param) : rr p ≠ 0 := p.2.2.1.property

theorem rr_pv (p : Param) : rr p (pv (rr p)) = 1 := pv_spec (rr_ne p)

theorem mm_pv (p : Param) (t : Fin 3) : mm p t (pv (rr p)) = 0 := by
  simp [mm]

theorem mm_ne (p : Param) (t : Fin 3) : mm p t ≠ 0 := by
  intro h
  apply (p.2.2.2.1 t).property
  funext i
  have := congrFun h ((pv (rr p)).succAbove i)
  simpa [mm, mr] using this

theorem mm_injective (p : Param) {s t : Fin 3} (h : mm p s = mm p t) : s = t := by
  apply p.2.2.2.1.injective
  apply Subtype.ext
  exact Fin.insertNth_right_injective _ h

def sig (p : Param) (t : Fin 3) : ℕ := (row p).s t

/-- The slope of `ρ₀`. -/
def beta (p : Param) : ℕ := betaOf (row p).s0 (jr p)

def coefL (p : Param) : Fin 3 → ZMod 2 := ![0, ee p, ee p + 1]

def rhoC (p : Param) : Fin 3 → ZMod 2 := ![aa p, aa p + 1 + ee p, aa p + ee p]

def rhoLin (p : Param) (t : Fin 3) (z : Z4) : ZMod 2 :=
  zdot (beta p) z + coefL p t * zdot (row p).s0 z

def rho (p : Param) (t : Fin 3) (z : Z4) : ZMod 2 := rhoC p t + rhoLin p t z

def bC (p : Param) : Fin 3 → ZMod 2 :=
  ![e0 p, if aa p + ee p = 1 then 1 else e1 p, if aa p + ee p = 1 then e1 p else 1]

def nuS (p : Param) (t : Fin 3) : ℕ := betaOf (sig p t) (jn p t)

def nu (p : Param) (t : Fin 3) (z : Z4) : ZMod 2 := bC p t + zdot (nuS p t) z

theorem rhoLin_add (p : Param) (t : Fin 3) (z w : Z4) :
    rhoLin p t (z + w) = rhoLin p t z + rhoLin p t w := by
  simp only [rhoLin, zdot_add]
  ring

theorem rhoLin_smul (p : Param) (t : Fin 3) (c : ZMod 2) (z : Z4) :
    rhoLin p t (c • z) = c * rhoLin p t z := by
  simp only [rhoLin, zdot_smul]
  ring

theorem rhoLin_zero (p : Param) (t : Fin 3) : rhoLin p t 0 = 0 := by
  simp [rhoLin, zdot_zero]

/-! ## Members -/

def inF (p : Param) (t : Fin 3) (v : V) : Prop :=
  (row p).inH t v.2 ∧ ydot (rr p) v.1 = rho p t v.2 ∧ ydot (mm p t) v.1 = nu p t v.2

noncomputable instance (p : Param) (t : Fin 3) : DecidablePred (inF p t) := by
  intro v; unfold inF; infer_instance

noncomputable irreducible_def Qpart (p : Param) : Finset V := Finset.univ.filter fun v => (row p).isQ v.2

noncomputable irreducible_def Fset (p : Param) (t : Fin 3) : Finset V := Finset.univ.filter (inF p t)

/-- The member with parameters `p`. -/
noncomputable irreducible_def Sset (p : Param) : Finset V := Qpart p ∪ Fset p 0 ∪ Fset p 1 ∪ Fset p 2

theorem mem_Sset {p : Param} {v : V} :
    v ∈ Sset p ↔ (row p).isQ v.2 ∨ inF p 0 v ∨ inF p 1 v ∨ inF p 2 v := by
  simp [Sset_def, Qpart_def, Fset_def]

/-! ## Facts about the row -/

theorem rok (p : Param) : RowOK (row p) := row_ok p.1

theorem sok (p : Param) (t : Fin 3) : SOK (sig p t) := by
  obtain ⟨⟨h0, h1, h2⟩, -⟩ := rok p
  fin_cases t
  · exact h0
  · exact h1
  · exact h2

theorem qout (p : Param) (z : Z4) (h : (row p).isQ z) :
    ¬(row p).inH 0 z ∧ ¬(row p).inH 1 z ∧ ¬(row p).inH 2 z := ((rok p).2.1 z).1 h

theorem shape (p : Param) (z : Z4) (h : ¬(row p).isQ z) : Shape (row p) z := ((rok p).2.1 z).2 h

theorem qcard (p : Param) : (Finset.univ.filter (row p).isQ).card = 3 := (rok p).2.2.2

theorem inH_zero_iff (p : Param) (t : Fin 3) : (row p).inH t 0 ↔ t ≠ 0 := by
  simp only [QRow.inH, zdot_zero]
  fin_cases t <;> simp [kap]

theorem not_isQ_zero (p : Param) : ¬(row p).isQ 0 := fun h =>
  (qout p 0 h).2.1 ((inH_zero_iff p 1).mpr (by decide))

theorem inH0_iff (p : Param) (z : Z4) : (row p).inH 0 z ↔ zdot (row p).s0 z = 1 := Iff.rfl

theorem zmod2_ne_add_one (x : ZMod 2) : x ≠ x + 1 := by
  revert x; decide

theorem two_z2 : (2 : ZMod 2) = 0 := rfl

theorem rho_01 (p : Param) {z : Z4} (h0 : zdot (row p).s0 z = 1) : rho p 1 z = rho p 0 z + 1 := by
  simp only [rho, rhoC, rhoLin, coefL, h0]
  simp
  linear_combination ee p * two_z2

theorem rho_02 (p : Param) {z : Z4} (h0 : zdot (row p).s0 z = 1) : rho p 2 z = rho p 0 z + 1 := by
  simp only [rho, rhoC, rhoLin, coefL, h0]
  simp
  linear_combination ee p * two_z2

theorem rho_12 (p : Param) {z : Z4} (h0 : zdot (row p).s0 z = 0) : rho p 1 z = rho p 2 z + 1 := by
  simp only [rho, rhoC, rhoLin, coefL, h0]
  simp
  ring

theorem not_inH0_of_12 (p : Param) {z : Z4} (h1 : (row p).inH 1 z) (h2 : (row p).inH 2 z) :
    ¬(row p).inH 0 z := by
  have hQ : ¬(row p).isQ z := fun hq => (qout p z hq).2.1 h1
  rcases shape p z hQ with h | h | h | h <;> simp_all

theorem zdot0_of_12 (p : Param) {z : Z4} (h1 : (row p).inH 1 z) (h2 : (row p).inH 2 z) :
    zdot (row p).s0 z = 0 := by
  have hn := not_inH0_of_12 p h1 h2
  rcases zmod2_cases (zdot (row p).s0 z) with h | h
  · exact h
  · exact absurd h hn

theorem ne01 (p : Param) {z : Z4} (h0 : (row p).inH 0 z) : rho p 0 z ≠ rho p 1 z := by
  rw [rho_01 p h0]; exact zmod2_ne_add_one _

theorem ne02 (p : Param) {z : Z4} (h0 : (row p).inH 0 z) : rho p 0 z ≠ rho p 2 z := by
  rw [rho_02 p h0]; exact zmod2_ne_add_one _

theorem ne12 (p : Param) {z : Z4} (h1 : (row p).inH 1 z) (h2 : (row p).inH 2 z) :
    rho p 1 z ≠ rho p 2 z := by
  rw [rho_12 p (zdot0_of_12 p h1 h2)]; exact (zmod2_ne_add_one _).symm

theorem rho_ne (p : Param) {s t : Fin 3} (hst : s ≠ t) {z : Z4} (hs : (row p).inH s z)
    (ht : (row p).inH t z) : rho p s z ≠ rho p t z := by
  fin_cases s <;> fin_cases t
  · exact absurd rfl hst
  · exact ne01 p hs
  · exact ne02 p hs
  · exact (ne01 p ht).symm
  · exact absurd rfl hst
  · exact ne12 p hs ht
  · exact (ne02 p ht).symm
  · exact (ne12 p ht hs).symm
  · exact absurd rfl hst

/-! ## Disjointness and the label `0` -/

theorem Fset_disjoint (p : Param) {s t : Fin 3} (hst : s ≠ t) : Disjoint (Fset p s) (Fset p t) := by
  rw [Finset.disjoint_left]
  intro v hs ht
  simp only [Fset_def, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
  exact rho_ne p hst hs.1 ht.1 (hs.2.1.symm.trans ht.2.1)

theorem Qpart_disjoint (p : Param) (t : Fin 3) : Disjoint (Qpart p) (Fset p t) := by
  rw [Finset.disjoint_left]
  intro v hq ht
  simp only [Qpart_def, Fset_def, Finset.mem_filter, Finset.mem_univ, true_and] at hq ht
  have := qout p v.2 hq
  fin_cases t
  · exact this.1 ht.1
  · exact this.2.1 ht.1
  · exact this.2.2 ht.1

theorem zero_not_mem (p : Param) : (0 : V) ∉ Sset p := by
  rw [mem_Sset]
  have hQ := not_isQ_zero p
  rintro (h | h | h | h)
  · exact hQ h
  · exact (inH_zero_iff p 0).mp h.1 rfl
  · obtain ⟨-, h1, h2⟩ := h
    simp only [Prod.fst_zero, Prod.snd_zero, ydot_zero, rho, nu, rhoLin_zero, zdot_zero,
      add_zero, rhoC, bC, Matrix.cons_val_one, Matrix.head_cons] at h1 h2
    revert h1 h2
    generalize aa p = a
    generalize ee p = e
    generalize e1 p = f
    revert a e f
    decide
  · obtain ⟨-, h1, h2⟩ := h
    simp only [Prod.fst_zero, Prod.snd_zero, ydot_zero, rho, nu, rhoLin_zero, zdot_zero,
      add_zero, rhoC, bC, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h1 h2
    revert h1 h2
    generalize aa p = a
    generalize ee p = e
    generalize e1 p = f
    revert a e f
    decide

/-! ## Each `F_t` is a flat of size `2^12` -/

noncomputable def phi (p : Param) (t : Fin 3) : V →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := ![zdot (sig p t) v.2, ydot (rr p) v.1 + rhoLin p t v.2,
    ydot (mm p t) v.1 + zdot (nuS p t) v.2]
  map_add' v w := by
    funext k
    fin_cases k <;>
      simp [zdot_add, ydot_add, rhoLin_add] <;> ring
  map_smul' c v := by
    funext k
    fin_cases k <;>
      simp [zdot_smul, ydot_smul, rhoLin_smul] <;> ring

def tgt (p : Param) (t : Fin 3) : Fin 3 → ZMod 2 := ![kap t, rhoC p t, bC p t]

theorem zmod2_add_eq_iff (a b c : ZMod 2) : a + b = c ↔ a = c + b := by
  revert a b c; decide

theorem phi_apply (p : Param) (t : Fin 3) (v : V) :
    phi p t v = ![zdot (sig p t) v.2, ydot (rr p) v.1 + rhoLin p t v.2,
      ydot (mm p t) v.1 + zdot (nuS p t) v.2] := rfl

theorem inF_iff (p : Param) (t : Fin 3) (v : V) : inF p t v ↔ phi p t v = tgt p t := by
  rw [phi_apply, tgt]
  constructor
  · rintro ⟨h0, h1, h2⟩
    funext k
    fin_cases k
    · exact h0
    · simpa [zmod2_add_eq_iff, rho] using h1
    · simpa [zmod2_add_eq_iff, nu] using h2
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at h0 h1 h2
    refine ⟨h0, ?_, ?_⟩
    · rw [rho]; exact (zmod2_add_eq_iff _ _ _).mp h1
    · rw [nu]; exact (zmod2_add_eq_iff _ _ _).mp h2

theorem phi_surj (p : Param) (t : Fin 3) : Function.Surjective (phi p t) := by
  obtain ⟨z1, hz1⟩ := zdot_surj (sok p t)
  have hm : ∃ q, mm p t q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact mm_ne p t (funext hc)
  obtain ⟨q, hq⟩ := hm
  have hq1 := zmod2_eq_one hq
  set k := pv (rr p)
  let yr : Yv := Pi.single k 1
  let ym : Yv := Pi.single q 1 + rr p q • Pi.single k 1
  have hA : phi p t (yr, 0) = ![0, 1, 0] := by
    rw [phi_apply]
    simp [yr, ydot_single, zdot_zero, rhoLin_zero, rr_pv, mm_pv, k]
  have hB : phi p t (ym, 0) = ![0, 0, 1] := by
    rw [phi_apply]
    have e1 : ydot (rr p) ym = 0 := by
      simp only [ym, ydot_add, ydot_smul, ydot_single, rr_pv, k]
      linear_combination rr p q * two_z2
    have e2 : ydot (mm p t) ym = 1 := by
      simp only [ym, ydot_add, ydot_smul, ydot_single, mm_pv, hq1, k]
      ring
    simp [e1, e2, zdot_zero, rhoLin_zero]
  intro w
  refine ⟨w 0 • ((0 : Yv), z1) + (w 1 - w 0 * rhoLin p t z1) • (yr, (0 : Z4)) +
    (w 2 - w 0 * zdot (nuS p t) z1) • (ym, (0 : Z4)), ?_⟩
  rw [map_add, map_add, map_smul, map_smul, map_smul, hA, hB, phi_apply]
  funext j
  fin_cases j <;> simp [hz1, ydot_zero] <;> ring

theorem finrank_V : Module.finrank (ZMod 2) V = 15 := by
  simp [V, Z4, Yv, Module.finrank_prod, Module.finrank_fin_fun]

theorem finrank_ker (p : Param) (t : Fin 3) :
    Module.finrank (ZMod 2) (LinearMap.ker (phi p t)) = 12 := by
  have h := LinearMap.finrank_range_add_finrank_ker (phi p t)
  rw [LinearMap.range_eq_top.mpr (phi_surj p t), finrank_top, Module.finrank_fin_fun,
    finrank_V] at h
  omega

noncomputable def bas (p : Param) (t : Fin 3) :
    Module.Basis (Fin 12) (ZMod 2) (LinearMap.ker (phi p t)) :=
  Module.finBasisOfFinrankEq _ _ (finrank_ker p t)

noncomputable def ub (p : Param) (t : Fin 3) (k : ℕ) : K :=
  if h : k < 12 then lab ((bas p t ⟨k, h⟩ : LinearMap.ker (phi p t)) : V) else 0

noncomputable def v0 (p : Param) (t : Fin 3) : V := Classical.choose (phi_surj p t (tgt p t))

theorem v0_spec (p : Param) (t : Fin 3) : phi p t (v0 p t) = tgt p t :=
  Classical.choose_spec (phi_surj p t (tgt p t))

/-- `lab` as an additive map, for sums. -/
noncomputable def labHom : V →+ K := AddMonoidHom.mk' lab lab_add

theorem lab_sum {ι : Type*} (s : Finset ι) (f : ι → V) : lab (∑ i ∈ s, f i) = ∑ i ∈ s, lab (f i) :=
  map_sum labHom f s

/-- The locator of `F_t`. -/
noncomputable irreducible_def Fl (p : Param) (t : Fin 3) : Polynomial K :=
  flatPoly (ub p t) 12 (lab (v0 p t))

theorem lab_ker (p : Param) (t : Fin 3) (w : LinearMap.ker (phi p t)) :
    ∃ a : ℕ → ZMod 2, lab (w : V) = ∑ k ∈ Finset.range 12, ψ (a k) * ub p t k := by
  refine ⟨fun k => if h : k < 12 then (bas p t).repr w ⟨k, h⟩ else 0, ?_⟩
  have hw := (bas p t).sum_repr w
  have hw' : (w : V) = ∑ k, (bas p t).repr w k • ((bas p t k : LinearMap.ker (phi p t)) : V) := by
    calc (w : V) = ((∑ k, (bas p t).repr w k • bas p t k : LinearMap.ker (phi p t)) : V) := by
          rw [hw]
      _ = _ := by rw [Submodule.coe_sum]; rfl
  rw [hw', lab_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ψ (if h : k < 12 then (bas p t).repr w ⟨k, h⟩ else 0) *
    ub p t k) 12]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lab_smul, ub, dif_pos k.isLt, dif_pos k.isLt]

theorem Fl_eval (p : Param) (t : Fin 3) {v : V} (hv : inF p t v) : (Fl p t).eval (lab v) = 0 := by
  have hv' := (inF_iff p t v).mp hv
  have hker : v - v0 p t ∈ LinearMap.ker (phi p t) := by
    rw [LinearMap.mem_ker, map_sub, hv', v0_spec, sub_self]
  obtain ⟨a, ha⟩ := lab_ker p t ⟨v - v0 p t, hker⟩
  have hv0 : lab v = lab (v0 p t) + lab (v - v0 p t) := by
    rw [← lab_add, add_sub_cancel]
  rw [hv0, ha, Fl_def]
  exact flatPoly_eval _ _ _ _

theorem Fl_gap (p : Param) (t : Fin 3) : (Fl p t - Xp 4096).natDegree ≤ 4096 - 2048 := by
  have h := flatPoly_gapX (ub p t) 12 (by norm_num) (lab (v0 p t))
  rw [Fl_def]
  exact h

/-! ## Sizes -/

theorem Fset_card (p : Param) (t : Fin 3) : (Fset p t).card = 4096 := by
  classical
  let g : LinearMap.ker (phi p t) → V := fun w => v0 p t + w.val
  have himg : Fset p t = (Finset.univ : Finset (LinearMap.ker (phi p t))).image g := by
    ext v
    simp only [Fset_def, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [inF_iff]
    constructor
    · intro hv
      have hk : v - v0 p t ∈ LinearMap.ker (phi p t) := by
        rw [LinearMap.mem_ker, map_sub, hv, v0_spec, sub_self]
      exact ⟨⟨v - v0 p t, hk⟩, by simp [g]⟩
    · rintro ⟨w, rfl⟩
      simp only [g]
      rw [map_add, v0_spec, LinearMap.mem_ker.mp w.property, add_zero]
  have hg : Function.Injective g := by
    intro w w' h
    exact Subtype.ext (add_left_cancel h)
  rw [himg, Finset.card_image_of_injective _ hg]
  rw [Finset.card_univ, Module.card_eq_pow_finrank (K := ZMod 2), finrank_ker, ZMod.card]
  norm_num

theorem Qpart_card (p : Param) : (Qpart p).card = 6144 := by
  classical
  have h : Qpart p = (Finset.univ : Finset Yv) ×ˢ Finset.univ.filter (row p).isQ := by
    ext v
    simp [Qpart_def]
  rw [h, Finset.card_product, qcard, Finset.card_univ]
  simp [Yv, ZMod.card]

theorem Sset_card (p : Param) : (Sset p).card = 18432 := by
  rw [Sset_def, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint, Qpart_card, Fset_card, Fset_card, Fset_card]
  · exact Qpart_disjoint p 0
  · rw [Finset.disjoint_union_left]
    exact ⟨Qpart_disjoint p 1, Fset_disjoint p (by decide)⟩
  · rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨Qpart_disjoint p 2, Fset_disjoint p (by decide)⟩, Fset_disjoint p (by decide)⟩

/-! ## The locator and its common top -/

noncomputable def cq (q : ℕ) : K := LW.eval (lab (0, zv q))

noncomputable def Gq (p : Param) : Polynomial K :=
  (LW - C (cq (row p).q1)) * (LW - C (cq (row p).q2)) * (LW - C (cq (row p).q3))

noncomputable def Fprod (p : Param) : Polynomial K := Fl p 0 * Fl p 1 * Fl p 2

noncomputable def Vp (p : Param) : Polynomial K := Gq p * Fprod p

noncomputable irreducible_def Rtop : Polynomial K := LW ^ 3 * Xp 12288

noncomputable def Cp (p : Param) : Polynomial K := Vp p - Rtop

theorem Vp_eval (p : Param) {v : V} (hv : v ∈ Sset p) : (Vp p).eval (lab v) = 0 := by
  rw [mem_Sset] at hv
  rcases hv with hq | h | h | h
  · have hfac : ∀ q, v.2 = zv q → (LW - C (cq q)).eval (lab v) = 0 := by
      intro q hq
      rw [eval_sub, eval_C, LW_eval, hq, cq, sub_self]
    rw [Vp, Gq, eval_mul, eval_mul, eval_mul]
    rcases hq with hq | hq | hq
    · rw [hfac _ hq]; ring
    · rw [hfac _ hq]; ring
    · rw [hfac _ hq]; ring
  · rw [Vp, Fprod, eval_mul, eval_mul, eval_mul, Fl_eval p 0 h]; ring
  · rw [Vp, Fprod, eval_mul, eval_mul, eval_mul, Fl_eval p 1 h]; ring
  · rw [Vp, Fprod, eval_mul, eval_mul, eval_mul, Fl_eval p 2 h]; ring

theorem Fprod_gap (p : Param) : (Fprod p - Xp 12288).natDegree ≤ 10240 := by
  have h01 : (Fl p 0 * Fl p 1 - Xp 8192).natDegree ≤ 8192 - 2048 :=
    gap_mulX (a := 4096) (b := 4096) (c := 8192) (w := 2048) (by norm_num) (by norm_num)
      (by norm_num) (Fl_gap p 0) (Fl_gap p 1)
  have h012 : (Fl p 0 * Fl p 1 * Fl p 2 - Xp 12288).natDegree ≤ 12288 - 2048 :=
    gap_mulX (a := 8192) (b := 4096) (c := 12288) (w := 2048) (by norm_num) (by norm_num)
      (by norm_num) h01 (Fl_gap p 2)
  rw [Fprod]
  exact h012

theorem LW_sub_C_natDegree (c : K) : (LW - C c).natDegree ≤ 2048 := by
  rw [natDegree_sub_C, LW_natDegree]

theorem Gq_natDegree (p : Param) : (Gq p).natDegree ≤ 6144 := by
  rw [Gq]
  refine natDegree_mul_le.trans ?_
  have h1 := LW_sub_C_natDegree (cq (row p).q1)
  have h2 := LW_sub_C_natDegree (cq (row p).q2)
  have h3 := LW_sub_C_natDegree (cq (row p).q3)
  have h12 := (natDegree_mul_le (p := LW - C (cq (row p).q1)) (q := LW - C (cq (row p).q2)))
  omega

theorem Gq_sub_natDegree (p : Param) : (Gq p - LW ^ 3).natDegree ≤ 4096 := by
  set c1 := cq (row p).q1
  set c2 := cq (row p).q2
  set c3 := cq (row p).q3
  have h : Gq p - LW ^ 3 = C (-(c1 + c2 + c3)) * LW ^ 2 + C (c1 * c2 + c1 * c3 + c2 * c3) * LW +
      C (-(c1 * c2 * c3)) := by
    rw [Gq]
    simp only [C_neg, C_add, C_mul]
    ring
  rw [h]
  have hL2 : (LW ^ 2).natDegree ≤ 4096 := by
    refine natDegree_pow_le.trans ?_
    rw [LW_natDegree]
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · exact (natDegree_C_mul_le _ _).trans hL2
  · exact (natDegree_C_mul_le _ _).trans (by rw [LW_natDegree]; norm_num)
  · rw [natDegree_C]; norm_num

theorem Cp_natDegree_le (p : Param) : (Cp p).natDegree ≤ 16384 := by
  have h : Cp p = Gq p * (Fprod p - Xp 12288) + (Gq p - LW ^ 3) * Xp 12288 := by
    rw [Cp, Vp, Rtop_def]
    ring
  rw [h]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    have := Gq_natDegree p
    have := Fprod_gap p
    omega
  · refine natDegree_mul_le.trans ?_
    have := Gq_sub_natDegree p
    rw [Xp_natDegree]
    omega

theorem Vp_split (p : Param) : Vp p = Rtop + Cp p := by
  rw [Cp]; ring

theorem Rtop_coeff : Rtop.coeff 18432 = 1 := by
  rw [Rtop_def, Xp_def, show (18432 : ℕ) = 6144 + 12288 by norm_num, coeff_mul_X_pow]
  have hm : (LW ^ 3).Monic := LW_monic.pow 3
  have hd : (LW ^ 3).natDegree = 6144 := by
    rw [LW_monic.natDegree_pow, LW_natDegree]
  rw [← hd]
  exact hm

theorem Rtop_natDegree : Rtop.natDegree ≤ 18432 := by
  rw [Rtop_def]
  refine natDegree_mul_le.trans ?_
  rw [Xp_natDegree, LW_monic.natDegree_pow, LW_natDegree]

theorem Vp_coeff (p : Param) : (Vp p).coeff 18432 = 1 := by
  rw [Vp_split, coeff_add, Rtop_coeff,
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (Cp_natDegree_le p) (by norm_num)), add_zero]

theorem Vp_ne_zero (p : Param) : Vp p ≠ 0 := by
  intro h
  have := Vp_coeff p
  rw [h, coeff_zero] at this
  exact zero_ne_one this

theorem Vp_natDegree_le (p : Param) : (Vp p).natDegree ≤ 18432 := by
  rw [Vp_split]
  refine (natDegree_add_le _ _).trans (max_le Rtop_natDegree ?_)
  exact (Cp_natDegree_le p).trans (by norm_num)

/-! ## The locator determines the member -/

theorem subset_of_vanish {Λ : Polynomial K} (hΛ : Λ ≠ 0) (hdeg : Λ.natDegree ≤ 18432)
    {S T : Finset V} (hS : S.card = 18432) (hvS : ∀ v ∈ S, Λ.eval (lab v) = 0)
    (hvT : ∀ v ∈ T, Λ.eval (lab v) = 0) : T ⊆ S := by
  classical
  intro v hv
  by_contra hvS'
  have hsub : (insert v S).image lab ⊆ Λ.roots.toFinset := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hΛ]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hvT _ hv
    · exact hvS _ hw
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ lab_injective, Finset.card_insert_of_notMem hvS', hS] at hcard
  have h2 := (Multiset.toFinset_card_le Λ.roots).trans (card_roots' Λ)
  omega

theorem Sset_eq_of_Cp {p p' : Param} (h : Cp p = Cp p') : Sset p = Sset p' := by
  have hV : Vp p = Vp p' := by rw [Vp_split, Vp_split, h]
  have h1 : ∀ v ∈ Sset p, (Vp p).eval (lab v) = 0 := fun v hv => Vp_eval p hv
  have h2 : ∀ v ∈ Sset p', (Vp p).eval (lab v) = 0 := by
    intro v hv
    rw [hV]
    exact Vp_eval p' hv
  have hsub : Sset p' ⊆ Sset p :=
    subset_of_vanish (Vp_ne_zero p) (Vp_natDegree_le p) (Sset_card p) h1 h2
  exact (Finset.eq_of_subset_of_card_le hsub ((Sset_card p).trans (Sset_card p').symm).le).symm

end ProximityPrize.SubmissionBinaryUpper.LabelFamily
