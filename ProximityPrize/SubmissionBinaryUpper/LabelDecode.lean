/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.LabelFamily

/-!
# A member determines its parameters

Fix `z` in two half spaces `H_s ∩ H_t`.  The fibre `y ↦ [(y, z) ∈ S]` is the `𝔽₂`-polynomial

`(R + A + 1)(M_s + B + 1) + (R + A)(M_t + C + 1)`,  `R = r·y`, `M = m·y`,

with `A = ρ_s(z)`, `B = ν_s(z)`, `C = ν_t(z)`.  Point reads recover everything:

* full fibres are exactly `Q` (a two-flat fibre has the second difference `r ∧ (m_s + m_t) ≠ 0`),
  so the row is read off;
* the second differences on `H₀ ∩ H₁` and `H₀ ∩ H₂` are the wedges `r ∧ μ₀₁` and `r ∧ μ₀₂`,
  whose spans meet in `r` (`wedge`), so `r` and the `μ` are read off;
* first differences give `m₀` up to `μ₀₁` and up to `μ₀₂`, hence exactly;
* the values at `0`, `e_{pv r}` and one more `e_j` give `A, B, C`, hence `ρ_t` and `ν_t` on
  every `H_t`, hence the remaining parameters (`LabelTable.beta_inj`).
-/

namespace ProximityPrize.SubmissionBinaryUpper.LabelDecode

set_option linter.constructorNameAsVariable false

attribute [local irreducible] SubspacePoly.nodeN FlatPoly.P SubspacePoly.L

open ProximityPrize.SubmissionBinaryUpper.FlatPoly
open ProximityPrize.SubmissionBinaryUpper.LabelSpace
open ProximityPrize.SubmissionBinaryUpper.LabelTable
open ProximityPrize.SubmissionBinaryUpper.LabelFamily

/-! ## The fibre polynomial and its reads -/

def F (R A Ms B Mt C : ZMod 2) : ZMod 2 := (R + A + 1) * (Ms + B + 1) + (R + A) * (Mt + C + 1)

theorem ite_F : ∀ R A Ms B Mt C : ZMod 2,
    (if (R = A ∧ Ms = B) ∨ (R = A + 1 ∧ Mt = C) then (1 : ZMod 2) else 0) = F R A Ms B Mt C := by
  decide

def e (i : Fin 11) : Yv := Pi.single i 1

theorem ydot_e (f : Yv) (i : Fin 11) : ydot f (e i) = f i := ydot_single f i

theorem vals_core : ∀ A B C A' B' C' a b : ZMod 2,
    F 0 A 0 B 0 C = F 0 A' 0 B' 0 C' → F 1 A 0 B 0 C = F 1 A' 0 B' 0 C' →
      F a A b B (b + 1) C = F a A' b B' (b + 1) C' → A = A' ∧ B = B' ∧ C = C' := by
  decide

theorem read1_core : ∀ a b c A B C : ZMod 2,
    F a A b B c C + F 0 A 0 B 0 C = b + A * (b + c) + a * (b + c + B + C) := by
  decide

theorem read2_core : ∀ a1 a2 b1 b2 c1 c2 A B C : ZMod 2,
    F (a1 + a2) A (b1 + b2) B (c1 + c2) C + F a1 A b1 B c1 C + F a2 A b2 B c2 C + F 0 A 0 B 0 C =
      a1 * (b2 + c2) + a2 * (b1 + c1) := by
  decide

section Reads

variable {f : Yv → ZMod 2} {r ms mt : Yv} {A B C : ZMod 2}

theorem read1 (hf : ∀ y, f y = F (ydot r y) A (ydot ms y) B (ydot mt y) C) (i : Fin 11) :
    f (e i) + f 0 = ms i + A * (ms i + mt i) + r i * (ms i + mt i + B + C) := by
  rw [hf, hf]
  simp only [ydot_e, ydot_zero]
  exact read1_core _ _ _ _ _ _

theorem read2 (hf : ∀ y, f y = F (ydot r y) A (ydot ms y) B (ydot mt y) C) (i j : Fin 11) :
    f (e i + e j) + f (e i) + f (e j) + f 0 = r i * (ms j + mt j) + r j * (ms i + mt i) := by
  rw [hf, hf, hf, hf]
  simp only [ydot_add, ydot_e, ydot_zero]
  exact read2_core _ _ _ _ _ _ _ _ _

theorem decode_vals {A' B' C' : ZMod 2}
    (hf : ∀ y, f y = F (ydot r y) A (ydot ms y) B (ydot mt y) C)
    (hf' : ∀ y, f y = F (ydot r y) A' (ydot ms y) B' (ydot mt y) C')
    {k0 j0 : Fin 11} (hr : r k0 = 1) (hms : ms k0 = 0) (hmt : mt k0 = 0) (hj : ms j0 + mt j0 = 1) :
    A = A' ∧ B = B' ∧ C = C' := by
  have h0 := (hf 0).symm.trans (hf' 0)
  have h1 := (hf (e k0)).symm.trans (hf' (e k0))
  have h2 := (hf (e j0)).symm.trans (hf' (e j0))
  simp only [ydot_e, ydot_zero, hr, hms, hmt] at h0 h1 h2
  have hmt' : mt j0 = ms j0 + 1 := by
    rw [← hj]
    linear_combination -(ms j0) * two_z2
  rw [hmt'] at h2
  exact vals_core _ _ _ _ _ _ _ _ h0 h1 h2

end Reads

/-! ## The wedge of two functionals determines their span -/

theorem wedge_core : ∀ a1 a2 a3 b1 b2 b3 c1 c2 c3 : ZMod 2,
    1 * 1 + c3 * 0 = a2 * b3 + a3 * b2 → c1 * 0 + 1 * c2 = a1 * b2 + a2 * b1 →
      c1 * 1 + c3 * c2 = a1 * b3 + a3 * b1 → a1 = a2 * c1 + (a3 + c3 * a2) * c2 := by
  decide

theorem wedge {u v u' v' : Yv} {k0 j0 : Fin 11} (hu : u k0 = 1) (hv : v k0 = 0) (hj : v j0 = 1)
    (hB : ∀ i j, u i * v j + u j * v i = u' i * v' j + u' j * v' i) (k : Fin 11) :
    u' k = u' k0 * u k + (u' j0 + u j0 * u' k0) * v k := by
  have e1 := hB k0 j0
  have e2 := hB k k0
  have e3 := hB k j0
  rw [hu, hv, hj] at e1
  rw [hu, hv] at e2
  rw [hj] at e3
  exact wedge_core _ _ _ _ _ _ _ _ _ e1 e2 e3

theorem zmod2_ne_iff_add (a b : ZMod 2) : a ≠ b ↔ a + b = 1 := by
  revert a b; decide

/-- Two distinct nonzero vectors have no common multiple other than `0`. -/
theorem mul_vec_eq {μ ν : Yv} {b b' : ZMod 2} {j j' : Fin 11} (hμ : μ j = 1) (hν : ν j' = 1)
    (hne : μ ≠ ν) (h : ∀ k, b * μ k = b' * ν k) : b = 0 ∧ b' = 0 := by
  rcases zmod2_cases b with rfl | rfl <;> rcases zmod2_cases b' with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · have := h j'; rw [hν] at this; simp at this
  · have := h j; rw [hμ] at this; simp at this
  · exact absurd (funext fun k => by simpa using h k) hne

/-! ## Fibres of a member -/

noncomputable def ind (p : Param) (v : V) : ZMod 2 := if v ∈ Sset p then 1 else 0

theorem qout' (p : Param) {z : Z4} (hq : (row p).isQ z) (w : Fin 3) : ¬(row p).inH w z := by
  have h := qout p z hq
  fin_cases w
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem mem_of_inF (p : Param) (t : Fin 3) {v : V} (h : inF p t v) : v ∈ Sset p := by
  rw [mem_Sset]
  fin_cases t
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem inF_iff' (p : Param) (t : Fin 3) {y : Yv} {z : Z4} (h : (row p).inH t z) :
    inF p t (y, z) ↔ ydot (rr p) y = LabelFamily.rho p t z ∧ ydot (mm p t) y = nu p t z := by
  simp [inF, h]

theorem ind_pair (p : Param) {s t u : Fin 3} (hcov : ∀ w : Fin 3, w = s ∨ w = t ∨ w = u)
    {z : Z4} (hs : (row p).inH s z) (ht : (row p).inH t z) (hu : ¬(row p).inH u z)
    (hρ : LabelFamily.rho p t z = LabelFamily.rho p s z + 1) (y : Yv) :
    ind p (y, z) = F (ydot (rr p) y) (LabelFamily.rho p s z) (ydot (mm p s) y) (nu p s z)
      (ydot (mm p t) y) (nu p t z) := by
  have hQ : ¬(row p).isQ z := fun hq => qout' p hq s hs
  have hmem : (y, z) ∈ Sset p ↔ inF p s (y, z) ∨ inF p t (y, z) := by
    constructor
    · intro h
      rw [mem_Sset] at h
      have key : ∀ w : Fin 3, inF p w (y, z) → inF p s (y, z) ∨ inF p t (y, z) := by
        intro w hw
        rcases hcov w with rfl | rfl | rfl
        · exact Or.inl hw
        · exact Or.inr hw
        · exact absurd hw.1 hu
      rcases h with hq | h | h | h
      · exact absurd hq hQ
      · exact key 0 h
      · exact key 1 h
      · exact key 2 h
    · rintro (h | h)
      · exact mem_of_inF p s h
      · exact mem_of_inF p t h
  have hcond : (y, z) ∈ Sset p ↔
      ((ydot (rr p) y = LabelFamily.rho p s z ∧ ydot (mm p s) y = nu p s z) ∨
        (ydot (rr p) y = LabelFamily.rho p s z + 1 ∧ ydot (mm p t) y = nu p t z)) := by
    rw [hmem, inF_iff' p s hs, inF_iff' p t ht, hρ]
  rw [ind, ← ite_F]
  by_cases hm : (y, z) ∈ Sset p
  · rw [if_pos hm, if_pos (hcond.mp hm)]
  · rw [if_neg hm, if_neg (fun h => hm (hcond.mpr h))]

theorem zmod2_flip {a b : ZMod 2} (h : a = b + 1) : b = a + 1 := by
  revert a b; decide

theorem not_inH2_of_01 (p : Param) {z : Z4} (h0 : (row p).inH 0 z) (h1 : (row p).inH 1 z) :
    ¬(row p).inH 2 z := by
  have hQ : ¬(row p).isQ z := fun hq => qout' p hq 0 h0
  rcases shape p z hQ with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact absurd h0 a
  · exact c
  · exact absurd h1 b
  · exact absurd h0 a

theorem not_inH1_of_02 (p : Param) {z : Z4} (h0 : (row p).inH 0 z) (h2 : (row p).inH 2 z) :
    ¬(row p).inH 1 z := by
  have hQ : ¬(row p).isQ z := fun hq => qout' p hq 0 h0
  rcases shape p z hQ with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact absurd h0 a
  · exact absurd h2 c
  · exact b
  · exact absurd h0 a

theorem fib01 (p : Param) {z : Z4} (h0 : (row p).inH 0 z) (h1 : (row p).inH 1 z) (y : Yv) :
    ind p (y, z) = F (ydot (rr p) y) (LabelFamily.rho p 0 z) (ydot (mm p 0) y) (nu p 0 z)
      (ydot (mm p 1) y) (nu p 1 z) :=
  ind_pair p (s := 0) (t := 1) (u := 2) (by decide) h0 h1 (not_inH2_of_01 p h0 h1) (rho_01 p h0) y

theorem fib02 (p : Param) {z : Z4} (h0 : (row p).inH 0 z) (h2 : (row p).inH 2 z) (y : Yv) :
    ind p (y, z) = F (ydot (rr p) y) (LabelFamily.rho p 0 z) (ydot (mm p 0) y) (nu p 0 z)
      (ydot (mm p 2) y) (nu p 2 z) :=
  ind_pair p (s := 0) (t := 2) (u := 1) (by decide) h0 h2 (not_inH1_of_02 p h0 h2) (rho_02 p h0) y

theorem fib12 (p : Param) {z : Z4} (h1 : (row p).inH 1 z) (h2 : (row p).inH 2 z) (y : Yv) :
    ind p (y, z) = F (ydot (rr p) y) (LabelFamily.rho p 1 z) (ydot (mm p 1) y) (nu p 1 z)
      (ydot (mm p 2) y) (nu p 2 z) :=
  ind_pair p (s := 1) (t := 2) (u := 0) (by decide) h1 h2 (not_inH0_of_12 p h1 h2)
    (zmod2_flip (rho_12 p (zdot0_of_12 p h1 h2))) y

/-- A coordinate where two distinct `m_s`, `m_t` differ. -/
theorem exists_diff (p : Param) {s t : Fin 3} (hst : s ≠ t) :
    ∃ j, mm p s j + mm p t j = 1 := by
  have hne : mm p s ≠ mm p t := fun h => hst (mm_injective p h)
  have : ∃ j, mm p s j ≠ mm p t j := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  obtain ⟨j, hj⟩ := this
  exact ⟨j, (zmod2_ne_iff_add _ _).mp hj⟩

theorem pair_not_full (p : Param) {s t : Fin 3} (hst : s ≠ t) {z : Z4} {A B C : ZMod 2}
    (hf : ∀ y, ind p (y, z) = F (ydot (rr p) y) A (ydot (mm p s) y) B (ydot (mm p t) y) C) :
    ∃ y, ind p (y, z) = 0 := by
  by_contra hall
  push_neg at hall
  have h1 : ∀ y, ind p (y, z) = 1 := fun y => zmod2_eq_one (hall y)
  obtain ⟨j, hj⟩ := exists_diff p hst
  have h2 := read2 (f := fun y => ind p (y, z)) hf (pv (rr p)) j
  simp only [h1, rr_pv, mm_pv, hj] at h2
  revert h2
  generalize rr p j = a
  revert a
  decide

theorem full_of_Q (p : Param) {z : Z4} (hq : (row p).isQ z) (y : Yv) : ind p (y, z) = 1 := by
  rw [ind, if_pos (mem_Sset.mpr (Or.inl hq))]

theorem not_full (p : Param) {z : Z4} (hQ : ¬(row p).isQ z) : ∃ y, ind p (y, z) = 0 := by
  rcases shape p z hQ with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · refine ⟨0, ?_⟩
    rw [ind, if_neg]
    rw [mem_Sset]
    rintro (h | h | h | h)
    · exact hQ h
    · exact a h.1
    · exact b h.1
    · exact c h.1
  · exact pair_not_full p (s := 0) (t := 1) (by decide) (fib01 p a b)
  · exact pair_not_full p (s := 0) (t := 2) (by decide) (fib02 p a c)
  · exact pair_not_full p (s := 1) (t := 2) (by decide) (fib12 p b c)

theorem isQ_iff_full (p : Param) (z : Z4) : (row p).isQ z ↔ ∀ y, ind p (y, z) = 1 := by
  constructor
  · exact fun hq => full_of_Q p hq
  · intro h
    by_contra hQ
    obtain ⟨y, hy⟩ := not_full p hQ
    rw [h y] at hy
    exact one_ne_zero hy

/-! ## The decoding -/

noncomputable def mu (p : Param) (s t : Fin 3) : Yv := fun k => mm p s k + mm p t k

theorem mu_pv (p : Param) (s t : Fin 3) : mu p s t (pv (rr p)) = 0 := by
  simp [mu, mm_pv]

theorem mu_ne (p : Param) {s t u : Fin 3} (htu : t ≠ u) : mu p s t ≠ mu p s u := by
  intro h
  apply htu
  apply mm_injective p
  funext k
  have := congrFun h k
  simp only [mu] at this
  linear_combination this

theorem wedge_read (p : Param) {f : Yv → ZMod 2} {s t : Fin 3} {A B C : ZMod 2}
    (hf : ∀ y, f y = F (ydot (rr p) y) A (ydot (mm p s) y) B (ydot (mm p t) y) C) (i j : Fin 11) :
    f (e i + e j) + f (e i) + f (e j) + f 0 =
      rr p i * mu p s t j + rr p j * mu p s t i := read2 hf i j

theorem m0_core : ∀ x1 x2 x3 x4 A B C A' B' C' : ZMod 2,
    x1 + A * (x1 + x3) + x4 * (x1 + x3 + B + C) = x2 + A' * (x1 + x3) + x4 * (x1 + x3 + B' + C') →
      0 + A * (0 + 0) + 1 * (0 + 0 + B + C) = 0 + A' * (0 + 0) + 1 * (0 + 0 + B' + C') →
        x1 + x2 = (A + A') * (x1 + x3) := by
  decide

theorem Sset_injective {p p' : Param} (hS : Sset p = Sset p') : p = p' := by
  have hind : ind p = ind p' := by
    funext v
    rw [ind, ind, hS]
  -- the row
  have hQ : ∀ z, (row p).isQ z ↔ (row p').isQ z := by
    intro z
    rw [isQ_iff_full p, isQ_iff_full p', hind]
  have hq1 : p.1 = p'.1 := row_eq_of_isQ hQ
  have hrow : row p' = row p := by simp only [row, hq1]
  have hH : ∀ (t : Fin 3) z, (row p).inH t z → (row p').inH t z := fun t z h => hrow ▸ h
  obtain ⟨⟨z1, a1, b1⟩, ⟨z2, a2, b2⟩⟩ := (rok p).2.2.1
  set k0 := pv (rr p) with hk0
  obtain ⟨j1, hj1⟩ := exists_diff p (s := 0) (t := 1) (by decide)
  obtain ⟨j2, hj2⟩ := exists_diff p (s := 0) (t := 2) (by decide)
  -- fibres on `H₀ ∩ H₁` and `H₀ ∩ H₂` under both parameters
  have F1 := fib01 p a1 b1
  have F1' : ∀ y, ind p (y, z1) = _ := fun y => (congrFun hind (y, z1)).trans
    (fib01 p' (hH 0 z1 a1) (hH 1 z1 b1) y)
  have F2 := fib02 p a2 b2
  have F2' : ∀ y, ind p (y, z2) = _ := fun y => (congrFun hind (y, z2)).trans
    (fib02 p' (hH 0 z2 a2) (hH 2 z2 b2) y)
  -- the wedges agree
  have W1 : ∀ i j, rr p i * mu p 0 1 j + rr p j * mu p 0 1 i =
      rr p' i * mu p' 0 1 j + rr p' j * mu p' 0 1 i := fun i j =>
    (wedge_read p (f := fun y => ind p (y, z1)) F1 i j).symm.trans
      (wedge_read p' (f := fun y => ind p (y, z1)) F1' i j)
  have W2 : ∀ i j, rr p i * mu p 0 2 j + rr p j * mu p 0 2 i =
      rr p' i * mu p' 0 2 j + rr p' j * mu p' 0 2 i := fun i j =>
    (wedge_read p (f := fun y => ind p (y, z2)) F2 i j).symm.trans
      (wedge_read p' (f := fun y => ind p (y, z2)) F2' i j)
  -- `r`
  have hr0 : rr p k0 = 1 := rr_pv p
  have w1 := wedge hr0 (mu_pv p 0 1) hj1 W1
  have w2 := wedge hr0 (mu_pv p 0 2) hj2 W2
  have hbb := mul_vec_eq (b := rr p' j1 + rr p j1 * rr p' k0) (b' := rr p' j2 + rr p j2 * rr p' k0)
    hj1 hj2 (mu_ne p (s := 0) (t := 1) (u := 2) (by decide)) (fun k => by
      have := (w1 k).symm.trans (w2 k)
      linear_combination this)
  have hr' : ∀ k, rr p' k = rr p' k0 * rr p k := fun k => by
    rw [w1 k, hbb.1, zero_mul, add_zero]
  have ha : rr p' k0 = 1 := by
    apply zmod2_eq_one
    intro h0
    apply rr_ne p'
    funext k
    rw [hr' k, h0, zero_mul]
    rfl
  have hr : rr p' = rr p := funext fun k => by rw [hr' k, ha, one_mul]
  have hpv : pv (rr p') = k0 := by rw [hr]
  -- the differences `μ`
  have hmu : ∀ {t : Fin 3} {j : Fin 11}, t ≠ 0 → mu p 0 t j = 1 →
      (∀ i j, rr p i * mu p 0 t j + rr p j * mu p 0 t i =
        rr p' i * mu p' 0 t j + rr p' j * mu p' 0 t i) → mu p' 0 t = mu p 0 t := by
    intro t j ht hj W
    have W' : ∀ i j, rr p i * mu p 0 t j + rr p j * mu p 0 t i =
        mu p' 0 t i * rr p' j + mu p' 0 t j * rr p' i := fun i j => by
      rw [W i j]; ring
    have w := wedge hr0 (mu_pv p 0 t) hj W'
    have h0 : mu p' 0 t k0 = 0 := by rw [← hpv]; exact mu_pv p' 0 t
    have hc : mu p' 0 t j = 1 := by
      apply zmod2_eq_one
      intro hz
      apply mu_ne p' (s := 0) (t := 0) (u := t) (Ne.symm ht)
      funext k
      rw [w k, h0, hz]
      simp only [mu, CharTwo.add_self_eq_zero]
      ring
    funext k
    rw [w k, h0, hc]
    ring
  have hmu1 := hmu (t := 1) (by decide) hj1 W1
  have hmu2 := hmu (t := 2) (by decide) hj2 W2
  -- `m₀`
  have hm0 : ∀ {t : Fin 3} {z : Z4} {A B C A' B' C' : ZMod 2},
      mu p' 0 t = mu p 0 t →
      (∀ y, ind p (y, z) = F (ydot (rr p) y) A (ydot (mm p 0) y) B (ydot (mm p t) y) C) →
      (∀ y, ind p (y, z) = F (ydot (rr p') y) A' (ydot (mm p' 0) y) B' (ydot (mm p' t) y) C') →
      ∀ i, mm p 0 i + mm p' 0 i = (A + A') * mu p 0 t i := by
    intro t z A B C A' B' C' hmut hf hf' i
    have l := (read1 (f := fun y => ind p (y, z)) hf i).symm.trans
      (read1 (f := fun y => ind p (y, z)) hf' i)
    have lk := (read1 (f := fun y => ind p (y, z)) hf k0).symm.trans
      (read1 (f := fun y => ind p (y, z)) hf' k0)
    have e1 : mm p' 0 i + mm p' t i = mm p 0 i + mm p t i := congrFun hmut i
    have e2 : mm p' 0 k0 = 0 := by rw [← hpv]; exact mm_pv p' 0
    have e3 : mm p' t k0 = 0 := by rw [← hpv]; exact mm_pv p' t
    rw [e1, hr] at l
    rw [e2, e3, hr, mm_pv, mm_pv, hr0] at lk
    exact m0_core _ _ _ _ _ _ _ _ _ _ l lk
  have d1 := hm0 hmu1 F1 F1'
  have d2 := hm0 hmu2 F2 F2'
  have hcc := mul_vec_eq hj1 hj2 (mu_ne p (s := 0) (t := 1) (u := 2) (by decide))
    (fun k => (d1 k).symm.trans (d2 k))
  have hm0' : mm p' 0 = mm p 0 := funext fun i => by
    have := d1 i
    rw [hcc.1, zero_mul] at this
    linear_combination this - mm p 0 i * two_z2
  have hmt : ∀ t : Fin 3, t ≠ 0 → mu p' 0 t = mu p 0 t → mm p' t = mm p t := by
    intro t _ h
    funext i
    have := congrFun h i
    simp only [mu, hm0'] at this
    linear_combination this
  have hmm : ∀ t, mm p' t = mm p t := by
    intro t
    fin_cases t
    · exact hm0'
    · exact hmt 1 (by decide) hmu1
    · exact hmt 2 (by decide) hmu2
  -- values of `ρ` and `ν` on the overlaps
  have vals : ∀ {s t : Fin 3} {z : Z4}, s ≠ t →
      (∀ y, ind p (y, z) = F (ydot (rr p) y) (LabelFamily.rho p s z) (ydot (mm p s) y) (nu p s z)
        (ydot (mm p t) y) (nu p t z)) →
      (∀ y, ind p (y, z) = F (ydot (rr p') y) (LabelFamily.rho p' s z) (ydot (mm p' s) y)
        (nu p' s z) (ydot (mm p' t) y) (nu p' t z)) →
      LabelFamily.rho p s z = LabelFamily.rho p' s z ∧ nu p s z = nu p' s z ∧
        nu p t z = nu p' t z := by
    intro s t z hst hf hf'
    rw [hr, hmm s, hmm t] at hf'
    obtain ⟨j, hj⟩ := exists_diff p hst
    exact decode_vals hf hf' hr0 (mm_pv p s) (mm_pv p t) hj
  have V01 : ∀ {z}, (row p).inH 0 z → (row p).inH 1 z → _ := fun {z} h0 h1 =>
    vals (s := 0) (t := 1) (z := z) (by decide) (fib01 p h0 h1)
      (fun y => (congrFun hind (y, z)).trans (fib01 p' (hH 0 z h0) (hH 1 z h1) y))
  have V02 : ∀ {z}, (row p).inH 0 z → (row p).inH 2 z → _ := fun {z} h0 h2 =>
    vals (s := 0) (t := 2) (z := z) (by decide) (fib02 p h0 h2)
      (fun y => (congrFun hind (y, z)).trans (fib02 p' (hH 0 z h0) (hH 2 z h2) y))
  have V12 : ∀ {z}, (row p).inH 1 z → (row p).inH 2 z → _ := fun {z} h1 h2 =>
    vals (s := 1) (t := 2) (z := z) (by decide) (fib12 p h1 h2)
      (fun y => (congrFun hind (y, z)).trans (fib12 p' (hH 1 z h1) (hH 2 z h2) y))
  have cover : ∀ {t : Fin 3} {z : Z4}, (row p).inH t z →
      ((row p).inH 0 z ∧ (row p).inH 1 z) ∨ ((row p).inH 0 z ∧ (row p).inH 2 z) ∨
        ((row p).inH 1 z ∧ (row p).inH 2 z) := by
    intro t z ht
    have hQ' : ¬(row p).isQ z := fun hq => qout' p hq t ht
    rcases shape p z hQ' with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · fin_cases t
      · exact absurd ht a
      · exact absurd ht b
      · exact absurd ht c
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr (Or.inl ⟨a, c⟩)
    · exact Or.inr (Or.inr ⟨b, c⟩)
  have hnu : ∀ (t : Fin 3) z, (row p).inH t z → nu p t z = nu p' t z := by
    intro t z ht
    rcases cover ht with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
    · fin_cases t
      · exact (V01 h0 h1).2.1
      · exact (V01 h0 h1).2.2
      · exact absurd ht (not_inH2_of_01 p h0 h1)
    · fin_cases t
      · exact (V02 h0 h2).2.1
      · exact absurd ht (not_inH1_of_02 p h0 h2)
      · exact (V02 h0 h2).2.2
    · fin_cases t
      · exact absurd ht (not_inH0_of_12 p h1 h2)
      · exact (V12 h1 h2).2.1
      · exact (V12 h1 h2).2.2
  have hrho : ∀ (t : Fin 3) z, (row p).inH t z → LabelFamily.rho p t z = LabelFamily.rho p' t z := by
    intro t z ht
    rcases cover ht with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
    · fin_cases t
      · exact (V01 h0 h1).1
      · show LabelFamily.rho p 1 z = LabelFamily.rho p' 1 z
        rw [rho_01 p h0, rho_01 p' (hH 0 z h0), (V01 h0 h1).1]
      · exact absurd ht (not_inH2_of_01 p h0 h1)
    · fin_cases t
      · exact (V02 h0 h2).1
      · exact absurd ht (not_inH1_of_02 p h0 h2)
      · show LabelFamily.rho p 2 z = LabelFamily.rho p' 2 z
        rw [rho_02 p h0, rho_02 p' (hH 0 z h0), (V02 h0 h2).1]
    · fin_cases t
      · exact absurd ht (not_inH0_of_12 p h1 h2)
      · exact (V12 h1 h2).1
      · show LabelFamily.rho p 2 z = LabelFamily.rho p' 2 z
        linear_combination -rho_12 p (zdot0_of_12 p h1 h2) +
          rho_12 p' (zdot0_of_12 p' (hH 1 z h1) (hH 2 z h2)) + (V12 h1 h2).1
  -- read the parameters
  have hsig : ∀ t, sig p' t = sig p t := fun t => by simp only [sig, hrow]
  have hjr : jr p = jr p' ∧ aa p = aa p' := by
    have hc : Clash (row p).s0 (kap (row p) 0) (jr p) (jr p') (aa p) (aa p') := by
      intro z hz
      have h := hrho 0 z hz
      have h' : aa p + (zdot (betaOf (row p).s0 (jr p)) z + 0 * zdot (row p).s0 z) =
          aa p' + (zdot (betaOf (row p').s0 (jr p')) z + 0 * zdot (row p').s0 z) := h
      rw [hrow] at h'
      simpa using h'
    obtain ⟨h1, h2⟩ := beta_inj (sok p 0) (jr p).isLt (jr p').isLt hc
    exact ⟨Fin.ext h1, h2⟩
  have hbeta : LabelFamily.beta p' = LabelFamily.beta p := by
    simp only [LabelFamily.beta, hrow, hjr.1]
  have hfac : ∀ z, (row p).inH 1 z → (ee p + ee p') * (1 + zdot (row p).s0 z) = 0 := by
    intro z hz
    have h := hrho 1 z hz
    rw [rho_one_formula p z, rho_one_formula p' z, hbeta, hrow, hjr.2] at h
    have h' : ee p * (1 + zdot (row p).s0 z) = ee p' * (1 + zdot (row p).s0 z) :=
      add_left_cancel h
    calc (ee p + ee p') * (1 + zdot (row p).s0 z)
        = ee p * (1 + zdot (row p).s0 z) + ee p' * (1 + zdot (row p).s0 z) := add_mul _ _ _
      _ = ee p' * (1 + zdot (row p).s0 z) + ee p' * (1 + zdot (row p).s0 z) := by rw [h']
      _ = 0 := CharTwo.add_self_eq_zero _
  have hee : ee p = ee p' := by
    by_cases hk : kap (row p) 1 = 0
    · have hz : (row p).inH 1 0 := (inH_zero_iff p 1).mpr hk
      have h := hfac 0 hz
      rw [zdot_zero, add_zero, mul_one] at h
      have h' : ee p = -ee p' := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at h'
    · have hk1 : kap (row p) 1 = 1 := by
        rcases zmod2_cases (kap (row p) 1) with h | h
        · exact absurd h hk
        · exact h
      obtain ⟨z, hz1, hz0⟩ := zdot_pair (s := (row p).s1) (s' := (row p).s0)
        (sok p 1) (sok p 0) (Ne.symm (sig_ne01 p)) (kap (row p) 1) 0
      have hz : (row p).inH 1 z := by
        simp only [QRow.inH, QRow.s, Matrix.cons_val_one, Matrix.cons_val_zero]
        simpa [hk1] using hz1
      have h := hfac z hz
      rw [hz0, add_zero, mul_one] at h
      have h' : ee p = -ee p' := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at h'
  have hjn : ∀ t, jn p t = jn p' t ∧ bC p t = bC p' t := by
    intro t
    have hc : Clash (sig p t) (kap (row p) t) (jn p t) (jn p' t) (bC p t) (bC p' t) := by
      intro z hz
      have h := hnu t z hz
      have h' : bC p t + zdot (betaOf (sig p t) (jn p t)) z =
          bC p' t + zdot (betaOf (sig p' t) (jn p' t)) z := h
      rw [hsig] at h'
      exact h'
    obtain ⟨h1, h2⟩ := beta_inj (sok p t) (jn p t).isLt (jn p' t).isLt hc
    exact ⟨Fin.ext h1, h2⟩
  have he0 : e0 p = e0 p' := (hjn 0).2
  have he1 : e1 p = e1 p' := by
    have h1 : (if aa p + ee p = 1 then 1 else e1 p) = (if aa p' + ee p' = 1 then 1 else e1 p') :=
      (hjn 1).2
    have h2 : (if aa p + ee p = 1 then e1 p else 1) = (if aa p' + ee p' = 1 then e1 p' else 1) :=
      (hjn 2).2
    rw [hjr.2, hee] at h1 h2
    by_cases hc : aa p' + ee p' = 1
    · rw [if_pos hc, if_pos hc] at h2; exact h2
    · rw [if_neg hc, if_neg hc] at h1; exact h1
  -- assemble
  have hemb : p.2.2.2.1 = p'.2.2.2.1 := by
    ext t : 1
    apply Subtype.ext
    have := hmm t
    simp only [mm, hr] at this
    exact (Fin.insertNth_right_injective _ this).symm
  obtain ⟨q, ⟨j, a, b⟩, r, m, n, c0, c1⟩ := p
  obtain ⟨q', ⟨j', a', b'⟩, r', m', n', c0', c1'⟩ := p'
  simp only [jr, aa, ee, e0, e1, rr] at hq1 hjr hee he0 he1 hr hemb
  have hn : n = n' := funext fun t => (hjn t).1
  have hr2 : r = r' := Subtype.ext hr.symm
  subst hq1 hr2 hemb hn he0 he1 hee
  rw [hjr.1, hjr.2]

theorem Cp_injective {p p' : Param} (h : Cp p = Cp p') : p = p' :=
  Sset_injective (Sset_eq_of_Cp h)

end ProximityPrize.SubmissionBinaryUpper.LabelDecode
