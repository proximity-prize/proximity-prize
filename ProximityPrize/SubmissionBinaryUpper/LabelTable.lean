/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.LabelSpace

/-!
# The configuration table of the label family

The top part `z ∈ 𝔽₂^4` of a label carries the configuration of a family member:
three reserved points `Q` of an affine plane `P = aff Q`, and three half spaces
`H₀, H₁, H₂` of `𝔽₂^4`, the complements of `P` together with one of the other three
translates of `P`.  Every `z` either lies in exactly two of them, or in none (the four
points of `P`).  When `0 ∉ P` the point `0` lies in `H₁ ∩ H₂`; when `0 ∈ P` it lies in no
half space, so the label `0` is avoided for free.

`H_t = {z : s_t · z = κ_t}` where `κ_t = 1 + s_t · q₁` is normalized by the first point of
`Q`.  Row `i` of `qrows` lists `Q = {q₁, q₂, q₃}` and `s₀, s₁, s₂`; all 455 rows are checked by
`decide`.  The first point `q₁` is chosen so that `κ₀ = 1`: when `0 ∉ aff Q` this gives
`κ = (1, 0, 0)` and `0 ∈ H₁ ∩ H₂`, and when `0 ∈ aff Q` it gives `κ = (1, 1, 1)` and `0` lies in
no half space at all.
-/

namespace ProximityPrize.SubmissionBinaryUpper.LabelTable

open ProximityPrize.SubmissionBinaryUpper.FlatPoly
open ProximityPrize.SubmissionBinaryUpper.LabelSpace

/-- The linear form on `𝔽₂^4` with coefficient bits `s`. -/
def zdot (s : ℕ) (z : Z4) : ZMod 2 :=
  bit s 0 * z.1 + bit s 1 * z.2.1 + bit s 2 * z.2.2.1 + bit s 3 * z.2.2.2

/-- The vector of the four low bits of `n`. -/
def zv (n : ℕ) : Z4 := (bit n 0, bit n 1, bit n 2, bit n 3)

theorem zdot_add (s : ℕ) (z w : Z4) : zdot s (z + w) = zdot s z + zdot s w := by
  simp only [zdot, Prod.fst_add, Prod.snd_add]
  ring

theorem zdot_smul (s : ℕ) (c : ZMod 2) (z : Z4) : zdot s (c • z) = c * zdot s z := by
  simp only [zdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem zdot_zero (s : ℕ) : zdot s 0 = 0 := by
  simp [zdot]

structure QRow where
  q1 : ℕ
  q2 : ℕ
  q3 : ℕ
  s0 : ℕ
  s1 : ℕ
  s2 : ℕ

def QRow.s (R : QRow) : Fin 3 → ℕ := ![R.s0, R.s1, R.s2]

/-- The constant of the half space `H_t`, normalized by the first point of `Q`.  Since `s_t` is
constant on `aff Q`, this equals `1 + s_t · q` for every `q ∈ aff Q`. -/
def kap (R : QRow) (t : Fin 3) : ZMod 2 := 1 + zdot (R.s t) (zv R.q1)

def QRow.inH (R : QRow) (t : Fin 3) (z : Z4) : Prop := zdot (R.s t) z = kap R t

def QRow.isQ (R : QRow) (z : Z4) : Prop := z = zv R.q1 ∨ z = zv R.q2 ∨ z = zv R.q3

instance (R : QRow) (t : Fin 3) (z : Z4) : Decidable (R.inH t z) := by
  unfold QRow.inH; infer_instance

instance (R : QRow) (z : Z4) : Decidable (R.isQ z) := by
  unfold QRow.isQ; infer_instance

def qrows0 : List QRow := [
  ⟨1, 2, 3, 4, 12, 8⟩, ⟨1, 2, 4, 8, 15, 7⟩, ⟨1, 3, 4, 8, 13, 5⟩, ⟨2, 3, 4, 8, 14, 6⟩, ⟨1, 2, 5, 8, 11, 3⟩, ⟨1, 3, 5, 8, 9, 1⟩,
  ⟨2, 3, 5, 8, 14, 6⟩, ⟨1, 4, 5, 2, 10, 8⟩, ⟨2, 4, 5, 8, 14, 6⟩, ⟨3, 4, 5, 8, 14, 6⟩, ⟨1, 2, 6, 8, 11, 3⟩, ⟨1, 3, 6, 8, 13, 5⟩,
  ⟨2, 3, 6, 8, 10, 2⟩, ⟨1, 4, 6, 8, 13, 5⟩, ⟨2, 4, 6, 1, 9, 8⟩, ⟨3, 4, 6, 8, 13, 5⟩, ⟨1, 5, 6, 8, 11, 3⟩, ⟨2, 5, 6, 8, 11, 3⟩,
  ⟨3, 5, 6, 7, 15, 8⟩, ⟨4, 5, 6, 8, 12, 4⟩, ⟨1, 2, 7, 8, 15, 7⟩, ⟨1, 3, 7, 8, 9, 1⟩, ⟨2, 3, 7, 8, 10, 2⟩, ⟨1, 4, 7, 8, 15, 7⟩,
  ⟨2, 4, 7, 8, 15, 7⟩, ⟨3, 4, 7, 3, 11, 8⟩, ⟨1, 5, 7, 8, 9, 1⟩, ⟨2, 5, 7, 5, 13, 8⟩, ⟨3, 5, 7, 8, 9, 1⟩, ⟨4, 5, 7, 8, 12, 4⟩,
  ⟨1, 6, 7, 6, 14, 8⟩, ⟨2, 6, 7, 8, 10, 2⟩, ⟨3, 6, 7, 8, 10, 2⟩, ⟨4, 6, 7, 8, 12, 4⟩, ⟨5, 6, 7, 8, 12, 4⟩, ⟨1, 2, 8, 4, 15, 11⟩,
  ⟨1, 3, 8, 4, 13, 9⟩, ⟨2, 3, 8, 4, 14, 10⟩, ⟨1, 4, 8, 2, 15, 13⟩, ⟨2, 4, 8, 1, 15, 14⟩, ⟨3, 4, 8, 3, 13, 14⟩, ⟨1, 5, 8, 2, 11, 9⟩,
  ⟨2, 5, 8, 5, 11, 14⟩, ⟨3, 5, 8, 7, 9, 14⟩, ⟨4, 5, 8, 2, 14, 12⟩, ⟨1, 6, 8, 6, 11, 13⟩, ⟨2, 6, 8, 1, 11, 10⟩, ⟨3, 6, 8, 7, 13, 10⟩,
  ⟨4, 6, 8, 1, 13, 12⟩, ⟨5, 6, 8, 7, 11, 12⟩, ⟨1, 7, 8, 6, 15, 9⟩, ⟨2, 7, 8, 5, 15, 10⟩, ⟨3, 7, 8, 3, 9, 10⟩, ⟨4, 7, 8, 3, 15, 12⟩,
  ⟨5, 7, 8, 5, 9, 12⟩, ⟨6, 7, 8, 6, 10, 12⟩, ⟨1, 2, 9, 4, 7, 3⟩, ⟨1, 3, 9, 4, 5, 1⟩, ⟨2, 3, 9, 4, 14, 10⟩, ⟨1, 4, 9, 2, 7, 5⟩,
  ⟨2, 4, 9, 9, 7, 14⟩, ⟨3, 4, 9, 11, 5, 14⟩, ⟨1, 5, 9, 2, 3, 1⟩, ⟨2, 5, 9, 13, 3, 14⟩, ⟨3, 5, 9, 15, 1, 14⟩
]

def qrows1 : List QRow := [
  ⟨4, 5, 9, 2, 14, 12⟩, ⟨1, 6, 9, 6, 3, 5⟩, ⟨2, 6, 9, 9, 3, 10⟩, ⟨3, 6, 9, 15, 5, 10⟩, ⟨4, 6, 9, 9, 5, 12⟩, ⟨5, 6, 9, 15, 3, 12⟩,
  ⟨1, 7, 9, 6, 7, 1⟩, ⟨2, 7, 9, 13, 7, 10⟩, ⟨3, 7, 9, 11, 1, 10⟩, ⟨4, 7, 9, 11, 7, 12⟩, ⟨5, 7, 9, 13, 1, 12⟩, ⟨6, 7, 9, 6, 10, 12⟩,
  ⟨1, 8, 9, 2, 6, 4⟩, ⟨2, 8, 9, 4, 14, 10⟩, ⟨3, 8, 9, 4, 14, 10⟩, ⟨4, 8, 9, 2, 14, 12⟩, ⟨5, 8, 9, 2, 14, 12⟩, ⟨6, 8, 9, 6, 10, 12⟩,
  ⟨7, 8, 9, 6, 10, 12⟩, ⟨1, 2, 10, 4, 7, 3⟩, ⟨1, 3, 10, 4, 13, 9⟩, ⟨2, 3, 10, 4, 6, 2⟩, ⟨1, 4, 10, 10, 7, 13⟩, ⟨2, 4, 10, 1, 7, 6⟩,
  ⟨3, 4, 10, 11, 13, 6⟩, ⟨1, 5, 10, 10, 3, 9⟩, ⟨2, 5, 10, 5, 3, 6⟩, ⟨3, 5, 10, 15, 9, 6⟩, ⟨4, 5, 10, 10, 6, 12⟩, ⟨1, 6, 10, 14, 3, 13⟩,
  ⟨2, 6, 10, 1, 3, 2⟩, ⟨3, 6, 10, 15, 13, 2⟩, ⟨4, 6, 10, 1, 13, 12⟩, ⟨5, 6, 10, 15, 3, 12⟩, ⟨1, 7, 10, 14, 7, 9⟩, ⟨2, 7, 10, 5, 7, 2⟩,
  ⟨3, 7, 10, 11, 9, 2⟩, ⟨4, 7, 10, 11, 7, 12⟩, ⟨5, 7, 10, 5, 9, 12⟩, ⟨6, 7, 10, 14, 2, 12⟩, ⟨1, 8, 10, 4, 13, 9⟩, ⟨2, 8, 10, 1, 5, 4⟩,
  ⟨3, 8, 10, 4, 13, 9⟩, ⟨4, 8, 10, 1, 13, 12⟩, ⟨5, 8, 10, 5, 9, 12⟩, ⟨6, 8, 10, 1, 13, 12⟩, ⟨7, 8, 10, 5, 9, 12⟩, ⟨1, 9, 10, 4, 7, 3⟩,
  ⟨2, 9, 10, 4, 7, 3⟩, ⟨3, 9, 10, 4, 15, 11⟩, ⟨4, 9, 10, 11, 7, 12⟩, ⟨5, 9, 10, 15, 3, 12⟩, ⟨6, 9, 10, 15, 3, 12⟩, ⟨7, 9, 10, 11, 7, 12⟩,
  ⟨8, 9, 10, 4, 12, 8⟩, ⟨1, 2, 11, 4, 15, 11⟩, ⟨1, 3, 11, 4, 5, 1⟩, ⟨2, 3, 11, 4, 6, 2⟩, ⟨1, 4, 11, 10, 15, 5⟩, ⟨2, 4, 11, 9, 15, 6⟩,
  ⟨3, 4, 11, 3, 5, 6⟩, ⟨1, 5, 11, 10, 11, 1⟩, ⟨2, 5, 11, 13, 11, 6⟩, ⟨3, 5, 11, 7, 1, 6⟩, ⟨4, 5, 11, 10, 6, 12⟩
]

def qrows2 : List QRow := [
  ⟨1, 6, 11, 14, 11, 5⟩, ⟨2, 6, 11, 9, 11, 2⟩, ⟨3, 6, 11, 7, 5, 2⟩, ⟨4, 6, 11, 9, 5, 12⟩, ⟨5, 6, 11, 7, 11, 12⟩, ⟨1, 7, 11, 14, 15, 1⟩,
  ⟨2, 7, 11, 13, 15, 2⟩, ⟨3, 7, 11, 3, 1, 2⟩, ⟨4, 7, 11, 3, 15, 12⟩, ⟨5, 7, 11, 13, 1, 12⟩, ⟨6, 7, 11, 14, 2, 12⟩, ⟨1, 8, 11, 4, 15, 11⟩,
  ⟨2, 8, 11, 4, 15, 11⟩, ⟨3, 8, 11, 3, 7, 4⟩, ⟨4, 8, 11, 3, 15, 12⟩, ⟨5, 8, 11, 7, 11, 12⟩, ⟨6, 8, 11, 7, 11, 12⟩, ⟨7, 8, 11, 3, 15, 12⟩,
  ⟨1, 9, 11, 4, 5, 1⟩, ⟨2, 9, 11, 4, 13, 9⟩, ⟨3, 9, 11, 4, 5, 1⟩, ⟨4, 9, 11, 9, 5, 12⟩, ⟨5, 9, 11, 13, 1, 12⟩, ⟨6, 9, 11, 9, 5, 12⟩,
  ⟨7, 9, 11, 13, 1, 12⟩, ⟨8, 9, 11, 4, 12, 8⟩, ⟨1, 10, 11, 4, 14, 10⟩, ⟨2, 10, 11, 4, 6, 2⟩, ⟨3, 10, 11, 4, 6, 2⟩, ⟨4, 10, 11, 10, 6, 12⟩,
  ⟨5, 10, 11, 10, 6, 12⟩, ⟨6, 10, 11, 14, 2, 12⟩, ⟨7, 10, 11, 14, 2, 12⟩, ⟨8, 10, 11, 4, 12, 8⟩, ⟨9, 10, 11, 4, 12, 8⟩, ⟨1, 2, 12, 12, 7, 11⟩,
  ⟨1, 3, 12, 12, 5, 9⟩, ⟨2, 3, 12, 12, 6, 10⟩, ⟨1, 4, 12, 2, 7, 5⟩, ⟨2, 4, 12, 1, 7, 6⟩, ⟨3, 4, 12, 3, 5, 6⟩, ⟨1, 5, 12, 2, 11, 9⟩,
  ⟨2, 5, 12, 13, 11, 6⟩, ⟨3, 5, 12, 15, 9, 6⟩, ⟨4, 5, 12, 2, 6, 4⟩, ⟨1, 6, 12, 14, 11, 5⟩, ⟨2, 6, 12, 1, 11, 10⟩, ⟨3, 6, 12, 15, 5, 10⟩,
  ⟨4, 6, 12, 1, 5, 4⟩, ⟨5, 6, 12, 15, 11, 4⟩, ⟨1, 7, 12, 14, 7, 9⟩, ⟨2, 7, 12, 13, 7, 10⟩, ⟨3, 7, 12, 3, 9, 10⟩, ⟨4, 7, 12, 3, 7, 4⟩,
  ⟨5, 7, 12, 13, 9, 4⟩, ⟨6, 7, 12, 14, 10, 4⟩, ⟨1, 8, 12, 2, 11, 9⟩, ⟨2, 8, 12, 1, 11, 10⟩, ⟨3, 8, 12, 3, 9, 10⟩, ⟨4, 8, 12, 1, 3, 2⟩,
  ⟨5, 8, 12, 2, 11, 9⟩, ⟨6, 8, 12, 1, 11, 10⟩, ⟨7, 8, 12, 3, 9, 10⟩, ⟨1, 9, 12, 2, 7, 5⟩, ⟨2, 9, 12, 13, 7, 10⟩
]

def qrows3 : List QRow := [
  ⟨3, 9, 12, 15, 5, 10⟩, ⟨4, 9, 12, 2, 7, 5⟩, ⟨5, 9, 12, 2, 15, 13⟩, ⟨6, 9, 12, 15, 5, 10⟩, ⟨7, 9, 12, 13, 7, 10⟩, ⟨8, 9, 12, 2, 10, 8⟩,
  ⟨1, 10, 12, 14, 7, 9⟩, ⟨2, 10, 12, 1, 7, 6⟩, ⟨3, 10, 12, 15, 9, 6⟩, ⟨4, 10, 12, 1, 7, 6⟩, ⟨5, 10, 12, 15, 9, 6⟩, ⟨6, 10, 12, 1, 15, 14⟩,
  ⟨7, 10, 12, 14, 7, 9⟩, ⟨8, 10, 12, 1, 9, 8⟩, ⟨9, 10, 12, 15, 7, 8⟩, ⟨1, 11, 12, 14, 11, 5⟩, ⟨2, 11, 12, 13, 11, 6⟩, ⟨3, 11, 12, 3, 5, 6⟩,
  ⟨4, 11, 12, 3, 5, 6⟩, ⟨5, 11, 12, 13, 11, 6⟩, ⟨6, 11, 12, 14, 11, 5⟩, ⟨7, 11, 12, 3, 14, 13⟩, ⟨8, 11, 12, 3, 11, 8⟩, ⟨9, 11, 12, 13, 5, 8⟩,
  ⟨10, 11, 12, 14, 6, 8⟩, ⟨1, 2, 13, 12, 15, 3⟩, ⟨1, 3, 13, 12, 13, 1⟩, ⟨2, 3, 13, 12, 6, 10⟩, ⟨1, 4, 13, 2, 15, 13⟩, ⟨2, 4, 13, 9, 15, 6⟩,
  ⟨3, 4, 13, 11, 13, 6⟩, ⟨1, 5, 13, 2, 3, 1⟩, ⟨2, 5, 13, 5, 3, 6⟩, ⟨3, 5, 13, 7, 1, 6⟩, ⟨4, 5, 13, 2, 6, 4⟩, ⟨1, 6, 13, 14, 3, 13⟩,
  ⟨2, 6, 13, 9, 3, 10⟩, ⟨3, 6, 13, 7, 13, 10⟩, ⟨4, 6, 13, 9, 13, 4⟩, ⟨5, 6, 13, 7, 3, 4⟩, ⟨1, 7, 13, 14, 15, 1⟩, ⟨2, 7, 13, 5, 15, 10⟩,
  ⟨3, 7, 13, 11, 1, 10⟩, ⟨4, 7, 13, 11, 15, 4⟩, ⟨5, 7, 13, 5, 1, 4⟩, ⟨6, 7, 13, 14, 10, 4⟩, ⟨1, 8, 13, 2, 15, 13⟩, ⟨2, 8, 13, 5, 15, 10⟩,
  ⟨3, 8, 13, 7, 13, 10⟩, ⟨4, 8, 13, 2, 15, 13⟩, ⟨5, 8, 13, 2, 7, 5⟩, ⟨6, 8, 13, 7, 13, 10⟩, ⟨7, 8, 13, 5, 15, 10⟩, ⟨1, 9, 13, 2, 3, 1⟩,
  ⟨2, 9, 13, 9, 3, 10⟩, ⟨3, 9, 13, 11, 1, 10⟩, ⟨4, 9, 13, 2, 11, 9⟩, ⟨5, 9, 13, 2, 3, 1⟩, ⟨6, 9, 13, 9, 3, 10⟩, ⟨7, 9, 13, 11, 1, 10⟩,
  ⟨8, 9, 13, 2, 10, 8⟩, ⟨1, 10, 13, 14, 3, 13⟩, ⟨2, 10, 13, 5, 3, 6⟩, ⟨3, 10, 13, 11, 13, 6⟩, ⟨4, 10, 13, 11, 13, 6⟩
]

def qrows4 : List QRow := [
  ⟨5, 10, 13, 5, 3, 6⟩, ⟨6, 10, 13, 14, 3, 13⟩, ⟨7, 10, 13, 5, 14, 11⟩, ⟨8, 10, 13, 5, 13, 8⟩, ⟨9, 10, 13, 11, 3, 8⟩, ⟨1, 11, 13, 14, 15, 1⟩,
  ⟨2, 11, 13, 9, 15, 6⟩, ⟨3, 11, 13, 7, 1, 6⟩, ⟨4, 11, 13, 9, 15, 6⟩, ⟨5, 11, 13, 7, 1, 6⟩, ⟨6, 11, 13, 7, 14, 9⟩, ⟨7, 11, 13, 14, 15, 1⟩,
  ⟨8, 11, 13, 7, 15, 8⟩, ⟨9, 11, 13, 9, 1, 8⟩, ⟨10, 11, 13, 14, 6, 8⟩, ⟨1, 12, 13, 2, 14, 12⟩, ⟨2, 12, 13, 12, 6, 10⟩, ⟨3, 12, 13, 12, 6, 10⟩,
  ⟨4, 12, 13, 2, 6, 4⟩, ⟨5, 12, 13, 2, 6, 4⟩, ⟨6, 12, 13, 14, 10, 4⟩, ⟨7, 12, 13, 14, 10, 4⟩, ⟨8, 12, 13, 2, 10, 8⟩, ⟨9, 12, 13, 2, 10, 8⟩,
  ⟨10, 12, 13, 14, 6, 8⟩, ⟨11, 12, 13, 14, 6, 8⟩, ⟨1, 2, 14, 12, 15, 3⟩, ⟨1, 3, 14, 12, 5, 9⟩, ⟨2, 3, 14, 12, 14, 2⟩, ⟨1, 4, 14, 10, 15, 5⟩,
  ⟨2, 4, 14, 1, 15, 14⟩, ⟨3, 4, 14, 11, 5, 14⟩, ⟨1, 5, 14, 10, 3, 9⟩, ⟨2, 5, 14, 13, 3, 14⟩, ⟨3, 5, 14, 7, 9, 14⟩, ⟨4, 5, 14, 10, 14, 4⟩,
  ⟨1, 6, 14, 6, 3, 5⟩, ⟨2, 6, 14, 1, 3, 2⟩, ⟨3, 6, 14, 7, 5, 2⟩, ⟨4, 6, 14, 1, 5, 4⟩, ⟨5, 6, 14, 7, 3, 4⟩, ⟨1, 7, 14, 6, 15, 9⟩,
  ⟨2, 7, 14, 13, 15, 2⟩, ⟨3, 7, 14, 11, 9, 2⟩, ⟨4, 7, 14, 11, 15, 4⟩, ⟨5, 7, 14, 13, 9, 4⟩, ⟨6, 7, 14, 6, 2, 4⟩, ⟨1, 8, 14, 6, 15, 9⟩,
  ⟨2, 8, 14, 1, 15, 14⟩, ⟨3, 8, 14, 7, 9, 14⟩, ⟨4, 8, 14, 1, 15, 14⟩, ⟨5, 8, 14, 7, 9, 14⟩, ⟨6, 8, 14, 1, 7, 6⟩, ⟨7, 8, 14, 6, 15, 9⟩,
  ⟨1, 9, 14, 6, 3, 5⟩, ⟨2, 9, 14, 13, 3, 14⟩, ⟨3, 9, 14, 11, 5, 14⟩, ⟨4, 9, 14, 11, 5, 14⟩, ⟨5, 9, 14, 13, 3, 14⟩, ⟨6, 9, 14, 6, 3, 5⟩,
  ⟨7, 9, 14, 6, 13, 11⟩, ⟨8, 9, 14, 6, 14, 8⟩, ⟨1, 10, 14, 10, 3, 9⟩, ⟨2, 10, 14, 1, 3, 2⟩, ⟨3, 10, 14, 11, 9, 2⟩
]

def qrows5 : List QRow := [
  ⟨4, 10, 14, 1, 11, 10⟩, ⟨5, 10, 14, 10, 3, 9⟩, ⟨6, 10, 14, 1, 3, 2⟩, ⟨7, 10, 14, 11, 9, 2⟩, ⟨8, 10, 14, 1, 9, 8⟩, ⟨9, 10, 14, 11, 3, 8⟩,
  ⟨1, 11, 14, 10, 15, 5⟩, ⟨2, 11, 14, 13, 15, 2⟩, ⟨3, 11, 14, 7, 5, 2⟩, ⟨4, 11, 14, 10, 15, 5⟩, ⟨5, 11, 14, 7, 13, 10⟩, ⟨6, 11, 14, 7, 5, 2⟩,
  ⟨7, 11, 14, 13, 15, 2⟩, ⟨8, 11, 14, 7, 15, 8⟩, ⟨9, 11, 14, 13, 5, 8⟩, ⟨10, 11, 14, 10, 2, 8⟩, ⟨1, 12, 14, 12, 5, 9⟩, ⟨2, 12, 14, 1, 13, 12⟩,
  ⟨3, 12, 14, 12, 5, 9⟩, ⟨4, 12, 14, 1, 5, 4⟩, ⟨5, 12, 14, 13, 9, 4⟩, ⟨6, 12, 14, 1, 5, 4⟩, ⟨7, 12, 14, 13, 9, 4⟩, ⟨8, 12, 14, 1, 9, 8⟩,
  ⟨9, 12, 14, 13, 5, 8⟩, ⟨10, 12, 14, 1, 9, 8⟩, ⟨11, 12, 14, 13, 5, 8⟩, ⟨1, 13, 14, 12, 15, 3⟩, ⟨2, 13, 14, 12, 15, 3⟩, ⟨3, 13, 14, 7, 12, 11⟩,
  ⟨4, 13, 14, 11, 15, 4⟩, ⟨5, 13, 14, 7, 3, 4⟩, ⟨6, 13, 14, 7, 3, 4⟩, ⟨7, 13, 14, 11, 15, 4⟩, ⟨8, 13, 14, 7, 15, 8⟩, ⟨9, 13, 14, 11, 3, 8⟩,
  ⟨10, 13, 14, 11, 3, 8⟩, ⟨11, 13, 14, 7, 15, 8⟩, ⟨12, 13, 14, 12, 4, 8⟩, ⟨1, 2, 15, 12, 7, 11⟩, ⟨1, 3, 15, 12, 13, 1⟩, ⟨2, 3, 15, 12, 14, 2⟩,
  ⟨1, 4, 15, 10, 7, 13⟩, ⟨2, 4, 15, 9, 7, 14⟩, ⟨3, 4, 15, 3, 13, 14⟩, ⟨1, 5, 15, 10, 11, 1⟩, ⟨2, 5, 15, 5, 11, 14⟩, ⟨3, 5, 15, 15, 1, 14⟩,
  ⟨4, 5, 15, 10, 14, 4⟩, ⟨1, 6, 15, 6, 11, 13⟩, ⟨2, 6, 15, 9, 11, 2⟩, ⟨3, 6, 15, 15, 13, 2⟩, ⟨4, 6, 15, 9, 13, 4⟩, ⟨5, 6, 15, 15, 11, 4⟩,
  ⟨1, 7, 15, 6, 7, 1⟩, ⟨2, 7, 15, 5, 7, 2⟩, ⟨3, 7, 15, 3, 1, 2⟩, ⟨4, 7, 15, 3, 7, 4⟩, ⟨5, 7, 15, 5, 1, 4⟩, ⟨6, 7, 15, 6, 2, 4⟩,
  ⟨1, 8, 15, 6, 11, 13⟩, ⟨2, 8, 15, 5, 11, 14⟩, ⟨3, 8, 15, 3, 13, 14⟩, ⟨4, 8, 15, 3, 13, 14⟩, ⟨5, 8, 15, 5, 11, 14⟩
]

def qrows6 : List QRow := [
  ⟨6, 8, 15, 6, 11, 13⟩, ⟨7, 8, 15, 3, 6, 5⟩, ⟨1, 9, 15, 6, 7, 1⟩, ⟨2, 9, 15, 9, 7, 14⟩, ⟨3, 9, 15, 15, 1, 14⟩, ⟨4, 9, 15, 9, 7, 14⟩,
  ⟨5, 9, 15, 15, 1, 14⟩, ⟨6, 9, 15, 6, 15, 9⟩, ⟨7, 9, 15, 6, 7, 1⟩, ⟨8, 9, 15, 6, 14, 8⟩, ⟨1, 10, 15, 10, 7, 13⟩, ⟨2, 10, 15, 5, 7, 2⟩,
  ⟨3, 10, 15, 15, 13, 2⟩, ⟨4, 10, 15, 10, 7, 13⟩, ⟨5, 10, 15, 5, 15, 10⟩, ⟨6, 10, 15, 15, 13, 2⟩, ⟨7, 10, 15, 5, 7, 2⟩, ⟨8, 10, 15, 5, 13, 8⟩,
  ⟨9, 10, 15, 15, 7, 8⟩, ⟨1, 11, 15, 10, 11, 1⟩, ⟨2, 11, 15, 9, 11, 2⟩, ⟨3, 11, 15, 3, 1, 2⟩, ⟨4, 11, 15, 3, 10, 9⟩, ⟨5, 11, 15, 10, 11, 1⟩,
  ⟨6, 11, 15, 9, 11, 2⟩, ⟨7, 11, 15, 3, 1, 2⟩, ⟨8, 11, 15, 3, 11, 8⟩, ⟨9, 11, 15, 9, 1, 8⟩, ⟨10, 11, 15, 10, 2, 8⟩, ⟨1, 12, 15, 12, 7, 11⟩,
  ⟨2, 12, 15, 12, 7, 11⟩, ⟨3, 12, 15, 3, 15, 12⟩, ⟨4, 12, 15, 3, 7, 4⟩, ⟨5, 12, 15, 15, 11, 4⟩, ⟨6, 12, 15, 15, 11, 4⟩, ⟨7, 12, 15, 3, 7, 4⟩,
  ⟨8, 12, 15, 3, 11, 8⟩, ⟨9, 12, 15, 15, 7, 8⟩, ⟨10, 12, 15, 15, 7, 8⟩, ⟨11, 12, 15, 3, 11, 8⟩, ⟨1, 13, 15, 12, 13, 1⟩, ⟨2, 13, 15, 5, 12, 9⟩,
  ⟨3, 13, 15, 12, 13, 1⟩, ⟨4, 13, 15, 9, 13, 4⟩, ⟨5, 13, 15, 5, 1, 4⟩, ⟨6, 13, 15, 9, 13, 4⟩, ⟨7, 13, 15, 5, 1, 4⟩, ⟨8, 13, 15, 5, 13, 8⟩,
  ⟨9, 13, 15, 9, 1, 8⟩, ⟨10, 13, 15, 5, 13, 8⟩, ⟨11, 13, 15, 9, 1, 8⟩, ⟨12, 13, 15, 12, 4, 8⟩, ⟨1, 14, 15, 6, 12, 10⟩, ⟨2, 14, 15, 12, 14, 2⟩,
  ⟨3, 14, 15, 12, 14, 2⟩, ⟨4, 14, 15, 10, 14, 4⟩, ⟨5, 14, 15, 10, 14, 4⟩, ⟨6, 14, 15, 6, 2, 4⟩, ⟨7, 14, 15, 6, 2, 4⟩, ⟨8, 14, 15, 6, 14, 8⟩,
  ⟨9, 14, 15, 6, 14, 8⟩, ⟨10, 14, 15, 10, 2, 8⟩, ⟨11, 14, 15, 10, 2, 8⟩, ⟨12, 14, 15, 12, 4, 8⟩, ⟨13, 14, 15, 12, 4, 8⟩
]

def qrows : List QRow := qrows0 ++ qrows1 ++ qrows2 ++ qrows3 ++ qrows4 ++ qrows5 ++ qrows6

theorem qrows_length : qrows.length = 455 := by decide +kernel

def qrow (i : Fin 455) : QRow := qrows.get ⟨i.val, by rw [qrows_length]; exact i.isLt⟩

theorem qrow_mem (i : Fin 455) : qrow i ∈ qrows := List.get_mem _ _

/-- The four shapes of a point outside `Q`: in no half space, or in exactly two. -/
def Shape (R : QRow) (z : Z4) : Prop :=
  (¬R.inH 0 z ∧ ¬R.inH 1 z ∧ ¬R.inH 2 z) ∨ (R.inH 0 z ∧ R.inH 1 z ∧ ¬R.inH 2 z) ∨
    (R.inH 0 z ∧ ¬R.inH 1 z ∧ R.inH 2 z) ∨ (¬R.inH 0 z ∧ R.inH 1 z ∧ R.inH 2 z)

instance (R : QRow) (z : Z4) : Decidable (Shape R z) := by unfold Shape; infer_instance

def QOut (R : QRow) (z : Z4) : Prop := R.isQ z → ¬R.inH 0 z ∧ ¬R.inH 1 z ∧ ¬R.inH 2 z

instance (R : QRow) (z : Z4) : Decidable (QOut R z) := by unfold QOut; infer_instance

def ShapeOut (R : QRow) (z : Z4) : Prop := ¬R.isQ z → Shape R z

instance (R : QRow) (z : Z4) : Decidable (ShapeOut R z) := by unfold ShapeOut; infer_instance

def Meet (R : QRow) (s t : Fin 3) (z : Z4) : Prop := R.inH s z ∧ R.inH t z

instance (R : QRow) (s t : Fin 3) (z : Z4) : Decidable (Meet R s t z) := by
  unfold Meet; infer_instance

def SOK (s : ℕ) : Prop := s ≠ 0 ∧ s < 16

instance (s : ℕ) : Decidable (SOK s) := by unfold SOK; infer_instance

def RowAllZ (R : QRow) : Prop := ∀ z, QOut R z ∧ ShapeOut R z

instance (R : QRow) : Decidable (RowAllZ R) := by unfold RowAllZ; infer_instance

def RowMeet (R : QRow) : Prop := (∃ z, Meet R 0 1 z) ∧ (∃ z, Meet R 0 2 z)

instance (R : QRow) : Decidable (RowMeet R) := by unfold RowMeet; infer_instance

def QCard (R : QRow) : Prop := (Finset.univ.filter R.isQ).card = 3

instance (R : QRow) : Decidable (QCard R) := by unfold QCard; infer_instance

/-- The shape of a row, as used by the family and by the decoding. -/
def RowOK (R : QRow) : Prop :=
  (SOK R.s0 ∧ SOK R.s1 ∧ SOK R.s2) ∧ RowAllZ R ∧ RowMeet R ∧ QCard R ∧
    (kap R 0 = 1) ∧ (∀ z : Z4, zdot (R.s 0) z + zdot (R.s 1) z + zdot (R.s 2) z = 0) ∧
    (R.s0 ≠ R.s1) ∧ ¬ R.isQ 0

instance (R : QRow) : Decidable (RowOK R) := by unfold RowOK; infer_instance

theorem rows_ok_0 : qrows0.all (fun R => decide (RowOK R)) = true := by decide +kernel
theorem rows_ok_1 : qrows1.all (fun R => decide (RowOK R)) = true := by decide +kernel
theorem rows_ok_2 : qrows2.all (fun R => decide (RowOK R)) = true := by decide +kernel
theorem rows_ok_3 : qrows3.all (fun R => decide (RowOK R)) = true := by decide +kernel
theorem rows_ok_4 : qrows4.all (fun R => decide (RowOK R)) = true := by decide +kernel
theorem rows_ok_5 : qrows5.all (fun R => decide (RowOK R)) = true := by decide +kernel
theorem rows_ok_6 : qrows6.all (fun R => decide (RowOK R)) = true := by decide +kernel

theorem rows_ok_all : qrows.all (fun R => decide (RowOK R)) = true := by
  simp only [qrows, List.all_append, rows_ok_0, rows_ok_1, rows_ok_2, rows_ok_3, rows_ok_4,
    rows_ok_5, rows_ok_6, Bool.and_self]

theorem row_ok (i : Fin 455) : RowOK (qrow i) := by
  have h := List.all_eq_true.mp rows_ok_all _ (qrow_mem i)
  exact of_decide_eq_true h

/-- The reserved cosets as a 16-bit mask. -/
def qmask (R : QRow) : ℕ :=
  (List.range 16).foldr (fun n acc => (if R.isQ (zv n) then 2 ^ n else 0) + acc) 0

/-- The rows are sorted by mask, so a linear chain check gives distinctness. -/
theorem qmask_chain : (List.ofFn fun i : Fin 455 => qmask (qrow i)).IsChain (· < ·) := by
  decide +kernel

theorem qmask_nodup : (List.ofFn fun i : Fin 455 => qmask (qrow i)).Nodup :=
  (List.isChain_iff_pairwise.mp qmask_chain).imp (fun h => ne_of_lt h)

theorem qmask_injective : Function.Injective fun i : Fin 455 => qmask (qrow i) :=
  List.nodup_ofFn.mp qmask_nodup

theorem qmask_congr {R R' : QRow} (h : ∀ z, R.isQ z ↔ R'.isQ z) : qmask R = qmask R' := by
  unfold qmask
  congr 1
  funext n acc
  rw [if_congr (h (zv n)) rfl rfl]

theorem row_eq_of_isQ {i i' : Fin 455} (h : ∀ z, (qrow i).isQ z ↔ (qrow i').isQ z) : i = i' :=
  qmask_injective (qmask_congr h)

/-! ## Canonical slopes on a half space

On `H = {z : s · z = κ}` an affine function is `b + β · z` for a unique `β` whose bit at
the lowest set bit of `s` is zero.  `betaOf s j` inserts that zero bit into `j < 8`. -/

def lowbit (s : ℕ) : ℕ :=
  if s.testBit 0 then 0 else if s.testBit 1 then 1 else if s.testBit 2 then 2 else 3

def betaOf (s j : ℕ) : ℕ := j % 2 ^ lowbit s + 2 ^ (lowbit s + 1) * (j / 2 ^ lowbit s)

/-- Two canonical affine functions agreeing on the half space `s · z = κ`. -/
def Clash (s : ℕ) (κ : ZMod 2) (j j' : ℕ) (b b' : ZMod 2) : Prop :=
  ∀ z : Z4, zdot s z = κ → b + zdot (betaOf s j) z = b' + zdot (betaOf s j') z

instance (s : ℕ) (κ : ZMod 2) (j j' : ℕ) (b b' : ZMod 2) : Decidable (Clash s κ j j' b b') := by
  unfold Clash; infer_instance

def ClashOK (s : ℕ) (κ : ZMod 2) (j j' : ℕ) : Prop :=
  ∀ b b' : ZMod 2, Clash s κ j j' b b' → j = j' ∧ b = b'

instance (s : ℕ) (κ : ZMod 2) (j j' : ℕ) : Decidable (ClashOK s κ j j') := by
  unfold ClashOK; infer_instance

def ClashOKs (s : ℕ) : Prop := ∀ κ : ZMod 2, ∀ j < 8, ∀ j' < 8, ClashOK s κ j j'

instance (s : ℕ) : Decidable (ClashOKs s) := by unfold ClashOKs; infer_instance

theorem clash_all : ∀ s < 16, s ≠ 0 → ClashOKs s := by decide +kernel

theorem beta_inj {s : ℕ} (hs : SOK s) {κ : ZMod 2} {j j' : ℕ} (hj : j < 8) (hj' : j' < 8)
    {b b' : ZMod 2} (h : Clash s κ j j' b b') : j = j' ∧ b = b' :=
  clash_all s hs.2 hs.1 κ j hj j' hj' b b' h

def HasOne (s : ℕ) : Prop := ∃ z : Z4, zdot s z = 1

instance (s : ℕ) : Decidable (HasOne s) := by unfold HasOne; infer_instance

theorem hasOne_all : ∀ s < 16, s ≠ 0 → HasOne s := by decide +kernel

theorem zdot_surj {s : ℕ} (hs : SOK s) : ∃ z : Z4, zdot s z = 1 := hasOne_all s hs.2 hs.1

/-- Two distinct nonzero functionals are independent, so they assume every pair of values. -/
theorem zdot_pair_surj : ∀ s s' : Fin 16, (s : ℕ) ≠ 0 → (s' : ℕ) ≠ 0 → s ≠ s' →
    ∀ c c' : ZMod 2, ∃ z : Z4, zdot (s : ℕ) z = c ∧ zdot (s' : ℕ) z = c' := by
  decide +kernel

theorem zdot_pair {s s' : ℕ} (hs : SOK s) (hs' : SOK s') (hne : s ≠ s') (c c' : ZMod 2) :
    ∃ z : Z4, zdot s z = c ∧ zdot s' z = c' :=
  zdot_pair_surj ⟨s, hs.2⟩ ⟨s', hs'.2⟩ hs.1 hs'.1 (by simpa using hne) c c'

end ProximityPrize.SubmissionBinaryUpper.LabelTable
