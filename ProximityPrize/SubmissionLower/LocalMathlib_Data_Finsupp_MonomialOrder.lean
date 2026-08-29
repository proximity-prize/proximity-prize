/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_Data_Finsupp_WellFounded

/-! . -/

/-! . -/

section ProximityFlatProofPort

/-- . -/
structure MonomialOrder (σ : Type*) where
  /-- . -/
  syn : Type*
  /-- . -/
  addCommMonoidSyn : AddCommMonoid syn := by infer_instance
  /-- . -/
  linearOrderSyn : LinearOrder syn := by infer_instance
  /-- . -/
  isOrderedAddMonoid_syn : IsOrderedAddMonoid syn := by infer_instance
  /-- . -/
  toSyn : (σ →₀ ℕ) ≃+ syn
  /-- . -/
  toSyn_monotone : Monotone toSyn
  /-- . -/
  wellFoundedLT_syn : WellFoundedLT syn := by infer_instance

attribute [instance] MonomialOrder.addCommMonoidSyn MonomialOrder.linearOrderSyn
  MonomialOrder.isOrderedAddMonoid_syn MonomialOrder.wellFoundedLT_syn

@[deprecated (since := "2026-07-07")] alias acm := MonomialOrder.addCommMonoidSyn

@[deprecated (since := "2026-07-07")] alias lo := MonomialOrder.linearOrderSyn

@[deprecated (since := "2026-07-07")] alias wf := MonomialOrder.wellFoundedLT_syn

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ)

instance : AddCancelCommMonoid m.syn where
  add_left_cancel := m.toSyn.symm.injective.isLeftCancelAdd _ (map_add _) |>.add_left_cancel

instance isOrderedCancelAddMonoid_syn : IsOrderedCancelAddMonoid m.syn :=
  IsOrderedAddMonoid.toIsOrderedCancelAddMonoid'

@[deprecated (since := "2026-07-07")] alias iocam := MonomialOrder.isOrderedCancelAddMonoid_syn

lemma le_add_right (a b : σ →₀ ℕ) :
    m.toSyn a ≤ m.toSyn a + m.toSyn b := by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add

instance orderBot : OrderBot (m.syn) where
  bot := 0
  bot_le a := by
    have := m.le_add_right 0 (m.toSyn.symm a)
    simpa [map_add, zero_add]

@[simp]
theorem bot_eq_zero : (⊥ : m.syn) = 0 := rfl

@[simp]
lemma zero_le (a : m.syn) : 0 ≤ a := bot_le

theorem eq_zero_iff {a : m.syn} : a = 0 ↔ a ≤ 0 := eq_bot_iff

lemma toSyn_eq_zero_iff (a : σ →₀ ℕ) :
    m.toSyn a = 0 ↔ a = 0 := AddEquiv.map_eq_zero_iff m.toSyn

lemma toSyn_lt_iff_ne_zero {a : m.syn} :
    0 < a ↔ a ≠ 0 := bot_lt_iff_ne_bot

lemma toSyn_strictMono : StrictMono (m.toSyn) := by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

/-- . -/
scoped
notation:50 c " ≺[" m:25 "] " d:50 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)

/-- . -/
scoped
notation:50 c " ≼[" m:25 "] " d:50 => (MonomialOrder.toSyn m c ≤ MonomialOrder.toSyn m d)

end MonomialOrder

section Lex

open Finsupp

open scoped MonomialOrder


noncomputable instance {α N : Type*} [LinearOrder α]
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Lex (α →₀ N)) where
  le_of_add_le_add_left a b c h := by simpa only [add_le_add_iff_left] using h
  add_le_add_left a b h c := by simpa using h

/-- . -/
example : toLex (Finsupp.single 0 2) > toLex (Finsupp.single 0 1 + Finsupp.single 1 1) := by
  use 0; simp

/-- . -/
example : toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 1) := by
  use 0; simp

/-- . -/
example : toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 2) := by
  use 0; simp

variable {σ : Type*} [LinearOrder σ]

/-- . -/
noncomputable def MonomialOrder.lex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := Lex (σ →₀ ℕ)
  toSyn :=
  { toEquiv := toLex
    map_add' := toLex_add }
  toSyn_monotone := Finsupp.toLex_monotone

theorem MonomialOrder.lex_le_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≼[lex] d ↔ toLex c ≤ toLex d := Iff.rfl

theorem MonomialOrder.lex_lt_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≺[lex] d ↔ toLex c < toLex d := Iff.rfl

theorem MonomialOrder.lex_lt_iff_of_unique [Unique σ] {c d : σ →₀ ℕ} :
    c ≺[lex] d ↔ c default < d default := by
  simp only [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff_of_unique, ofLex_toLex]

theorem MonomialOrder.lex_le_iff_of_unique [Unique σ] {c d : σ →₀ ℕ} :
    c ≼[lex] d ↔ c default ≤ d default := by
  simp only [MonomialOrder.lex_le_iff, Finsupp.Lex.le_iff_of_unique, ofLex_toLex]

end Lex
