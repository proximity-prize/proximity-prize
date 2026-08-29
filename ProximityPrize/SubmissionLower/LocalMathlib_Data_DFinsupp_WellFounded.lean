/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_Order_GameAdd

/-! . -/

/-! . -/

section ProximityFlatProofPort


variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

open Relation Prod

section Zero

variable [∀ i, Zero (α i)] (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop)

/-- . -/
theorem lex_fibration [∀ (i) (s : Set ι), Decidable (i ∈ s)] :
    Fibration (InvImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s)) snd) (DFinsupp.Lex r s)
      fun x => piecewise x.2.1 x.2.2 x.1 := by
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩
  simp_rw [piecewise_apply] at hs hr
  split_ifs at hs with hp
  · refine ⟨⟨{ j | r j i → j ∈ p }, piecewise x₁ x { j | r j i }, x₂⟩,
      .fst ⟨i, fun j hj ↦ ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_setOf_eq]
    · simp only [if_pos hj]
    · split_ifs with hi
      · rwa [hr i hi, if_pos hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_setOf_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₂, if_pos (h₁ h₂)]
      · rw [Classical.not_imp] at h₁
        rw [hr j h₁.1, if_neg h₁.2]
  · refine ⟨⟨{ j | r j i ∧ j ∈ p }, x₁, piecewise x₂ x { j | r j i }⟩,
      .snd ⟨i, fun j hj ↦ ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_setOf_eq]
    · exact if_pos hj
    · split_ifs with hi
      · rwa [hr i hi, if_neg hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_setOf_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₁.1, if_pos h₁.2]
      · rw [hr j h₂, if_neg]
        simpa [h₂] using h₁

variable {r s}

theorem Lex.acc_of_single_erase [DecidableEq ι] {x : Π₀ i, α i} (i : ι)
    (hs : Acc (DFinsupp.Lex r s) <| single i (x i)) (hu : Acc (DFinsupp.Lex r s) <| x.erase i) :
    Acc (DFinsupp.Lex r s) x := by
  classical
    convert! ←
      @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{ i }, _⟩
        (InvImage.accessible snd <| hs.prod_gameAdd hu)
    convert! piecewise_single_erase x i

theorem Lex.acc_zero (hbot : ∀ ⦃i a⦄, ¬s i a 0) : Acc (DFinsupp.Lex r s) 0 :=
  Acc.intro 0 fun _ ⟨_, _, h⟩ => (hbot h).elim

theorem Lex.acc_of_single (hbot : ∀ ⦃i a⦄, ¬s i a 0) [DecidableEq ι]
    [∀ (i) (x : α i), Decidable (x ≠ 0)] (x : Π₀ i, α i) :
    (∀ i ∈ x.support, Acc (DFinsupp.Lex r s) <| single i (x i)) → Acc (DFinsupp.Lex r s) x := by
  generalize ht : x.support = t; revert x
  classical
    induction t using Finset.induction with
    | empty =>
      intro x ht
      rw [support_eq_empty.1 ht]
      exact fun _ => Lex.acc_zero hbot
    | insert b t hb ih =>
      refine fun x ht h => Lex.acc_of_single_erase b (h b <| t.mem_insert_self b) ?_
      refine ih _ (by rw [support_erase, ht, Finset.erase_insert hb]) fun a ha => ?_
      rw [erase_ne (ha.ne_of_notMem hb)]
      exact h a (Finset.mem_insert_of_mem ha)

theorem Lex.acc_single (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    [DecidableEq ι] {i : ι} (hi : Acc (rᶜ ⊓ (· ≠ ·)) i) :
    ∀ a, Acc (DFinsupp.Lex r s) (single i a) := by
  induction hi with | _ i _ ih
  refine fun a => WellFounded.induction (hs i)
    (C := fun x ↦ Acc (DFinsupp.Lex r s) (single i x)) a fun a ha ↦ ?_
  refine Acc.intro _ fun x ↦ ?_
  rintro ⟨k, hr, hs⟩
  rw [single_apply] at hs
  split_ifs at hs with hik
  swap
  · exact (hbot hs).elim
  subst hik
  classical
    refine Lex.acc_of_single hbot x fun j hj ↦ ?_
    obtain rfl | hij := eq_or_ne j i
    · exact ha _ hs
    by_cases h : r j i
    · rw [hr j h, single_eq_of_ne hij, single_zero]
      exact Lex.acc_zero hbot
    · exact ih _ ⟨h, hij⟩ _

theorem Lex.acc (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)] (x : Π₀ i, α i)
    (h : ∀ i ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) i) : Acc (DFinsupp.Lex r s) x :=
  Lex.acc_of_single hbot x fun i hi => Lex.acc_single hbot hs (h i hi) _

theorem Lex.wellFounded (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (DFinsupp.Lex r s) :=
  ⟨fun x => by
    classical
    letI : DecidableEq ι := Classical.decEq ι
    exact Lex.acc hbot hs x fun i _ => hr.apply i⟩

theorem Lex.wellFounded' (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    [Std.Trichotomous r] (hr : WellFounded (Function.swap r)) : WellFounded (DFinsupp.Lex r s) :=
  Lex.wellFounded hbot hs <| Subrelation.wf
    (fun {i j} h ↦ Not.imp_symm (@Std.Trichotomous.trichotomous ι r _ i j h.left) h.right) hr

end Zero

instance Lex.wellFoundedLT [LT ι] [@Std.Trichotomous ι (· < ·)] [hι : WellFoundedGT ι]
    [∀ i, AddMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsBotZeroClass (α i)]
    [hα : ∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨Lex.wellFounded' (fun _ _ => not_lt_zero) (fun i => (hα i).wf) hι.wf⟩

instance Colex.wellFoundedLT [LT ι] [@Std.Trichotomous ι (· < ·)] [WellFoundedLT ι]
    [∀ i, AddMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsBotZeroClass (α i)]
    [∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (Colex (Π₀ i, α i)) :=
  Lex.wellFoundedLT (ι := ιᵒᵈ)

end DFinsupp

open DFinsupp

variable (r : ι → ι → Prop) {s : ∀ i, α i → α i → Prop}

theorem Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite ι] (hs : ∀ i, WellFounded (s i)) :
    WellFounded (Pi.Lex r (fun {i} ↦ s i)) := by
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
  · convert! emptyWf.wf
  letI : ∀ i, Zero (α i) := fun i => ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩
  haveI := Fintype.ofFinite ι
  refine InvImage.wf equivFunOnFintype.symm (Lex.wellFounded' (fun i a => ?_) hs ?_)
  exacts [(hs i).not_lt_min ⊤ trivial, Finite.wellFounded_of_trans_of_irrefl (Function.swap r)]

instance Pi.Lex.wellFoundedLT [LinearOrder ι] [Finite ι] [∀ i, LT (α i)]
    [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Lex (∀ i, α i)) :=
  ⟨Pi.Lex.wellFounded (· < ·) fun i => (hwf i).1⟩

instance Pi.Colex.wellFoundedLT [LinearOrder ι] [Finite ι] [∀ i, LT (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Colex (∀ i, α i)) :=
  Pi.Lex.wellFoundedLT (ι := ιᵒᵈ)

instance Function.Lex.wellFoundedLT {α} [LinearOrder ι] [Finite ι] [LT α] [WellFoundedLT α] :
    WellFoundedLT (Lex (ι → α)) :=
  Pi.Lex.wellFoundedLT

theorem DFinsupp.Lex.wellFounded_of_finite [IsStrictTotalOrder ι r] [Finite ι] [∀ i, Zero (α i)]
    (hs : ∀ i, WellFounded (s i)) : WellFounded (DFinsupp.Lex r s) :=
  have := Fintype.ofFinite ι
  InvImage.wf equivFunOnFintype (Pi.Lex.wellFounded r hs)

instance DFinsupp.Lex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [∀ i, Zero (α i)]
    [∀ i, LT (α i)] [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨DFinsupp.Lex.wellFounded_of_finite (· < ·) fun i => (hwf i).1⟩

instance DFinsupp.Colex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [∀ i, Zero (α i)]
    [∀ i, LT (α i)] [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Colex (Π₀ i, α i)) :=
  DFinsupp.Lex.wellFoundedLT_of_finite (ι := ιᵒᵈ)

protected theorem DFinsupp.wellFoundedLT [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] (hbot : ∀ ⦃i⦄ ⦃a : α i⦄, ¬a < 0) : WellFoundedLT (Π₀ i, α i) :=
  ⟨by
    set β := fun i ↦ Antisymmetrization (α i) (· ≤ ·)
    set e : (i : ι) → α i → β i := fun i ↦ toAntisymmetrization (· ≤ ·)
    let _ : ∀ i, Zero (β i) := fun i ↦ ⟨e i 0⟩
    have : WellFounded (DFinsupp.Lex (Function.swap <| @WellOrderingRel ι)
        (fun _ ↦ (· < ·) : (i : ι) → β i → β i → Prop)) := by
      refine Lex.wellFounded' ?_ (fun i ↦ IsWellFounded.wf) ?_
      · rintro i ⟨a⟩
        apply hbot
      · simp +unfoldPartialApp only [Function.swap]
        exact IsWellFounded.wf
    refine Subrelation.wf (fun h => ?_) <| InvImage.wf (mapRange e fun _ ↦ rfl) this
    obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder (Function.swap WellOrderingRel) h
    exact ⟨i, fun j hj ↦ Quot.sound (he j hj), hl⟩⟩

instance DFinsupp.wellFoundedLT'
    [∀ i, AddMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsBotZeroClass (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  DFinsupp.wellFoundedLT fun _ _ => not_lt_zero

instance Pi.wellFoundedLT [Finite ι] [∀ i, Preorder (α i)] [hw : ∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (∀ i, α i) :=
  ⟨by
    obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
    · convert! emptyWf.wf
    letI : ∀ i, Zero (α i) := fun i => ⟨(hw i).wf.min ⊤ ⟨x i, trivial⟩⟩
    haveI := Fintype.ofFinite ι
    refine InvImage.wf equivFunOnFintype.symm (DFinsupp.wellFoundedLT fun i a => ?_).wf
    exact (hw i).wf.not_lt_min ⊤ trivial⟩

instance Function.wellFoundedLT {α} [Finite ι] [Preorder α] [WellFoundedLT α] :
    WellFoundedLT (ι → α) :=
  Pi.wellFoundedLT

instance DFinsupp.wellFoundedLT_of_finite [Finite ι] [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  have := Fintype.ofFinite ι
  ⟨InvImage.wf equivFunOnFintype Pi.wellFoundedLT.wf⟩
