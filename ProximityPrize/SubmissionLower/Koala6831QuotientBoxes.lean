import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases

namespace ProximityPrize.SubmissionLower.Koala6831Quotient

open scoped BigOperators

def separatedExponents (D w y s L₀ L₁ : ℕ) : Set (Fin 5 →₀ ℕ) :=
  {d | d 0 + w * (d 1 + d 2) < D ∧ d 1 + d 2 ≤ y ∧ d 2 ≤ s ∧
    d 1 + d 3 ≤ L₀ ∧ d 2 + d 4 ≤ L₁}

abbrev SeparatedIndex (D w y s L₀ L₁ : ℕ) :=
  (j : Fin (s + 1)) × (i : Fin (y + 1 - j.val)) ×
    Fin (D - w * (i.val + j.val)) × Fin (L₀ + 1 - i.val) × Fin (L₁ + 1 - j.val)

private noncomputable def exponent (x i j a b : ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![x, i, j, a, b]

private noncomputable def fromIndex {D w y s L₀ L₁ : ℕ}
    (v : SeparatedIndex D w y s L₀ L₁) : separatedExponents D w y s L₀ L₁ := by
  obtain ⟨j, i, x, a, b⟩ := v
  refine ⟨exponent x i j a b, ?_⟩
  have hj := j.isLt
  have hi := i.isLt
  have hx := x.isLt
  have ha := a.isLt
  have hb := b.isLt
  simp [separatedExponents, exponent]
  omega

private theorem fromIndex_injective {D w y s L₀ L₁ : ℕ} :
    Function.Injective (fromIndex (D := D) (w := w) (y := y) (s := s) (L₀ := L₀) (L₁ := L₁)) := by
  rintro ⟨⟨j, hj⟩, ⟨i, hi⟩, ⟨x, hx⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩
    ⟨⟨j', hj'⟩, ⟨i', hi'⟩, ⟨x', hx'⟩, ⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
  have powers := congrArg Subtype.val h
  change exponent x i j a b = exponent x' i' j' a' b' at powers
  have x_eq : x = x' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 0) powers
  have i_eq : i = i' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 1) powers
  have j_eq : j = j' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 2) powers
  have a_eq : a = a' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 3) powers
  have b_eq : b = b' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 4) powers
  subst j' i' x' a' b'
  rfl

private theorem fromIndex_surjective {D w y s L₀ L₁ : ℕ} :
    Function.Surjective (fromIndex (D := D) (w := w) (y := y) (s := s) (L₀ := L₀) (L₁ := L₁)) := by
  rintro ⟨d, bounds⟩
  rcases bounds with ⟨hd, hy, hs, ha, hb⟩
  let j : Fin (s + 1) := ⟨d 2, by omega⟩
  let i : Fin (y + 1 - j.val) := ⟨d 1, by dsimp [j]; omega⟩
  refine ⟨⟨j, i, ⟨d 0, ?_⟩, ⟨d 3, ?_⟩, ⟨d 4, ?_⟩⟩, ?_⟩
  · dsimp [i, j]
    omega
  · dsimp [i]
    omega
  · dsimp [j]
    omega
  · apply Subtype.ext
    change exponent (d 0) (d 1) (d 2) (d 3) (d 4) = d
    ext k
    fin_cases k <;> simp [exponent]

private noncomputable def separatedIndexEquiv (D w y s L₀ L₁ : ℕ) :
    SeparatedIndex D w y s L₀ L₁ ≃ separatedExponents D w y s L₀ L₁ :=
  Equiv.ofBijective fromIndex ⟨fromIndex_injective, fromIndex_surjective⟩

noncomputable instance (D w y s L₀ L₁ : ℕ) : Fintype (separatedExponents D w y s L₀ L₁) :=
  Fintype.ofEquiv _ (separatedIndexEquiv D w y s L₀ L₁)

noncomputable abbrev separatedBox (K : Type*) [Field K] (D w y s L₀ L₁ : ℕ) :
    Submodule K (MvPolynomial (Fin 5) K) :=
  MvPolynomial.restrictSupport K (separatedExponents D w y s L₀ L₁)

instance (K : Type*) [Field K] (D w y s L₀ L₁ : ℕ) : Module.Finite K (separatedBox K D w y s L₀ L₁) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (separatedExponents D w y s L₀ L₁))

def separatedColumns (D w y s L₀ L₁ : ℕ) : ℕ :=
  ∑ j : Fin (s + 1), ∑ i : Fin (y + 1 - j.val),
    (D - w * (i.val + j.val)) * (L₀ + 1 - i.val) * (L₁ + 1 - j.val)

theorem separatedBox_finrank (K : Type*) [Field K] (D w y s L₀ L₁ : ℕ) :
    Module.finrank K (separatedBox K D w y s L₀ L₁) = separatedColumns D w y s L₀ L₁ := by
  rw [Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport K (separatedExponents D w y s L₀ L₁)),
    ← Fintype.card_congr (separatedIndexEquiv D w y s L₀ L₁)]
  simp [SeparatedIndex, separatedColumns, Fintype.card_sigma, Nat.mul_assoc]

theorem separatedColumns_mono_cutoff (w y s L₀ L₁ : ℕ) :
    Monotone (fun D => separatedColumns D w y s L₀ L₁) := by
  intro D D' cut_le
  unfold separatedColumns
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right cut_le _))

theorem longSeparatedDimensionGate (excess : ℕ) (long : 9555 ≤ excess) :
    separatedColumns (16 * 181084 - 131071 - excess) 131071 21 21 177 161 +
      262144 * (separatedColumns 16 1 15 22 178 162 -
        separatedColumns 15 1 14 21 177 161) <
      separatedColumns (16 * 181084) 131071 22 22 178 162 := by
  have threshold :
      separatedColumns (16 * 181084 - 131071 - 9555) 131071 21 21 177 161 +
        262144 * (separatedColumns 16 1 15 22 178 162 -
          separatedColumns 15 1 14 21 177 161) <
        separatedColumns (16 * 181084) 131071 22 22 178 162 := by
    decide +kernel
  apply lt_of_le_of_lt _ threshold
  exact Nat.add_le_add_right (separatedColumns_mono_cutoff _ _ _ _ _ (Nat.sub_le_sub_left long _)) _

def ordinaryExponents (D w y L : ℕ) : Set (Fin 5 →₀ ℕ) :=
  {d | d 0 + w * (d 1 + d 2) < D ∧ d 1 + d 2 ≤ y ∧
    d 1 + d 2 + d 3 + d 4 ≤ L}

abbrev OrdinaryIndex (D w y L : ℕ) :=
  (t : Fin (min y L + 1)) × Fin (t.val + 1) × Fin (D - w * t.val) ×
    (a : Fin (L + 1 - t.val)) × Fin (L + 1 - t.val - a.val)

private noncomputable def fromOrdinaryIndex {D w y L : ℕ}
    (v : OrdinaryIndex D w y L) : ordinaryExponents D w y L := by
  obtain ⟨t, i, x, a, b⟩ := v
  refine ⟨exponent x i (t.val - i.val) a b, ?_⟩
  have ht := t.isLt
  have hi := i.isLt
  have hx := x.isLt
  have ha := a.isLt
  have hb := b.isLt
  have total : i.val + (t.val - i.val) = t.val := by omega
  simp [ordinaryExponents, exponent, total]
  omega

private theorem fromOrdinaryIndex_injective {D w y L : ℕ} :
    Function.Injective (fromOrdinaryIndex (D := D) (w := w) (y := y) (L := L)) := by
  rintro ⟨⟨t, ht⟩, ⟨i, hi⟩, ⟨x, hx⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩
    ⟨⟨t', ht'⟩, ⟨i', hi'⟩, ⟨x', hx'⟩, ⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
  have powers := congrArg Subtype.val h
  change exponent x i (t - i) a b = exponent x' i' (t' - i') a' b' at powers
  have x_eq : x = x' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 0) powers
  have i_eq : i = i' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 1) powers
  have j_eq : t - i = t' - i' := by
    simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 2) powers
  have a_eq : a = a' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 3) powers
  have b_eq : b = b' := by simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d 4) powers
  have t_eq : t = t' := by
    change i < t + 1 at hi
    change i' < t' + 1 at hi'
    omega
  subst t' i' x' a' b'
  rfl

private theorem fromOrdinaryIndex_surjective {D w y L : ℕ} :
    Function.Surjective (fromOrdinaryIndex (D := D) (w := w) (y := y) (L := L)) := by
  rintro ⟨d, bounds⟩
  rcases bounds with ⟨hd, hy, hL⟩
  let t : Fin (min y L + 1) := ⟨d 1 + d 2, by omega⟩
  let a : Fin (L + 1 - t.val) := ⟨d 3, by dsimp [t]; omega⟩
  refine ⟨⟨t, ⟨d 1, ?_⟩, ⟨d 0, ?_⟩, a, ⟨d 4, ?_⟩⟩, ?_⟩
  · dsimp [t]
    omega
  · dsimp [t]
    omega
  · dsimp [t, a]
    omega
  · apply Subtype.ext
    change exponent (d 0) (d 1) (d 1 + d 2 - d 1) (d 3) (d 4) = d
    rw [Nat.add_sub_cancel_left]
    ext k
    fin_cases k <;> simp [exponent]

private noncomputable def ordinaryIndexEquiv (D w y L : ℕ) :
    OrdinaryIndex D w y L ≃ ordinaryExponents D w y L :=
  Equiv.ofBijective fromOrdinaryIndex ⟨fromOrdinaryIndex_injective, fromOrdinaryIndex_surjective⟩

noncomputable instance (D w y L : ℕ) : Fintype (ordinaryExponents D w y L) :=
  Fintype.ofEquiv _ (ordinaryIndexEquiv D w y L)

noncomputable abbrev ordinaryBox (K : Type*) [Field K] (D w y L : ℕ) :
    Submodule K (MvPolynomial (Fin 5) K) :=
  MvPolynomial.restrictSupport K (ordinaryExponents D w y L)

instance (K : Type*) [Field K] (D w y L : ℕ) : Module.Finite K (ordinaryBox K D w y L) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (ordinaryExponents D w y L))

def ordinaryColumns (D w y L : ℕ) : ℕ :=
  ∑ t : Fin (min y L + 1),
    (t.val + 1) * (D - w * t.val) *
      (∑ a : Fin (L + 1 - t.val), (L + 1 - t.val - a.val))

theorem ordinaryBox_finrank (K : Type*) [Field K] (D w y L : ℕ) :
    Module.finrank K (ordinaryBox K D w y L) = ordinaryColumns D w y L := by
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K (ordinaryExponents D w y L)),
    ← Fintype.card_congr (ordinaryIndexEquiv D w y L)]
  simp [OrdinaryIndex, ordinaryColumns, Fintype.card_sigma, Nat.mul_assoc]

theorem ordinaryColumns_mono_cutoff (w y L : ℕ) : Monotone (fun D => ordinaryColumns D w y L) := by
  intro D D' cut_le
  unfold ordinaryColumns
  apply Finset.sum_le_sum
  intro t _
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right cut_le _))

def ordinaryProfiles : Fin 9 → ℕ × ℕ × ℕ :=
  ![(14, 19, 166), (11, 15, 65), (6, 8, 30), (5, 6, 19), (4, 5, 13),
    (3, 4, 15), (3, 4, 13), (3, 4, 12), (2, 2, 13)]

set_option maxRecDepth 30000 in

theorem ordinaryDimensionGate (c : Fin 9) (excess : ℕ) (large : 11000 ≤ excess) :
    let (m, y, L) := ordinaryProfiles c
    ordinaryColumns (m * 181084 - 131071 - excess) 131071 (y - 1) (L - (c.val + 2)) +
      262144 * (ordinaryColumns m 1 (m - 1) L -
        ordinaryColumns (m - 1) 1 (m - 2) (L - (c.val + 2))) <
      ordinaryColumns (m * 181084) 131071 y L := by
  have threshold :
      let (m, y, L) := ordinaryProfiles c
      ordinaryColumns (m * 181084 - 131071 - 11000) 131071 (y - 1) (L - (c.val + 2)) +
        262144 * (ordinaryColumns m 1 (m - 1) L -
          ordinaryColumns (m - 1) 1 (m - 2) (L - (c.val + 2))) <
        ordinaryColumns (m * 181084) 131071 y L := by
    fin_cases c <;> decide +kernel
  cases profile : ordinaryProfiles c with
  | mk m caps =>
      obtain ⟨y, L⟩ := caps
      simp only [profile] at threshold ⊢
      apply lt_of_le_of_lt _ threshold
      exact Nat.add_le_add_right (ordinaryColumns_mono_cutoff _ _ _ (Nat.sub_le_sub_left large _)) _

end ProximityPrize.SubmissionLower.Koala6831Quotient
