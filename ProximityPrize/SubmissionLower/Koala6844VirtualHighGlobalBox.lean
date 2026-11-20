import ProximityPrize.SubmissionLower.Koala6844VirtualHighBoxes


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators Classical Matrix
noncomputable section
set_option autoImplicit false

def globalExponents (D w y b c : ℕ) : Set (Fin 4 →₀ ℕ) :=
  { e | e 0 + w * e 1 < D ∧ e 1 ≤ y ∧ e 2 ≤ b ∧ e 3 ≤ c }

private abbrev GlobalIndex (D w y b c : ℕ) :=
  Σ j : Fin (y+1), Fin (D-w*j.val) × Fin (b+1) × Fin (c+1)

private def buildExponent {D w y b c : ℕ} (i : GlobalIndex D w y b c) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i.2.1.val, i.1.val, i.2.2.1.val, i.2.2.2.val]

private theorem buildExponent_mem {D w y b c : ℕ} (i : GlobalIndex D w y b c) :
    buildExponent i ∈ globalExponents D w y b c := by
  rcases i with ⟨j, x, s, t⟩
  have hx := x.isLt
  change _ ∧ _ ∧ _ ∧ _
  simp only [buildExponent, Finsupp.coe_equivFunOnFinite_symm,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  exact ⟨by omega, Nat.le_of_lt_succ j.isLt, Nat.le_of_lt_succ s.isLt, Nat.le_of_lt_succ t.isLt⟩

private def globalExponentEquiv (D w y b c : ℕ) : globalExponents D w y b c ≃ GlobalIndex D w y b c where
  toFun e :=
    ⟨⟨e.val 1, Nat.lt_succ_of_le e.property.2.1⟩,
      ⟨e.val 0, by change e.val 0 < D - w * e.val 1; exact Nat.lt_sub_of_add_lt e.property.1⟩,
      ⟨e.val 2, Nat.lt_succ_of_le e.property.2.2.1⟩,
      ⟨e.val 3, Nat.lt_succ_of_le e.property.2.2.2⟩⟩
  invFun i := ⟨buildExponent i, buildExponent_mem i⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [buildExponent, Matrix.cons_val_two, Matrix.cons_val_three]
  right_inv i := by
    rcases i with ⟨j, ⟨x, hx⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
    cases j
    rfl

variable (K : Type) [Field K]

private abbrev globalCoefficients := (MvPolynomial.basisMonomials (Fin 4) K).repr

def globalBox (D w y b c : ℕ) : Submodule K (MvPolynomial (Fin 4) K) :=
  (Finsupp.supported K K (globalExponents D w y b c)).comap (globalCoefficients K).toLinearMap

theorem mem_globalBox (D w y b c : ℕ) (Q : MvPolynomial (Fin 4) K) :
    Q ∈ globalBox K D w y b c ↔
      ∀ e ∈ Q.support, e 0 + w * e 1 < D ∧ e 1 ≤ y ∧ e 2 ≤ b ∧ e 3 ≤ c := by
  change globalCoefficients K Q ∈ Finsupp.supported K K (globalExponents D w y b c) ↔ _
  rw [Finsupp.mem_supported]
  rfl

private noncomputable instance (D w y b c : ℕ) : Fintype (globalExponents D w y b c) :=
  Fintype.ofEquiv _ (globalExponentEquiv D w y b c).symm

private def globalBoxEquiv (D w y b c : ℕ) :
    globalBox K D w y b c ≃ₗ[K] (globalExponents D w y b c →₀ K) :=
  ((globalCoefficients K).ofSubmodule' _).trans
    (Finsupp.supportedEquivFinsupp (R := K) (M := K) _)

instance (D w y b c : ℕ) : Module.Finite K (globalBox K D w y b c) :=
  Module.Finite.equiv (globalBoxEquiv K D w y b c).symm

theorem finrank_globalBox (D w y b c : ℕ) :
    Module.finrank K (globalBox K D w y b c) =
      ∑ j : Fin (y+1), (D-w*j.val)*(b+1)*(c+1) := by
  rw [(globalBoxEquiv K D w y b c).finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_congr (globalExponentEquiv D w y b c)]
  simp [GlobalIndex, Fintype.card_sigma, Fintype.card_prod, Nat.mul_assoc]

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
