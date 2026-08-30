import ProximityPrize.SubmissionLower.ContactFreshCoefficientFieldGeneration

/-! Removing the one fresh rational-function parameter from the recovered
coefficient field. -/

namespace ProximityPrize.SubmissionLower.ContactCoefficientFieldTrdeg

open ContactFreshCoefficientFieldGeneration

noncomputable section

variable {k L : Type} [Field k] [Field L] [Algebra k L]

theorem trdeg_le_one_of_tower
    {k B E : Type} [Field k] [Field B] [Field E]
    [Algebra k B] [Algebra B E] [Algebra k E] [IsScalarTower k B E]
    (hE : Algebra.trdeg k E ≤ 2) (htrans : Algebra.Transcendental B E) :
    Algebra.trdeg k B ≤ 1 := by
  letI : Algebra.Transcendental B E := htrans
  have hb : 0 < Algebra.trdeg B E := trdeg_pos B E
  have hsum : Algebra.trdeg k B + Algebra.trdeg B E = Algebra.trdeg k E :=
    trdeg_add_eq k B
  have hab : Algebra.trdeg k B + Algebra.trdeg B E ≤ 2 := by
    rw [hsum]
    exact hE
  by_contra hnot
  have ha : (1 : Cardinal) < Algebra.trdeg k B := lt_of_not_ge hnot
  have htwo : (2 : Cardinal) ≤ Algebra.trdeg k B := by
    have h := Cardinal.add_one_le_of_lt ha
    norm_num at h
    exact h
  have hbone : (1 : Cardinal) ≤ Algebra.trdeg B E := Cardinal.one_le_iff_pos.mpr hb
  have hthree : (3 : Cardinal) ≤ Algebra.trdeg k B + Algebra.trdeg B E := by
    calc
      (3 : Cardinal) = 2+1 := by norm_num
      _ ≤ _ := add_le_add htwo hbone
  have : (3 : Cardinal) ≤ 2 := hthree.trans hab
  norm_num at this

section RationalExtension

variable {k L : Type} [Field k] [Field L] [Algebra k L]

theorem coefficient_trdeg_le_one_of_rational_extension
    (B : IntermediateField k L) (E : IntermediateField k (RatFunc L))
    (hmap : B.map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤ E)
    (hX : (RatFunc.X : RatFunc L) ∈ E)
    (hE : Algebra.trdeg k E ≤ 2) : Algebra.trdeg k B ≤ 1 := by
  let f : L →ₐ[k] RatFunc L := IsScalarTower.toAlgHom k L (RatFunc L)
  let bToE : B →ₐ[k] E :=
    (IntermediateField.inclusion hmap).comp (B.equivMap f).toAlgHom
  letI : Algebra B E := bToE.toRingHom.toAlgebra
  letI : IsScalarTower k B E := IsScalarTower.of_algebraMap_eq fun c => by
    change bToE (algebraMap k B c) = algebraMap k E c
    exact bToE.commutes c
  let xE : E := ⟨RatFunc.X,hX⟩
  have hcomp : RingHom.comp (algebraMap L (RatFunc L)) B.val =
      RingHom.comp E.val (algebraMap B E) := by
    ext b
    rfl
  have hxE : Transcendental B xE :=
    (show Transcendental L (E.val xE) by
      simpa [xE] using (RatFunc.transcendental_X :
        Transcendental L (RatFunc.X : RatFunc L))).of_ringHom_of_comp_eq
      (f := B.val) (g := E.val) B.val.injective hcomp
  exact trdeg_le_one_of_tower hE ⟨xE,hxE⟩

end RationalExtension

def baseCoefficientField (P : Polynomial L) (γ : L) : IntermediateField k L :=
  IntermediateField.adjoin k
    (insert γ (Set.range (fun j : ℕ => P.coeff j)))

theorem baseCoefficientField_map_le (P : Polynomial L) (γ : L) :
    (baseCoefficientField (k := k) P γ).map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤
      coefficientField (k := k) P γ := by
  rw [IntermediateField.map_le_iff_le_comap]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases hx with h | hx
  · rw [h]
    change algebraMap L (RatFunc L) γ ∈ coefficientField (k := k) P γ
    exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
  obtain ⟨j,hj⟩ := hx
  rw [← hj]
  change algebraMap L (RatFunc L) (P.coeff j) ∈ coefficientField (k := k) P γ
  exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))

/-- A two-parameter bound on the field recovered after adding tau becomes a
one-parameter bound on the genuine coefficient field. -/
theorem baseCoefficientField_trdeg_le_one
    (P : Polynomial L) (γ : L)
    (hE : Algebra.trdeg k (coefficientField (k := k) P γ) ≤ 2) :
    Algebra.trdeg k (baseCoefficientField (k := k) P γ) ≤ 1 := by
  apply coefficient_trdeg_le_one_of_rational_extension
    (B := baseCoefficientField (k := k) P γ)
    (E := coefficientField (k := k) P γ)
    (baseCoefficientField_map_le P γ) _ hE
  exact IntermediateField.subset_adjoin k _ (Or.inl rfl)

end
end ProximityPrize.SubmissionLower.ContactCoefficientFieldTrdeg
