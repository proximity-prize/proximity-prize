import ProximityPrize.SubmissionLower.Koala6831PrimitiveLiftDegrees
import ProximityPrize.SubmissionLower.Koala6831CarrierPrime

namespace ProximityPrize.SubmissionLower.Koala6831Comparison

open MvPolynomial Koala6831Ordinary

noncomputable section

variable {K : Type*} [Field K]

private abbrev ValuePolynomial (K : Type*) [Field K] :=
  MvPolynomial (Fin 2) (SeedCoefficients K)

private def toOrdinaryIndex : (Fin 2 ⊕ Option (Fin 2)) → Fin 5
  | .inl i => ![1, 2] i
  | .inr none => 0
  | .inr (some i) => ![3, 4] i

private def fromOrdinaryIndex : Fin 5 → (Fin 2 ⊕ Option (Fin 2)) :=
  ![.inr none, .inl 0, .inl 1, .inr (some 0), .inr (some 1)]

private def coordinateEquiv : (Fin 2 ⊕ Option (Fin 2)) ≃ Fin 5 where
  toFun := toOrdinaryIndex
  invFun := fromOrdinaryIndex
  left_inv := by
    intro j
    rcases j with j | j
    · fin_cases j <;> rfl
    · cases j with
      | none => rfl
      | some j => fin_cases j <;> rfl
  right_inv := by
    intro j
    fin_cases j <;> rfl

private def unpack : ValuePolynomial K ≃+* Koala6831Ordinary.Poly K :=
  (MvPolynomial.mapEquiv (Fin 2) (MvPolynomial.optionEquivLeft K (Fin 2)).symm.toRingEquiv).trans
    ((MvPolynomial.sumRingEquiv K (Fin 2) (Option (Fin 2))).symm.trans
      (MvPolynomial.renameEquiv K coordinateEquiv).toRingEquiv)

private theorem sumEquiv_symm_constant (r : MvPolynomial (Option (Fin 2)) K) :
    (MvPolynomial.sumRingEquiv K (Fin 2) (Option (Fin 2))).symm
      (MvPolynomial.C r) = MvPolynomial.rename Sum.inr r := by
  have h :
      (MvPolynomial.sumRingEquiv K (Fin 2) (Option (Fin 2))).symm.toRingHom.comp MvPolynomial.C =
        (MvPolynomial.rename Sum.inr).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  exact RingHom.congr_fun h r

private theorem unpack_C (r : SeedCoefficients K) :
    unpack (MvPolynomial.C r) = retainCarrier (carrierOfSeedCoefficients r) := by
  have hcoord : coordinateEquiv ∘ Sum.inr =
      carrierCoordinates ∘ carrierCoefficientCoordinates := by
    funext i
    cases i with
    | none => rfl
    | some i => fin_cases i <;> rfl
  simp only [unpack, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
    sumEquiv_symm_constant]
  change MvPolynomial.renameEquiv K coordinateEquiv (MvPolynomial.rename Sum.inr
    ((MvPolynomial.optionEquivLeft K (Fin 2)).symm r)) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename, hcoord]
  unfold retainCarrier carrierOfSeedCoefficients
  rw [RingHom.comp_apply]
  exact (MvPolynomial.rename_rename _ _ _).symm

private theorem unpack_X (i : Fin 2) :
    unpack (MvPolynomial.X i : ValuePolynomial K) = MvPolynomial.X (toOrdinaryIndex (.inl i)) := by
  simp [unpack, coordinateEquiv]

private def valueRow (q : SymbolicRow (SeedRing K)) : ValuePolynomial K :=
  MvPolynomial.C q.beta + MvPolynomial.C q.first * MvPolynomial.X 0 +
    MvPolynomial.C q.second * MvPolynomial.X 1

private theorem valueRow_coeff_beta (q : SymbolicRow (SeedRing K)) :
    (valueRow q).coeff 0 = q.beta := by
  simp [valueRow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]

private theorem zero_ne_value_exponent (i : Fin 2) :
    (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 := by
  intro he
  have h := congrArg (fun e : Fin 2 →₀ ℕ => e i) he
  simp at h

private theorem valueRow_coeff_first (q : SymbolicRow (SeedRing K)) :
    (valueRow q).coeff (Finsupp.single 0 1) = q.first := by
  simp [valueRow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
    Finsupp.single_eq_single_iff, zero_ne_value_exponent]

private theorem valueRow_coeff_second (q : SymbolicRow (SeedRing K)) :
    (valueRow q).coeff (Finsupp.single 1 1) = q.second := by
  simp [valueRow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
    Finsupp.single_eq_single_iff, zero_ne_value_exponent]

private theorem valueRow_degree_one (q : SymbolicRow (SeedRing K))
    (ha : q.first ≠ 0 ∨ q.second ≠ 0) : (valueRow q).totalDegree = 1 := by
  apply le_antisymm
  · unfold valueRow
    have h₀ : (MvPolynomial.C q.first * (MvPolynomial.X 0 : ValuePolynomial K)).totalDegree ≤ 1 := by
      simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C q.first)
        (MvPolynomial.X 0 : ValuePolynomial K)
    have h₁ : (MvPolynomial.C q.second * (MvPolynomial.X 1 : ValuePolynomial K)).totalDegree ≤ 1 := by
      simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C q.second)
        (MvPolynomial.X 1 : ValuePolynomial K)
    apply (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ h₁)
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) h₀)
  · rcases ha with h₀ | h₁
    · have hs : Finsupp.single 0 1 ∈ (valueRow q).support :=
        MvPolynomial.mem_support_iff.mpr (by rwa [valueRow_coeff_first])
      simpa using MvPolynomial.le_totalDegree hs
    · have hs : Finsupp.single 1 1 ∈ (valueRow q).support :=
        MvPolynomial.mem_support_iff.mpr (by rwa [valueRow_coeff_second])
      simpa using MvPolynomial.le_totalDegree hs

theorem primitiveRowLift_prime (q : SymbolicRow (SeedRing K))
    (hp : IsPrimitiveRow q) (ha : q.first ≠ 0 ∨ q.second ≠ 0) :
    Prime (primitiveRowLift q) := by
  have hir : Irreducible (valueRow q) :=
    Koala6831CarrierPrime.irreducible_of_linear_primitive _ (valueRow_degree_one q ha) (by
      intro a hdiv
      apply hp a
      · simpa only [valueRow_coeff_beta] using hdiv 0
      · simpa only [valueRow_coeff_first] using hdiv (Finsupp.single 0 1)
      · simpa only [valueRow_coeff_second] using hdiv (Finsupp.single 1 1))
  have hq : unpack (valueRow q) = primitiveRowLift q := by
    simp only [valueRow, primitiveRowLift, comparisonRow, map_add, map_mul, unpack_C, unpack_X]
    rfl
  rw [← hq]
  exact (MulEquiv.prime_iff unpack).mpr hir.prime

end

end ProximityPrize.SubmissionLower.Koala6831Comparison
