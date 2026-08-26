import ProximityPrize.SubmissionLower.BCHKSParameters6401
import ProximityPrize.SubmissionLower.BCHKSResidual6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSLinearYKernelAudit6401
open BCHKSSubstitutionVanish
open BCHKSResidual6400
open scoped BigOperators
def n6401 : Nat := 262144
def k6401 : Nat := 131071
def a6401 : Nat := bchksAgreements6401
def multiplicity6401 : Nat := 1
def xCap6401 : Nat := 196608
def yCap6401 : Nat := 2
def zCap6401 : Nat := 65538
def residualGap6401 : Nat := 11254
def variableCountAt6401 (r : Nat) : Nat :=
  xCap6401 * (zCap6401 + r) +
    (xCap6401 - k6401) * (zCap6401 + r - 1)
def constraintCountAt6401 (r : Nat) : Nat :=
  n6401 * (zCap6401 + r)
abbrev VarIndexAt6401 (r : Nat) :=
  Σ j : Fin yCap6401,
    Fin (xCap6401 - k6401 * (j : Nat)) ×
      Fin (zCap6401 + r - (j : Nat))
abbrev ConIndexAt6401 (r : Nat) :=
  Fin n6401 × Σ t : Fin multiplicity6401,
    Fin (multiplicity6401 - (t : Nat)) ×
      Fin (zCap6401 + r - (t : Nat))
theorem concrete_index_cards_exact6401 (r : Nat) :
    Fintype.card (VarIndexAt6401 r) = variableCountAt6401 r ∧
      Fintype.card (ConIndexAt6401 r) = constraintCountAt6401 r := by
  constructor
  · rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin,
      Finset.sum_fin_eq_sum_range]
    norm_num [VarIndexAt6401, variableCountAt6401, yCap6401,
      xCap6401, k6401, zCap6401, Finset.sum_range_succ]
  · rw [Fintype.card_prod, Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin,
      Finset.sum_fin_eq_sum_range]
    norm_num [ConIndexAt6401, constraintCountAt6401,
      multiplicity6401, n6401, zCap6401]
theorem linearY_base_counts_exact6401 :
    variableCountAt6401 0 = 17180393473 ∧
      constraintCountAt6401 0 = 17180393472 ∧
      variableCountAt6401 0 = constraintCountAt6401 0 + 1 := by
  norm_num [variableCountAt6401, constraintCountAt6401,
    xCap6401, zCap6401, k6401, n6401]
theorem linearY_dimension_surplus_exact6401 (r : Nat) :
    variableCountAt6401 r = constraintCountAt6401 r + (r + 1) := by
  simp only [variableCountAt6401, constraintCountAt6401,
    xCap6401, zCap6401, k6401, n6401]
  omega
theorem linearY_support_widths_exact6401 :
    xCap6401 - k6401 = 65537 ∧
      zCap6401 - 1 = 65537 ∧
      xCap6401 - a6401 = residualGap6401 := by
  norm_num [xCap6401, k6401, zCap6401, a6401,
    bchksAgreements6401, residualGap6401]
def globalAffineGraphMultiplierDim6401 (r : Nat) : Nat :=
  (xCap6401 - k6401) * (zCap6401 + r - 1)
theorem linearY_endpoint_counts_exact6401 :
    variableCountAt6401 0 = 17180393473 ∧
      constraintCountAt6401 0 = 17180393472 ∧
      variableCountAt6401 11254 = 20130573303 ∧
      constraintCountAt6401 11254 = 20130562048 ∧
      variableCountAt6401 76790 = 37310508023 ∧
      constraintCountAt6401 76790 = 37310431232 ∧
      globalAffineGraphMultiplierDim6401 0 = 4295098369 ∧
      globalAffineGraphMultiplierDim6401 11254 = 5032651767 ∧
      globalAffineGraphMultiplierDim6401 76790 = 9327684599 := by
  norm_num [variableCountAt6401, constraintCountAt6401,
    globalAffineGraphMultiplierDim6401, xCap6401, zCap6401, k6401, n6401]
def naiveResidualKernelLower6401 (r : Nat) : Nat :=
  (r + 1) - residualGap6401
theorem naive_graphKernel_endpoints6401 :
    naiveResidualKernelLower6401 0 = 0 ∧
      naiveResidualKernelLower6401 11254 = 1 ∧
      naiveResidualKernelLower6401 76790 = 65537 := by
  norm_num [naiveResidualKernelLower6401, residualGap6401]
theorem linearY_kernel_finrank_ge6401
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (r : Nat) (T : V →ₗ[F] W)
    (hV : Module.finrank F V = variableCountAt6401 r)
    (hW : Module.finrank F W = constraintCountAt6401 r) :
    r + 1 ≤ Module.finrank F (LinearMap.ker T) := by
  have hrank : Module.finrank F (LinearMap.range T) ≤ Module.finrank F W :=
    Submodule.finrank_le _
  have hranknull := LinearMap.finrank_range_add_finrank_ker T
  rw [hW] at hrank
  rw [hV, linearY_dimension_surplus_exact6401 r] at hranknull
  omega
theorem concrete_linearY_kernel_finrank_ge6401
    {F : Type*} [Field F] (r : Nat)
    (T : (VarIndexAt6401 r → F) →ₗ[F] (ConIndexAt6401 r → F)) :
    r + 1 ≤ Module.finrank F (LinearMap.ker T) := by
  apply linearY_kernel_finrank_ge6401 r T
  · simp only [Module.finrank_fintype_fun_eq_card]
    exact (concrete_index_cards_exact6401 r).1
  · simp only [Module.finrank_fintype_fun_eq_card]
    exact (concrete_index_cards_exact6401 r).2
noncomputable def scalarShiftEval6401
    {F : Type*} [Field F] (r : Nat) (z : F) :
    (Fin (r + 1) → F) →ₗ[F] F where
  toFun c := ∑ i, c i * z ^ (i : Nat)
  map_add' c d := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
theorem scalarShiftEval_kernel_finrank_ge6401
    {F : Type*} [Field F] (r : Nat) (z : F) :
    r ≤ Module.finrank F (LinearMap.ker (scalarShiftEval6401 r z)) := by
  have hrank : Module.finrank F
      (LinearMap.range (scalarShiftEval6401 r z)) ≤ Module.finrank F F :=
    Submodule.finrank_le _
  have hranknull := LinearMap.finrank_range_add_finrank_ker
    (scalarShiftEval6401 r z)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_self] at hrank hranknull
  omega
noncomputable def scalarShiftSpecialize6401
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (r : Nat) (z : F) (q : V) : (Fin (r + 1) → F) →ₗ[F] V :=
  LinearMap.smulRight (scalarShiftEval6401 r z) q
theorem scalarShiftSpecialize_apply6401
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (r : Nat) (z : F) (q : V) (c : Fin (r + 1) → F) :
    scalarShiftSpecialize6401 r z q c =
      scalarShiftEval6401 r z c • q := by
  rfl
theorem scalarShift_twoByTwo_minor_zero6401
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (r : Nat) (z : F) (q : V) (c d : Fin (r + 1) → F)
    (f g : V →ₗ[F] F) :
    f (scalarShiftSpecialize6401 r z q c) *
        g (scalarShiftSpecialize6401 r z q d) -
      f (scalarShiftSpecialize6401 r z q d) *
        g (scalarShiftSpecialize6401 r z q c) = 0 := by
  simp only [scalarShiftSpecialize_apply6401, map_smul, smul_eq_mul]
  ring
theorem scalarShift_corrected_projective_count6401 (r : Nat) :
    (r + 1) - r = 1 := by
  omega
def quotientEntryDegreeCap6401 (r : Nat) : Nat := 65537 + r
def quotientMaximalMinorDegreeCap6401 (r : Nat) : Nat :=
  residualGap6401 * quotientEntryDegreeCap6401 r
def quotientMinorAggregateCap6401 (r : Nat) : Nat :=
  quotientMaximalMinorDegreeCap6401 r * 84607
theorem quotientMinor_endpoint_caps_exact6401 :
    quotientMaximalMinorDegreeCap6401 0 = 737553398 ∧
      quotientMaximalMinorDegreeCap6401 11254 = 864205914 ∧
      quotientMaximalMinorDegreeCap6401 76790 = 1601748058 ∧
      quotientMinorAggregateCap6401 0 = 62402180344586 ∧
      quotientMinorAggregateCap6401 11254 = 73117869765798 ∧
      quotientMinorAggregateCap6401 76790 = 135519097943206 := by
  norm_num [quotientMaximalMinorDegreeCap6401,
    quotientEntryDegreeCap6401, quotientMinorAggregateCap6401,
    residualGap6401]
theorem quotientMinor_conditional_fieldBudget6401 :
    quotientMinorAggregateCap6401 76790 +
        1688975428 + 442776953815040 = 578297740733674 ∧
      quotientMinorAggregateCap6401 76790 +
          1688975428 + 442776953815040 < 274980700000000000 ∧
      274980700000000000 -
          (quotientMinorAggregateCap6401 76790 +
            1688975428 + 442776953815040) = 274402402259266326 := by
  norm_num [quotientMinorAggregateCap6401,
    quotientMaximalMinorDegreeCap6401, quotientEntryDegreeCap6401,
    residualGap6401]
theorem exists_linearY_locator_residual6401
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (omega : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F)
    (hA : a6401 ≤ A.card)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < multiplicity6401 →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (omega i))
        (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ k6401)
    (hcap : ∀ j x, ((Q.coeff j).coeff x) ≠ 0 →
      x + k6401 * j < xCap6401) :
    ∃ E : Polynomial F,
      triEval Q z P =
        (∏ i ∈ A, (Polynomial.X - Polynomial.C (omega i))) * E ∧
      E.natDegree ≤ 11253 := by
  obtain ⟨E, hfac, hE⟩ := exists_triEval_locator_residual
    Q z P omega A yZ multiplicity6401 k6401 xCap6401 residualGap6401
    (by norm_num [xCap6401]) (by norm_num [residualGap6401])
    hvan hmatch hP hcap (by
      norm_num [multiplicity6401, a6401, bchksAgreements6401,
        xCap6401, residualGap6401] at hA ⊢
      omega)
  refine ⟨E, ?_, by norm_num [residualGap6401] at hE ⊢; omega⟩
  simpa [multiplicity6401] using hfac
theorem exists_linearY_locator_residual_of_support6401
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (omega : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F)
    (hA : a6401 ≤ A.card)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < multiplicity6401 →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (omega i))
        (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ k6401)
    (hsupport : ∀ j x, ((Q.coeff j).coeff x) ≠ 0 →
      j < yCap6401 ∧ x + k6401 * j < xCap6401 ∧
        ((Q.coeff j).coeff x).natDegree + j < zCap6401) :
    ∃ E : Polynomial F,
      triEval Q z P =
        (∏ i ∈ A, (Polynomial.X - Polynomial.C (omega i))) * E ∧
      E.natDegree ≤ 11253 := by
  exact exists_linearY_locator_residual6401 Q z P omega A yZ hA hvan hmatch hP
    (fun j x hx ↦ (hsupport j x hx).2.1)
end BCHKSLinearYKernelAudit6401
end ProximityPrize.SubmissionLower
