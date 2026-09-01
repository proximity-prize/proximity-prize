import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.R7
import ProximityPrize.SubmissionLower.X3
import ProximityPrize.SubmissionLower.X7

namespace ProximityPrize.SubmissionLower.GlobalShearSumPrototype

open scoped Classical BigOperators
open RCN001 RCN002 RCN005 RCN006 RCN007 RCN008 RCN009 RCN011 RCN013 RCN022
open RCN023 RCN045 RCN264 RCN351 RCN371 RCN372 RCN021

noncomputable section

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]

def shearEvaluation
    (a : Omega)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] :
    MvPolynomial (Fin 3) Omega →ₐ[Omega] CoordinateField Omega P :=
  (coordinateEvaluation Omega P).comp (unshearAlgHom a)

@[simp] theorem shearEvaluation_X_zero
    (a : Omega)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] :
    shearEvaluation a P (MvPolynomial.X 0) = coordinate Omega P 0 := by
  simp [shearEvaluation, unshearImage, coordinate, Algebra.smul_def]

@[simp] theorem shearEvaluation_X_one
    (a : Omega)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] :
    shearEvaluation a P (MvPolynomial.X 1) =
      coordinate Omega P 1 + a • coordinate Omega P 2 := by
  simp [shearEvaluation, unshearImage, coordinate, Algebra.smul_def]

@[simp] theorem shearEvaluation_X_two
    (a : Omega)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] :
    shearEvaluation a P (MvPolynomial.X 2) = coordinate Omega P 2 := by
  simp [shearEvaluation, unshearImage, coordinate]

theorem shearEvaluation_shear
    (a : Omega)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (F : MvPolynomial (Fin 3) Omega) :
    shearEvaluation a P (shearAlgHom a F) =
      coordinateEvaluation Omega P F := by
  have hcomp := unshear_comp_shear a
  change coordinateEvaluation Omega P
      (((unshearAlgHom a).comp
        (shearAlgHom a)) F) = _
  rw [hcomp]
  rfl

theorem shearEvaluation_ker
    (a : Omega)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] :
    RingHom.ker (shearEvaluation a P).toRingHom =
      P.comap (unshearAlgHom a).toRingHom := by
  change RingHom.ker
      ((coordinateEvaluation Omega P).toRingHom.comp
        (unshearAlgHom a).toRingHom) = _
  rw [← RingHom.comap_ker, coordinateEvaluation_ker]

theorem unshear_surjective (a : Omega) :
    Function.Surjective (unshearAlgHom a) := by
  intro F
  refine ⟨shearAlgHom a F, ?_⟩
  have h := DFunLike.congr_fun (unshear_comp_shear a) F
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h

theorem shearEvaluation_kernel_family_injective
    {I : Type} [Fintype I]
    (a : Omega)
    (Q : I → Ideal (MvPolynomial (Fin 3) Omega))
    [∀ i, (Q i).IsPrime]
    (hinj : Function.Injective Q) :
    Function.Injective (fun i ↦ RingHom.ker (shearEvaluation a (Q i)).toRingHom) := by
  intro i j hij
  apply hinj
  change RingHom.ker (shearEvaluation a (Q i)).toRingHom =
    RingHom.ker (shearEvaluation a (Q j)).toRingHom at hij
  rw [shearEvaluation_ker a (Q i), shearEvaluation_ker a (Q j)] at hij
  exact Ideal.comap_injective_of_surjective
    (unshearAlgHom a).toRingHom (unshear_surjective a) hij

theorem shearEvaluation_generators
    (a : Omega)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hS : Transcendental Omega
      (coordinate Omega P 1 + a • coordinate Omega P 2)) :
    let hbase : Transcendental Omega
        (shearEvaluation a P (MvPolynomial.X 1)) := by simpa
    letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
      (elementEmbedding Omega (CoordinateField Omega P)
        (shearEvaluation a P (MvPolynomial.X 1)) hbase).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc Omega)
      ({shearEvaluation a P (MvPolynomial.X 2),
        shearEvaluation a P (MvPolynomial.X 0)} :
        Set (CoordinateField Omega P)) = ⊤ := by
  let hbase : Transcendental Omega
      (shearEvaluation a P (MvPolynomial.X 1)) := by simpa
  letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
    (elementEmbedding Omega (CoordinateField Omega P)
      (shearEvaluation a P (MvPolynomial.X 1)) hbase).toRingHom.toAlgebra
  let S : IntermediateField (RatFunc Omega) (CoordinateField Omega P) :=
    IntermediateField.adjoin (RatFunc Omega)
      ({shearEvaluation a P (MvPolynomial.X 2),
        shearEvaluation a P (MvPolynomial.X 0)} :
        Set (CoordinateField Omega P))
  have hzero : coordinate Omega P 0 ∈ S := by
    simpa [S] using IntermediateField.mem_adjoin_pair_right
      (RatFunc Omega)
      (shearEvaluation a P (MvPolynomial.X 2))
      (shearEvaluation a P (MvPolynomial.X 0))
  have htwo : coordinate Omega P 2 ∈ S := by
    simpa [S] using IntermediateField.mem_adjoin_pair_left
      (RatFunc Omega)
      (shearEvaluation a P (MvPolynomial.X 2))
      (shearEvaluation a P (MvPolynomial.X 0))
  have hsum : coordinate Omega P 1 + a • coordinate Omega P 2 ∈ S := by
    have hmem := S.algebraMap_mem
      (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)
    change elementEmbedding Omega (CoordinateField Omega P)
        (shearEvaluation a P (MvPolynomial.X 1)) hbase
          (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X) ∈ S at hmem
    rw [elementEmbedding_variable] at hmem
    simpa using hmem
  have hone : coordinate Omega P 1 ∈ S := by
    have haZ : a • coordinate Omega P 2 ∈ S := by
      have h := S.mul_mem
        (S.algebraMap_mem (algebraMap Omega (RatFunc Omega) a)) htwo
      simpa only [Algebra.smul_def, ← IsScalarTower.algebraMap_apply] using h
    have := S.sub_mem hsum haZ
    simpa using this
  have hcoords : Set.range (coordinate Omega P) ⊆ S.restrictScalars Omega := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hzero
    · exact hone
    · exact htwo
  have htop : S.restrictScalars Omega = ⊤ := by
    apply top_unique
    rw [← adjoin_coordinates_eq_top Omega P]
    exact IntermediateField.adjoin_le_iff.mpr hcoords
  exact (IntermediateField.restrictScalars_eq_top_iff.mp htop)

theorem sheared_originalMixedDegree_le_R_add_Z
    (a : Omega)
    (G T : MvPolynomial (Fin 3) Omega) :
    originalMixedDegree Omega (Equiv.swap (0 : Fin 3) 1)
        (shearAlgHom a G) (shearAlgHom a T) ≤
      coordinateMixedDegree Omega G T 1 +
        coordinateMixedDegree Omega G T 2 := by
  rw [coordinateMixedDegree_one, coordinateMixedDegree_two]
  change
    (shearAlgHom a T).degreeOf 0 *
          (shearAlgHom a G).degreeOf 2 +
        (shearAlgHom a G).degreeOf 0 *
          (shearAlgHom a T).degreeOf 2 ≤
      (T.degreeOf 0 * G.degreeOf 2 + G.degreeOf 0 * T.degreeOf 2) +
        (T.degreeOf 0 * G.degreeOf 1 + G.degreeOf 0 * T.degreeOf 1)
  have hT0 := shear_degreeOf_zero_le a T
  have hG0 := shear_degreeOf_zero_le a G
  have hT2 := shear_degreeOf_two_le a T
  have hG2 := shear_degreeOf_two_le a G
  calc
    _ ≤ T.degreeOf 0 * (G.degreeOf 2 + G.degreeOf 1) +
          G.degreeOf 0 * (T.degreeOf 2 + T.degreeOf 1) :=
      Nat.add_le_add (Nat.mul_le_mul hT0 hG2) (Nat.mul_le_mul hG0 hT2)
    _ = _ := by ring

theorem sheared_family_finite_and_sum_finrank
    {I : Type} [Fintype I]
    (a : Omega)
    (Q : I → Ideal (MvPolynomial (Fin 3) Omega))
    [∀ i, (Q i).IsPrime]
    (hinj : Function.Injective Q)
    (G T : MvPolynomial (Fin 3) Omega)
    (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i)
    (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T)
    (hS : ∀ i, Transcendental Omega
      (coordinate Omega (Q i) 1 + a • coordinate Omega (Q i) 2)) :
    let hbase : ∀ i, Transcendental Omega
        (shearEvaluation a (Q i) (MvPolynomial.X 1)) := fun i ↦ by
          simpa using hS i
    letI : ∀ i, Algebra (RatFunc Omega) (CoordinateField Omega (Q i)) :=
      fun i ↦ (elementEmbedding Omega (CoordinateField Omega (Q i))
        (shearEvaluation a (Q i) (MvPolynomial.X 1))
        (hbase i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc Omega) (CoordinateField Omega (Q i))) ∧
      (∑ i, Module.finrank (RatFunc Omega) (CoordinateField Omega (Q i))) ≤
        coordinateMixedDegree Omega G T 1 +
          coordinateMixedDegree Omega G T 2 := by
  classical
  let hbase : ∀ i, Transcendental Omega
      (shearEvaluation a (Q i) (MvPolynomial.X 1)) := fun i ↦ by
    simpa using hS i
  letI : ∀ i, Algebra (RatFunc Omega) (CoordinateField Omega (Q i)) :=
    fun i ↦ (elementEmbedding Omega (CoordinateField Omega (Q i))
      (shearEvaluation a (Q i) (MvPolynomial.X 1))
      (hbase i)).toRingHom.toAlgebra
  let initial : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
  let E : I → Type := fun i ↦ CoordinateField Omega (Q i)
  let e : ∀ i, MvPolynomial (Fin 3) Omega →ₐ[Omega] E i :=
    fun i ↦ shearEvaluation a (Q i)
  let GS := shearAlgHom a G
  let TS := shearAlgHom a T
  have hGS : Irreducible GS := by
    exact (shear_irreducible_iff a G).2 hG
  have hproperS : ¬ GS ∣ TS := by
    simpa only [GS, TS, shear_dvd_iff] using hproper
  have hrootG : ∀ i, e i GS = 0 := by
    intro i
    rw [show e i GS = coordinateEvaluation Omega (Q i) G by
      simpa only [e, GS] using shearEvaluation_shear a (Q i) G]
    change G ∈ RingHom.ker (coordinateEvaluation Omega (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hGmem i
  have hrootT : ∀ i, e i TS = 0 := by
    intro i
    rw [show e i TS = coordinateEvaluation Omega (Q i) T by
      simpa only [e, TS] using shearEvaluation_shear a (Q i) T]
    change T ∈ RingHom.ker (coordinateEvaluation Omega (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hTmem i
  have hkernels : Function.Injective
      (fun i ↦ RingHom.ker (e i).toRingHom) := by
    simpa only [e] using shearEvaluation_kernel_family_injective a Q hinj
  have htInitial : ∀ i,
      Transcendental Omega (e i (MvPolynomial.X (initial 0))) := by
    intro i
    simpa only [initial, Equiv.swap_apply_left, e] using hbase i
  have hgenInitial : ∀ i,
      IntermediateField.adjoin (RatFunc Omega)
        ({e i (MvPolynomial.X (initial 2)),
          e i (MvPolynomial.X (initial 1))} : Set (E i)) = ⊤ := by
    intro i
    have htwo : initial (2 : Fin 3) = 2 := by
      simp [initial, Equiv.swap_apply_def]
    have hone : initial (1 : Fin 3) = 0 := by
      simp [initial, Equiv.swap_apply_def]
    simpa only [htwo, hone, e, E] using
        shearEvaluation_generators a (Q i) (hS i)
  by_cases hI : Nonempty I
  · let i0 : I := Classical.choice hI
    have hirr := rationalMap_irreducible_of_evaluation
      Omega (E i0) initial (e i0) GS hGS (hrootG i0) (htInitial i0)
    rcases positive_degree_of_irreducible (rationalMap Omega initial GS) hirr with
      houter | hinner
    · have hpositive : 0 < (planeMap Omega initial GS).natDegree := by
        change 0 < (bivariateEquiv (RatFunc Omega)
          (rationalMap Omega initial GS)).natDegree
        rwa [bivariateEquiv_natDegree]
      have hbound := finite_sum_finrank_bound Omega initial E e htInitial
        hgenInitial hkernels GS TS hGS hrootG hrootT hproperS hpositive
      refine ⟨hbound.1, hbound.2.trans ?_⟩
      exact (plane_budget_le_original Omega initial GS TS).trans
        (by simpa only [initial, GS, TS] using
          sheared_originalMixedDegree_le_R_add_Z a G T)
    · let order := swapOtherOrder initial
      have hpositive : 0 < (planeMap Omega order GS).natDegree := by
        dsimp only [order]
        rwa [swapped_outer_degree]
      have htOrder : ∀ i,
          Transcendental Omega (e i (MvPolynomial.X (order 0))) := by
        intro i
        simpa only [order, swapOtherOrder_zero] using htInitial i
      have hgenOrder : ∀ i,
          IntermediateField.adjoin (RatFunc Omega)
            ({e i (MvPolynomial.X (order 2)),
              e i (MvPolynomial.X (order 1))} : Set (E i)) = ⊤ := by
        intro i
        simpa only [order, swapOtherOrder_one, swapOtherOrder_two,
          Set.pair_comm] using hgenInitial i
      have hbound := finite_sum_finrank_bound Omega order E e htOrder
        hgenOrder hkernels GS TS hGS hrootG hrootT hproperS hpositive
      refine ⟨hbound.1, hbound.2.trans ?_⟩
      exact (plane_budget_le_original Omega order GS TS).trans
        ((originalMixedDegree_swap Omega initial GS TS).le.trans
          (by simpa only [initial, GS, TS] using
            sheared_originalMixedDegree_le_R_add_Z a G T))
  · letI : IsEmpty I := ⟨fun i ↦ hI ⟨i⟩⟩
    exact ⟨fun i ↦ isEmptyElim i, by simp⟩

section CommonRegularShear

variable {G T H : MvPolynomial (Fin 3) Omega}

theorem coordinate_finite_separable_of_single_mixed_gate
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (p : ℕ) [CharP Omega p]
    (G T : MvPolynomial (Fin 3) Omega)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P)
    (hproper : ¬ G ∣ T)
    (hGdegree : ∀ k : Fin 3, G.degreeOf k < p)
    (j : Fin 3)
    (hmixed : coordinateMixedDegree Omega G T j < p)
    (hj : Transcendental Omega (coordinate Omega P j)) :
    letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
      rationalBaseAlgebra Omega P j hj
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) ∧
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) := by
  let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 j
  have ht : Transcendental Omega (coordinate Omega P (order 0)) := by
    simpa only [order, Equiv.swap_apply_left] using hj
  have hresult := RCN004.original_finite_separable_finrank_bound
    Omega order P ht p G T hG hGmem hTmem hproper
    (hGdegree (order 1)) (hGdegree (order 2))
    (by simpa only [coordinateMixedDegree] using hmixed)
  simpa only [order, Equiv.swap_apply_left] using ⟨hresult.1, hresult.2.1⟩

def ProjectionSeparableAt
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (j : Fin 3) : Prop :=
  ∀ h : Transcendental Omega (coordinate Omega P j),
    letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
      rationalBaseAlgebra Omega P j h
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)

structure CommonRegularShearData
    (hfinite : ∀ C : RegularComponent Omega G T H,
      ProjectionsFinite Omega C.1)
    (hsepZ : ∀ C : RegularComponent Omega G T H,
      ProjectionSeparableAt C.1 2) where
  coeff : Omega
  coeff_ne : coeff ≠ 0
  shear_transcendental : ∀ (C : RegularComponent Omega G T H)
    (hZ : Transcendental Omega (coordinate Omega C.1 2)),
      Transcendental Omega
        (coordinate Omega C.1 1 + coeff • coordinate Omega C.1 2)
  shear_finite : ∀ (C : RegularComponent Omega G T H)
    (hZ : Transcendental Omega (coordinate Omega C.1 2)),
      let hS := shear_transcendental C hZ
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 1 + coeff • coordinate Omega C.1 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)
  shear_separable : ∀ (C : RegularComponent Omega G T H)
    (hZ : Transcendental Omega (coordinate Omega C.1 2)),
      let hS := shear_transcendental C hZ
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 1 + coeff • coordinate Omega C.1 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)

theorem exists_commonRegularShearData
    (hfinite : ∀ C : RegularComponent Omega G T H,
      ProjectionsFinite Omega C.1)
    (hsepZ : ∀ C : RegularComponent Omega G T H,
      ProjectionSeparableAt C.1 2) :
    Nonempty (CommonRegularShearData hfinite hsepZ) := by
  classical
  let I := {C : RegularComponent Omega G T H //
    Transcendental Omega (coordinate Omega C.1 2)}
  let E : I → Type := fun C ↦ CoordinateField Omega C.1.1
  let r : ∀ C : I, E C := fun C ↦ coordinate Omega C.1.1 1
  let z : ∀ C : I, E C := fun C ↦ coordinate Omega C.1.1 2
  let embeddingZ : ∀ C : I, RatFunc Omega →ₐ[Omega] E C := fun C ↦
    rationalBaseEmbedding Omega C.1.1 2 C.2
  have hvalueZ : ∀ C : I, embeddingZ C
      (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X) = z C := by
    intro C
    exact rationalBaseEmbedding_polynomial Omega C.1.1 2 C.2 Polynomial.X
      |>.trans (Polynomial.aeval_X _)
  have hfiniteZ : ∀ C : I,
      letI : Algebra (RatFunc Omega) (E C) :=
        (embeddingZ C).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (E C) := by
    intro C
    exact hfinite C.1 2 C.2
  have hseparableZ : ∀ C : I,
      letI : Algebra (RatFunc Omega) (E C) :=
        (embeddingZ C).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (E C) := by
    intro C
    exact hsepZ C.1 C.2
  obtain ⟨a, ha0, hdata⟩ :=
    exists_common_finite_separable_shear Omega E r z
      embeddingZ hvalueZ hfiniteZ hseparableZ
  let hS : ∀ (C : RegularComponent Omega G T H)
      (hZ : Transcendental Omega (coordinate Omega C.1 2)),
        Transcendental Omega
          (coordinate Omega C.1 1 + a • coordinate Omega C.1 2) :=
    fun C hZ ↦ Classical.choose (hdata (⟨C, hZ⟩ : I))
  refine ⟨⟨a, ha0, hS, ?_, ?_⟩⟩
  · intro C hZ
    have hp : hS C hZ =
        Classical.choose (hdata (⟨C, hZ⟩ : I)) := Subsingleton.elim _ _
    cases hp
    simpa only [E, r, z, hS] using!
      (Classical.choose_spec (hdata (⟨C, hZ⟩ : I))).1
  · intro C hZ
    have hp : hS C hZ =
        Classical.choose (hdata (⟨C, hZ⟩ : I)) := Subsingleton.elim _ _
    cases hp
    simpa only [E, r, z, hS] using!
      (Classical.choose_spec (hdata (⟨C, hZ⟩ : I))).2

def commonShearDegree
    {hfinite : ∀ C : RegularComponent Omega G T H,
      ProjectionsFinite Omega C.1}
    {hsepZ : ∀ C : RegularComponent Omega G T H,
      ProjectionSeparableAt C.1 2}
    (D : CommonRegularShearData hfinite hsepZ)
    (C : RegularComponent Omega G T H) : ℕ :=
  if hZ : Transcendental Omega (coordinate Omega C.1 2) then
    let hbase : Transcendental Omega
        (shearEvaluation D.coeff C.1 (MvPolynomial.X 1)) := by
      simpa using D.shear_transcendental C hZ
    letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
      (elementEmbedding Omega (CoordinateField Omega C.1)
        (shearEvaluation D.coeff C.1 (MvPolynomial.X 1))
        hbase).toRingHom.toAlgebra
    Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)
  else 0

theorem commonShearDegree_of_transcendental
    {hfinite : ∀ C : RegularComponent Omega G T H,
      ProjectionsFinite Omega C.1}
    {hsepZ : ∀ C : RegularComponent Omega G T H,
      ProjectionSeparableAt C.1 2}
    (D : CommonRegularShearData hfinite hsepZ)
    (C : RegularComponent Omega G T H)
    (hZ : Transcendental Omega (coordinate Omega C.1 2)) :
    commonShearDegree D C =
      (let hbase : Transcendental Omega
          (shearEvaluation D.coeff C.1 (MvPolynomial.X 1)) := by
            simpa using D.shear_transcendental C hZ
       letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (shearEvaluation D.coeff C.1 (MvPolynomial.X 1))
           hbase).toRingHom.toAlgebra
       Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)) := by
  simp only [commonShearDegree, dif_pos hZ]

theorem sum_commonShearDegree_le
    (G T H : MvPolynomial (Fin 3) Omega)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hfinite : ∀ C : RegularComponent Omega G T H,
      ProjectionsFinite Omega C.1)
    (hsepZ : ∀ C : RegularComponent Omega G T H,
      ProjectionSeparableAt C.1 2)
    (D : CommonRegularShearData hfinite hsepZ) :
    (∑ C : RegularComponent Omega G T H, commonShearDegree D C) ≤
      coordinateMixedDegree Omega G T 1 +
        coordinateMixedDegree Omega G T 2 := by
  classical
  let s : Set (RegularComponent Omega G T H) :=
    {C | Transcendental Omega (coordinate Omega C.1 2)}
  let d : s → ℕ := fun C ↦
    let hbase : Transcendental Omega
        (shearEvaluation D.coeff C.1.1 (MvPolynomial.X 1)) := by
      simpa using D.shear_transcendental C.1 C.2
    letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1.1) :=
      (elementEmbedding Omega (CoordinateField Omega C.1.1)
        (shearEvaluation D.coeff C.1.1 (MvPolynomial.X 1))
        hbase).toRingHom.toAlgebra
    Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)
  have hinj : Function.Injective (fun C : s ↦ C.1.1) := by
    intro C E h
    apply Subtype.ext
    exact Subtype.ext h
  have hbound := sheared_family_finite_and_sum_finrank D.coeff
    (Q := fun C : s ↦ C.1.1) hinj G T hG
    (fun C ↦ regularComponent_G_mem Omega G T H C.1)
    (fun C ↦ regularComponent_T_mem Omega G T H C.1) hproper
    (fun C ↦ D.shear_transcendental C.1 C.2)
  change
    (∀ C : s,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1.1)
          (shearEvaluation D.coeff C.1.1 (MvPolynomial.X 1))
          (by simpa using D.shear_transcendental C.1 C.2)).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1.1)) ∧
    (∑ C : s, d C) ≤ coordinateMixedDegree Omega G T 1 +
      coordinateMixedDegree Omega G T 2 at hbound
  calc
    (∑ C : RegularComponent Omega G T H, commonShearDegree D C) =
        ∑ C : s, d C := by
      apply Finset.sum_congr_set s (fun C ↦ commonShearDegree D C) d
      · intro C hC
        exact commonShearDegree_of_transcendental D C hC
      · intro C hC
        change ¬ Transcendental Omega (coordinate Omega C.1 2) at hC
        exact dif_neg hC
    _ ≤ _ := hbound.2

end CommonRegularShear

end

end ProximityPrize.SubmissionLower.GlobalShearSumPrototype
