import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneCharacteristicFreeFamilyDegree
import ProximityPrize.SubmissionLower.PlaneFunctionFieldDegree
import ProximityPrize.SubmissionLower.PlaneCoefficientExtension
import ProximityPrize.SubmissionLower.PlaneSmallCharacteristicDegree

/-!
# Characteristic-free planar degree for an actual finite root family

The family is grouped by the minimal polynomial of its first generator.
Each group is represented canonically by the corresponding `AdjoinRoot`;
relative relation kernels remain distinct and CRT supplies the summed
relative power-basis bound.  The grouped determinant theorem then charges
the complete family degree to one resultant.
-/

namespace ProximityPrize.SubmissionLower.PlaneCharacteristicFreeFamilyRoots

open scoped Classical BigOperators
open PlaneFunctionFieldDegree

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

variable (K : Type) [Field K]
variable {I : Type} [Fintype I]
variable (E : I → Type) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
variable [∀ i, FiniteDimensional K (E i)]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem sum_finrank_le_resultant_natDegree
    (y r : ∀ i, E i)
    (hgenerate : ∀ i,
      IntermediateField.adjoin K ({y i, r i} : Set (E i)) = ⊤)
    (hkernels : Function.Injective
      (fun i ↦ relationIdeal K (E i) (y i) (r i)))
    (P Q : Polynomial (Polynomial K))
    (hPirr : Irreducible P) (hPpos : 0 < P.natDegree)
    (hPy : ∀ i, planeEval K (E i) (y i) (r i) P = 0)
    (hQy : ∀ i, planeEval K (E i) (y i) (r i) Q = 0)
    (hres : Polynomial.resultant P Q P.natDegree Q.natDegree ≠ 0) :
    (∑ i, Module.finrank K (E i)) ≤
      (Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree := by
  classical
  let μ : I → Polynomial K := fun i ↦ minpoly K (y i)
  let mus : Finset (Polynomial K) := Finset.univ.image μ
  let J := {f : Polynomial K // f ∈ mus}
  letI : Fintype J := Fintype.ofFinset mus (fun _ ↦ Iff.rfl)
  letI : DecidableEq J := Classical.decEq J
  let rep : J → I := fun j ↦ (Finset.mem_image.mp j.property).choose
  have hrep (j : J) : μ (rep j) = j.1 :=
    (Finset.mem_image.mp j.property).choose_spec.2
  have hyint (i : I) : IsIntegral K (y i) :=
    Algebra.IsIntegral.isIntegral (y i)
  have hμirr (j : J) : Irreducible j.1 := by
    rw [← hrep j]
    exact minpoly.irreducible (hyint (rep j))
  have hμmonic (j : J) : j.1.Monic := by
    rw [← hrep j]
    exact minpoly.monic (hyint (rep j))
  letI hfact (j : J) : Fact (Irreducible j.1) := ⟨hμirr j⟩
  let A : J → Type := fun j ↦ AdjoinRoot j.1
  let x : ∀ j, A j := fun j ↦ AdjoinRoot.root j.1
  let group : I → J := fun i ↦
    ⟨μ i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let Fib : J → Type := fun j ↦ {i : I // group i = j}
  letI (j : J) : Fintype (Fib j) := Fintype.ofFinite (Fib j)
  letI (j : J) : DecidableEq (Fib j) := Classical.decEq (Fib j)
  let EE : ∀ j, Fib j → Type := fun _ i ↦ E i.1
  let yy : ∀ j (i : Fib j), EE j i := fun _ i ↦ r i.1
  let toE : ∀ j (i : Fib j), A j →ₐ[K] EE j i := fun j i ↦
    AdjoinRoot.liftAlgHom j.1 (Algebra.ofId K (E i.1)) (y i.1) (by
      change Polynomial.aeval (y i.1) j.1 = 0
      calc
        Polynomial.aeval (y i.1) j.1 =
            Polynomial.aeval (y i.1) (μ i.1) :=
          congrArg _ (congrArg Subtype.val i.2).symm
        _ = 0 := minpoly.aeval K (y i.1))
  letI algAE (j : J) (i : Fib j) : Algebra (A j) (EE j i) :=
    (toE j i).toRingHom.toAlgebra
  letI towerAE (j : J) (i : Fib j) : IsScalarTower K (A j) (EE j i) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (toE j i).commutes a |>.symm
  have htoEroot (j : J) (i : Fib j) :
      algebraMap (A j) (EE j i) (x j) = y i.1 := by
    exact AdjoinRoot.liftAlgHom_root j.1 (Algebra.ofId K (E i.1))
      (y i.1) _
  let specialize (j : J) : Polynomial (Polynomial K) →+* Polynomial (A j) :=
    Polynomial.mapRingHom (Polynomial.eval₂RingHom (algebraMap K (A j)) (x j))
  have hspecialize (j : J) (i : Fib j) (R : Polynomial (Polynomial K)) :
      Polynomial.eval₂ (algebraMap (A j) (EE j i)) (r i.1)
        (specialize j R) = planeEval K (E i.1) (y i.1) (r i.1) R := by
    change Polynomial.eval₂ (algebraMap (A j) (E i.1)) (r i.1)
      (R.map (Polynomial.eval₂RingHom (algebraMap K (A j)) (x j))) = _
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂
      ((algebraMap (A j) (E i.1)).comp
        (Polynomial.eval₂RingHom (algebraMap K (A j)) (x j)))
      (r i.1) R = _
    have hcoeff : (algebraMap (A j) (E i.1)).comp
        (Polynomial.eval₂RingHom (algebraMap K (A j)) (x j)) =
        Polynomial.eval₂RingHom (algebraMap K (E i.1)) (y i.1) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C]
        exact (IsScalarTower.algebraMap_apply K (A j) (E i.1) a).symm
      · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_X]
        exact htoEroot j i
    rw [hcoeff]
    exact (PlaneSmallCharacteristicDegree.planeEval_eq_eval₂
      K (E i.1) (y i.1) (r i.1) R).symm
  have hPspec_ne (j : J) : specialize j P ≠ 0 := by
    have h := PlaneCoefficientExtension.bimap_specialization_ne_zero
      (algebraMap K (A j)) P
      (hPirr.isPrimitive (Nat.ne_of_gt hPpos)) (x j)
    rw [PlaneCoefficientExtension.bimap_specialization] at h
    exact h
  have hrint (j : J) (i : Fib j) : IsIntegral (A j) (r i.1) := by
    refine IsAlgebraic.isIntegral ⟨specialize j P, hPspec_ne j, ?_⟩
    exact (hspecialize j i P).trans (hPy i.1)
  have htop (j : J) (i : Fib j) :
      IntermediateField.adjoin (A j) ({r i.1} : Set (E i.1)) = ⊤ := by
    apply top_unique
    intro z _
    have hz : z ∈ IntermediateField.adjoin K
        ({y i.1, r i.1} : Set (E i.1)) := by rw [hgenerate i.1]; trivial
    exact IntermediateField.adjoin_induction K
      (p := fun z _ ↦ z ∈ IntermediateField.adjoin (A j) {r i.1})
      (fun z hz ↦ by
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · rw [← htoEroot j i]
          exact (bot_le : (⊥ : IntermediateField (A j) (E i.1)) ≤ _)
            (IntermediateField.algebraMap_mem _ _)
        · have : z = r i.1 := Set.mem_singleton_iff.mp hz
          subst z
          exact IntermediateField.subset_adjoin (A j) {r i.1}
            (Set.mem_singleton _))
      (fun a ↦ by
        rw [IsScalarTower.algebraMap_apply K (A j) (E i.1)]
        exact (bot_le : (⊥ : IntermediateField (A j) (E i.1)) ≤ _)
          (IntermediateField.algebraMap_mem _ _))
      (fun _ _ _ _ ha hb ↦ add_mem ha hb)
      (fun _ _ ha ↦ inv_mem ha)
      (fun _ _ _ _ ha hb ↦ mul_mem ha hb) hz
  let eTop (j : J) (i : Fib j) :
      IntermediateField.adjoin (A j) {r i.1} ≃ₐ[A j] E i.1 :=
    (IntermediateField.equivOfEq (htop j i)).trans IntermediateField.topEquiv
  let pbA (j : J) : PowerBasis K (A j) :=
    AdjoinRoot.powerBasis (hμirr j).ne_zero
  let pbE (j : J) (i : Fib j) : PowerBasis (A j) (EE j i) :=
    (IntermediateField.adjoin.powerBasis (hrint j i)).map (eTop j i)
  letI fdA (j : J) : FiniteDimensional K (A j) := (pbA j).finite
  letI fdAdjoin (j : J) (i : Fib j) :
      FiniteDimensional (A j) (IntermediateField.adjoin (A j) {r i.1}) :=
    IntermediateField.adjoin.finiteDimensional (hrint j i)
  letI fdE (j : J) (i : Fib j) : FiniteDimensional (A j) (EE j i) :=
    Module.Finite.of_surjective (eTop j i).toLinearMap (eTop j i).surjective
  have hgenA (j : J) : (pbA j).gen = x j := by rfl
  have hgenE (j : J) (i : Fib j) : (pbE j i).gen = yy j i := by
    simp only [pbE, yy, PowerBasis.map_gen,
      IntermediateField.adjoin.powerBasis_gen]
    rfl
  have hrelativeKernels (j : J) : Function.Injective (fun i : Fib j ↦
      RingHom.ker (Polynomial.eval₂RingHom
        (algebraMap (A j) (EE j i)) (yy j i))) := by
    intro i k hik
    apply Subtype.ext
    apply hkernels
    apply Ideal.ext
    intro R
    change planeEval K (E i.1) (y i.1) (r i.1) R = 0 ↔
      planeEval K (E k.1) (y k.1) (r k.1) R = 0
    rw [← hspecialize j i R, ← hspecialize j k R]
    constructor
    · intro hm
      change specialize j R ∈ (fun i : Fib j ↦ RingHom.ker
        (Polynomial.eval₂RingHom (algebraMap (A j) (EE j i)) (yy j i))) i at hm
      rw [hik] at hm
      exact hm
    · intro hm
      change specialize j R ∈ (fun i : Fib j ↦ RingHom.ker
        (Polynomial.eval₂RingHom (algebraMap (A j) (EE j i)) (yy j i))) k at hm
      rw [← hik] at hm
      exact hm
  have hrelativeDim (j : J) : (∑ i : Fib j, (pbE j i).dim) ≤
      P.natDegree + Q.natDegree := by
    let mpoly : Fib j → Polynomial (A j) :=
      fun i ↦ minpoly (A j) (r i.1)
    have hpair : Pairwise (fun i k ↦ IsCoprime (mpoly i) (mpoly k)) := by
      intro i k hik
      have hiirr : Irreducible (mpoly i) := minpoly.irreducible (hrint j i)
      have hkirr : Irreducible (mpoly k) := minpoly.irreducible (hrint j k)
      by_contra hcop
      have hdvd : mpoly i ∣ mpoly k :=
        hiirr.dvd_iff_not_isCoprime.mpr hcop
      have hassoc := hiirr.associated_of_dvd hkirr hdvd
      have heq : mpoly i = mpoly k :=
        Polynomial.eq_of_monic_of_associated
          (minpoly.monic (hrint j i)) (minpoly.monic (hrint j k)) hassoc
      apply hik
      apply hrelativeKernels j
      change RingHom.ker (Polynomial.aeval (r i.1)) =
        RingHom.ker (Polynomial.aeval (r k.1))
      rw [minpoly.ker_aeval_eq_span_minpoly,
        minpoly.ker_aeval_eq_span_minpoly]
      change (Polynomial (A j) ∙ mpoly i) = (Polynomial (A j) ∙ mpoly k)
      rw [heq]
    have hdvd (i : Fib j) : mpoly i ∣ specialize j P := by
      apply minpoly.dvd (A j) (r i.1)
      exact (hspecialize j i P).trans (hPy i.1)
    have hprod : (∏ i : Fib j, mpoly i) ∣ specialize j P :=
      Fintype.prod_dvd_of_coprime hpair hdvd
    calc
      (∑ i : Fib j, (pbE j i).dim) =
          (∏ i : Fib j, mpoly i).natDegree := by
        rw [Polynomial.natDegree_prod_of_monic]
        · apply Finset.sum_congr rfl
          intro i _
          simpa [mpoly, hgenE j i] using (pbE j i).natDegree_minpoly.symm
        · intro i _
          exact minpoly.monic (hrint j i)
      _ ≤ (specialize j P).natDegree :=
        Polynomial.natDegree_le_of_dvd hprod (hPspec_ne j)
      _ ≤ P.natDegree := Polynomial.natDegree_map_le
      _ ≤ P.natDegree + Q.natDegree := Nat.le_add_right _ _
  have hbaseCoprime : Pairwise (fun a b : J ↦ IsCoprime a.1 b.1) := by
    intro a b hab
    by_contra hcop
    have hdvd : a.1 ∣ b.1 :=
      (hμirr a).dvd_iff_not_isCoprime.mpr hcop
    have hassoc := (hμirr a).associated_of_dvd (hμirr b) hdvd
    have heq : a.1 = b.1 :=
      Polynomial.eq_of_monic_of_associated (hμmonic a) (hμmonic b) hassoc
    exact hab (Subtype.ext heq)
  have hminx (j : J) : minpoly K (x j) = j.1 := by
    rw [AdjoinRoot.minpoly_root (hμirr j).ne_zero,
      (hμmonic j).leadingCoeff, inv_one, Polynomial.C_1, mul_one]
  have hPy' (j : J) (i : Fib j) :
      Polynomial.eval₂ (algebraMap (A j) (EE j i)) (yy j i)
        (P.map (Polynomial.eval₂RingHom (algebraMap K (A j)) (x j))) = 0 :=
    (hspecialize j i P).trans (hPy i.1)
  have hQy' (j : J) (i : Fib j) :
      Polynomial.eval₂ (algebraMap (A j) (EE j i)) (yy j i)
        (Q.map (Polynomial.eval₂RingHom (algebraMap K (A j)) (x j))) = 0 :=
    (hspecialize j i Q).trans (hQy i.1)
  have hbound := PlaneCharacteristicFreeFamilyDegree.sum_finrank_le_resultant_natDegree
    (I := Fib) A EE x yy pbA pbE hgenA hgenE
    P Q P.natDegree Q.natDegree le_rfl le_rfl
    (by simpa only [hminx] using hbaseCoprime)
    hrelativeKernels hrelativeDim hPy' hQy' hres
  let groupEquiv : (Σ j, Fib j) ≃ I := Equiv.sigmaFiberEquiv group
  calc
    (∑ i, Module.finrank K (E i)) =
        ∑ z : (Σ j, Fib j), Module.finrank K (E (groupEquiv z)) :=
      (Equiv.sum_comp groupEquiv (fun i ↦ Module.finrank K (E i))).symm
    _ = ∑ j : J, ∑ i : Fib j, Module.finrank K (EE j i) := by
      rw [Fintype.sum_sigma]
      rfl
    _ ≤ _ := hbound

end

end ProximityPrize.SubmissionLower.PlaneCharacteristicFreeFamilyRoots

#print axioms ProximityPrize.SubmissionLower.PlaneCharacteristicFreeFamilyRoots.sum_finrank_le_resultant_natDegree
