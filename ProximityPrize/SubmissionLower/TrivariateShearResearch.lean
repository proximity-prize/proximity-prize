import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_MvPolynomial_Homogeneous

/-! .










 -/

namespace ProximityPrize.SubmissionLower.TrivariateShearResearch

open scoped Classical BigOperators

noncomputable section

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

abbrev Poly3 (K : Type) [Field K] := MvPolynomial (Fin 3) K

def shearImage (a : K) (i : Fin 3) : Poly3 K :=
  ![MvPolynomial.X 0,
    MvPolynomial.X 1 - MvPolynomial.C a * MvPolynomial.X 2,
    MvPolynomial.X 2] i

def unshearImage (a : K) (i : Fin 3) : Poly3 K :=
  ![MvPolynomial.X 0,
    MvPolynomial.X 1 + MvPolynomial.C a * MvPolynomial.X 2,
    MvPolynomial.X 2] i

def shearAlgHom (a : K) : Poly3 K →ₐ[K] Poly3 K :=
  MvPolynomial.aeval (shearImage a)

def unshearAlgHom (a : K) : Poly3 K →ₐ[K] Poly3 K :=
  MvPolynomial.aeval (unshearImage a)

@[simp] theorem shearAlgHom_X (a : K) (i : Fin 3) :
    shearAlgHom a (MvPolynomial.X i) = shearImage a i := by
  simp [shearAlgHom]

@[simp] theorem unshearAlgHom_X (a : K) (i : Fin 3) :
    unshearAlgHom a (MvPolynomial.X i) = unshearImage a i := by
  simp [unshearAlgHom]

theorem unshear_comp_shear (a : K) :
    (unshearAlgHom a).comp (shearAlgHom a) = AlgHom.id K (Poly3 K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [shearImage, unshearImage, shearAlgHom, unshearAlgHom] <;> ring

theorem shear_comp_unshear (a : K) :
    (shearAlgHom a).comp (unshearAlgHom a) = AlgHom.id K (Poly3 K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [shearImage, unshearImage, shearAlgHom, unshearAlgHom] <;> ring

/-- .
 -/
def shearEquiv (a : K) : Poly3 K ≃ₐ[K] Poly3 K :=
  AlgEquiv.ofAlgHom (shearAlgHom a) (unshearAlgHom a)
    (shear_comp_unshear a) (unshear_comp_shear a)

@[simp] theorem shearEquiv_apply (a : K) (F : Poly3 K) :
    shearEquiv a F = shearAlgHom a F := rfl

theorem shear_irreducible_iff (a : K) (F : Poly3 K) :
    Irreducible (shearAlgHom a F) ↔ Irreducible F := by
  simpa only [shearEquiv_apply] using
    (MulEquiv.irreducible_iff (shearEquiv a))

theorem shear_dvd_iff (a : K) (F G : Poly3 K) :
    shearAlgHom a F ∣ shearAlgHom a G ↔ F ∣ G := by
  simpa only [shearEquiv_apply] using (map_dvd_iff (shearEquiv a))

/-- .
 -/
theorem aeval_shear (F : Poly3 K) (y s z : K) (a : K) :
    MvPolynomial.aeval ![y, s, z] (shearAlgHom a F) =
      MvPolynomial.aeval ![y, s - a * z, z] F := by
  have hhom :
      (MvPolynomial.aeval ![y, s, z]).comp (shearAlgHom a) =
        MvPolynomial.aeval ![y, s - a * z, z] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [shearImage, shearAlgHom] <;> ring
  exact DFunLike.congr_fun hhom F

/-- .
 -/
theorem aeval_shear_at_add (F : Poly3 K) (y r z : K) (a : K) :
    MvPolynomial.aeval ![y, r + a * z, z] (shearAlgHom a F) =
      MvPolynomial.aeval ![y, r, z] F := by
  rw [aeval_shear]
  congr 2
  funext i
  fin_cases i <;> simp <;> ring

section WeightedDegree

/-- . -/
def weightEmbed (weights : Fin 3 → ℕ) : (Fin 3 →₀ ℕ) →+ (Fin 4 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
    Finsupp.single 2 (d 2) + Finsupp.single 3 (Finsupp.weight weights d)
  map_zero' := by simp
  map_add' d e := by
    ext i
    fin_cases i <;> simp [Finsupp.add_apply, map_add]

theorem weightEmbed_castSucc (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) (i : Fin 3) :
    weightEmbed weights d i.castSucc = d i := by
  fin_cases i <;> simp [weightEmbed]

theorem weightEmbed_last (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) :
    weightEmbed weights d (3 : Fin 4) = Finsupp.weight weights d := by
  simp [weightEmbed]

theorem weightEmbed_injective (weights : Fin 3 → ℕ) :
    Function.Injective (weightEmbed weights) := by
  intro d e h
  ext i
  have hi := congrArg (fun b : Fin 4 →₀ ℕ ↦ b i.castSucc) h
  simpa only [weightEmbed_castSucc] using hi

def weightedLift (weights : Fin 3 → ℕ) : Poly3 K →+* MvPolynomial (Fin 4) K :=
  AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)

theorem weightedLift_injective (weights : Fin 3 → ℕ) :
    Function.Injective (weightedLift (K := K) weights) :=
  AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)

theorem support_weightedLift (weights : Fin 3 → ℕ) (F : Poly3 K) :
    (weightedLift weights F).support = F.support.image (weightEmbed weights) := by
  change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff F)).support =
    Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff F).support
  exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _

theorem degree_weightedLift (weights : Fin 3 → ℕ) (F : Poly3 K) :
    (weightedLift weights F).degreeOf (3 : Fin 4) =
      MvPolynomial.weightedTotalDegree weights F := by
  change (weightedLift weights F).degreeOf (3 : Fin 4) =
    F.support.sup (Finsupp.weight weights)
  rw [MvPolynomial.degreeOf_eq_sup, support_weightedLift, Finset.sup_image]
  apply congrArg (fun f : (Fin 3 →₀ ℕ) → ℕ ↦ F.support.sup f)
  funext d
  exact weightEmbed_last weights d

def wt (weights : Fin 3 → ℕ) (F : Poly3 K) : ℕ :=
  MvPolynomial.weightedTotalDegree weights F

theorem wt_mul_le (weights : Fin 3 → ℕ) (F G : Poly3 K) :
    wt weights (F * G) ≤ wt weights F + wt weights G := by
  unfold wt
  rw [← degree_weightedLift, map_mul]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_mul_le (3 : Fin 4)
      (weightedLift weights F) (weightedLift weights G)

theorem wt_sub_le (weights : Fin 3 → ℕ) (F G : Poly3 K) :
    wt weights (F - G) ≤ max (wt weights F) (wt weights G) := by
  unfold wt
  rw [← degree_weightedLift, map_sub]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_sub_le (3 : Fin 4)
      (weightedLift weights F) (weightedLift weights G)

theorem wt_pow_le (weights : Fin 3 → ℕ) (F : Poly3 K) (n : ℕ) :
    wt weights (F ^ n) ≤ n * wt weights F := by
  unfold wt
  rw [← degree_weightedLift, map_pow]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_pow_le (3 : Fin 4) (weightedLift weights F) n

theorem wt_C (weights : Fin 3 → ℕ) (c : K) :
    wt weights (MvPolynomial.C c : Poly3 K) = 0 := by
  unfold wt MvPolynomial.weightedTotalDegree
  simp

theorem wt_X (weights : Fin 3 → ℕ) (i : Fin 3) :
    wt weights (MvPolynomial.X i : Poly3 K) = weights i := by
  unfold wt MvPolynomial.weightedTotalDegree
  simp [MvPolynomial.support_X, Finsupp.weight_single]

def pullWeights (weights : Fin 3 → ℕ) : Fin 3 → ℕ :=
  ![weights 0, max (weights 1) (weights 2), weights 2]

theorem shearImage_wt_le (weights : Fin 3 → ℕ) (a : K) (i : Fin 3) :
    wt weights (shearImage a i) ≤ pullWeights weights i := by
  fin_cases i
  · simp [shearImage, pullWeights, wt_X]
  · dsimp [shearImage, pullWeights]
    have hm := wt_mul_le weights (MvPolynomial.C a : Poly3 K) (MvPolynomial.X 2)
    rw [wt_C, Nat.zero_add, wt_X] at hm
    have hx : wt weights (MvPolynomial.X (1 : Fin 3) : Poly3 K) = weights 1 :=
      wt_X weights 1
    exact (wt_sub_le weights (MvPolynomial.X 1)
      (MvPolynomial.C a * MvPolynomial.X 2)).trans
        (by rw [hx]; exact max_le_max le_rfl hm)
  · simp [shearImage, pullWeights, wt_X]

theorem wt_finset_prod_le_sum {ι : Type*} [DecidableEq ι]
    (weights : Fin 3 → ℕ) (I : Finset ι) (f : ι → Poly3 K) :
    wt weights (∏ i ∈ I, f i) ≤ ∑ i ∈ I, wt weights (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [wt, MvPolynomial.weightedTotalDegree]
  | @insert i I hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (wt_mul_le weights (f i) (∏ j ∈ I, f j)).trans
        (Nat.add_le_add le_rfl ih)

theorem wt_finset_sum_le {ι : Type*} [DecidableEq ι]
    (weights : Fin 3 → ℕ) (I : Finset ι) (f : ι → Poly3 K) (cap : ℕ)
    (hf : ∀ i ∈ I, wt weights (f i) ≤ cap) :
    wt weights (∑ i ∈ I, f i) ≤ cap := by
  unfold wt
  rw [← degree_weightedLift, map_sum]
  apply (MvPolynomial.degreeOf_sum_le (3 : Fin 4) I
    (fun i ↦ weightedLift weights (f i))).trans
  apply Finset.sup_le
  intro i hi
  rw [degree_weightedLift]
  exact hf i hi

theorem shear_monomial_product_wt_le
    (weights : Fin 3 → ℕ) (a : K) (d : Fin 3 →₀ ℕ) :
    wt weights (∏ i ∈ d.support, shearImage a i ^ d i) ≤
      Finsupp.weight (pullWeights weights) d := by
  apply (wt_finset_prod_le_sum weights d.support
    (fun i ↦ shearImage a i ^ d i)).trans
  calc
    (∑ i ∈ d.support, wt weights (shearImage a i ^ d i)) ≤
        ∑ i ∈ d.support, d i * pullWeights weights i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (wt_pow_le weights (shearImage a i) (d i)).trans
        (Nat.mul_le_mul_left _ (shearImage_wt_le weights a i))
    _ = Finsupp.weight (pullWeights weights) d := by
      rw [Finsupp.weight_apply]
      simp only [Finsupp.sum, nsmul_eq_mul]
      simp

/-- . -/
theorem shear_wt_le_pulled (weights : Fin 3 → ℕ) (a : K) (F : Poly3 K) :
    wt weights (shearAlgHom a F) ≤ wt (pullWeights weights) F := by
  change wt weights (MvPolynomial.eval₂ MvPolynomial.C (shearImage a) F) ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply wt_finset_sum_le
  intro d hd
  have hprod := shear_monomial_product_wt_le weights a d
  have hcoeff : wt weights (MvPolynomial.C (F.coeff d) : Poly3 K) = 0 :=
    wt_C weights _
  have hmul := wt_mul_le weights (MvPolynomial.C (F.coeff d) : Poly3 K)
    (∏ i ∈ d.support, shearImage a i ^ d i)
  rw [hcoeff, Nat.zero_add] at hmul
  exact hmul.trans (hprod.trans
    (MvPolynomial.le_weightedTotalDegree (pullWeights weights) hd))

theorem shear_degreeOf_zero_le (a : K) (F : Poly3 K) :
    (shearAlgHom a F).degreeOf 0 ≤ F.degreeOf 0 := by
  have h := shear_wt_le_pulled (Pi.single (0 : Fin 3) 1) a F
  have hp : pullWeights (Pi.single (0 : Fin 3) 1) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> simp [pullWeights]
  rw [hp] at h
  simpa [wt] using h

theorem shear_degreeOf_one_le (a : K) (F : Poly3 K) :
    (shearAlgHom a F).degreeOf 1 ≤ F.degreeOf 1 := by
  have h := shear_wt_le_pulled (Pi.single (1 : Fin 3) 1) a F
  have hp : pullWeights (Pi.single (1 : Fin 3) 1) = Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp [pullWeights]
  rw [hp] at h
  simpa [wt] using h

theorem weight_fin3 (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight weights d =
      d 0 * weights 0 + d 1 * weights 1 + d 2 * weights 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i
    fin_cases i <;> simp
  rw [hd, map_add, map_add]
  simp [Finsupp.weight_single, Nat.mul_comm]

theorem two_weight_degree_le (F : Poly3 K) :
    wt (![0, 1, 1] : Fin 3 → ℕ) F ≤ F.degreeOf 1 + F.degreeOf 2 := by
  unfold wt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  rw [weight_fin3]
  change d 0 * 0 + d 1 * 1 + d 2 * 1 ≤ _
  have h1 := MvPolynomial.le_degreeOf_of_mem_support 1 hd
  have h2 := MvPolynomial.le_degreeOf_of_mem_support 2 hd
  simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
  omega

theorem shear_degreeOf_two_le (a : K) (F : Poly3 K) :
    (shearAlgHom a F).degreeOf 2 ≤ F.degreeOf 2 + F.degreeOf 1 := by
  have h := shear_wt_le_pulled (Pi.single (2 : Fin 3) 1) a F
  have hp : pullWeights (Pi.single (2 : Fin 3) 1) = (![0, 1, 1] : Fin 3 → ℕ) := by
    funext i
    fin_cases i <;> simp [pullWeights]
  rw [hp] at h
  have h' : (shearAlgHom a F).degreeOf 2 ≤ wt (![0, 1, 1] : Fin 3 → ℕ) F := by
    simpa [wt] using h
  exact h'.trans (by simpa [Nat.add_comm] using two_weight_degree_le F)

end WeightedDegree

end

end ProximityPrize.SubmissionLower.TrivariateShearResearch
