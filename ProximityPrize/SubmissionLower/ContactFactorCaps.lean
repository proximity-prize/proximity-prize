import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactInterpolation
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_MvPolynomial_WeightedHomogeneous
import ProximityPrize.SubmissionLower.LocalMathlib_Algebra_MvPolynomial_NoZeroDivisors


/-! .












 -/

namespace ProximityPrize.SubmissionLower.ContactFactorCaps

open ContactInterpolation

noncomputable section

/-- . -/
def weightEmbed (weights : Fin 4 → ℕ) : (Fin 4 →₀ ℕ) →+ (Fin 5 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
    Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3) +
    Finsupp.single 4 (Finsupp.weight weights d)
  map_zero' := by simp
  map_add' d e := by
    ext i
    fin_cases i <;> simp [Finsupp.add_apply, map_add]

theorem weightEmbed_castSucc (weights : Fin 4 → ℕ) (d : Fin 4 →₀ ℕ) (i : Fin 4) :
    weightEmbed weights d i.castSucc = d i := by
  fin_cases i <;> simp [weightEmbed]

theorem weightEmbed_last (weights : Fin 4 → ℕ) (d : Fin 4 →₀ ℕ) :
    weightEmbed weights d (4 : Fin 5) = Finsupp.weight weights d := by
  simp [weightEmbed]

theorem weightEmbed_injective (weights : Fin 4 → ℕ) :
    Function.Injective (weightEmbed weights) := by
  intro d e h
  ext i
  have hi := congrArg (fun a : Fin 5 →₀ ℕ => a i.castSucc) h
  simpa only [weightEmbed_castSucc] using hi

variable {K : Type*} [Field K]

/-- . -/
def weightedLift (K : Type*) [Field K] (weights : Fin 4 → ℕ) :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 5) K :=
  AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)

theorem weightedLift_injective (weights : Fin 4 → ℕ) :
    Function.Injective (weightedLift K weights) :=
  AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)

theorem weightedLift_ne_zero (weights : Fin 4 → ℕ) (P : MvPolynomial (Fin 4) K)
    (hP : P ≠ 0) : weightedLift K weights P ≠ 0 := by
  intro hzero
  apply hP
  apply weightedLift_injective weights
  simpa only [map_zero] using hzero

theorem coeff_weightedLift_at (weights : Fin 4 → ℕ) (P : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff (weightEmbed weights d) (weightedLift K weights P) =
      MvPolynomial.coeff d P := by
  change Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff P)
    (weightEmbed weights d) = (AddMonoidAlgebra.coeff P) d
  exact Finsupp.mapDomain_apply (weightEmbed_injective weights) _ d

theorem support_weightedLift (weights : Fin 4 → ℕ) (P : MvPolynomial (Fin 4) K) :
    (weightedLift K weights P).support = P.support.image (weightEmbed weights) := by
  change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff P)).support =
    Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff P).support
  exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _

theorem degree_weightedLift (weights : Fin 4 → ℕ) (P : MvPolynomial (Fin 4) K) :
    (weightedLift K weights P).degreeOf (4 : Fin 5) =
      MvPolynomial.weightedTotalDegree weights P := by
  change (weightedLift K weights P).degreeOf (4 : Fin 5) =
    P.support.sup (Finsupp.weight weights)
  rw [MvPolynomial.degreeOf_eq_sup, support_weightedLift, Finset.sup_image]
  apply congrArg (fun f : (Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
  funext d
  exact weightEmbed_last weights d

/-- . -/
theorem weightedTotalDegree_mul (weights : Fin 4 → ℕ)
    (P Q : MvPolynomial (Fin 4) K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    MvPolynomial.weightedTotalDegree weights (P * Q) =
      MvPolynomial.weightedTotalDegree weights P +
        MvPolynomial.weightedTotalDegree weights Q := by
  calc
    MvPolynomial.weightedTotalDegree weights (P * Q) =
        (weightedLift K weights (P * Q)).degreeOf (4 : Fin 5) :=
      (degree_weightedLift weights (P * Q)).symm
    _ = (weightedLift K weights P * weightedLift K weights Q).degreeOf (4 : Fin 5) := by
      rw [map_mul]
    _ = (weightedLift K weights P).degreeOf (4 : Fin 5) +
        (weightedLift K weights Q).degreeOf (4 : Fin 5) :=
      MvPolynomial.degreeOf_mul_eq (weightedLift_ne_zero weights P hP)
        (weightedLift_ne_zero weights Q hQ)
    _ = MvPolynomial.weightedTotalDegree weights P +
        MvPolynomial.weightedTotalDegree weights Q := by
      rw [degree_weightedLift, degree_weightedLift]

theorem weightedTotalDegree_le_of_dvd (weights : Fin 4 → ℕ)
    (P Q : MvPolynomial (Fin 4) K) (hdiv : P ∣ Q) (hQ : Q ≠ 0) :
    MvPolynomial.weightedTotalDegree weights P ≤
      MvPolynomial.weightedTotalDegree weights Q := by
  rcases hdiv with ⟨G, rfl⟩
  rcases mul_ne_zero_iff.mp hQ with ⟨hP, hG⟩
  rw [weightedTotalDegree_mul weights P G hP hG]
  exact Nat.le_add_right _ _

theorem weightedTotalDegree_le_iff (weights : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) K) (cap : ℕ) :
    MvPolynomial.weightedTotalDegree weights P ≤ cap ↔
      ∀ d ∈ P.support, Finsupp.weight weights d ≤ cap := by
  simp only [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]

theorem weight_fin4 (weights : Fin 4 → ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight weights d =
      d 0 * weights 0 + d 1 * weights 1 + d 2 * weights 2 + d 3 * weights 3 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3) := by
    ext i
    fin_cases i <;> simp
  calc
    Finsupp.weight weights d = Finsupp.weight weights
        (Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
          Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3)) := congrArg _ hd
    _ = _ := by simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, Nat.cast_id]

def seedWeights : Fin 4 → ℕ := ![0, 1, 0, 1]
def slopeWeights : Fin 4 → ℕ := ![0, 0, 1, 0]
def contactWeights (w : ℕ) : Fin 4 → ℕ := ![1, w, w - 1, 0]

theorem seed_weight (d : Fin 4 →₀ ℕ) : Finsupp.weight seedWeights d = d 1 + d 3 := by
  rw [weight_fin4]
  simp [seedWeights]

theorem slope_weight (d : Fin 4 →₀ ℕ) : Finsupp.weight slopeWeights d = d 2 := by
  rw [weight_fin4]
  simp [slopeWeights]

theorem contact_weight (w : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (contactWeights w) d = d 0 + w * d 1 + (w - 1) * d 2 := by
  rw [weight_fin4]
  simp [contactWeights, Nat.mul_comm]

/-- .
 -/
theorem mem_globalCoefficientBox_iff (P : MvPolynomial (Fin 4) K)
    (D w L s : ℕ) (hD : 0 < D) :
    P ∈ globalCoefficientBox K D w L s ↔
      MvPolynomial.weightedTotalDegree seedWeights P ≤ L ∧
      MvPolynomial.weightedTotalDegree slopeWeights P ≤ s ∧
      MvPolynomial.weightedTotalDegree (contactWeights w) P ≤ D - 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply (weightedTotalDegree_le_iff seedWeights P L).mpr
      intro d hd
      rw [seed_weight]
      exact (h hd).1
    · apply (weightedTotalDegree_le_iff slopeWeights P s).mpr
      intro d hd
      rw [slope_weight]
      exact (h hd).2.1
    · apply (weightedTotalDegree_le_iff (contactWeights w) P (D - 1)).mpr
      intro d hd
      rw [contact_weight]
      have hh := (h hd).2.2
      omega
  · rintro ⟨hseed, hslope, hcontact⟩ d hd
    have hs := (MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hseed
    have hr := (MvPolynomial.le_weightedTotalDegree slopeWeights hd).trans hslope
    have hc := (MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hcontact
    rw [seed_weight] at hs
    rw [slope_weight] at hr
    rw [contact_weight] at hc
    exact ⟨hs, hr, by omega⟩

/-- .
 -/
theorem mem_globalCoefficientBox_of_dvd
    (F Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hQ : Q ≠ 0) (hdiv : F ∣ Q)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    F ∈ globalCoefficientBox K D w L s := by
  have hD : 0 < D := by
    rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d, hd⟩
    have hh := (hbox hd).2.2
    omega
  have hcaps := (mem_globalCoefficientBox_iff Q D w L s hD).mp hbox
  apply (mem_globalCoefficientBox_iff F D w L s hD).mpr
  exact ⟨(weightedTotalDegree_le_of_dvd seedWeights F Q hdiv hQ).trans hcaps.1,
    (weightedTotalDegree_le_of_dvd slopeWeights F Q hdiv hQ).trans hcaps.2.1,
    (weightedTotalDegree_le_of_dvd (contactWeights w) F Q hdiv hQ).trans hcaps.2.2⟩

theorem degreeOf_le_of_dvd (i : Fin 4) (F Q : MvPolynomial (Fin 4) K)
    (hdiv : F ∣ Q) (hQ : Q ≠ 0) : F.degreeOf i ≤ Q.degreeOf i := by
  rcases hdiv with ⟨G, rfl⟩
  rcases mul_ne_zero_iff.mp hQ with ⟨hF, hG⟩
  rw [MvPolynomial.degreeOf_mul_eq hF hG]
  exact Nat.le_add_right _ _

/-- .
 -/
theorem sum_degreeOf_le_of_prod_dvd {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin 4) K) (Q : MvPolynomial (Fin 4) K)
    (hQ : Q ≠ 0) (hdiv : (∏ j ∈ I, f j) ∣ Q) (i : Fin 4) :
    (∑ j ∈ I, (f j).degreeOf i) ≤ Q.degreeOf i := by
  classical
  have hprod : (∏ j ∈ I, f j) ≠ 0 := by
    intro hz
    rcases hdiv with ⟨G, hG⟩
    apply hQ
    rw [hG, hz, zero_mul]
  have hf : ∀ j ∈ I, f j ≠ 0 := Finset.prod_ne_zero_iff.mp hprod
  calc
    (∑ j ∈ I, (f j).degreeOf i) = (∏ j ∈ I, f j).degreeOf i :=
      (MvPolynomial.degreeOf_prod_eq (n := i) I f hf).symm
    _ ≤ Q.degreeOf i := degreeOf_le_of_dvd i _ Q hdiv hQ

theorem separated_degree_budgets_of_prod_dvd {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin 4) K) (Q : MvPolynomial (Fin 4) K)
    (hQ : Q ≠ 0) (hdiv : (∏ j ∈ I, f j) ∣ Q) :
    (∑ j ∈ I, (f j).degreeOf (1 : Fin 4)) ≤ Q.degreeOf (1 : Fin 4) ∧
    (∑ j ∈ I, (f j).degreeOf (2 : Fin 4)) ≤ Q.degreeOf (2 : Fin 4) ∧
    (∑ j ∈ I, (f j).degreeOf (3 : Fin 4)) ≤ Q.degreeOf (3 : Fin 4) :=
  ⟨sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 1,
    sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 2,
    sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 3⟩

/-- .
 -/
theorem degreeOf_eq_sum_of_scalar_factorization {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin 4) K) (Q : MvPolynomial (Fin 4) K)
    (c : K) (hQ : Q ≠ 0) (hfactor : Q = MvPolynomial.C c * ∏ j ∈ I, f j) (i : Fin 4) :
    Q.degreeOf i = ∑ j ∈ I, (f j).degreeOf i := by
  classical
  have hnonzero : MvPolynomial.C c * (∏ j ∈ I, f j) ≠ 0 := by
    rw [← hfactor]
    exact hQ
  rcases mul_ne_zero_iff.mp hnonzero with ⟨hc, hprod⟩
  have hf : ∀ j ∈ I, f j ≠ 0 := Finset.prod_ne_zero_iff.mp hprod
  rw [hfactor, MvPolynomial.degreeOf_mul_eq hc hprod, MvPolynomial.degreeOf_C,
    Nat.zero_add, MvPolynomial.degreeOf_prod_eq I f hf]

/-- .
 -/
theorem degreeOf_Y_le_of_mem_box (Q : MvPolynomial (Fin 4) K)
    (D w L s : ℕ) (hw : 0 < w)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    Q.degreeOf (1 : Fin 4) ≤ (D - 1) / w := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  apply (Nat.le_div_iff_mul_le hw).mpr
  have hc := (hbox hd).2.2
  have hm : d 1 * w = w * d 1 := Nat.mul_comm _ _
  omega

theorem degreeOf_R_le_of_mem_box (Q : MvPolynomial (Fin 4) K)
    (D w L s : ℕ) (hbox : Q ∈ globalCoefficientBox K D w L s) :
    Q.degreeOf (2 : Fin 4) ≤ s := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  exact (hbox hd).2.1

theorem degreeOf_Z_le_of_mem_box (Q : MvPolynomial (Fin 4) K)
    (D w L s : ℕ) (hbox : Q ∈ globalCoefficientBox K D w L s) :
    Q.degreeOf (3 : Fin 4) ≤ L := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hs := (hbox hd).1
  omega

theorem degree_bounds_of_mem_box (Q : MvPolynomial (Fin 4) K)
    (D w L s : ℕ) (hw : 0 < w)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    Q.degreeOf (1 : Fin 4) ≤ (D - 1) / w ∧
    Q.degreeOf (2 : Fin 4) ≤ s ∧ Q.degreeOf (3 : Fin 4) ≤ L :=
  ⟨degreeOf_Y_le_of_mem_box Q D w L s hw hbox,
    degreeOf_R_le_of_mem_box Q D w L s hbox,
    degreeOf_Z_le_of_mem_box Q D w L s hbox⟩

/-- .
 -/
theorem separated_factor_caps_of_prod_dvd {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin 4) K) (Q : MvPolynomial (Fin 4) K)
    (D w L s : ℕ) (hw : 0 < w) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w L s) (hdiv : (∏ j ∈ I, f j) ∣ Q) :
    (∑ j ∈ I, (f j).degreeOf (1 : Fin 4)) ≤ (D - 1) / w ∧
    (∑ j ∈ I, (f j).degreeOf (2 : Fin 4)) ≤ s ∧
    (∑ j ∈ I, (f j).degreeOf (3 : Fin 4)) ≤ L := by
  have hsum := separated_degree_budgets_of_prod_dvd I f Q hQ hdiv
  have hcaps := degree_bounds_of_mem_box Q D w L s hw hbox
  exact ⟨hsum.1.trans hcaps.1, hsum.2.1.trans hcaps.2.1, hsum.2.2.trans hcaps.2.2⟩

end

end ProximityPrize.SubmissionLower.ContactFactorCaps
