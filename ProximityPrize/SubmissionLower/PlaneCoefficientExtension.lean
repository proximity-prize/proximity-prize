import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneResultantIrreducible
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Polynomial_ContentIdeal

/-!
# Actual planar proper-cut bounds after coefficient field extension

Model label: gpt-5.

Primitivity over K[Y] is transported through its actual unit content ideal.
Thus extension to any field L creates no identically zero scalar fiber.
The actual-degree resultant is mapped and remains nonzero, and both degree
caps are preserved. The resulting bound counts actual L-valued points;
geometric irreducibility of the mapped first polynomial is not assumed.
-/

namespace ProximityPrize.SubmissionLower.PlaneCoefficientExtension

noncomputable section

variable {K L : Type} [Field K] [Field L]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq L := Classical.decEq L

def bimap (f : K →+* L) (P : Polynomial (Polynomial K)) :
    Polynomial (Polynomial L) := P.map (Polynomial.mapRingHom f)

theorem bimap_primitive (f : K →+* L)
    (P : Polynomial (Polynomial K)) (hP : P.IsPrimitive) :
    (bimap f P).IsPrimitive := by
  apply Polynomial.isPrimitive_of_contentIdeal_eq_top
  rw [bimap, Polynomial.contentIdeal_map_eq_map_contentIdeal,
    (Polynomial.isPrimitive_iff_contentIdeal_eq_top P).mp hP, Ideal.map_top]

theorem bimap_natDegree_le (f : K →+* L) (P : Polynomial (Polynomial K)) :
    (bimap f P).natDegree ≤ P.natDegree :=
  Polynomial.natDegree_map_le

theorem bimap_degreeX_le (f : K →+* L) (P : Polynomial (Polynomial K)) :
    Polynomial.Bivariate.degreeX (bimap f P) ≤ Polynomial.Bivariate.degreeX P := by
  classical
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro j _
  rw [show (bimap f P).coeff j = (P.coeff j).map f by simp [bimap]]
  exact Polynomial.natDegree_map_le.trans
    (Polynomial.Bivariate.coeff_natDegree_le_degreeX P j)

theorem bimap_specialization (f : K →+* L)
    (P : Polynomial (Polynomial K)) (x : L) :
    (bimap f P).map (Polynomial.evalRingHom x) =
      P.map (Polynomial.eval₂RingHom f x) := by
  ext j
  simp [bimap, Polynomial.eval_map]

theorem bimap_eval_natural (f : K →+* L)
    (P : Polynomial (Polynomial K)) (x y : K) :
    ((bimap f P).map (Polynomial.evalRingHom (f x))).eval (f y) =
      f ((P.map (Polynomial.evalRingHom x)).eval y) := by
  have h : (bimap f P).map (Polynomial.evalRingHom (f x)) =
      (P.map (Polynomial.evalRingHom x)).map f := by
    ext j
    simp [bimap, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [h, Polynomial.eval_map_apply]

theorem bimap_comp {M : Type} [Field M]
    (f : K →+* L) (g : L →+* M) (P : Polynomial (Polynomial K)) :
    bimap g (bimap f P) = bimap (g.comp f) P := by
  ext j i
  simp [bimap]

theorem bimap_resultant_ne_zero (f : K →+* L)
    (P Q : Polynomial (Polynomial K)) (m n : ℕ)
    (hres : Polynomial.resultant P Q m n ≠ 0) :
    Polynomial.resultant (bimap f P) (bimap f Q) m n ≠ 0 := by
  unfold bimap
  rw [Polynomial.resultant_map_map]
  intro hzero
  apply hres
  apply Polynomial.map_injective f f.injective
  simpa only [Polynomial.coe_mapRingHom, Polynomial.map_zero] using hzero

theorem bimap_specialization_ne_zero (f : K →+* L)
    (P : Polynomial (Polynomial K)) (hP : P.IsPrimitive) (x : L) :
    (bimap f P).map (Polynomial.evalRingHom x) ≠ 0 := by
  classical
  exact PlaneResultantIrreducible.primitive_specialization_ne_zero
    (bimap f P) (bimap_primitive f P hP) x

/-- The original irreducibility/properness gates give an actual point count
over every coefficient field extension, even if the mapped curve splits. -/
theorem common_points_card_le_after_extension (f : K →+* L)
    (P Q : Polynomial (Polynomial K)) (points : Finset (L × L))
    (hP : Irreducible P) (hdeg : 0 < P.natDegree) (hproper : ¬ P ∣ Q)
    (hroots : ∀ point ∈ points,
      ((bimap f P).map (Polynomial.evalRingHom point.1)).eval point.2 = 0 ∧
      ((bimap f Q).map (Polynomial.evalRingHom point.1)).eval point.2 = 0) :
    points.card ≤ Q.natDegree * Polynomial.Bivariate.degreeX P +
      P.natDegree * Polynomial.Bivariate.degreeX Q := by
  classical
  have hcount := PlaneResultantPointCount.common_points_card_le_bidegree_bound
    (bimap f P) (bimap f Q) P.natDegree Q.natDegree points
    (bimap_natDegree_le f P) (bimap_natDegree_le f Q)
    (bimap_resultant_ne_zero f P Q P.natDegree Q.natDegree
      (PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
        P Q hP hdeg hproper))
    (fun point _ => Or.inl (bimap_specialization_ne_zero f P
      (hP.isPrimitive (Nat.ne_of_gt hdeg)) point.1)) hroots
  exact hcount.trans (Nat.add_le_add
    (Nat.mul_le_mul_left _ (bimap_degreeX_le f P))
    (Nat.mul_le_mul_left _ (bimap_degreeX_le f Q)))

end

end ProximityPrize.SubmissionLower.PlaneCoefficientExtension

#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.bimap_primitive
#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.bimap_natDegree_le
#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.bimap_degreeX_le
#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.bimap_specialization
#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.bimap_eval_natural
#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.bimap_comp
#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.bimap_resultant_ne_zero
#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.bimap_specialization_ne_zero
#print axioms ProximityPrize.SubmissionLower.PlaneCoefficientExtension.common_points_card_le_after_extension
