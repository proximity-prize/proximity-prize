import ProximityPrize.SubmissionLower.UpperBranch1

set_option autoImplicit false
set_option Elab.async false

namespace Rect51PoleWindow
noncomputable section

open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1 (otherBlock)
open K1_14_1_7 K1_14_1_7_2
open P1_7_1_1
open scoped BigOperators Polynomial

/-- Coefficient support for a CRT source with separate seed-degree caps. -/
def RectShaped {F : Type} [Field F] (s : Shape) (u : Fin 2 → ℕ)
    (P : TrueSource F) : Prop :=
  Shaped s P ∧ ∀ j i a e, sourceCoeff P j i a e ≠ 0 → ∀ k, e k ≤ u k

/-- A local row can increase the degree in its active seed only. -/
def Window {F : Type} [Field F] (u : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) (g : Seed F) : Prop :=
  g.degreeOf 0 ≤ u 0 + (if (0 : Fin 2) = side then d else 0) ∧
  g.degreeOf 1 ≤ u 1 + (if (1 : Fin 2) = side then d else 0)

theorem rect_map {F E : Type} [Field F] [Field E]
    (f : F →+* E) {s : Shape} {u : Fin 2 → ℕ} {P : TrueSource F}
    (hP : RectShaped s u P) : RectShaped s u (mapSource f P) := by
  refine ⟨shaped_map f hP.1, ?_⟩
  intro j i a e hn
  apply hP.2 j i a e
  intro hz
  apply hn
  simpa [sourceCoeff, mapSource, Polynomial.coeff_map, MvPolynomial.coeff_map] using
    (congrArg f hz).trans (map_zero f)

theorem rect_combination {F ι : Type} [Field F] [Fintype ι]
    {s : Shape} {u : Fin 2 → ℕ} {P : ι → TrueSource F} (hP : ∀ i, RectShaped s u (P i))
    (v : ι → F) : RectShaped s u (Fintype.linearCombination F P v) := by
  refine ⟨shaped_combination (fun i => (hP i).1) v, ?_⟩
  intro j i a e hn k
  by_contra hbad
  apply hn
  change readCoeff j i a e (Fintype.linearCombination F P v) = 0
  rw [Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_eq_zero fun z _ => ?_
  have he : sourceCoeff (P z) j i a e = 0 := by
    by_contra hz
    exact hbad ((hP z).2 j i a e hz k)
  rw [map_smul]
  change v z • sourceCoeff (P z) j i a e = 0
  rw [he, smul_zero]

private theorem taylor_degree {F : Type} [Field F] {s : Shape} {u : Fin 2 → ℕ} (α : F)
    (P : TrueSource F) (hP : RectShaped s u P) (j i t : ℕ) (side : Fin 2) :
    ((inputTaylor α P j i).coeff t).degreeOf side ≤ u side := by
  have hc (a : ℕ) : (((P.coeff j).coeff i).coeff a).degreeOf side ≤ u side := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact hP.2 j i a e (MvPolynomial.mem_support_iff.mp he) side
  rw [inputTaylor, taylor_coeff, eval_eq_sum_range]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
  rw [hasseDeriv_coeff]
  have he :
      ((k + t).choose t : Seed F) * ((P.coeff j).coeff i).coeff (k + t) *
          (algebraMap F (Seed F) α) ^ k =
        MvPolynomial.C (((k + t).choose t : F) * α ^ k) *
          ((P.coeff j).coeff i).coeff (k + t) := by
    simp only [MvPolynomial.algebraMap_eq, map_mul, map_pow, map_natCast]
    ring
  rw [he]
  exact (MvPolynomial.degreeOf_mul_le _ _ _).trans
    (by simpa only [MvPolynomial.degreeOf_C, zero_add] using hc (k + t))

open private polynomialTest_apply side_degrees from ProximityPrize.SubmissionLower.UpperBranch1

theorem polynomial_window {F : Type} [Field F] {s : Shape} {t : Offset s}
    {u : Fin 2 → ℕ} (α : F) (side : Fin 2) (v : Column s t → F[X]) {d : ℕ}
    (hd : ∀ i, (v i).natDegree ≤ d) {P : TrueSource F} (hP : RectShaped s u P) :
    Window u d side (polynomialTest α side v P) := by
  have cap (k : Fin 2) :
      (polynomialTest α side v P).degreeOf k ≤ u k + (if k = side then d else 0) := by
    rw [polynomialTest_apply]
    refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun i _ => ?_)
    have hv : ((v i).toMvPolynomial side).degreeOf k ≤ if k = side then d else 0 := by
      by_cases hk : k = side
      · subst k
        simp only [ite_true]
        exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans
          ((side_degrees side (v i)).2.trans (hd i))
      · have ho : k = otherBlock side := by fin_cases k <;> fin_cases side <;> simp_all [otherBlock]
        rw [if_neg hk, ho]
        exact (side_degrees side (v i)).1
    have hi : (input α i P).degreeOf k ≤ u k :=
      taylor_degree α P hP _ _ _ k
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans
      ((Nat.add_le_add hv hi).trans_eq (Nat.add_comm _ _))
  exact ⟨cap 0, cap 1⟩

abbrev Slots (u : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) :=
  Fin (u 0 + (if (0 : Fin 2) = side then d else 0) + 1) ×
  Fin (u 1 + (if (1 : Fin 2) = side then d else 0) + 1)

private def exponent {u : Fin 2 → ℕ} {d : ℕ} {side : Fin 2} (k : Slots u d side) : Exponent :=
  Finsupp.equivFunOnFinite.symm ![k.1.val, k.2.val]

def read (F : Type) [Field F] (u : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) :
    Seed F →ₗ[F] (Slots u d side → F) :=
  LinearMap.pi fun k => MvPolynomial.lcoeff F (exponent k)

theorem read_eq_zero {F : Type} [Field F] {u : Fin 2 → ℕ} {d : ℕ} {side : Fin 2}
    {g : Seed F} (hg : Window u d side g) (hread : read F u d side g = 0) : g = 0 := by
  apply MvPolynomial.ext
  intro e
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hn
  have hsupport := MvPolynomial.mem_support_iff.mpr hn
  let r : Slots u d side :=
    (⟨e 0, Nat.lt_succ_of_le ((MvPolynomial.le_degreeOf_of_mem_support 0 hsupport).trans hg.1)⟩,
     ⟨e 1, Nat.lt_succ_of_le ((MvPolynomial.le_degreeOf_of_mem_support 1 hsupport).trans hg.2)⟩)
  have he : exponent r = e := by
    ext i
    fin_cases i <;> rfl
  have hz := congrFun hread r
  change g.coeff (exponent r) = 0 at hz
  exact hn (he ▸ hz)

end
end Rect51PoleWindow
