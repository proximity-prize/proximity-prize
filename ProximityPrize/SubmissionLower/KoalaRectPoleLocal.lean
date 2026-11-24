import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace KoalaRectPole
noncomputable section

open Polynomial
open K1_14 (Shape)
open K1_14_1 (jetConstant otherBlock)
open K1_14_1_7 K1_14_1_7_2
open P1_7_1 (columnCount groupedPoleMoment poleRows)
open P1_7_1_1 (Column Offset Pivot bounded_pole_minors firstJet input
  outputLength pascal_spans poleMatrix polynomialTest polynomialTests_to_poleMatrix rowIndex rowIndex_sum)
open scoped BigOperators Matrix Polynomial
open P1_7_1_1 (polynomialTest_apply side_degrees)

def RectSupport {F : Type} [CommSemiring F] (U : Fin 2 → ℕ) (P : TrueSource F) : Prop :=
  ∀ j i a e, sourceCoeff P j i a e ≠ 0 → ∀ z, e z ≤ U z

def rectWindow {F : Type} [Field F] (U : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) (g : Seed F) : Prop :=
  ∀ z, g.degreeOf z ≤ U z + if z = side then d else 0

theorem rect_map {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {U : Fin 2 → ℕ} {P : TrueSource R} (hP : RectSupport U P) :
    RectSupport U (mapSource f P) := by
  intro j i a e hne
  apply hP j i a e
  intro hz
  apply hne
  simpa [sourceCoeff, mapSource, Polynomial.coeff_map, MvPolynomial.coeff_map] using
    (congrArg f hz).trans (map_zero f)

theorem rect_combination {F ι : Type} [Field F] [Fintype ι]
    {U : Fin 2 → ℕ} {P : ι → TrueSource F} (hP : ∀ k, RectSupport U (P k)) (v : ι → F) :
    RectSupport U (Fintype.linearCombination F P v) := by
  intro j i a e hne z
  by_contra hbad
  apply hne
  change readCoeff j i a e (Fintype.linearCombination F P v) = 0
  rw [Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  have he : sourceCoeff (P k) j i a e = 0 := by
    by_contra hz
    exact hbad (hP k j i a e hz z)
  rw [map_smul]
  change v k • sourceCoeff (P k) j i a e = 0
  rw [he, smul_zero]

private theorem taylor_coordinate {F : Type} [Field F] (α : F) (P : TrueSource F)
    {U : Fin 2 → ℕ} (hP : RectSupport U P) (j i t : ℕ) (z : Fin 2) :
    (inputTaylorCoeff α j i t P).degreeOf z ≤ U z := by
  have hc (a : ℕ) : (((P.coeff j).coeff i).coeff a).degreeOf z ≤ U z := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact hP j i a e (MvPolynomial.mem_support_iff.mp he) z
  rw [inputTaylorCoeff_apply, inputTaylor, taylor_coeff, eval_eq_sum_range]
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

theorem polynomialTest_rect {F : Type} [Field F] {s : Shape} {t : Offset s}
    (α : F) (side : Fin 2) (v : Column s t → (Polynomial F)) {U : Fin 2 → ℕ} {d : ℕ}
    (hd : ∀ u, (v u).natDegree ≤ d) {P : TrueSource F} (hP : RectSupport U P) :
    rectWindow U d side (polynomialTest α side v P) := by
  intro z
  rw [polynomialTest_apply]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun u _ => ?_)
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  have hg : (input α u P).degreeOf z ≤ U z := taylor_coordinate α P hP _ _ _ _
  have hf := side_degrees side (v u)
  by_cases hz : z = side
  · rw [ite_eq_left hz]
    have hv := (MvPolynomial.degreeOf_le_totalDegree ((v u).toMvPolynomial side) z).trans
      (hf.2.trans (hd u))
    exact (Nat.add_le_add hv hg).trans_eq (Nat.add_comm _ _)
  · have ho : z = otherBlock side := by fin_cases z <;> fin_cases side <;> simp_all [otherBlock]
    have hv : ((v u).toMvPolynomial side).degreeOf z ≤ 0 := ho.symm ▸ hf.1
    simpa only [ite_eq_right hz, zero_add, add_zero] using Nat.add_le_add hv hg

def LocalTests : Prop :=
  ∀ (F : Type) [Field F] [CharP F K1.p] (s : Shape),
    s.B < K1.p → ∀ (U : Fin 2 → ℕ) (H : (Polynomial F)) (lift : (Polynomial (SeedFrac F)))
      (α : F) (side : Fin 2) (a b c : F),
      H.eval α = 0 → H.derivative.eval α ≠ 0 → b ≠ 0 →
      lift.eval (algebraMap F (SeedFrac F) α) = residue side a b c →
      ∃ d : Fin (poleRows s) → ℕ,
        (∑ r, d r) ≤ groupedPoleMoment s.B s.J ∧
        ∃ tests : Fin (poleRows s) → TrueSource F →ₗ[F] Seed F,
          (∀ r P, RectSupport U P → rectWindow U (d r) side (tests r P)) ∧
          ∀ P, Shaped s P → (∀ r, tests r P = 0) →
            (jetConstant ((Polynomial.X (R := SeedFrac F) -
                Polynomial.C (algebraMap F (SeedFrac F) α)) ^ (s.B+s.J)) :
              JetPolys (SeedFrac F)) ∣ forward H lift P

theorem local_of_children (hLocal : P1_7_1_1.c1) (hBasis : P1_7_1_1.c2) : LocalTests := by
  classical
  intro F _ _ s _ U H lift α side a b c hH _ hb hz
  have hRows (t : Offset s) :=
    hBasis F (Pivot s t) (Column s t) _ _ (bounded_pole_minors F s t a b c hb)
  choose Q L d hL hdeg hsum using hRows
  let tests (t : Offset s) (r : Pivot s t) := polynomialTest α side (Q t r)
  let e := rowIndex s
  refine ⟨fun k => d (e k).1 (e k).2, rowIndex_sum s d hsum,
    fun k => tests (e k).1 (e k).2, ?_, ?_⟩
  · intro k P hP
    exact polynomialTest_rect α side _ (hdeg _ _) hP
  · intro P hP hzero
    have ht (t : Offset s) (r : Pivot s t) : tests t r P = 0 := by
      let testAt (k : Σ t : Offset s, Pivot s t) := tests k.1 k.2 P
      have hk : testAt (e (e.symm ⟨t, r⟩)) = 0 := hzero (e.symm ⟨t, r⟩)
      rw [e.apply_symm_apply] at hk
      exact hk
    let z := residue side a b c
    have hslots := hLocal F s α z
      (fun t q => pascal_spans (SeedFrac F) (firstJet s t) (columnCount s.B s.J t.val q.val)
        (outputLength s t q)) P hP
      (fun t => polynomialTests_to_poleMatrix t α side a b c P (Q t) (L t) (hL t) (ht t))
    have hd := K1_14_1_7_2_2.proof F s (localSlots s α z P) hslots
    rw [← K1_14_1_7_2_1.proof F s α z P hP] at hd
    exact transfer_dvd H lift α z (s.B+s.J) P hH hz
      (linear_pole_dvd α z (s.B+s.J) P hd)

theorem local_tests : LocalTests :=
  local_of_children P1_7_1_1_1.proof P1_7_1_1_2.proof

#print axioms local_tests

end
end KoalaRectPole
