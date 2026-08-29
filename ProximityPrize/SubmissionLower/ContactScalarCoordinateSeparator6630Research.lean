import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularComponentYZPositivity6630Research
import ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
import ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum
import ProximityPrize.SubmissionLower.ContactCurveComponents
import ProximityPrize.SubmissionLower.ContactWeakSeparableSeparatorResearch
import ProximityPrize.SubmissionLower.ContactProperCutSeedCount

/-! .












 -/

namespace ProximityPrize.SubmissionLower.ContactScalarCoordinateSeparator6630Research

open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds ActualPlaneCoordinateCaps
open ActualCoordinateDegreeSum
open ContactCurveComponents ContactRegularComponentCover
open ContactGenericSurface ContactProperCutSeedCount
open ContactWeakSeparableSeparatorResearch
open ContactRegularComponentYZPositivity6630Research

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]

abbrev Poly3 := MvPolynomial (Fin 3) Omega

/-- .
 -/
theorem exists_coordinate_difference_mem_of_isAlgebraic
    (P : Ideal (Poly3 (Omega := Omega))) [P.IsPrime] (i : Fin 3)
    (hi : IsAlgebraic Omega (coordinate Omega P i)) :
    ∃ c : Omega, MvPolynomial.X i - MvPolynomial.C c ∈ P := by
  obtain ⟨c, hc⟩ := coordinate_eq_scalar_of_isAlgebraic Omega P i hi
  refine ⟨c, ?_⟩
  rw [← aeval_coordinate_ker Omega P]
  change MvPolynomial.aeval (coordinate Omega P)
      (MvPolynomial.X i - MvPolynomial.C c) = 0
  simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  rw [← hc, sub_self]

/-- .
 -/
theorem not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos
    (G : Poly3 (Omega := Omega)) (hG : G ≠ 0)
    (hdep : 0 < G.degreeOf (1 : Fin 3)) (c : Omega) :
    ¬ G ∣ (MvPolynomial.X (2 : Fin 3) - MvPolynomial.C c) := by
  let H : Poly3 (Omega := Omega) :=
    MvPolynomial.X (2 : Fin 3) - MvPolynomial.C c
  have hHne : H ≠ 0 := coordinate_difference_ne_zero Omega 2 c
  have hHdegree : H.degreeOf (1 : Fin 3) ≤ 0 := by
    calc
      H.degreeOf (1 : Fin 3) ≤
          max ((MvPolynomial.X (2 : Fin 3) : Poly3).degreeOf 1)
            ((MvPolynomial.C c : Poly3).degreeOf 1) := by
        simpa only [H] using MvPolynomial.degreeOf_sub_le (1 : Fin 3)
          (MvPolynomial.X (2 : Fin 3) : Poly3) (MvPolynomial.C c)
      _ = 0 := by
        rw [MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 3) ≠ 2),
          MvPolynomial.degreeOf_C]
        rfl
  intro hdiv
  obtain ⟨A, hA⟩ := hdiv
  have hHA : H = G * A := by simpa only [H] using hA
  have hAne : A ≠ 0 := by
    intro hzero
    apply hHne
    rw [hHA, hzero, mul_zero]
  have hle : G.degreeOf (1 : Fin 3) ≤ H.degreeOf (1 : Fin 3) := by
    calc
      G.degreeOf (1 : Fin 3) ≤
          G.degreeOf (1 : Fin 3) + A.degreeOf (1 : Fin 3) :=
        Nat.le_add_right _ _
      _ = (G * A).degreeOf (1 : Fin 3) := by
        rw [MvPolynomial.degreeOf_mul_eq hG hAne]
      _ = H.degreeOf (1 : Fin 3) := by rw [hHA]
  omega

/-- .
 -/
theorem finite_separable_at_y_of_z_algebraic
    (P : Ideal (Poly3 (Omega := Omega))) [P.IsPrime]
    (p : ℕ) [CharP Omega p]
    (G : Poly3 (Omega := Omega))
    (hG : Irreducible G) (hGmem : G ∈ P)
    (hdep : 0 < G.degreeOf (1 : Fin 3))
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hY : Transcendental Omega (coordinate Omega P 0))
    (hZ : IsAlgebraic Omega (coordinate Omega P 2)) :
    letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
      rationalBaseAlgebra Omega P 0 hY
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) ∧
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) := by
  obtain ⟨c, hHmem⟩ :=
    exists_coordinate_difference_mem_of_isAlgebraic P 2 hZ
  let H : Poly3 (Omega := Omega) :=
    MvPolynomial.X (2 : Fin 3) - MvPolynomial.C c
  have hproper : ¬ G ∣ H :=
    not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos G hG.ne_zero hdep c
  have hHone : H.degreeOf (1 : Fin 3) ≤ 0 := by
    calc
      H.degreeOf (1 : Fin 3) ≤
          max ((MvPolynomial.X (2 : Fin 3) : Poly3).degreeOf 1)
            ((MvPolynomial.C c : Poly3).degreeOf 1) := by
        simpa only [H] using MvPolynomial.degreeOf_sub_le (1 : Fin 3)
          (MvPolynomial.X (2 : Fin 3) : Poly3) (MvPolynomial.C c)
      _ = 0 := by
        rw [MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 3) ≠ 2),
          MvPolynomial.degreeOf_C]
        rfl
  have hHtwo : H.degreeOf (2 : Fin 3) ≤ 1 := by
    calc
      H.degreeOf (2 : Fin 3) ≤
          max ((MvPolynomial.X (2 : Fin 3) : Poly3).degreeOf 2)
            ((MvPolynomial.C c : Poly3).degreeOf 2) := by
        simpa only [H] using MvPolynomial.degreeOf_sub_le (2 : Fin 3)
          (MvPolynomial.X (2 : Fin 3) : Poly3) (MvPolynomial.C c)
      _ = 1 := by simp
  have hmixed : coordinateMixedDegree Omega G H 0 < p := by
    rw [coordinateMixedDegree_zero]
    calc
      H.degreeOf 1 * G.degreeOf 2 + G.degreeOf 1 * H.degreeOf 2 ≤
          0 * G.degreeOf 2 + G.degreeOf 1 * 1 :=
        Nat.add_le_add (Nat.mul_le_mul hHone (Nat.le_refl _))
          (Nat.mul_le_mul (Nat.le_refl _) hHtwo)
      _ = G.degreeOf 1 := by simp
      _ < p := hdegree 1
  exact finite_separable_at_of_original_coordinate_gate Omega P 0 hY p G H
    hG hGmem hHmem hproper hdegree hmixed

/-- .

 -/
theorem exists_separableLiteralCoordinate_y_or_z
    (P : Ideal (Poly3 (Omega := Omega))) [P.IsPrime]
    (p : ℕ) [CharP Omega p]
    (G T : Poly3 (Omega := Omega))
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P)
    (hproper : ¬ G ∣ T)
    (hdep : 0 < G.degreeOf (1 : Fin 3))
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedZ : coordinateMixedDegree Omega G T 2 < p)
    (hYZ : Transcendental Omega (coordinate Omega P 0) ∨
      Transcendental Omega (coordinate Omega P 2)) :
    ∃ D : SeparableLiteralCoordinate P,
      D.index = 0 ∨ D.index = 2 := by
  by_cases hZ : Transcendental Omega (coordinate Omega P 2)
  · have hz := finite_separable_at_of_original_coordinate_gate
      Omega P 2 hZ p G T hG hGmem hTmem hproper hdegree hmixedZ
    exact ⟨⟨2, hZ, hz.1, hz.2⟩, Or.inr rfl⟩
  · have hY : Transcendental Omega (coordinate Omega P 0) :=
      hYZ.resolve_right hZ
    have hZalg : IsAlgebraic Omega (coordinate Omega P 2) := not_not.mp hZ
    have hy := finite_separable_at_y_of_z_algebraic P p G hG hGmem hdep
      hdegree hY hZalg
    exact ⟨⟨0, hY, hy.1, hy.2⟩, Or.inl rfl⟩

/-- . -/
theorem regularComponent_exists_separableLiteralCoordinate6630
    {K : Type} [Field K]
    (phi : Polynomial K →+* Omega)
    (F : MvPolynomial (Fin 4) K)
    (G T : Poly3 (Omega := Omega))
    (p : ℕ) [CharP Omega p]
    (hdiv : G ∣ surfaceMap phi F)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hdep : 0 < G.degreeOf (1 : Fin 3))
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedZ : coordinateMixedDegree Omega G T 2 < p)
    (C : RegularComponent Omega G T (regularitySurface phi F)) :
    ∃ D : SeparableLiteralCoordinate C.1,
      D.index = 0 ∨ D.index = 2 := by
  apply exists_separableLiteralCoordinate_y_or_z C.1 p G T hG
    (regularComponent_G_mem Omega G T (regularitySurface phi F) C)
    (regularComponent_T_mem Omega G T (regularitySurface phi F) C)
    hproper hdep hdegree hmixedZ
  exact regularComponent_y_or_z_transcendental phi F G T hdiv C

theorem regularComponent_nonempty_separableLiteralCoordinate6630
    {K : Type} [Field K]
    (phi : Polynomial K →+* Omega)
    (F : MvPolynomial (Fin 4) K)
    (G T : Poly3 (Omega := Omega))
    (p : ℕ) [CharP Omega p]
    (hdiv : G ∣ surfaceMap phi F)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hdep : 0 < G.degreeOf (1 : Fin 3))
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedZ : coordinateMixedDegree Omega G T 2 < p)
    (C : RegularComponent Omega G T (regularitySurface phi F)) :
    Nonempty (SeparableLiteralCoordinate C.1) := by
  obtain ⟨D, _⟩ := regularComponent_exists_separableLiteralCoordinate6630
    phi F G T p hdiv hG hproper hdep hdegree hmixedZ C
  exact ⟨D⟩

end

end ProximityPrize.SubmissionLower.ContactScalarCoordinateSeparator6630Research
