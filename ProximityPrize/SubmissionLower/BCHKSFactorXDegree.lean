import ProximityPrize.SubmissionLower.BCHKSConcreteGoodSpecialization
import ProximityPrize.SubmissionLower.BCHKSResultantDegree

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

set_option maxHeartbeats 2000000

/-- The fixed separability resultant has the expected degree bound in the
middle variable.  The coefficient variable is embedded in its fraction field,
so that the standard bivariate bound can be used over a field. -/
theorem rawSepResultant_natDegree_le
    {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (DX : ℕ)
    (hX : degreeX (mapZToRatFunc R) ≤ DX) :
    (rawSepResultant R).natDegree ≤ (2 * R.natDegree + 1) * DX := by
  let g : Polynomial F →+* RatFunc F := algebraMap _ _
  let B : Polynomial (Polynomial (RatFunc F)) :=
    R.map (Polynomial.mapRingHom g)
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hmap : (rawSepResultant R).map g =
      Polynomial.resultant B B.derivative R.natDegree (R.natDegree - 1) := by
    change (Polynomial.mapRingHom g)
        (Polynomial.resultant R R.derivative R.natDegree (R.natDegree - 1)) = _
    rw [Polynomial.derivative_map]
    exact (Polynomial.resultant_map_map R R.derivative R.natDegree
      (R.natDegree - 1) (Polynomial.mapRingHom g)).symm
  have hdegmap : ((rawSepResultant R).map g).natDegree =
      (rawSepResultant R).natDegree :=
    Polynomial.natDegree_map_eq_of_injective hg _
  have hdX : degreeX B.derivative ≤ DX :=
    (degreeX_derivative_le B).trans hX
  have hb := bivariate_resultant_natDegree_le
    B B.derivative R.natDegree (R.natDegree - 1)
  rw [← hdegmap, hmap]
  calc
    (Polynomial.resultant B B.derivative R.natDegree
      (R.natDegree - 1)).natDegree
        ≤ (R.natDegree - 1) * degreeX B + R.natDegree * degreeX B.derivative := hb
    _ ≤ (R.natDegree - 1) * DX + R.natDegree * DX :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hX) (Nat.mul_le_mul_left _ hdX)
    _ ≤ (2 * R.natDegree + 1) * DX := by
      have hn : (R.natDegree - 1) + R.natDegree ≤ 2 * R.natDegree + 1 := by omega
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right DX hn

/-- Including the leading coefficient costs at most one further block of
`DX`. -/
theorem factorXObstruction_natDegree_le
    {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (DX : ℕ)
    (hX : degreeX (mapZToRatFunc R) ≤ DX)
    (hlead : R.leadingCoeff.natDegree ≤ DX) :
    (factorXObstruction R).natDegree ≤ (2 * R.natDegree + 2) * DX := by
  calc
    (factorXObstruction R).natDegree
      ≤ R.leadingCoeff.natDegree + (rawSepResultant R).natDegree := by
        simpa [factorXObstruction] using
          (Polynomial.natDegree_mul_le :
            (R.leadingCoeff * rawSepResultant R).natDegree ≤
              R.leadingCoeff.natDegree + (rawSepResultant R).natDegree)
    _ ≤ DX + (2 * R.natDegree + 1) * DX :=
      Nat.add_le_add hlead (rawSepResultant_natDegree_le R DX hX)
    _ = (2 * R.natDegree + 2) * DX := by
      calc
        DX + (2 * R.natDegree + 1) * DX =
            1 * DX + (2 * R.natDegree + 1) * DX := by simp
        _ = (1 + (2 * R.natDegree + 1)) * DX := (Nat.add_mul ..).symm
        _ = (2 * R.natDegree + 2) * DX := by congr 1 <;> omega


/-- After specializing `X`, the factor obstruction has `Z`-degree at most
`2 * d * DZ`.  This uses the bivariate resultant bound directly; the older
`(2*d-1)*DZ` estimate omitted the leading-coefficient contribution. -/
theorem factorXObstruction_eval_natDegree_le
    {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (x : F) (d DZ : ℕ)
    (hpos : 0 < R.natDegree) (hdR : R.natDegree ≤ d)
    (hYZ : degreeX (triSpecializeX R x) ≤ DZ)
    (hlead : (Polynomial.eval (Polynomial.C x) R.leadingCoeff).natDegree ≤ DZ) :
    (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
      2 * d * DZ := by
  let B := triSpecializeX R x
  have hder : triSpecializeX R.derivative x = B.derivative := by
    simp [B, triSpecializeX, Polynomial.derivative_map]
  have hderZ : degreeX B.derivative ≤ DZ :=
    (degreeX_derivative_le B).trans hYZ
  have hresZ : (Polynomial.resultant B B.derivative R.natDegree
      (R.natDegree - 1)).natDegree ≤ (2 * R.natDegree - 1) * DZ := by
    calc
      _ ≤ (R.natDegree - 1) * degreeX B + R.natDegree * degreeX B.derivative :=
        bivariate_resultant_natDegree_le B B.derivative R.natDegree
          (R.natDegree - 1)
      _ ≤ (R.natDegree - 1) * DZ + R.natDegree * DZ :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hYZ) (Nat.mul_le_mul_left _ hderZ)
      _ = (2 * R.natDegree - 1) * DZ := by
        rw [← Nat.add_mul]
        congr 1
        omega
  have heval : Polynomial.eval (Polynomial.C x) (factorXObstruction R) =
      Polynomial.eval (Polynomial.C x) R.leadingCoeff *
        Polynomial.resultant B B.derivative R.natDegree (R.natDegree - 1) := by
    rw [factorXObstruction, Polynomial.eval_mul]
    congr 1
    calc
      Polynomial.eval (Polynomial.C x)
          (Polynomial.resultant R R.derivative R.natDegree (R.natDegree - 1)) =
        (Polynomial.evalRingHom (Polynomial.C x))
          (Polynomial.resultant R R.derivative R.natDegree (R.natDegree - 1)) := rfl
      _ = Polynomial.resultant
          (R.map (Polynomial.evalRingHom (Polynomial.C x)))
          (R.derivative.map (Polynomial.evalRingHom (Polynomial.C x)))
          R.natDegree (R.natDegree - 1) :=
        (Polynomial.resultant_map_map R R.derivative R.natDegree
          (R.natDegree - 1) (Polynomial.evalRingHom (Polynomial.C x))).symm
      _ = Polynomial.resultant B B.derivative R.natDegree
          (R.natDegree - 1) := by
        change Polynomial.resultant (triSpecializeX R x)
          (triSpecializeX R.derivative x) R.natDegree (R.natDegree - 1) = _
        rw [hder]
  rw [heval]
  calc
    (Polynomial.eval (Polynomial.C x) R.leadingCoeff *
      Polynomial.resultant B B.derivative R.natDegree
      (R.natDegree - 1)).natDegree ≤
        (Polynomial.eval (Polynomial.C x) R.leadingCoeff).natDegree +
        (Polynomial.resultant B B.derivative R.natDegree
          (R.natDegree - 1)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ DZ + (2 * R.natDegree - 1) * DZ := Nat.add_le_add hlead hresZ
    _ = 2 * R.natDegree * DZ := by
      calc
        DZ + (2 * R.natDegree - 1) * DZ =
            (1 + (2 * R.natDegree - 1)) * DZ := by simp [Nat.add_mul]
        _ = 2 * R.natDegree * DZ := by congr 1 <;> omega
    _ ≤ 2 * d * DZ := Nat.mul_le_mul_right DZ (Nat.mul_le_mul_left 2 hdR)

end ProximityPrize.SubmissionLower
