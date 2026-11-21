import ProximityPrize.SubmissionLower.Fast065

namespace ProjectivePole
noncomputable section
open Polynomial K1_14_1_7
open scoped BigOperators Polynomial

/-- Homogeneous change of basis on a fixed active-seed slice. The passive
seed exponent fixes d, so the single scalar on the left works for the slice. -/
theorem homogeneous_reexpansion {R : Type*} [CommRing R] (a b c z : R)
    (d i : ℕ) (hi : i ≤ d) :
    (a*b)^d * z^i =
      ∑ k ∈ Finset.range (d-i+1),
        ((d-i).choose k : R) * b^i * (-c)^k * a^(d-i-k) *
          (a*z)^(i+k) * (b+c*z)^(d-i-k) := by
  have hlin : -c*(a*z) + a*(b+c*z) = a*b := by ring
  have hpow : i+(d-i) = d := Nat.add_sub_of_le hi
  calc
    _ = b^i*(a*z)^i * ((-c)*(a*z) + a*(b+c*z))^(d-i) := by
      rw [hlin, ← hpow, pow_add]
      simp only [Nat.add_sub_cancel_left]
      rw [mul_pow, mul_pow]
      ring
    _ = _ := by
      rw [add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mul_pow,pow_add]
      ring

/-- Evaluate a normalized weight-k column at the actual projective centre.
Every column in active degree d acquires the same nonzero factor. -/
theorem evaluate_column {F : Type} [Field F] (side : Fin 2) (a b c : F) (hb : b ≠ 0)
    (d k : ℕ) (hk : k ≤ d) :
    let z := algebraMap (Seed F) (SeedFrac F) (MvPolynomial.X side)
    let den := algebraMap F (SeedFrac F) b + algebraMap F (SeedFrac F) c * z
    den ≠ 0 ∧
      (algebraMap F (SeedFrac F) a * z)^k * den^(d-k) =
        den^d * (residue side a b c)^k := by
  dsimp only
  let z := algebraMap (Seed F) (SeedFrac F) (MvPolynomial.X side)
  let den := algebraMap F (SeedFrac F) b + algebraMap F (SeedFrac F) c * z
  have nonzero : K1_14_1_7_2.denominator side b c ≠ 0 := by
    intro eq
    have h := congrArg (fun p : Seed F => p.coeff 0) eq
    apply hb
    simpa [K1_14_1_7_2.denominator, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero_X] using h
  have mapC (t : F) : algebraMap (Seed F) (SeedFrac F) (MvPolynomial.C t) =
      algebraMap F (SeedFrac F) t := (IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F) t).symm
  have hn : den ≠ 0 := by
    have h := (IsFractionRing.injective (Seed F) (SeedFrac F)).ne nonzero
    simpa [K1_14_1_7_2.denominator,K1_14_1_7_2.numerator,mapC,den,z] using h
  refine ⟨hn,?_⟩
  change _ = den^d * ((algebraMap F (SeedFrac F) a * z) / den)^k
  have split : den^d = den^k * den^(d-k) := by rw [← pow_add,Nat.add_sub_of_le hk]
  rw [split,div_pow]
  field_simp
  simp [den,z,mul_comm]

/-- The previously proved simple-pole normalization accepts exactly the
truncated chart whose matrix is counted in PoleBlocks. -/
theorem local_to_CRT {F : Type} [Field F] (H : F[X]) (lift : (SeedFrac F)[X])
    (α : F) (side : Fin 2) (a b c : F) (M : ℕ) (P : TrueSource F)
    (hH : H.eval α = 0)
    (hz : lift.eval (algebraMap F (SeedFrac F) α) = residue side a b c)
    (htest : (K1_14_1.jetConstant ((Polynomial.X (R := SeedFrac F)) ^ M) :
      JetPolys (SeedFrac F)) ∣ K1_14_1_7_2.zeroSubst (K1_14_1_7_2.centered α (residue side a b c) P)) :
    (K1_14_1.jetConstant ((Polynomial.X - Polynomial.C (algebraMap F (SeedFrac F) α)) ^ M) :
      JetPolys (SeedFrac F)) ∣ K1_14_1_7.forward H lift P :=
  K1_14_1_7_2.transfer_dvd H lift α _ M P hH hz (K1_14_1_7_2.linear_pole_dvd α _ M P htest)

end
end ProjectivePole
