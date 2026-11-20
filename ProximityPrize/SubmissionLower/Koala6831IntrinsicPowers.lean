import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open Polynomial

noncomputable section

set_option autoImplicit false

variable {K E : Type*} [Field K] [Field E]

def powerField (E : Type*) [Field E] (p : ℕ) [ExpChar E p] : Subfield E :=
  (frobenius E p).fieldRange

theorem mem_powerField_iff {p : ℕ} [ExpChar E p] {x : E} :
    x ∈ powerField E p ↔ ∃ y : E, y ^ p = x :=
  RingHom.mem_fieldRange

theorem pow_mem_powerField (p : ℕ) [ExpChar E p] (x : E) :
    x ^ p ∈ powerField E p :=
  mem_powerField_iff.mpr ⟨x, rfl⟩

theorem algebraMap_mem_powerField [Algebra K E] (p : ℕ) [ExpChar E p] [PerfectRing K p]
    (a : K) : algebraMap K E a ∈ powerField E p := by
  obtain ⟨b, hb⟩ := (PerfectRing.bijective_frobenius (R := K) (p := p)).2 a
  change b ^ p = a at hb
  exact mem_powerField_iff.mpr ⟨algebraMap K E b, by rw [← map_pow, hb]⟩

theorem minpoly_powerField_degree (p : ℕ) [ExpChar E p] (hp : p.Prime)
    (z : E) (hz : z ∉ powerField E p) :
    (minpoly (powerField E p) z).natDegree = p := by
  let A := powerField E p
  let a : A := ⟨z ^ p, pow_mem_powerField p z⟩
  let f : A[X] := Polynomial.X ^ p - Polynomial.C a
  have hnopow (b : A) : b ^ p ≠ a := by
    intro h
    have hb : (b : E) ^ p = z ^ p := by exact congrArg Subtype.val h
    have heq : (b : E) = z := (frobenius E p).injective hb
    exact hz (heq ▸ b.property)
  have hirr : Irreducible f := X_pow_sub_C_irreducible_of_prime hp hnopow
  have hroot : aeval z f = 0 := by
    simp only [f, map_sub, map_pow, aeval_X, aeval_C]
    change z ^ p - z ^ p = 0
    exact sub_self _
  have hmonic : f.Monic := monic_X_pow_sub_C a hp.ne_zero
  rw [← minpoly.eq_of_irreducible hirr hroot, hmonic.leadingCoeff, inv_one, C_1, mul_one]
  exact natDegree_X_pow_sub_C

theorem eq_zero_of_aeval_powerField (p : ℕ) [ExpChar E p] (hp : p.Prime)
    (z : E) (hz : z ∉ powerField E p) (F : (powerField E p)[X])
    (hdeg : F.natDegree < p) (hroot : aeval z F = 0) :
    F = 0 := by
  by_contra hne
  have hdiv : minpoly (powerField E p) z ∣ F := minpoly.dvd (powerField E p) z hroot
  have hle := natDegree_le_of_dvd hdiv hne
  rw [minpoly_powerField_degree p hp z hz] at hle
  omega

theorem power_affine_parameters_subsingleton [Algebra K E] (p : ℕ)
    [ExpChar E p] [PerfectRing K p] (y z : E)
    (hactive : y ∉ powerField E p ∨ z ∉ powerField E p) :
    {a : K | y + algebraMap K E a * z ∈ powerField E p}.Subsingleton := by
  let A := powerField E p
  intro a ha b hb
  by_contra hne
  have hdiff : algebraMap K E (a - b) * z ∈ A := by
    have hs := A.sub_mem ha hb
    rw [show (y + algebraMap K E a * z) - (y + algebraMap K E b * z) =
        algebraMap K E (a - b) * z by rw [map_sub]; ring] at hs
    exact hs
  have han : algebraMap K E (a - b) ≠ 0 :=
    by simpa only [map_zero] using (algebraMap K E).injective.ne (sub_ne_zero.mpr hne)
  have hz : z ∈ A := by
    have h := A.mul_mem (A.inv_mem (algebraMap_mem_powerField p (a-b))) hdiff
    rwa [← mul_assoc, inv_mul_cancel₀ han, one_mul] at h
  have hy : y ∈ A := by
    have h := A.sub_mem ha (A.mul_mem (algebraMap_mem_powerField p a) hz)
    rwa [add_sub_cancel_right] at h
  rcases hactive with hactive | hactive
  · exact hactive hy
  · exact hactive hz

theorem ratFunc_X_ne_pow (p : ℕ) (hp : p.Prime) (a : RatFunc K) :
    a ^ p ≠ RatFunc.X := by
  intro ha
  let ι := algebraMap K[X] (RatFunc K)
  have hinj : Function.Injective ι := IsFractionRing.injective _ _
  have hden : ι a.denom ^ p ≠ 0 := pow_ne_zero _ (by
    simpa only [map_zero] using hinj.ne (RatFunc.denom_ne_zero a))
  have hquot : ι a.num ^ p / ι a.denom ^ p = RatFunc.X := by
    rw [← div_pow, RatFunc.num_div_denom, ha]
  have hmul : a.num ^ p = (Polynomial.X : K[X]) * a.denom ^ p := by
    apply hinj
    simpa only [ι, map_pow, map_mul, RatFunc.algebraMap_X] using (div_eq_iff hden).mp hquot
  have hdeg := congrArg Polynomial.natDegree hmul
  rw [natDegree_pow, natDegree_mul X_ne_zero (pow_ne_zero _ (RatFunc.denom_ne_zero _)),
    natDegree_X, natDegree_pow] at hdeg
  have hdvd : p ∣ 1 + p * a.denom.natDegree := hdeg ▸ dvd_mul_right p a.num.natDegree
  have hone : p ∣ (1 + p * a.denom.natDegree) - p * a.denom.natDegree :=
    Nat.dvd_sub hdvd (dvd_mul_right p _)
  exact hp.not_dvd_one (by simpa using hone)

theorem separating_ratFunc_coordinate_notin_powerField (p : ℕ) (hp : p.Prime)
    [ExpChar (RatFunc K) p] [ExpChar E p] [Algebra (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] :
    algebraMap (RatFunc K) E (RatFunc.X : RatFunc K) ∉ powerField E p := by
  intro h
  obtain ⟨a, ha⟩ := mem_powerField_iff.mp h
  have hbot : IntermediateField.adjoin (RatFunc K) ({a ^ p} : Set E) ≤
      (⊥ : IntermediateField (RatFunc K) E) :=
    IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.mem_bot.mpr ⟨RatFunc.X, ha.symm⟩)
  have heq := IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable'
    (RatFunc K) E a p
  rw [← heq] at hbot
  have hmem : a ∈ (⊥ : IntermediateField (RatFunc K) E) :=
    hbot (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.mp hmem
  apply ratFunc_X_ne_pow p hp b
  apply (algebraMap (RatFunc K) E).injective
  rw [map_pow, hb, ha]

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
