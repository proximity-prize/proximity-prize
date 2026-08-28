import ProximityPrize.SubmissionLower.BCHKSHilbert90FiniteSeeds6400
import ProximityPrize.SubmissionLower.BCHKSFrobeniusCoordinateOwners6400
import ProximityPrize.SubmissionLower.BCHKSInhomogeneousCyclicCompatibility6400

/-!
# Exact scalar six-cycle compatibility over the production sextic field

For nonzero Frobenius coefficient `b`, equal cyclic norms make the explicit
six-cycle compatibility equation both necessary and sufficient for solving
`a*d + b*sigma(d) = r`.  The proof sandwiches dimensions: the semilinear
map has kernel dimension at most one, while Dedekind independence makes the
compatibility functional nonzero and hence gives its kernel dimension at
most five.
-/

open scoped BigOperators

namespace ProximityPrize.SubmissionLower.BCHKSScalarCyclicCompatibilityExact6400

open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower
open BCHKSHilbert90FiniteSeeds6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSInhomogeneousCyclicCompatibility6400
open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem koalaSextic_finrank6400 :
    Module.finrank KoalaBear.Field IRSProfile.Field = 6 := by
  have hcard := Module.card_eq_pow_finrank
    (K := KoalaBear.Field) (V := IRSProfile.Field)
  rw [KoalaBear.card_ext6] at hcard
  have hbase : Fintype.card KoalaBear.Field = KoalaBear.fieldSize := by
    norm_num [KoalaBear.Field, KoalaBear.fieldSize]
  rw [hbase] at hcard
  exact Nat.pow_right_injective (a := KoalaBear.fieldSize)
    (by norm_num [KoalaBear.fieldSize]) hcard.symm

@[simp]
theorem koalaFrobeniusAlgCharacter6400_one_apply
    (x : IRSProfile.Field) :
    koalaFrobeniusAlgCharacter6400 (1 : Fin 6) x =
      koalaSexticFrobenius x := by
  have h := koalaFrobeniusMonoidCharacter6400_eq_iterate
    (1 : Fin 6) x
  change koalaFrobeniusAlgCharacter6400 (1 : Fin 6) x =
    (koalaSexticFrobenius^[1]) x at h
  simpa only [Function.iterate_one] using h

noncomputable def koalaScalarSemilinear6400
    (a b : IRSProfile.Field) :
    IRSProfile.Field →ₗ[KoalaBear.Field] IRSProfile.Field :=
  LinearMap.mulLeft KoalaBear.Field a +
    LinearMap.mulLeft KoalaBear.Field b ∘ₗ
      (koalaFrobeniusAlgCharacter6400 (1 : Fin 6)).toLinearMap

@[simp]
theorem koalaScalarSemilinear6400_apply
    (a b d : IRSProfile.Field) :
    koalaScalarSemilinear6400 a b d =
      a * d + b * koalaSexticFrobenius d := by
  simp [koalaScalarSemilinear6400,
    koalaFrobeniusAlgCharacter6400_one_apply]

theorem koalaScalarSemilinear6400_finrank_ker_le_one
    (a b : IRSProfile.Field) (hab : ¬(a = 0 ∧ b = 0)) :
    Module.finrank KoalaBear.Field
      (koalaScalarSemilinear6400 a b).ker ≤ 1 := by
  classical
  let T := koalaScalarSemilinear6400 a b
  let kernelFinset : Finset IRSProfile.Field :=
    Finset.univ.filter fun d => T d = 0
  have hpair : ¬(b = 0 ∧ -a = 0) := by
    rintro ⟨hb, ha⟩
    apply hab
    exact ⟨neg_eq_zero.mp ha, hb⟩
  have hkernel_eq_fiber :
      kernelFinset = frobeniusValueFiber koalaSexticFrobenius b (-a) := by
    ext d
    simp only [kernelFinset, frobeniusValueFiber, Finset.mem_filter,
      Finset.mem_univ, true_and, T, koalaScalarSemilinear6400_apply]
    constructor <;> intro h <;> linear_combination h
  have hkernel : kernelFinset.card ≤ 2130706433 := by
    rw [hkernel_eq_fiber]
    exact
      card_frobeniusValueFiber_le koalaSexticFrobenius
        2130706433 (by norm_num) koalaSexticFrobenius_apply
        b (-a) hpair
  letI : Fintype T.ker := Fintype.ofFinite T.ker
  have hcard : Fintype.card T.ker ≤ 2130706433 := by
    rw [Fintype.card_of_subtype kernelFinset (by
      intro d
      simp only [kernelFinset, Finset.mem_filter, Finset.mem_univ,
        true_and, LinearMap.mem_ker])]
    exact hkernel
  have hmodule := Module.card_eq_pow_finrank
    (K := KoalaBear.Field) (V := T.ker)
  have hbase : Fintype.card KoalaBear.Field = 2130706433 := by
    norm_num [KoalaBear.Field, KoalaBear.fieldSize]
  rw [hbase] at hmodule
  have hpow :
      2130706433 ^ Module.finrank KoalaBear.Field T.ker ≤
        2130706433 ^ 1 := by
    rw [← hmodule]
    simpa using hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2130706433)).mp hpow

noncomputable def koalaScalarConjugate6400
    (i : Fin 6) (x : IRSProfile.Field) : IRSProfile.Field :=
  koalaFrobeniusAlgCharacter6400 i x

noncomputable def koalaScalarCompatibilityCoefficients6400
    (a b : IRSProfile.Field) : Fin 6 → IRSProfile.Field :=
  fun i => match i.1 with
    | 0 => -(koalaScalarConjugate6400 5 a *
        koalaScalarConjugate6400 4 a *
        koalaScalarConjugate6400 3 a *
        koalaScalarConjugate6400 2 a *
        koalaScalarConjugate6400 1 a)
    | 1 => koalaScalarConjugate6400 5 a *
        koalaScalarConjugate6400 4 a *
        koalaScalarConjugate6400 3 a *
        koalaScalarConjugate6400 2 a *
        koalaScalarConjugate6400 0 b
    | 2 => -(koalaScalarConjugate6400 5 a *
        koalaScalarConjugate6400 4 a *
        koalaScalarConjugate6400 3 a *
        koalaScalarConjugate6400 0 b *
        koalaScalarConjugate6400 1 b)
    | 3 => koalaScalarConjugate6400 5 a *
        koalaScalarConjugate6400 4 a *
        koalaScalarConjugate6400 0 b *
        koalaScalarConjugate6400 1 b *
        koalaScalarConjugate6400 2 b
    | 4 => -(koalaScalarConjugate6400 5 a *
        koalaScalarConjugate6400 0 b *
        koalaScalarConjugate6400 1 b *
        koalaScalarConjugate6400 2 b *
        koalaScalarConjugate6400 3 b)
    | _ => koalaScalarConjugate6400 0 b *
        koalaScalarConjugate6400 1 b *
        koalaScalarConjugate6400 2 b *
        koalaScalarConjugate6400 3 b *
        koalaScalarConjugate6400 4 b

noncomputable def koalaScalarCompatibilityLinear6400
    (a b : IRSProfile.Field) :
    IRSProfile.Field →ₗ[KoalaBear.Field] IRSProfile.Field :=
  koalaFrobeniusCombinationLinear6400
    (koalaScalarCompatibilityCoefficients6400 a b)

theorem koalaScalarCompatibilityLinear6400_apply
    (a b r : IRSProfile.Field) :
    koalaScalarCompatibilityLinear6400 a b r =
      koalaScalarConjugate6400 0 b *
          koalaScalarConjugate6400 1 b *
          koalaScalarConjugate6400 2 b *
          koalaScalarConjugate6400 3 b *
          koalaScalarConjugate6400 4 b *
          koalaScalarConjugate6400 5 r -
        koalaScalarConjugate6400 5 a *
          koalaScalarConjugate6400 0 b *
          koalaScalarConjugate6400 1 b *
          koalaScalarConjugate6400 2 b *
          koalaScalarConjugate6400 3 b *
          koalaScalarConjugate6400 4 r +
        koalaScalarConjugate6400 5 a *
          koalaScalarConjugate6400 4 a *
          koalaScalarConjugate6400 0 b *
          koalaScalarConjugate6400 1 b *
          koalaScalarConjugate6400 2 b *
          koalaScalarConjugate6400 3 r -
        koalaScalarConjugate6400 5 a *
          koalaScalarConjugate6400 4 a *
          koalaScalarConjugate6400 3 a *
          koalaScalarConjugate6400 0 b *
          koalaScalarConjugate6400 1 b *
          koalaScalarConjugate6400 2 r +
        koalaScalarConjugate6400 5 a *
          koalaScalarConjugate6400 4 a *
          koalaScalarConjugate6400 3 a *
          koalaScalarConjugate6400 2 a *
          koalaScalarConjugate6400 0 b *
          koalaScalarConjugate6400 1 r -
        koalaScalarConjugate6400 5 a *
          koalaScalarConjugate6400 4 a *
          koalaScalarConjugate6400 3 a *
          koalaScalarConjugate6400 2 a *
          koalaScalarConjugate6400 1 a *
          koalaScalarConjugate6400 0 r := by
  change (∑ i : Fin 6,
    koalaScalarCompatibilityCoefficients6400 a b i *
      koalaFrobeniusAlgCharacter6400 i r) = _
  rw [Fin.sum_univ_six]
  norm_num [koalaScalarCompatibilityCoefficients6400,
    koalaScalarConjugate6400]
  ring

theorem koalaScalarCompatibilityLinear6400_ne_zero
    (a b : IRSProfile.Field) (hb : b ≠ 0) :
    koalaScalarCompatibilityLinear6400 a b ≠ 0 := by
  have hconj (i : Fin 6) : koalaScalarConjugate6400 i b ≠ 0 := by
    exact (_root_.map_ne_zero
      (f := koalaFrobeniusAlgCharacter6400 i)).mpr hb
  have hc5 : koalaScalarCompatibilityCoefficients6400 a b (5 : Fin 6) ≠ 0 := by
    change koalaScalarConjugate6400 0 b *
      koalaScalarConjugate6400 1 b *
      koalaScalarConjugate6400 2 b *
      koalaScalarConjugate6400 3 b *
      koalaScalarConjugate6400 4 b ≠ 0
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (hconj 0) (hconj 1)) (hconj 2)) (hconj 3)) (hconj 4)
  obtain ⟨t, ht⟩ :=
    exists_koalaFrobeniusCharacterCombination_ne_zero6400
      (koalaScalarCompatibilityCoefficients6400 a b) ⟨5, hc5⟩
  intro hzero
  have hvalue := LinearMap.congr_fun hzero t
  apply ht
  change (∑ i : Fin 6,
    koalaScalarCompatibilityCoefficients6400 a b i *
      koalaFrobeniusAlgCharacter6400 i t) = 0 at hvalue
  have hcoerce (i : Fin 6) :
      koalaFrobeniusMonoidCharacter6400 i t =
        koalaFrobeniusAlgCharacter6400 i t := rfl
  simpa only [hcoerce] using hvalue

theorem koalaScalarCompatibilityLinear6400_finrank_ker_le_five
    (a b : IRSProfile.Field) (hb : b ≠ 0) :
    Module.finrank KoalaBear.Field
      (koalaScalarCompatibilityLinear6400 a b).ker ≤ 5 := by
  have hne := koalaScalarCompatibilityLinear6400_ne_zero a b hb
  have hker : (koalaScalarCompatibilityLinear6400 a b).ker ≠ ⊤ := by
    intro htop
    exact hne (LinearMap.ker_eq_top.mp htop)
  have hlt := Submodule.finrank_lt hker
  rw [koalaSextic_finrank6400] at hlt
  omega

theorem koalaFrobeniusConjugate_C_iterate6400
    (n : Nat) (x : IRSProfile.Field) :
    koalaFrobeniusConjugate n (Polynomial.C x) =
      Polynomial.C ((koalaSexticFrobenius^[n]) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate, ih, Polynomial.map_C]
      simp only [Function.iterate_succ_apply']
      change Polynomial.C
        (koalaSexticFrobenius ((koalaSexticFrobenius^[n]) x)) = _
      rfl

theorem koalaFrobeniusConjugate_C_scalar6400
    (i : Fin 6) (x : IRSProfile.Field) :
    koalaFrobeniusConjugate i.1 (Polynomial.C x) =
      Polynomial.C (koalaScalarConjugate6400 i x) := by
  rw [koalaFrobeniusConjugate_C_iterate6400]
  congr 1
  symm
  have h := koalaFrobeniusMonoidCharacter6400_eq_iterate i x
  change koalaFrobeniusAlgCharacter6400 i x =
    (koalaSexticFrobenius^[i.1]) x at h
  simpa only [koalaScalarConjugate6400] using h

@[simp] theorem koalaFrobeniusConjugate_C_zero6400
    (x : IRSProfile.Field) :
    koalaFrobeniusConjugate 0 (Polynomial.C x) =
      Polynomial.C (koalaScalarConjugate6400 0 x) := by
  simpa using koalaFrobeniusConjugate_C_scalar6400 (0 : Fin 6) x

@[simp] theorem koalaFrobeniusConjugate_C_one6400
    (x : IRSProfile.Field) :
    koalaFrobeniusConjugate 1 (Polynomial.C x) =
      Polynomial.C (koalaScalarConjugate6400 1 x) := by
  simpa using koalaFrobeniusConjugate_C_scalar6400 (1 : Fin 6) x

@[simp] theorem koalaFrobeniusConjugate_C_two6400
    (x : IRSProfile.Field) :
    koalaFrobeniusConjugate 2 (Polynomial.C x) =
      Polynomial.C (koalaScalarConjugate6400 2 x) := by
  simpa using koalaFrobeniusConjugate_C_scalar6400 (2 : Fin 6) x

@[simp] theorem koalaFrobeniusConjugate_C_three6400
    (x : IRSProfile.Field) :
    koalaFrobeniusConjugate 3 (Polynomial.C x) =
      Polynomial.C (koalaScalarConjugate6400 3 x) := by
  simpa using koalaFrobeniusConjugate_C_scalar6400 (3 : Fin 6) x

@[simp] theorem koalaFrobeniusConjugate_C_four6400
    (x : IRSProfile.Field) :
    koalaFrobeniusConjugate 4 (Polynomial.C x) =
      Polynomial.C (koalaScalarConjugate6400 4 x) := by
  simpa using koalaFrobeniusConjugate_C_scalar6400 (4 : Fin 6) x

@[simp] theorem koalaFrobeniusConjugate_C_five6400
    (x : IRSProfile.Field) :
    koalaFrobeniusConjugate 5 (Polynomial.C x) =
      Polynomial.C (koalaScalarConjugate6400 5 x) := by
  simpa using koalaFrobeniusConjugate_C_scalar6400 (5 : Fin 6) x

noncomputable def koalaScalarCyclicNormSix6400
    (a : IRSProfile.Field) : IRSProfile.Field :=
  koalaScalarConjugate6400 0 a *
    koalaScalarConjugate6400 1 a *
    koalaScalarConjugate6400 2 a *
    koalaScalarConjugate6400 3 a *
    koalaScalarConjugate6400 4 a *
    koalaScalarConjugate6400 5 a

theorem koalaCyclicNormSix_C6400 (a : IRSProfile.Field) :
    koalaCyclicNormSix (Polynomial.C a) =
      Polynomial.C (koalaScalarCyclicNormSix6400 a) := by
  simp only [koalaCyclicNormSix, koalaScalarCyclicNormSix6400,
    koalaFrobeniusConjugate_C_zero6400,
    koalaFrobeniusConjugate_C_one6400,
    koalaFrobeniusConjugate_C_two6400,
    koalaFrobeniusConjugate_C_three6400,
    koalaFrobeniusConjugate_C_four6400,
    koalaFrobeniusConjugate_C_five6400,
    Polynomial.C_mul]

theorem koalaCyclicCompatibilitySix_C6400
    (a b r : IRSProfile.Field) :
    koalaCyclicCompatibilitySix (Polynomial.C a) (Polynomial.C b)
        (Polynomial.C r) =
      Polynomial.C (koalaScalarCompatibilityLinear6400 a b r) := by
  rw [koalaScalarCompatibilityLinear6400_apply]
  simp only [koalaCyclicCompatibilitySix,
    koalaFrobeniusConjugate_C_zero6400,
    koalaFrobeniusConjugate_C_one6400,
    koalaFrobeniusConjugate_C_two6400,
    koalaFrobeniusConjugate_C_three6400,
    koalaFrobeniusConjugate_C_four6400,
    koalaFrobeniusConjugate_C_five6400,
    Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub]

theorem koalaScalarCompatibilityLinear6400_semilinear_eq_zero
    (a b d : IRSProfile.Field)
    (hnorm : koalaScalarCyclicNormSix6400 a =
      koalaScalarCyclicNormSix6400 b) :
    koalaScalarCompatibilityLinear6400 a b
        (koalaScalarSemilinear6400 a b d) = 0 := by
  have hnormC :
      koalaCyclicNormSix (Polynomial.C a) =
        koalaCyclicNormSix (Polynomial.C b) := by
    rw [koalaCyclicNormSix_C6400, koalaCyclicNormSix_C6400, hnorm]
  have h := koalaCyclicCompatibilitySix_eq_zero_of_norm_eq
    (Polynomial.C a) (Polynomial.C b) (Polynomial.C d) hnormC
  have hforcing :
      Polynomial.C a * Polynomial.C d +
          Polynomial.C b *
            (Polynomial.C d).map koalaSexticFrobenius.toRingHom =
        Polynomial.C (koalaScalarSemilinear6400 a b d) := by
    simp only [Polynomial.map_C, Polynomial.C_mul, Polynomial.C_add,
      koalaScalarSemilinear6400_apply]
    have hcoe : koalaSexticFrobenius.toRingHom d =
        koalaSexticFrobenius d := rfl
    rw [hcoe]
  rw [hforcing, koalaCyclicCompatibilitySix_C6400] at h
  exact Polynomial.C_eq_zero.mp h

theorem koalaScalarSemilinear6400_range_le_compatibility_ker
    (a b : IRSProfile.Field)
    (hnorm : koalaScalarCyclicNormSix6400 a =
      koalaScalarCyclicNormSix6400 b) :
    (koalaScalarSemilinear6400 a b).range ≤
      (koalaScalarCompatibilityLinear6400 a b).ker := by
  rintro r ⟨d, rfl⟩
  exact LinearMap.mem_ker.mpr
    (koalaScalarCompatibilityLinear6400_semilinear_eq_zero
      a b d hnorm)

theorem koalaScalarSemilinear6400_finrank_range_ge_five
    (a b : IRSProfile.Field) (hab : ¬(a = 0 ∧ b = 0)) :
    5 ≤ Module.finrank KoalaBear.Field
      (koalaScalarSemilinear6400 a b).range := by
  have hker := koalaScalarSemilinear6400_finrank_ker_le_one a b hab
  have hrank :=
    (koalaScalarSemilinear6400 a b).finrank_range_add_finrank_ker
  rw [koalaSextic_finrank6400] at hrank
  omega

theorem koalaScalarSemilinear6400_range_eq_compatibility_ker
    (a b : IRSProfile.Field) (hb : b ≠ 0)
    (hnorm : koalaScalarCyclicNormSix6400 a =
      koalaScalarCyclicNormSix6400 b) :
    (koalaScalarSemilinear6400 a b).range =
      (koalaScalarCompatibilityLinear6400 a b).ker := by
  have hab : ¬(a = 0 ∧ b = 0) := by
    rintro ⟨_, hbzero⟩
    exact hb hbzero
  have hrange := koalaScalarSemilinear6400_range_le_compatibility_ker
    a b hnorm
  apply Submodule.eq_of_le_of_finrank_le hrange
  exact (koalaScalarCompatibilityLinear6400_finrank_ker_le_five
    a b hb).trans
      (koalaScalarSemilinear6400_finrank_range_ge_five a b hab)

/-- Equal cyclic norms make the explicit six-cycle equation not only
necessary but sufficient for scalar semilinear solvability. -/
theorem koalaScalarCompatibilityLinear6400_eq_zero_iff_exists
    (a b r : IRSProfile.Field) (hb : b ≠ 0)
    (hnorm : koalaScalarCyclicNormSix6400 a =
      koalaScalarCyclicNormSix6400 b) :
    koalaScalarCompatibilityLinear6400 a b r = 0 ↔
      ∃ d : IRSProfile.Field,
        a * d + b * koalaSexticFrobenius d = r := by
  constructor
  · intro hr
    have hrker : r ∈ (koalaScalarCompatibilityLinear6400 a b).ker :=
      LinearMap.mem_ker.mpr hr
    rw [← koalaScalarSemilinear6400_range_eq_compatibility_ker
      a b hb hnorm] at hrker
    obtain ⟨d, hd⟩ := hrker
    exact ⟨d, by simpa only [koalaScalarSemilinear6400_apply] using hd⟩
  · rintro ⟨d, rfl⟩
    simpa only [koalaScalarSemilinear6400_apply] using
      koalaScalarCompatibilityLinear6400_semilinear_eq_zero
        a b d hnorm

end ProximityPrize.SubmissionLower.BCHKSScalarCyclicCompatibilityExact6400
