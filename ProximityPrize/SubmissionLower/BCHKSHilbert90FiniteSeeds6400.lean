import ProximityPrize.SubmissionLower.BCHKSCyclicNormSpecialization6400

/-!
# Six fixed Hilbert--90 seeds over the production sextic field

Dedekind independence guarantees that a nontrivial linear combination of
distinct Frobenius characters is nonzero somewhere in the sextic field.  In
the production extension those character combinations are linear over the
KoalaBear base field.  The six coordinate vectors therefore suffice: every
nontrivial scalar or polynomial combination is nonzero at one of six fixed
seeds.

Applied to the six-term Hilbert--90 numerator, this replaces an arbitrary
per-specialization seed by one of six globally fixed choices.  The result is
only a finite uniformization lemma; it does not assert that a common seed by
itself gives affine alignment.
-/

open scoped BigOperators

open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower
open ProximityPrize.SubmissionLower.BCHKSCyclicNormErrorEvaluator6400

namespace ProximityPrize.SubmissionLower.BCHKSHilbert90FiniteSeeds6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

local instance : CharP IRSProfile.Field 2130706433 :=
  ProximityPrize.SubmissionLower.koalaSexticChar

local instance : Fact (Nat.Prime 2130706433) :=
  ProximityPrize.SubmissionLower.koalaPrimeFact

noncomputable def koalaCoordinateSeed6400 (i : Fin 6) : IRSProfile.Field :=
  CompPoly.Extension.Ext.ofFn fun j => if j = i then 1 else 0

@[simp]
theorem koalaCoordinateSeed6400_coeff (i j : Fin 6) :
    CompPoly.Extension.Ext.coeff (koalaCoordinateSeed6400 i) j =
      if j = i then 1 else 0 := by
  simp [koalaCoordinateSeed6400]

theorem koalaCoordinateSeed6400_sum (x : IRSProfile.Field) :
    ∑ i : Fin 6,
        CompPoly.Extension.Ext.coeff x i • koalaCoordinateSeed6400 i = x := by
  apply CompPoly.Extension.Ext.ext
  intro j
  let coeffLinear : IRSProfile.Field →ₗ[KoalaBear.Field] KoalaBear.Field :=
    { toFun := fun y => CompPoly.Extension.Ext.coeff y j
      map_add' := fun a b => CompPoly.Extension.Ext.coeff_add a b j
      map_smul' := fun a y => CompPoly.Extension.Ext.coeff_smul a y j }
  change coeffLinear (∑ i : Fin 6,
      CompPoly.Extension.Ext.coeff x i • koalaCoordinateSeed6400 i) =
        coeffLinear x
  rw [map_sum]
  simp [coeffLinear, koalaCoordinateSeed6400]

theorem koalaExt6Gen_cubed_ne_one6400 :
    KoalaBear.ext6Gen ^ 3 ≠ (1 : IRSProfile.Field) := by
  intro h
  have hroot := KoalaBear.ext6Gen_cubed_is_primitive_cube_root
  rw [h] at hroot
  have hcoeff := congrArg
    (fun x : IRSProfile.Field =>
      CompPoly.Extension.Ext.coeff x (0 : Fin 6)) hroot
  have hthree : (3 : KoalaBear.Field) ≠ 0 := by
    intro hzero
    have hdvd : KoalaBear.fieldSize ∣ 3 :=
      (CharP.cast_eq_zero_iff KoalaBear.Field KoalaBear.fieldSize 3).mp hzero
    norm_num [KoalaBear.fieldSize] at hdvd
  apply hthree
  have hzeroBase : (1 : KoalaBear.Field) + 1 + 1 = 0 := by
    simpa only [one_pow, CompPoly.Extension.Ext.coeff_add,
    CompPoly.Extension.Ext.coeff_one,
    CompPoly.Extension.Ext.coeff_ofBase,
    CompPoly.Extension.Ext.coeff_zero, Fin.val_zero, if_pos] using hcoeff
  norm_num at hzeroBase ⊢
  exact hzeroBase

theorem koalaExt6Gen_order6400 :
    orderOf (KoalaBear.ext6Gen : IRSProfile.Field) = 9 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · exact KoalaBear.ext6Gen_pow_nine
  · intro p hp hpdiv
    have hp3 : p = 3 := by
      have hpdivpow : p ∣ 3 ^ 2 := by
        norm_num at hpdiv ⊢
        exact hpdiv
      have hpdivthree : p ∣ 3 := hp.dvd_of_dvd_pow hpdivpow
      exact (Nat.prime_dvd_prime_iff_eq hp
        Nat.prime_three).mp hpdivthree
    subst p
    norm_num
    exact koalaExt6Gen_cubed_ne_one6400

/-- The first six powers of the base-field Frobenius, packaged as algebra
maps so that their base-linearity is available later. -/
noncomputable def koalaFrobeniusAlgCharacter6400 (i : Fin 6) :
    IRSProfile.Field →ₐ[KoalaBear.Field] IRSProfile.Field :=
  FiniteField.frobeniusAlgHom KoalaBear.Field IRSProfile.Field ^ i.1

theorem koalaFrobeniusAlgCharacter6400_apply
    (i : Fin 6) (x : IRSProfile.Field) :
    koalaFrobeniusAlgCharacter6400 i x =
      x ^ (Fintype.card KoalaBear.Field ^ i.1) := by
  simp [koalaFrobeniusAlgCharacter6400, AlgHom.coe_pow,
    FiniteField.coe_frobeniusAlgHom, pow_iterate]

noncomputable def koalaFrobeniusMonoidCharacter6400 (i : Fin 6) :
    IRSProfile.Field →* IRSProfile.Field :=
  (koalaFrobeniusAlgCharacter6400 i).toMonoidHom

def koalaFrobeniusResidue6400 : Fin 6 → Fin 9 :=
  ![1, 2, 4, 8, 7, 5]

theorem koalaFrobeniusResidue6400_injective :
    Function.Injective koalaFrobeniusResidue6400 := by
  decide

theorem koalaFrobeniusResidue6400_apply (i : Fin 6) :
    (2130706433 ^ i.1) % 9 = (koalaFrobeniusResidue6400 i).1 := by
  fin_cases i <;> decide

theorem koalaFrobeniusMonoidCharacter6400_eq_power
    (i j : Fin 6)
    (hij : koalaFrobeniusMonoidCharacter6400 i =
      koalaFrobeniusMonoidCharacter6400 j) :
    (KoalaBear.ext6Gen : IRSProfile.Field) ^
        (Fintype.card KoalaBear.Field ^ i.1) =
      KoalaBear.ext6Gen ^ (Fintype.card KoalaBear.Field ^ j.1) := by
  have hvalue := DFunLike.congr_fun hij
    (KoalaBear.ext6Gen : IRSProfile.Field)
  simpa [koalaFrobeniusMonoidCharacter6400,
    koalaFrobeniusAlgCharacter6400_apply] using hvalue

set_option maxHeartbeats 200000 in
theorem koalaFrobeniusMonoidCharacter6400_eq_mod_nine
    (i j : Fin 6)
    (hpow :
      (KoalaBear.ext6Gen : IRSProfile.Field) ^
          (Fintype.card KoalaBear.Field ^ i.1) =
        KoalaBear.ext6Gen ^ (Fintype.card KoalaBear.Field ^ j.1)) :
    Fintype.card KoalaBear.Field ^ i.1 ≡
      Fintype.card KoalaBear.Field ^ j.1 [MOD 9] := by
  have horder :
      Fintype.card KoalaBear.Field ^ i.1 ≡
        Fintype.card KoalaBear.Field ^ j.1
          [MOD orderOf (KoalaBear.ext6Gen : IRSProfile.Field)] :=
    (show IsOfFinOrder (KoalaBear.ext6Gen : IRSProfile.Field) from
      isOfFinOrder_iff_pow_eq_one.mpr
        ⟨9, by norm_num, KoalaBear.ext6Gen_pow_nine⟩).pow_eq_pow_iff_modEq.mp hpow
  simpa only [koalaExt6Gen_order6400] using horder

theorem koalaFrobeniusMonoidCharacter6400_injective :
    Function.Injective koalaFrobeniusMonoidCharacter6400 := by
  intro i j hij
  have hmod := koalaFrobeniusMonoidCharacter6400_eq_mod_nine i j
    (koalaFrobeniusMonoidCharacter6400_eq_power i j hij)
  have hcard : Fintype.card KoalaBear.Field = 2130706433 := by
    norm_num [KoalaBear.Field, KoalaBear.fieldSize]
  rw [hcard] at hmod
  change (2130706433 ^ i.1) % 9 = (2130706433 ^ j.1) % 9 at hmod
  apply koalaFrobeniusResidue6400_injective
  apply Fin.ext
  rw [← koalaFrobeniusResidue6400_apply i,
    ← koalaFrobeniusResidue6400_apply j]
  exact hmod

theorem koalaFrobeniusMonoidCharacter6400_eq_iterate
    (i : Fin 6) (x : IRSProfile.Field) :
    koalaFrobeniusMonoidCharacter6400 i x =
      (koalaSexticFrobenius^[i.1]) x := by
  have hcard : Fintype.card KoalaBear.Field = 2130706433 := by
    norm_num [KoalaBear.Field, KoalaBear.fieldSize]
  rw [koalaFrobeniusMonoidCharacter6400]
  change koalaFrobeniusAlgCharacter6400 i x =
    (koalaSexticFrobenius^[i.1]) x
  rw [koalaFrobeniusAlgCharacter6400_apply, hcard]
  symm
  simpa only [koalaSexticFrobenius, coe_frobeniusEquiv] using
    (iterate_frobenius (R := IRSProfile.Field) 2130706433 i.1 x)

theorem koalaFrobeniusCharacter6400_linearIndependent :
    LinearIndependent IRSProfile.Field
      (fun i : Fin 6 =>
        (koalaFrobeniusMonoidCharacter6400 i :
          IRSProfile.Field → IRSProfile.Field)) := by
  exact (linearIndependent_monoidHom IRSProfile.Field IRSProfile.Field).comp
    koalaFrobeniusMonoidCharacter6400
    koalaFrobeniusMonoidCharacter6400_injective

theorem exists_koalaFrobeniusCharacterCombination_ne_zero6400
    (c : Fin 6 → IRSProfile.Field) (hc : ∃ i, c i ≠ 0) :
    ∃ t : IRSProfile.Field,
      ∑ i, c i * koalaFrobeniusMonoidCharacter6400 i t ≠ 0 := by
  classical
  let l : Fin 6 →₀ IRSProfile.Field := Finsupp.equivFunOnFinite.symm c
  have hl : l ≠ 0 := by
    obtain ⟨i, hi⟩ := hc
    intro hzero
    apply hi
    have hcoeff := congrArg (fun v : Fin 6 →₀ IRSProfile.Field => v i) hzero
    simpa [l] using hcoeff
  have hcomb :
      Finsupp.linearCombination IRSProfile.Field
        (fun i : Fin 6 =>
          (koalaFrobeniusMonoidCharacter6400 i :
            IRSProfile.Field → IRSProfile.Field)) l ≠ 0 := by
    intro hzero
    exact hl ((linearIndependent_iff.mp
      koalaFrobeniusCharacter6400_linearIndependent) l hzero)
  by_contra hall
  push Not at hall
  apply hcomb
  funext t
  simpa [Finsupp.linearCombination, Finsupp.sum_fintype, l] using hall t

noncomputable def koalaFrobeniusCombinationLinear6400
    (c : Fin 6 → IRSProfile.Field) :
    IRSProfile.Field →ₗ[KoalaBear.Field] IRSProfile.Field where
  toFun t := ∑ i, c i * koalaFrobeniusAlgCharacter6400 i t
  map_add' x y := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [map_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Algebra.smul_def]
    rw [RingHom.id_apply]
    ring

theorem exists_koalaCoordinateSeedCombination_ne_zero6400
    (c : Fin 6 → IRSProfile.Field) (hc : ∃ i, c i ≠ 0) :
    ∃ j : Fin 6,
      ∑ i, c i * koalaFrobeniusMonoidCharacter6400 i
        (koalaCoordinateSeed6400 j) ≠ 0 := by
  obtain ⟨t, ht⟩ :=
    exists_koalaFrobeniusCharacterCombination_ne_zero6400 c hc
  let G := koalaFrobeniusCombinationLinear6400 c
  have hGt : G t ≠ 0 := by
    simpa [G, koalaFrobeniusCombinationLinear6400,
      koalaFrobeniusMonoidCharacter6400] using ht
  by_contra hall
  push Not at hall
  have hseed : ∀ j : Fin 6, G (koalaCoordinateSeed6400 j) = 0 := by
    intro j
    simpa [G, koalaFrobeniusCombinationLinear6400,
      koalaFrobeniusMonoidCharacter6400] using hall j
  apply hGt
  calc
    G t = G (∑ j : Fin 6,
        CompPoly.Extension.Ext.coeff t j • koalaCoordinateSeed6400 j) := by
      rw [koalaCoordinateSeed6400_sum]
    _ = ∑ j : Fin 6, CompPoly.Extension.Ext.coeff t j •
        G (koalaCoordinateSeed6400 j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
    _ = 0 := by simp [hseed]

theorem exists_koalaCoordinateSeedPolynomialCombination_ne_zero6400
    (C : Fin 6 → Polynomial IRSProfile.Field) (hC : ∃ i, C i ≠ 0) :
    ∃ j : Fin 6,
      ∑ i, C i * Polynomial.C
        (koalaFrobeniusMonoidCharacter6400 i
          (koalaCoordinateSeed6400 j)) ≠ 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hC
  have hcoeff : ∃ n, (C i₀).coeff n ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hi₀
    apply Polynomial.ext
    intro n
    exact hall n
  obtain ⟨n, hn⟩ := hcoeff
  let c : Fin 6 → IRSProfile.Field := fun i => (C i).coeff n
  obtain ⟨j, hj⟩ := exists_koalaCoordinateSeedCombination_ne_zero6400
    c ⟨i₀, by simpa [c] using hn⟩
  refine ⟨j, ?_⟩
  intro hzero
  have hcoefficient := congrArg
    (fun P : Polynomial IRSProfile.Field => P.coeff n) hzero
  apply hj
  simpa [c, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C] using hcoefficient

/-- Coefficients of the six-term Hilbert--90 numerator.  The `i`th
coefficient uses `A` in the first `i` Frobenius lanes and `B` in the
remaining lanes. -/
noncomputable def koalaHilbert90Coefficient6400
    (A B : Polynomial IRSProfile.Field) (i : Fin 6) :
    Polynomial IRSProfile.Field :=
  ∏ k : Fin 5,
    koalaFrobeniusConjugate k.1 (if k.1 < i.1 then A else B)

noncomputable def koalaHilbert90Numerator6400
    (A B : Polynomial IRSProfile.Field) (t : IRSProfile.Field) :
    Polynomial IRSProfile.Field :=
  ∑ i : Fin 6, koalaHilbert90Coefficient6400 A B i *
    Polynomial.C (koalaFrobeniusMonoidCharacter6400 i t)

theorem exists_koalaCoordinateSeed_hilbert90Numerator_ne_zero6400
    (A B : Polynomial IRSProfile.Field) (hB : B ≠ 0) :
    ∃ j : Fin 6,
      koalaHilbert90Numerator6400 A B (koalaCoordinateSeed6400 j) ≠ 0 := by
  have hcoefficient : ∃ i : Fin 6,
      koalaHilbert90Coefficient6400 A B i ≠ 0 := by
    refine ⟨0, ?_⟩
    simp only [koalaHilbert90Coefficient6400, Fin.val_zero,
      Nat.not_lt_zero, ↓reduceIte]
    exact Finset.prod_ne_zero_iff.mpr fun k hk =>
      koalaFrobeniusConjugate_ne_zero B hB k.1
  simpa [koalaHilbert90Numerator6400] using
    exists_koalaCoordinateSeedPolynomialCombination_ne_zero6400
      (koalaHilbert90Coefficient6400 A B) hcoefficient

end ProximityPrize.SubmissionLower.BCHKSHilbert90FiniteSeeds6400
