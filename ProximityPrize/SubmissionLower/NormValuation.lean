import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.SeparableIdealNorm


/-! .














 -/

namespace ProximityPrize.SubmissionLower.NormValuation

open scoped BigOperators nonZeroDivisors
open UniqueFactorizationMonoid IsDedekindDomain

noncomputable section

section Orders

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

/-- .
 -/
def orderAt (v : HeightOneSpectrum A) (x : FractionRing A) : ℤ :=
  -(v.valuation (FractionRing A) x).log

theorem orderAt_algebraMap (v : HeightOneSpectrum A) (x : A) (hx : x ≠ 0) :
    orderAt v (algebraMap A (FractionRing A) x) =
      ((normalizedFactors (Ideal.span {x})).count v.asIdeal : ℤ) := by
  rw [orderAt, v.valuation_of_algebraMap, v.intValuation_if_neg hx,
    WithZero.log_exp, neg_neg,
    Ideal.count_associates_factors_eq (by simpa using hx) v.isPrime v.ne_bot]

theorem orderAt_div (v : HeightOneSpectrum A) (x y : FractionRing A)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    orderAt v (x / y) = orderAt v x - orderAt v y := by
  unfold orderAt
  rw [map_div₀, WithZero.log_div (by simpa using hx) (by simpa using hy)]
  ring

end Orders

section FixedExtension

variable (R S : Type*) [CommRing R] [CommRing S]
variable [IsDedekindDomain R] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

local instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra _ _

variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

/-- .
 -/
def primeFiber (v : HeightOneSpectrum R) : Finset (Ideal S) :=
  IsDedekindDomain.primesOverFinset v.asIdeal S

theorem mem_primeFiber_iff (v : HeightOneSpectrum R) (P : Ideal S) :
    P ∈ primeFiber R S v ↔ P.IsPrime ∧ P.LiesOver v.asIdeal :=
  IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot S

/-- .
 -/
def fiberPlace (v : HeightOneSpectrum R)
    (P : {P : Ideal S // P ∈ primeFiber R S v}) : HeightOneSpectrum S :=
  ⟨P.1, ((mem_primeFiber_iff R S v P.1).mp P.2).1,
    Ideal.ne_bot_of_mem_primesOver v.ne_bot
      ((mem_primeFiber_iff R S v P.1).mp P.2)⟩

/-- . -/
theorem factorCount_relNorm_prime (v : HeightOneSpectrum R)
    (P : Ideal S) (hPzero : P ≠ ⊥) (hPprime : P.IsPrime) :
    (normalizedFactors (Ideal.relNorm R P)).count v.asIdeal =
      if P.under R = v.asIdeal then P.inertiaDeg R else 0 := by
  classical
  letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPzero hPprime
  have hUnderZero : P.under R ≠ ⊥ :=
    mt Ideal.eq_bot_of_comap_eq_bot hPzero
  have hUnderPrime : (P.under R).IsPrime := inferInstance
  have hUnderIrred : Irreducible (P.under R) :=
    (Ideal.prime_of_isPrime hUnderZero hUnderPrime).irreducible
  rw [SeparableIdealNorm.relNorm_prime_eq_pow R S P (P.under R),
    hUnderIrred.normalizedFactors_pow, normalize_eq, Multiset.count_replicate]

/-- .

 -/
theorem factorCount_relNorm (v : HeightOneSpectrum R)
    (I : Ideal S) (hI : I ≠ ⊥) :
    (normalizedFactors (Ideal.relNorm R I)).count v.asIdeal =
      ∑ P ∈ primeFiber R S v,
        P.inertiaDeg R * (normalizedFactors I).count P := by
  classical
  let C : Ideal S → Prop := fun J ↦ J ≠ 0 ∧
    (normalizedFactors (Ideal.relNorm R J)).count v.asIdeal =
      ∑ P ∈ primeFiber R S v,
        P.inertiaDeg R * (normalizedFactors J).count P
  have hC : C (normalizedFactors I).prod := by
    refine Multiset.prod_induction C (normalizedFactors I) ?_ ?_ ?_
    · intro J K hJ hK
      change _ ∧ _ at hJ hK ⊢
      refine ⟨mul_ne_zero hJ.1 hK.1, ?_⟩
      have hNJ : Ideal.relNorm R J ≠ 0 := by simpa using hJ.1
      have hNK : Ideal.relNorm R K ≠ 0 := by simpa using hK.1
      rw [map_mul, normalizedFactors_mul hNJ hNK, Multiset.count_add,
        hJ.2, hK.2, normalizedFactors_mul hJ.1 hK.1]
      simp only [Multiset.count_add, mul_add, Finset.sum_add_distrib]
    · change _ ∧ _
      exact ⟨one_ne_zero, by
        simp only [map_one, normalizedFactors_one, Multiset.count_zero,
          mul_zero, Finset.sum_const_zero]⟩
    · intro P hP
      have hPzero : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
      have hPprime : P.IsPrime := (Ideal.mem_normalizedFactors_iff hI).mp hP |>.1
      have hPirred : Irreducible P :=
        (Ideal.prime_of_isPrime hPzero hPprime).irreducible
      have hFactors : normalizedFactors P = {P} := by
        simpa using normalizedFactors_irreducible hPirred
      change _ ∧ _
      refine ⟨hPzero, ?_⟩
      rw [factorCount_relNorm_prime R S v P hPzero hPprime, hFactors]
      by_cases hUnder : P.under R = v.asIdeal
      · letI : P.LiesOver v.asIdeal := by rw [← hUnder]; infer_instance
        have hMem : P ∈ primeFiber R S v :=
          (mem_primeFiber_iff R S v P).mpr ⟨hPprime, inferInstance⟩
        simp [hUnder, Multiset.count_singleton, hMem]
      · have hNotMem : P ∉ primeFiber R S v := by
          intro hMem
          letI : P.LiesOver v.asIdeal :=
            ((mem_primeFiber_iff R S v P).mp hMem).2
          exact hUnder (Ideal.over_def P v.asIdeal).symm
        simp [hUnder, Multiset.count_singleton, hNotMem]
  have hCI : C I := by
    rwa [Ideal.prod_normalizedFactors_eq_self hI] at hC
  exact hCI.2

/-- .
 -/
theorem orderAt_intNorm (v : HeightOneSpectrum R) (x : S) (hx : x ≠ 0) :
    orderAt v (algebraMap R (FractionRing R) (Algebra.intNorm R S x)) =
      ∑ P ∈ (primeFiber R S v).attach,
        (P.1.inertiaDeg R : ℤ) *
          orderAt (fiberPlace R S v P)
            (algebraMap S (FractionRing S) x) := by
  classical
  have hCount := factorCount_relNorm R S v (Ideal.span {x}) (by simpa using hx)
  rw [Ideal.relNorm_singleton] at hCount
  have hTerms :
      (∑ P ∈ (primeFiber R S v).attach,
        (P.1.inertiaDeg R : ℤ) *
          orderAt (fiberPlace R S v P)
            (algebraMap S (FractionRing S) x)) =
      ∑ P ∈ primeFiber R S v,
        (P.inertiaDeg R : ℤ) * ((normalizedFactors (Ideal.span {x})).count P : ℤ) := by
    calc
      _ = ∑ P ∈ (primeFiber R S v).attach,
          (P.1.inertiaDeg R : ℤ) *
            ((normalizedFactors (Ideal.span {x})).count P.1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [orderAt_algebraMap _ x hx]
        rfl
      _ = _ := Finset.sum_attach (primeFiber R S v)
        (fun P : Ideal S ↦ (P.inertiaDeg R : ℤ) *
          ((normalizedFactors (Ideal.span {x})).count P : ℤ))
  rw [hTerms, orderAt_algebraMap v (Algebra.intNorm R S x) (by simpa using hx)]
  exact_mod_cast hCount

/-- .

 -/
theorem orderAt_fieldNorm (v : HeightOneSpectrum R)
    (x : FractionRing S) (hx : x ≠ 0) :
    orderAt v (Algebra.norm (FractionRing R) x) =
      ∑ P ∈ (primeFiber R S v).attach,
        (P.1.inertiaDeg R : ℤ) * orderAt (fiberPlace R S v P) x := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hbzero : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hazero : a ≠ 0 := by
    intro ha
    apply hx
    simp [ha]
  have hNorm :
      Algebra.norm (FractionRing R)
          (algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b) =
        algebraMap R (FractionRing R) (Algebra.intNorm R S a) /
          algebraMap R (FractionRing R) (Algebra.intNorm R S b) := by
    simp [div_eq_mul_inv, Algebra.norm_inv, Algebra.algebraMap_intNorm_fractionRing]
  rw [hNorm, orderAt_div v _ _ (by simpa using hazero) (by simpa using hbzero),
    orderAt_intNorm R S v a hazero, orderAt_intNorm R S v b hbzero,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro P _
  rw [orderAt_div _ _ _ (by simpa using hazero) (by simpa using hbzero), mul_sub]

end FixedExtension

end

end ProximityPrize.SubmissionLower.NormValuation
