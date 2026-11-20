import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantWitness
import ProximityPrize.SubmissionLower.Koala6844VirtualHighValueFreeDerivatives
import ProximityPrize.SubmissionLower.Koala6844VirtualHighRawLocal


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic MvPolynomial RCN065 RCN135 RCN136 RCN344 RCN347

noncomputable section

variable {K : Type} [Field K]

theorem curve_plain_persistence_of_trim (F V W S theta : Carrier K)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (carrier : surfaceMap (polynomialEmbedding K) F ∈ C)
    (regular : surfaceMap (polynomialEmbedding K) (implicitRegularity F) ∉ C)
    (divisor_ne : surfaceMap (polynomialEmbedding K) V ∉ C)
    (seed_ne : surfaceMap (polynomialEmbedding K) S ∉ C)
    (shape : W = S * MvPolynomial.X 1 - theta)
    (sX : S.degreeOf 0 ≤ 0) (sY : S.degreeOf 1 ≤ 0)
    (vY : V.degreeOf 1 ≤ 0) (thetaY : theta.degreeOf 1 ≤ 0)
    (trimDegree divisorDegree plainDegree : ℕ)
    (vDegree : V.degreeOf 0 ≤ divisorDegree)
    (thetaDegree : theta.degreeOf 0 ≤ divisorDegree)
    (hdegree : trimDegree+divisorDegree ≤ plainDegree)
    (later : ∀ j, surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W (trimDegree+j)) ∈ C) :
    ∀ delay, surfaceMap (polynomialEmbedding K) (tailNumerator F (plainDegree+delay)) ∈ C := by
  let φ := polynomialEmbedding K
  let coeff := componentCoefficients φ C
  let point := componentPoint φ C
  have zero (P : Carrier K) :
      MvPolynomial.eval₂Hom coeff point P = 0 ↔ surfaceMap φ P ∈ C :=
    component_evaluation_zero_iff φ C P
  have fixed : regularDerivation F (regularImage F S) = 0 :=
    iterate_regularDerivation_eq_zero_of_value_free F S 0 1 sY sX (by omega)
  intro j
  apply (zero _).mp
  apply persistent_raw_tails_from_trim F V W S theta coeff point
    ((zero F).mpr carrier) ((not_congr (zero _)).mpr regular)
    ((not_congr (zero _)).mpr divisor_ne) ((not_congr (zero _)).mpr seed_ne)
    shape fixed trimDegree divisorDegree divisorDegree plainDegree hdegree (by omega)
  · intro i hi
    obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact (zero _).mpr (later delay)
  · intro i hi
    exact iterate_regularDerivation_eq_zero_of_value_free F V divisorDegree i vY vDegree hi
  · intro i hi
    exact iterate_regularDerivation_eq_zero_of_value_free F theta divisorDegree i thetaY thetaDegree hi
  · omega

theorem rawTrimmedTail_dvd_add (F V W : Carrier K) (first : ℕ)
    (hfirst : F ∣ rawTrimmedTail F V W first) (delay : ℕ) :
    F ∣ rawTrimmedTail F V W (first+delay) := by
  have stable (A : Carrier K) (hA : F ∣ A) : F ∣ clearedImplicit F A := by
    obtain ⟨B, rfl⟩ := hA
    have hF : trimDerivation F F = 0 := by
      rw [trimDerivation_apply, clearedImplicit, implicitRegularity]
      ring
    rw [← trimDerivation_apply, leibniz_product, hF, zero_mul, zero_add]
    exact dvd_mul_right _ _
  induction delay with
  | zero => simpa only [Nat.add_zero] using hfirst
  | succ j ih =>
    rw [Nat.add_succ, rawTrimmedTail_succ]
    exact dvd_sub (dvd_mul_of_dvd_right (stable _ ih) _) (dvd_mul_of_dvd_right ih _)

structure InvariantTrim (V W : Carrier K) (first plain : ℕ) where
  denominator : Carrier K
  remainder : Carrier K
  divisorDegree : ℕ
  shape : W = denominator * MvPolynomial.X 1 - remainder
  denominator_X : denominator.degreeOf 0 ≤ 0
  denominator_Y : denominator.degreeOf 1 ≤ 0
  divisor_Y : V.degreeOf 1 ≤ 0
  remainder_Y : remainder.degreeOf 1 ≤ 0
  divisor_X : V.degreeOf 0 ≤ divisorDegree
  remainder_X : remainder.degreeOf 0 ≤ divisorDegree
  enlargedDegree : first+divisorDegree ≤ plain

theorem InvariantTrim.component_persistence {F V W : Carrier K} {first plain : ℕ}
    (trim : InvariantTrim V W first plain)
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (Fmem : surfaceMap (polynomialEmbedding K) F ∈ C)
    (Hnot : surfaceMap (polynomialEmbedding K) (implicitRegularity F) ∉ C)
    (Vnot : surfaceMap (polynomialEmbedding K) V ∉ C)
    (Snot : surfaceMap (polynomialEmbedding K) trim.denominator ∉ C)
    (later : ∀ j, surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W (first+j)) ∈ C) :
    ∀ j, surfaceMap (polynomialEmbedding K) (tailNumerator F (plain+j)) ∈ C :=
  curve_plain_persistence_of_trim F V W trim.denominator trim.remainder C
    Fmem Hnot Vnot Snot trim.shape trim.denominator_X trim.denominator_Y trim.divisor_Y
    trim.remainder_Y first trim.divisorDegree plain trim.divisor_X trim.remainder_X
    trim.enlargedDegree later

theorem InvariantTrim.geometric_factor_persistence {F V W : Carrier K} {first plain : ℕ}
    (trim : InvariantTrim V W first plain)
    (G : MvPolynomial (Fin 3) (GenericField K))
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (Hnot : ¬ G ∣ surfaceMap (polynomialEmbedding K) (implicitRegularity F))
    (Vnot : ¬ G ∣ surfaceMap (polynomialEmbedding K) V)
    (Snot : ¬ G ∣ surfaceMap (polynomialEmbedding K) trim.denominator)
    (whole : F ∣ rawTrimmedTail F V W first) :
    ∀ j, G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F (plain+j)) := by
  let C := Ideal.span ({G} : Set (MvPolynomial (Fin 3) (GenericField K)))
  letI : C.IsPrime := Ideal.isPrime_span_singleton_of_prime hG.prime
  have mem (P : Carrier K) : surfaceMap (polynomialEmbedding K) P ∈ C ↔
      G ∣ surfaceMap (polynomialEmbedding K) P := Ideal.mem_span_singleton
  intro j
  exact (mem _).mp (trim.component_persistence C ((mem _).mpr hdiv)
    ((not_congr (mem _)).mpr Hnot) ((not_congr (mem _)).mpr Vnot)
    ((not_congr (mem _)).mpr Snot)
    (fun delay => (mem _).mpr
      (hdiv.trans (map_dvd (surfaceMap (polynomialEmbedding K))
        (rawTrimmedTail_dvd_add F V W first whole delay)))) j)

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
