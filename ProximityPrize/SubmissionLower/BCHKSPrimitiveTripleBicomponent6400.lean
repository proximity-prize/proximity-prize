import ProximityPrize.SubmissionLower.BCHKSPrimitiveTripleRelation6400

/-!
# Eliminating one-lane primitive rank-one relations

The full-gcd quotient pair is coprime over the challenge fraction field.  If
one quotient lane vanished, the other would therefore be constant in the
locator variable.  Away from the zeros of its single challenge coefficient,
the homogeneous error relation would force every genuine error coordinate
into the fixed coordinate defect set.  The shell has at least `76771` genuine
errors, whereas that set has at most `54291` coordinates.  Since the
coefficient has challenge degree at most the Cramer cap, it cannot vanish on
the entire retained owner family.

Consequently both quotient lanes are nonzero.  The smaller Frobenius-lane
degree then sharpens the primitive factor bound from `54291` to `22488`.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSPrimitiveTripleBicomponent6400

open Polynomial
open Polynomial.Bivariate
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSPrimitiveTripleRelation6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

private abbrev CramerChallengeCap : Nat := 76779 * 2130706433

/-- A polynomial which becomes a unit after injecting its coefficient ring
into the fraction field is constant in the outer variable. -/
theorem natDegree_eq_zero_of_fractionMap_isUnit
    (P : IRSProfile.Field[X][X])
    (hunit : IsUnit
      (P.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X])))) :
    P.natDegree = 0 := by
  let K := FractionRing IRSProfile.Field[X]
  let iota : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  have hinj : Function.Injective iota :=
    IsFractionRing.injective IRSProfile.Field[X] K
  have hmap : (P.map iota).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [Polynomial.natDegree_map_eq_of_injective hinj P] at hmap
  exact hmap

/-- A factor quotient inherits the coordinatewise challenge-degree cap of
the product. -/
theorem quotient_coeff_zero_natDegree_le
    (P H Q : IRSProfile.Field[X][X]) (S : Nat)
    (hfactor : P = H * Q) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hcoeff : ∀ n, (P.coeff n).natDegree ≤ S) :
    (Q.coeff 0).natDegree ≤ S := by
  have hPdegree : degreeX P ≤ S :=
    degreeX_le_of_coeff_natDegree_le P S hcoeff
  have hmul : degreeX (H * Q) = degreeX H + degreeX Q :=
    Polynomial.Bivariate.degreeX_mul H Q hH hQ
  have hQdegree : degreeX Q ≤ S := by
    rw [hfactor, hmul] at hPdegree
    omega
  exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX Q 0).trans hQdegree

/-- On a retained shell family, a coprime primitive quotient relation cannot
have a zero homogeneous lane. -/
theorem score6400_primitive_quotient_pair_both_ne_zero
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A' B' C' : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (T : Finset IRSProfile.Field)
    (hqdegree : ∀ n, (q n).natDegree ≤ CramerChallengeCap)
    (hHpositive : 0 < H.natDegree)
    (hHcap : H.natDegree ≤ homogeneousLocatorCap)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A')
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B')
    (hcoprime :
      IsCoprime
        (A'.map (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X])))
        (B'.map (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X]))))
    (hpairNe : A' ≠ 0 ∨ B' ≠ 0)
    (hFixedCard : Fixed.card ≤ H.natDegree)
    (hrelations :
      ∀ z ∈ T,
        ∀ A : Finset IRSProfile.Index, ∀ P : IRSProfile.Field[X],
          185364 ≤ A.card →
          P.natDegree ≤ 131071 →
          (∀ i ∈ A,
            P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) →
          ∀ i, i ∉ Fixed →
            (A'.map (Polynomial.evalRingHom z)).eval
                  (IRSProfile.domain i) *
                ((f₀ i + z * f₁ i) -
                  P.eval (IRSProfile.domain i)) +
              (B'.map (Polynomial.evalRingHom z)).eval
                  (IRSProfile.domain i) *
                (koalaSexticFrobenius (f₀ i + z * f₁ i) -
                  (P.map koalaSexticFrobenius.toRingHom).eval
                    (IRSProfile.domain i)) = 0)
    (hTcard : ownerFloor ≤ T.card)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    A' ≠ 0 ∧ B' ≠ 0 := by
  classical
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero] at hHpositive
    simp at hHpositive
  constructor
  · intro hAzero
    have hBne : B' ≠ 0 :=
      hpairNe.resolve_left (fun hAne ↦ hAne hAzero)
    have hBunit : IsUnit
        (B'.map (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X]))) := by
      rw [hAzero, Polynomial.map_zero] at hcoprime
      exact isCoprime_zero_left.mp hcoprime
    have hBdegree : B'.natDegree = 0 :=
      natDegree_eq_zero_of_fractionMap_isUnit B' hBunit
    let b : IRSProfile.Field[X] := B'.coeff 0
    have hBeq : B' = Polynomial.C b := by
      simpa only [b] using Polynomial.eq_C_of_natDegree_eq_zero hBdegree
    have hbne : b ≠ 0 := by
      intro hbzero
      apply hBne
      rw [hBeq, hbzero, Polynomial.C_0]
    have hbdegree : b.natDegree ≤ CramerChallengeCap := by
      apply quotient_coeff_zero_natDegree_le
        (score6400PolynomialLocatorRelationPair q).2.1 H B'
          CramerChallengeCap hBfactor hHne hBne
      intro n
      exact score6400PolynomialLocatorRelationPair_snd_coeff_natDegree_le
        q CramerChallengeCap n hqdegree
    have hbRoots : ∀ z ∈ T, b.eval z = 0 := by
      intro z hz
      by_contra hbz
      obtain ⟨A, P, E, hAcard, hPdegree, hagree, _hpair,
          hEdef, hElower, _hEupper⟩ :=
        exists_score6400_large_error_witness
          f₀ f₁ z (hbad z hz) (hnotOld z hz)
      have hrelation := hrelations z hz A P hAcard hPdegree hagree
      have hEsub : E ⊆ Fixed := by
        intro i hiE
        by_contra hiFixed
        have hrel := hrelation i hiFixed
        rw [hAzero, Polynomial.map_zero, hBeq,
          Polynomial.map_C, Polynomial.eval_zero, zero_mul, zero_add,
          Polynomial.eval_C] at hrel
        have hsecond :
            koalaSexticFrobenius (f₀ i + z * f₁ i) -
                (P.map koalaSexticFrobenius.toRingHom).eval
                  (IRSProfile.domain i) = 0 :=
          (mul_eq_zero.mp hrel).resolve_left hbz
        have hiError :
            (f₀ i + z * f₁ i) -
                P.eval (IRSProfile.domain i) ≠ 0 := by
          rw [hEdef] at hiE
          exact (Finset.mem_filter.mp hiE).2
        have hmapEval := polynomial_map_eval_of_fixed_locator
          koalaSexticFrobenius P (IRSProfile.domain i)
            (koalaSexticFrobenius_fixed_domain i)
        have hsecond' :
            koalaSexticFrobenius
              ((f₀ i + z * f₁ i) -
                P.eval (IRSProfile.domain i)) = 0 := by
          rw [map_sub, ← hmapEval]
          exact hsecond
        apply hiError
        apply koalaSexticFrobenius.injective
        simpa only [map_zero] using hsecond'
      have hEcard := Finset.card_le_card hEsub
      norm_num [homogeneousLocatorCap] at hHcap
      omega
    apply hbne
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      b T hbRoots
    have hcaplt : CramerChallengeCap < ownerFloor := by
      norm_num [CramerChallengeCap, ownerFloor]
    exact hbdegree.trans_lt (hcaplt.trans_le hTcard)
  · intro hBzero
    have hAne : A' ≠ 0 :=
      hpairNe.resolve_right (fun hBne ↦ hBne hBzero)
    have hAunit : IsUnit
        (A'.map (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X]))) := by
      rw [hBzero, Polynomial.map_zero] at hcoprime
      exact isCoprime_zero_right.mp hcoprime
    have hAdegree : A'.natDegree = 0 :=
      natDegree_eq_zero_of_fractionMap_isUnit A' hAunit
    let a : IRSProfile.Field[X] := A'.coeff 0
    have hAeq : A' = Polynomial.C a := by
      simpa only [a] using Polynomial.eq_C_of_natDegree_eq_zero hAdegree
    have hane : a ≠ 0 := by
      intro hazero
      apply hAne
      rw [hAeq, hazero, Polynomial.C_0]
    have hadegree : a.natDegree ≤ CramerChallengeCap := by
      apply quotient_coeff_zero_natDegree_le
        (score6400PolynomialLocatorRelationPair q).1.1 H A'
          CramerChallengeCap hAfactor hHne hAne
      intro n
      exact score6400PolynomialLocatorRelationPair_fst_coeff_natDegree_le
        q CramerChallengeCap n hqdegree
    have haRoots : ∀ z ∈ T, a.eval z = 0 := by
      intro z hz
      by_contra haz
      obtain ⟨A, P, E, hAcard, hPdegree, hagree, _hpair,
          hEdef, hElower, _hEupper⟩ :=
        exists_score6400_large_error_witness
          f₀ f₁ z (hbad z hz) (hnotOld z hz)
      have hrelation := hrelations z hz A P hAcard hPdegree hagree
      have hEsub : E ⊆ Fixed := by
        intro i hiE
        by_contra hiFixed
        have hrel := hrelation i hiFixed
        rw [hBzero, Polynomial.map_zero, hAeq,
          Polynomial.map_C, Polynomial.eval_zero, zero_mul, add_zero,
          Polynomial.eval_C] at hrel
        have hfirst :
            (f₀ i + z * f₁ i) -
                P.eval (IRSProfile.domain i) = 0 :=
          (mul_eq_zero.mp hrel).resolve_left haz
        rw [hEdef] at hiE
        exact (Finset.mem_filter.mp hiE).2 hfirst
      have hEcard := Finset.card_le_card hEsub
      norm_num [homogeneousLocatorCap] at hHcap
      omega
    apply hane
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      a T haRoots
    have hcaplt : CramerChallengeCap < ownerFloor := by
      norm_num [CramerChallengeCap, ownerFloor]
    exact hadegree.trans_lt (hcaplt.trans_le hTcard)

/-- Production endpoint with the spurious one-lane cases removed.  Since the
Frobenius quotient is nonzero, the common primitive factor has locator degree
at most `22488`, the sharp cap of the smaller homogeneous lane. -/
theorem exists_score6400_rankOne_bicomponentPrimitiveTriple
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLtwo : 2 ≤ L)
    (hrankOne : ∀ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 = 0)
    (T : Finset IRSProfile.Field)
    (hTcard : ownerFloor ≤ T.card)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∃ q : Score6400LocatorMinorIndex → IRSProfile.Field[X],
      ∃ H A' B' C' : IRSProfile.Field[X][X],
        ∃ Fixed : Finset IRSProfile.Index,
          q ∈ LinearMap.ker
              (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin ∧
          (∀ n, (q n).natDegree ≤ CramerChallengeCap) ∧
          H.IsPrimitive ∧ 0 < H.natDegree ∧
          H.natDegree ≤ 22488 ∧
          (score6400PolynomialLocatorRelationPair q).1.1 = H * A' ∧
          (score6400PolynomialLocatorRelationPair q).2.1 = H * B' ∧
          score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C' ∧
          IsCoprime
            (A'.map (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X])))
            (B'.map (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X]))) ∧
          A' ≠ 0 ∧ B' ≠ 0 ∧
          Fixed = fixedCoordinateDefect H ∧
          Fixed.card ≤ H.natDegree ∧
          ∀ z ∈ T,
            ∀ A : Finset IRSProfile.Index, ∀ P : IRSProfile.Field[X],
              185364 ≤ A.card →
              P.natDegree ≤ 131071 →
              (∀ i ∈ A,
                P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) →
              C'.map (Polynomial.evalRingHom z) =
                  A'.map (Polynomial.evalRingHom z) * P +
                    B'.map (Polynomial.evalRingHom z) *
                      P.map koalaSexticFrobenius.toRingHom ∧
                ∀ i, i ∉ Fixed →
                  (A'.map (Polynomial.evalRingHom z)).eval
                        (IRSProfile.domain i) *
                      ((f₀ i + z * f₁ i) -
                        P.eval (IRSProfile.domain i)) +
                    (B'.map (Polynomial.evalRingHom z)).eval
                        (IRSProfile.domain i) *
                      (koalaSexticFrobenius (f₀ i + z * f₁ i) -
                        (P.map koalaSexticFrobenius.toRingHom).eval
                          (IRSProfile.domain i)) = 0 := by
  classical
  obtain ⟨q, H, A', B', C', Fixed, hqker, hqdegree, hHprimitive,
      hHpositive, hHcap, hAfactor, hBfactor, hCfactor, hcoprime,
      hpairNe, hFixed, hFixedCard, howners⟩ :=
    exists_score6400_rankOne_fixedCoordinateSemilinearRelation
      f₀ f₁ L hkernelRank hLtwo hrankOne T hTcard hbad hnotOld
  have hboth := score6400_primitive_quotient_pair_both_ne_zero
    f₀ f₁ q H A' B' C' Fixed T hqdegree hHpositive hHcap
      hAfactor hBfactor hcoprime hpairNe hFixedCard
      (fun z hz A P hA hP hagree i hi ↦
        (howners z hz A P hA hP hagree).2 i hi)
      hTcard hbad hnotOld
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero] at hHpositive
    simp at hHpositive
  have hBrawNe :
      (score6400PolynomialLocatorRelationPair q).2.1 ≠ 0 := by
    rw [hBfactor]
    exact mul_ne_zero hHne hboth.2
  have hBrawDegree :
      (score6400PolynomialLocatorRelationPair q).2.1.natDegree <
        locatorFrobeniusRows6400 := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hBrawNe]
    exact Polynomial.mem_degreeLT.mp
      (score6400PolynomialLocatorRelationPair q).2.2
  have hdegreeEq := congrArg Polynomial.natDegree hBfactor
  rw [Polynomial.natDegree_mul hHne hboth.2] at hdegreeEq
  have hHsharp : H.natDegree ≤ 22488 := by
    norm_num [locatorFrobeniusRows6400] at hBrawDegree
    omega
  exact ⟨q, H, A', B', C', Fixed, hqker, hqdegree, hHprimitive,
    hHpositive, hHsharp, hAfactor, hBfactor, hCfactor, hcoprime,
    hboth.1, hboth.2, hFixed, hFixedCard, howners⟩

end BCHKSPrimitiveTripleBicomponent6400
end ProximityPrize.SubmissionLower
