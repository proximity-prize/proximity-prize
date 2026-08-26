import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphGaugeSupportFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveFaithfulGraphGauge6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphGaugeFork6401
open BCHKSFrobeniusGraphHilbert90Audit6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
section Dedekind
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
theorem exists_characterCombination_ne_zero6401
    (phi : I → F →* F) (hphi : Function.Injective phi)
    (c : I → F) (hc : ∃ i, c i ≠ 0) :
    ∃ t : F, ∑ i, c i * phi i t ≠ 0 := by
  classical
  let l : I →₀ F := Finsupp.equivFunOnFinite.symm c
  have hl : l ≠ 0 := by
    obtain ⟨i, hi⟩ := hc
    intro hzero
    apply hi
    have hcoeff := congrArg (fun v : I →₀ F => v i) hzero
    simpa [l] using hcoeff
  have hLI : LinearIndependent F (fun i => (phi i : F → F)) :=
    (linearIndependent_monoidHom F F).comp phi hphi
  have hcomb :
      Finsupp.linearCombination F (fun i => (phi i : F → F)) l ≠ 0 := by
    intro hzero
    exact hl ((linearIndependent_iff.mp hLI) l hzero)
  by_contra hall
  push Not at hall
  apply hcomb
  funext t
  simpa [Finsupp.linearCombination, Finsupp.sum_fintype, l] using hall t
theorem exists_bivariateCharacterCombination_ne_zero6401
    (phi : I → F →* F) (hphi : Function.Injective phi)
    (C : I → F[X][X]) (hC : ∃ i, C i ≠ 0) :
    ∃ t : F,
      ∑ i, C i * Polynomial.C (Polynomial.C (phi i t)) ≠ 0 := by
  classical
  obtain ⟨i0, hi0⟩ := hC
  have houter : ∃ n, (C i0).coeff n ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hi0
    apply Polynomial.ext
    intro n
    exact hall n
  obtain ⟨n, hn⟩ := houter
  have hinner : ∃ m, ((C i0).coeff n).coeff m ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hn
    apply Polynomial.ext
    intro m
    exact hall m
  obtain ⟨m, hm⟩ := hinner
  let c : I → F := fun i => ((C i).coeff n).coeff m
  obtain ⟨t, ht⟩ := exists_characterCombination_ne_zero6401
    phi hphi c ⟨i0, by simpa [c] using hm⟩
  refine ⟨t, ?_⟩
  intro hzero
  have hcoeff := congrArg
    (fun P : F[X][X] => (P.coeff n).coeff m) hzero
  apply ht
  simpa [c, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C] using hcoeff
end Dedekind
section GraphGauge
variable {F : Type*} [Field F] [DecidableEq F]
def frobeniusIterateRingHom6401 (sigma : F →+* F) : Nat → F →+* F
  | 0 => RingHom.id F
  | n + 1 => sigma.comp (frobeniusIterateRingHom6401 sigma n)
def sixFrobeniusCharacter6401
    (sigma : F →+* F) (i : Fin 6) : F →* F :=
  (frobeniusIterateRingHom6401 sigma i.1).toMonoidHom
theorem comp_X_pow_injective6401 (q : Nat) (hq : 0 < q) :
    Function.Injective
      (fun P : F[X] => P.comp (Polynomial.X ^ q)) := by
  intro P Q heq
  have hzero : (P - Q).comp (Polynomial.X ^ q) = 0 := by
    rw [Polynomial.sub_comp]
    exact sub_eq_zero.mpr heq
  rw [Polynomial.comp_eq_zero_iff] at hzero
  rcases hzero with hdiff | hconstant
  · exact sub_eq_zero.mp hdiff
  · exfalso
    have hnonconstant : (Polynomial.X ^ q : F[X]) ≠
        Polynomial.C ((Polynomial.X ^ q : F[X]).coeff 0) := by
      intro heqConstant
      have hdegree := congrArg Polynomial.natDegree heqConstant
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at hdegree
      omega
    exact hnonconstant hconstant.2
theorem challengeFrobeniusRingHom_injective6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q) :
    Function.Injective
      (challengeFrobeniusRingHom6401 sigma q) := by
  change Function.Injective
    (fun P : F[X] => (P.map sigma).comp (Polynomial.X ^ q))
  exact (comp_X_pow_injective6401 q hq).comp
    (Polynomial.map_injective sigma sigma.injective)
theorem graphTwist_ne_zero6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (P : F[X][X]) (hP : P ≠ 0) :
    graphTwist6401 sigma q P ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff
    (challengeFrobeniusRingHom_injective6401 sigma q hq)).2 hP
theorem graphHilbert90Denominator_ne_zero6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (B : F[X][X]) (hB : B ≠ 0) :
    graphHilbert90Denominator6401 sigma q B ≠ 0 := by
  have h1 : graphTwist6401 sigma q B ≠ 0 :=
    graphTwist_ne_zero6401 sigma q hq B hB
  have h2 : graphTwistTwo6401 sigma q B ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h1
  have h3 : graphTwistThree6401 sigma q B ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h2
  have h4 : graphTwistFour6401 sigma q B ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h3
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hB h1) h2) h3) h4
noncomputable def graphGaugeCoefficient6401
    (sigma : F →+* F) (q : Nat) (A B : F[X][X]) : Fin 6 → F[X][X] :=
  ![
    graphHilbert90Denominator6401 sigma q B,
    A * graphTwist6401 sigma q B * graphTwistTwo6401 sigma q B *
      graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B,
    A * graphTwist6401 sigma q A * graphTwistTwo6401 sigma q B *
      graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B,
    A * graphTwist6401 sigma q A * graphTwistTwo6401 sigma q A *
      graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B,
    A * graphTwist6401 sigma q A * graphTwistTwo6401 sigma q A *
      graphTwistThree6401 sigma q A * graphTwistFour6401 sigma q B,
    A * graphTwist6401 sigma q A * graphTwistTwo6401 sigma q A *
      graphTwistThree6401 sigma q A * graphTwistFour6401 sigma q A]
theorem graphGaugeLastCoefficient_ne_zero6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (A B : F[X][X]) (hA : A ≠ 0) :
    graphGaugeCoefficient6401 sigma q A B (5 : Fin 6) ≠ 0 := by
  have h1 : graphTwist6401 sigma q A ≠ 0 :=
    graphTwist_ne_zero6401 sigma q hq A hA
  have h2 : graphTwistTwo6401 sigma q A ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h1
  have h3 : graphTwistThree6401 sigma q A ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h2
  have h4 : graphTwistFour6401 sigma q A ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h3
  simpa [graphGaugeCoefficient6401] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hA h1) h2) h3) h4
theorem graphHilbert90Numerator_eq_characterSum6401
    (sigma : F →+* F) (q : Nat) (A B : F[X][X]) (t : F) :
    graphHilbert90Numerator6401 sigma q A B t =
      ∑ i : Fin 6,
        graphGaugeCoefficient6401 sigma q A B i *
          Polynomial.C
            (Polynomial.C (sixFrobeniusCharacter6401 sigma i t)) := by
  simp [graphHilbert90Numerator6401, graphGaugeCoefficient6401,
    sixFrobeniusCharacter6401, frobeniusIterateRingHom6401,
    Fin.sum_univ_succ]
  ring
theorem exists_nonzeroGraphHilbert90Numerator_of_faithful_denominator6401
    (sigma : F →+* F) (q : Nat) (A B : F[X][X])
    (hfaithful : Function.Injective (sixFrobeniusCharacter6401 sigma))
    (hdenom : graphHilbert90Denominator6401 sigma q B ≠ 0) :
    ∃ t : F, graphHilbert90Numerator6401 sigma q A B t ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_bivariateCharacterCombination_ne_zero6401
    (sixFrobeniusCharacter6401 sigma) hfaithful
      (graphGaugeCoefficient6401 sigma q A B)
      ⟨0, by simpa [graphGaugeCoefficient6401] using hdenom⟩
  refine ⟨t, ?_⟩
  rw [graphHilbert90Numerator_eq_characterSum6401]
  exact ht
theorem exists_nonzeroGraphHilbert90Numerator_of_faithful_lane6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q) (A B : F[X][X])
    (hfaithful : Function.Injective (sixFrobeniusCharacter6401 sigma))
    (hB : B ≠ 0) :
    ∃ t : F, graphHilbert90Numerator6401 sigma q A B t ≠ 0 :=
  exists_nonzeroGraphHilbert90Numerator_of_faithful_denominator6401
    sigma q A B hfaithful
      (graphHilbert90Denominator_ne_zero6401 sigma q hq B hB)
theorem exists_nonzeroGraphHilbert90Numerator_of_faithful_eitherLane6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q) (A B : F[X][X])
    (hfaithful : Function.Injective (sixFrobeniusCharacter6401 sigma))
    (hlane : A ≠ 0 ∨ B ≠ 0) :
    ∃ t : F, graphHilbert90Numerator6401 sigma q A B t ≠ 0 := by
  rcases hlane with hA | hB
  · obtain ⟨t, ht⟩ := exists_bivariateCharacterCombination_ne_zero6401
      (sixFrobeniusCharacter6401 sigma) hfaithful
        (graphGaugeCoefficient6401 sigma q A B)
        ⟨5, graphGaugeLastCoefficient_ne_zero6401 sigma q hq A B hA⟩
    refine ⟨t, ?_⟩
    rw [graphHilbert90Numerator_eq_characterSum6401]
    exact ht
  · exact exists_nonzeroGraphHilbert90Numerator_of_faithful_lane6401
      sigma q hq A B hfaithful hB
theorem exists_nonzeroPrimitiveFamilyGraphGauge_of_faithful_lanes6401
    {K : Type} [Field K] [DecidableEq K]
    {sigma : K →+* K} {alpha : Fin n6401 ↪ K}
    {u0 u1 : Fin n6401 → K}
    {S : Finset K} {Aset : K → Finset (Fin n6401)}
    {P : K → Polynomial K}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S Aset P)
    (hfaithful : Function.Injective (sixFrobeniusCharacter6401 sigma))
    (hlane : primitiveBivariateFailureLaneZero6401 W ≠ 0 ∨
      primitiveBivariateFailureLaneOne6401 W ≠ 0) :
    ∃ t : K, primitiveFamilyGraphGaugeNumerator6401 W t ≠ 0 := by
  simpa [primitiveFamilyGraphGaugeNumerator6401] using
    exists_nonzeroGraphHilbert90Numerator_of_faithful_eitherLane6401
      sigma q6401 (by native_decide)
        (primitiveBivariateFailureLaneZero6401 W)
        (primitiveBivariateFailureLaneOne6401 W) hfaithful hlane
theorem exists_nonzeroPrimitiveFamilyGraphGauge_cross_of_faithful_lanes6401
    {K : Type} [Field K] [DecidableEq K]
    {sigma : K →+* K} {alpha : Fin n6401 ↪ K}
    {u0 u1 : Fin n6401 → K}
    {S : Finset K} {Aset : K → Finset (Fin n6401)}
    {P : K → Polynomial K}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S Aset P)
    (hfaithful : Function.Injective (sixFrobeniusCharacter6401 sigma))
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hnorm : primitiveFamilyNormObstruction6401 W = 0)
    (hlane : primitiveBivariateFailureLaneZero6401 W ≠ 0 ∨
      primitiveBivariateFailureLaneOne6401 W ≠ 0) :
    ∃ t : K,
      primitiveFamilyGraphGaugeNumerator6401 W t ≠ 0 ∧
      primitiveBivariateFailureLaneZero6401 W *
            graphTwist6401 sigma q6401
              (primitiveFamilyGraphGaugeNumerator6401 W t) *
            primitiveFamilyGraphGaugeDenominator6401 W =
        primitiveBivariateFailureLaneOne6401 W *
            primitiveFamilyGraphGaugeNumerator6401 W t *
            graphTwist6401 sigma q6401
              (primitiveFamilyGraphGaugeDenominator6401 W) := by
  obtain ⟨t, ht⟩ :=
    exists_nonzeroPrimitiveFamilyGraphGauge_of_faithful_lanes6401
      W hfaithful hlane
  exact ⟨t, ht, primitiveFamilyGraphGauge_cross6401 W horder hnorm t⟩
end GraphGauge
end BCHKSExtremePrimitiveFaithfulGraphGauge6401
end ProximityPrize.SubmissionLower
