import ProximityPrize.SubmissionLower.BCHKSJ0PrimitiveTransform6400
import ProximityPrize.SubmissionLower.BCHKSUniversalOuterCover6399
import ProximityPrize.SubmissionLower.BCHKSUniversalPairFiberBridge6399
import ProximityPrize.SubmissionLower.BCHKSUniversalResultantSelection
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteObstruction
import ProximityPrize.SubmissionLower.BCHKSDynamicCoreSelector6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSFreshQuotientUniversalSelector6400
open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open scoped BigOperators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open UniversalOuterCover6399
open UniversalPairFiberBridge6399
open UniversalNumerator
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
abbrev F := IRSProfile.Field
abbrev TriPoly := Polynomial (Polynomial (Polynomial F))
abbrev BiPoly := Polynomial (Polynomial F)
abbrev Pair := TriPoly × BiPoly
def freshLength : Nat := 241914
def freshRootCap : Nat := 110841
def freshAgreement : Nat := 165134
def freshExponent : Nat := 221681
def freshFactorMass : Nat := 41
def freshFactorZMass : Nat := 835
def freshErrors : Nat := 76780
def freshRawResultantCap : Nat :=
  2 * freshExponent * freshFactorMass * freshFactorZMass
def freshFusedResultantCap : Nat := 36643605576
def freshSelectorThreshold : Nat :=
  freshFactorZMass + 2 * freshFactorZMass * freshFactorMass +
    (freshFusedResultantCap + (freshErrors + 1) * freshFactorMass)
def SupportCaps (Q : TriPoly) : Prop :=
  ∀ j a, (Q.coeff j).coeff a ≠ 0 →
    j < 42 ∧ a + freshRootCap * j < 4623752 ∧
      ((Q.coeff j).coeff a).natDegree + j < 836
theorem fresh_constants_exact :
    freshExponent = 2 * freshRootCap - 1 ∧
      freshRawResultantCap = 15178498070 ∧
      freshSelectorThreshold = 36646822902 ∧
      (freshLength - freshRootCap) * freshRawResultantCap ≤
        (freshAgreement - freshRootCap) * freshFusedResultantCap := by
  norm_num [freshExponent, freshRootCap, freshRawResultantCap,
    freshFactorMass, freshFactorZMass, freshSelectorThreshold,
    freshFusedResultantCap, freshLength, freshAgreement, freshErrors]
local instance freshConcreteChar : CharP F 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem natDegree_le_factorMass
    (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    Q.natDegree ≤ freshFactorMass := by
  have hlead : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlead
  have hcoeff : (Q.coeff Q.natDegree).coeff a ≠ 0 :=
    Polynomial.mem_support_iff.mp ha
  have hj := (hcaps Q.natDegree a hcoeff).1
  norm_num [freshFactorMass] at hj ⊢
  omega
theorem normalizedFactor_X_caps
    (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    (∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      degreeX (mapZToRatFunc R) ≤ 4623752) ∧
    (∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.leadingCoeff.natDegree ≤ 4623752) := by
  constructor
  · intro R hRQ
    have hRW := WeightedFactorCaps.normalizedFactor_weightedX_cap
      Q R freshRootCap 4623752 hQ hRQ
        (fun j a h ↦ (hcaps j a h).2.1)
    unfold degreeX
    apply Finset.sup_le
    intro j hj
    simp only [mapZToRatFunc, Polynomial.coeff_map]
    apply Polynomial.natDegree_map_le.trans
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hne : (R.coeff j).coeff (R.coeff j).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have hw := hRW j (R.coeff j).natDegree hne
      norm_num [freshRootCap] at hw ⊢
      omega
  · intro R hRQ
    by_cases hz : R.leadingCoeff = 0
    · simp [hz]
    · have hRW := WeightedFactorCaps.normalizedFactor_weightedX_cap
        Q R freshRootCap 4623752 hQ hRQ
          (fun j a h ↦ (hcaps j a h).2.1)
      have hne :
          (R.coeff R.natDegree).coeff R.leadingCoeff.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have hw := hRW R.natDegree R.leadingCoeff.natDegree hne
      norm_num [freshRootCap] at hw ⊢
      omega
theorem normalizedFactor_swap_caps
    (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    (∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q, ∀ j,
      (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤
        freshFactorZMass) ∧
    (∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q, ∀ j,
      Polynomial.Bivariate.degreeX
        (Polynomial.Bivariate.swap (R.coeff j)) ≤ 4623752) := by
  constructor
  · intro R hRQ j
    have hRYZ := YZFactorCap.normalizedFactor_YZ_cap
      Q R 836 hQ hRQ (fun j a h ↦ (hcaps j a h).2.2)
    rw [show (Polynomial.Bivariate.swap (R.coeff j)).natDegree =
        Polynomial.Bivariate.natDegreeY
          (Polynomial.Bivariate.swap (R.coeff j)) from rfl,
      Polynomial.Bivariate.natDegreeY_swap]
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have h := hRYZ j a (Polynomial.mem_support_iff.mp ha)
    norm_num [freshFactorZMass] at h ⊢
    omega
  · intro R hRQ j
    have hRW := WeightedFactorCaps.normalizedFactor_weightedX_cap
      Q R freshRootCap 4623752 hQ hRQ
        (fun j a h ↦ (hcaps j a h).2.1)
    rw [Polynomial.Bivariate.degreeX_swap]
    change (R.coeff j).natDegree ≤ 4623752
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hw := hRW j (R.coeff j).natDegree (by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz)
      norm_num [freshRootCap] at hw ⊢
      omega
private theorem eval_C_ne_zero_of_ratfunc_map_eval_ne_zero
    (P : Polynomial (Polynomial F)) (x : F)
    (h : Polynomial.eval (algebraMap F (RatFunc F) x)
      (P.map (algebraMap F[X] (RatFunc F))) ≠ 0) :
    Polynomial.eval (Polynomial.C x) P ≠ 0 := by
  intro hz
  apply h
  rw [← Polynomial.eval₂_eq_eval_map]
  have hx : (algebraMap F[X] (RatFunc F)) (Polynomial.C x) =
      algebraMap F (RatFunc F) x := by simp
  rw [← hx, Polynomial.eval₂_hom, hz]
  exact map_zero _
private theorem factorXObstruction_ne_zero_of_outer
    (Q R : TriPoly) (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hRpos : 0 < R.natDegree) (hQdeg : Q.natDegree ≤ freshFactorMass) :
    factorXObstruction R ≠ 0 := by
  have hRirr :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
  have hRdeg : R.natDegree ≤ Q.natDegree :=
    Polynomial.natDegree_le_of_dvd
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hQ
  have hRlt : R.natDegree < 2130706433 :=
    lt_of_le_of_lt (hRdeg.trans hQdeg) (by norm_num [freshFactorMass])
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hRirr.ne_zero)
    (rawSepResultant_ne_zero_of_irreducible 2130706433 R
      hRirr hRpos hRlt)
theorem exists_x0_primitive_and_factor_good
    (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    ∃ x₀ : F,
      ∀ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R ↦ 0 < R.natDegree),
        (triSpecializeX R x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0 := by
  classical
  let Outer :=
    (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R ↦ 0 < R.natDegree)
  let T := Outer.attach
  have hQdeg := natDegree_le_factorMass Q hQ hcaps
  obtain ⟨hX, hlead⟩ := normalizedFactor_X_caps Q hQ hcaps
  obtain ⟨hZ, hXswap⟩ := normalizedFactor_swap_caps Q hQ hcaps
  let cert : ∀ r : ↥Outer,
      EffectivePrimitiveObstruction F (r : TriPoly) := fun r ↦
    Classical.choose
      (BCHKSJ0PrimitiveTransform6400.effectivePrimitiveObstruction_of_irreducible_caps
        (r : TriPoly)
        (UniqueFactorizationMonoid.prime_of_normalized_factor (r : TriPoly)
          (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1)).irreducible
        (Finset.mem_filter.mp r.property).2 freshFactorZMass 4623752
        (by
          rw [CompPoly.Extension.Ext.card_ext]
          norm_num [freshFactorZMass, F, IRSProfile.Field,
            KoalaBear.Ext6, KoalaBear.fieldSize])
        (hZ (r : TriPoly)
          (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1))
        (hXswap (r : TriPoly)
          (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1)))
  have hcertDegree : ∀ r : ↥Outer,
      (cert r).obstruction.natDegree ≤
        2 * (freshFactorZMass + 1) * 4623752 := by
    intro r
    exact Classical.choose_spec
      (BCHKSJ0PrimitiveTransform6400.effectivePrimitiveObstruction_of_irreducible_caps
        (r : TriPoly)
        (UniqueFactorizationMonoid.prime_of_normalized_factor (r : TriPoly)
          (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1)).irreducible
        (Finset.mem_filter.mp r.property).2 freshFactorZMass 4623752
        (by
          rw [CompPoly.Extension.Ext.card_ext]
          norm_num [freshFactorZMass, F, IRSProfile.Field,
            KoalaBear.Ext6, KoalaBear.fieldSize])
        (hZ (r : TriPoly)
          (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1))
        (hXswap (r : TriPoly)
          (Multiset.mem_toFinset.mp (Finset.mem_filter.mp r.property).1)))
  let g : Polynomial F →+* RatFunc F := algebraMap _ _
  let primRat : ↥Outer → Polynomial (RatFunc F) := fun r ↦
    (cert r).obstruction.map (algebraMap F (RatFunc F))
  let factorRat : ↥Outer → Polynomial (RatFunc F) := fun r ↦
    (factorXObstruction (r : TriPoly)).map g
  let combined : ↥Outer → Polynomial (RatFunc F) := fun r ↦
    primRat r * factorRat r
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hf : Function.Injective (algebraMap F (RatFunc F)) :=
    FaithfulSMul.algebraMap_injective F (RatFunc F)
  have hcombined : ∀ r ∈ T, combined r ≠ 0 := by
    intro r hr
    exact mul_ne_zero
      ((Polynomial.map_ne_zero_iff hf).mpr (cert r).ne)
      ((Polynomial.map_ne_zero_iff hg).mpr (by
        have hmem := Finset.mem_filter.mp r.property
        exact factorXObstruction_ne_zero_of_outer Q (r : TriPoly) hQ
          (Multiset.mem_toFinset.mp hmem.1) hmem.2 hQdeg))
  have hOuterMass : (∑ R ∈ Outer, R.natDegree) ≤ freshFactorMass := by
    simpa [Outer] using
      UniversalX0Avoidance6399.positive_outer_factor_degree_sum_le
        Q hQ freshFactorMass hQdeg
  have hOuterCard : Outer.card ≤ freshFactorMass := by
    calc
      Outer.card = Outer.card • (1 : Nat) := by simp
      _ ≤ ∑ R ∈ Outer, R.natDegree := by
        apply Finset.card_nsmul_le_sum
        intro R hR
        exact (Finset.mem_filter.mp hR).2
      _ ≤ freshFactorMass := hOuterMass
  have hprimSum :
      (∑ r ∈ T, (cert r).obstruction.natDegree) ≤
        freshFactorMass * (2 * (freshFactorZMass + 1) * 4623752) := by
    calc
      (∑ r ∈ T, (cert r).obstruction.natDegree) ≤
          ∑ _r ∈ T, 2 * (freshFactorZMass + 1) * 4623752 :=
        Finset.sum_le_sum (fun r _hr ↦ hcertDegree r)
      _ = T.card * (2 * (freshFactorZMass + 1) * 4623752) := by simp
      _ ≤ freshFactorMass *
          (2 * (freshFactorZMass + 1) * 4623752) := by
        exact Nat.mul_le_mul_right _ (by simpa [T] using hOuterCard)
  have hfactorSum :
      (∑ r ∈ T, (factorXObstruction (r : TriPoly)).natDegree) ≤
        4 * 4623752 * freshFactorMass := by
    have hb :=
      UniversalX0Avoidance6399.sum_factorXObstruction_natDegree_le_four_mul
        Outer id 4623752 freshFactorMass
        (by intro R hR; exact (Finset.mem_filter.mp hR).2)
        hOuterMass (by
          intro R hR
          have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
            Multiset.mem_toFinset.mp (Finset.mem_filter.mp hR).1
          exact factorXObstruction_natDegree_le R 4623752
            (hX R hRQ) (hlead R hRQ))
    rw [← Finset.sum_attach] at hb
    simpa [T] using hb
  have hdegree :
      (∑ r ∈ T, (combined r).natDegree) < Fintype.card F := by
    have hle : (∑ r ∈ T, (combined r).natDegree) ≤
        freshFactorMass * (2 * (freshFactorZMass + 1) * 4623752) +
          4 * 4623752 * freshFactorMass := by
      calc
        (∑ r ∈ T, (combined r).natDegree) ≤
            ∑ r ∈ T, ((cert r).obstruction.natDegree +
              (factorXObstruction (r : TriPoly)).natDegree) := by
          apply Finset.sum_le_sum
          intro r hr
          exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add
            (by simpa [primRat] using
              (Polynomial.natDegree_map_le (p := (cert r).obstruction)
                (f := algebraMap F (RatFunc F))))
            (by simpa [factorRat] using
              (Polynomial.natDegree_map_le
                (p := factorXObstruction (r : TriPoly)) (f := g))))
        _ = (∑ r ∈ T, (cert r).obstruction.natDegree) +
            ∑ r ∈ T, (factorXObstruction (r : TriPoly)).natDegree := by
          rw [Finset.sum_add_distrib]
        _ ≤ freshFactorMass *
              (2 * (freshFactorZMass + 1) * 4623752) +
            4 * 4623752 * freshFactorMass :=
          Nat.add_le_add hprimSum hfactorSum
    rw [CompPoly.Extension.Ext.card_ext]
    exact hle.trans_lt (by
      norm_num [freshFactorMass, freshFactorZMass, F, IRSProfile.Field,
        KoalaBear.Ext6, KoalaBear.fieldSize])
  obtain ⟨x₀, hx⟩ := exists_base_point_avoiding_ratfunc_polynomials
    T combined hcombined hdegree
  refine ⟨x₀, ?_⟩
  intro R hR
  let r : ↥Outer := ⟨R, by simpa [Outer] using hR⟩
  have hprod := hx r (by simpa [T] using r.property)
  have hprod' :
      Polynomial.eval (algebraMap F (RatFunc F) x₀) (primRat r) *
        Polynomial.eval (algebraMap F (RatFunc F) x₀) (factorRat r) ≠ 0 := by
    simpa [combined, Polynomial.eval_mul] using hprod
  have hpRat := left_ne_zero_of_mul hprod'
  have hoRat := right_ne_zero_of_mul hprod'
  have hp : Polynomial.eval x₀ (cert r).obstruction ≠ 0 := by
    intro hp0
    apply hpRat
    simpa [primRat, Polynomial.eval_map, hp0]
  have ho :
      Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 :=
    eval_C_ne_zero_of_ratfunc_map_eval_ne_zero _ _ (by
      change Polynomial.eval (algebraMap F (RatFunc F) x₀)
        ((factorXObstruction R).map g) ≠ 0
      simpa only [factorRat, r] using hoRat)
  have hlead0 : Polynomial.eval (Polynomial.C x₀) R.leadingCoeff ≠ 0 := by
    intro hz
    apply ho
    rw [factorXObstruction, Polynomial.eval_mul, hz, zero_mul]
  have hraw :
      Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0 := by
    intro hz
    apply ho
    rw [factorXObstruction, Polynomial.eval_mul, hz, mul_zero]
  have hR0 : triSpecializeX R x₀ ≠ 0 := by
    intro hz
    apply hlead0
    have hc := congrArg
      (fun B : Polynomial (Polynomial F) ↦ B.coeff R.natDegree) hz
    simpa only [triSpecializeX, Polynomial.coeff_map, Polynomial.coeff_zero,
      Polynomial.coe_evalRingHom, Polynomial.leadingCoeff] using hc
  have hdeg : (triSpecializeX R x₀).natDegree = R.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Polynomial.evalRingHom (Polynomial.C x₀)) hlead0
  exact ⟨(cert r).property x₀ hp, ho, hR0, hdeg, hraw⟩
theorem qBad_card_le
    (S : Finset F) (Q : TriPoly) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    (qBad S Q).card ≤ freshFactorZMass := by
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hQ
  have hj0 : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hj0
  have ha0 : (Q.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
  have hdeg : ((Q.coeff j).coeff a).natDegree < 836 := by
    have h := (hcaps j a ha0).2.2
    omega
  have hcard := badZSpecializations_card_lt Q S j a 836 ha0 hdeg
  norm_num [qBad, freshFactorZMass] at hcard ⊢
  omega
private theorem factor_eval_Z_caps
    (Q R : TriPoly) (x₀ : F) (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hcaps : SupportCaps Q) :
    degreeX (triSpecializeX R x₀) ≤ freshFactorZMass ∧
    (Polynomial.eval (Polynomial.C x₀) R.leadingCoeff).natDegree ≤
      freshFactorZMass := by
  have hRYZ := YZFactorCap.normalizedFactor_YZ_cap Q R 836 hQ hRQ
    (fun j a h ↦ (hcaps j a h).2.2)
  have hcoeffCap : ∀ j, degreeX (R.coeff j) ≤ freshFactorZMass := by
    intro j
    unfold degreeX
    apply Finset.sup_le
    intro a ha
    have h := hRYZ j a (Polynomial.mem_support_iff.mp ha)
    norm_num [freshFactorZMass] at h ⊢
    omega
  have hevalCap : ∀ p : Polynomial (Polynomial F),
      degreeX p ≤ freshFactorZMass →
      (Polynomial.eval (Polynomial.C x₀) p).natDegree ≤
        freshFactorZMass := by
    intro p hp
    have heq : (Polynomial.Bivariate.swap p).map
        (Polynomial.evalRingHom x₀) = Polynomial.eval (Polynomial.C x₀) p := by
      rw [← Polynomial.Bivariate.evalX_eq_map]
      exact (Polynomial.Bivariate.evalY_eq_evalX_swap x₀ p).symm
    rw [← heq]
    exact Polynomial.natDegree_map_le.trans (by
      rw [show (Polynomial.Bivariate.swap p).natDegree =
        Polynomial.Bivariate.natDegreeY
          (Polynomial.Bivariate.swap p) from rfl,
        Polynomial.Bivariate.natDegreeY_swap]
      exact hp)
  constructor
  · unfold degreeX
    apply Finset.sup_le
    intro j hj
    simp only [triSpecializeX, Polynomial.coeff_map]
    exact hevalCap (R.coeff j) (hcoeffCap j)
  · exact hevalCap R.leadingCoeff (by
      rw [← Polynomial.coeff_natDegree]
      exact hcoeffCap R.natDegree)
theorem outerBad_sum_card_le
    (Q : TriPoly) (x₀ : F) (hQ : Q ≠ 0) (hcaps : SupportCaps Q) :
    (∑ R ∈ outerFactors Q, (outerBad x₀ R).card) ≤
      2 * freshFactorZMass * freshFactorMass := by
  have hQdeg := natDegree_le_factorMass Q hQ hcaps
  have hsum : (∑ R ∈ outerFactors Q, R.natDegree) ≤
      freshFactorMass := by
    simpa [outerFactors] using
      UniversalX0Avoidance6399.positive_outer_factor_degree_sum_le
        Q hQ freshFactorMass hQdeg
  have hone : ∀ R ∈ outerFactors Q, (outerBad x₀ R).card ≤
      2 * R.natDegree * freshFactorZMass := by
    intro R hR
    have hmem := Finset.mem_filter.mp hR
    have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp hmem.1
    have hcap := factor_eval_Z_caps Q R x₀ hQ hRQ hcaps
    calc
      (outerBad x₀ R).card ≤
          (Polynomial.eval (Polynomial.C x₀)
            (factorXObstruction R)).roots.card := Multiset.toFinset_card_le _
      _ ≤ (Polynomial.eval (Polynomial.C x₀)
            (factorXObstruction R)).natDegree := Polynomial.card_roots' _
      _ ≤ 2 * R.natDegree * freshFactorZMass :=
        factorXObstruction_eval_natDegree_le R x₀ R.natDegree
          freshFactorZMass hmem.2 le_rfl hcap.1 hcap.2
  calc
    (∑ R ∈ outerFactors Q, (outerBad x₀ R).card) ≤
        ∑ R ∈ outerFactors Q, 2 * R.natDegree * freshFactorZMass :=
      Finset.sum_le_sum hone
    _ = 2 * freshFactorZMass *
        (∑ R ∈ outerFactors Q, R.natDegree) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      ring
    _ ≤ 2 * freshFactorZMass * freshFactorMass :=
      Nat.mul_le_mul_left _ hsum
theorem exists_outer_pair_cover
    (S : Finset F) (Pz : F → Polynomial F) (Q : TriPoly)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (Pz z) = 0)
    (hcaps : SupportCaps Q) :
    ∃ x₀ : F,
      (qBad S Q).card ≤ freshFactorZMass ∧
      (∑ R ∈ outerFactors Q, (outerBad x₀ R).card) ≤
        2 * freshFactorZMass * freshFactorMass ∧
      (pairs Q x₀).card ≤ freshFactorMass ∧
      (∀ R ∈ outerFactors Q,
        (triSpecializeX R x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) ≠ 0) ∧
      ∀ z ∈ S \ (qBad S Q ∪
          (outerFactors Q).biUnion (outerBad x₀)),
        ∃ RH ∈ pairs Q x₀, pairRel Pz x₀ z RH := by
  classical
  have hQdeg := natDegree_le_factorMass Q hQ hcaps
  obtain ⟨x₀, hx⟩ := exists_x0_primitive_and_factor_good Q hQ hcaps
  refine ⟨x₀, qBad_card_le S Q hQ hcaps,
    outerBad_sum_card_le Q x₀ hQ hcaps,
    positiveNormalizedFactorPairs_card_le_unconditional Q hQ x₀
      freshFactorMass hQdeg, ?_, ?_⟩
  · simpa [outerFactors] using hx
  · intro z hz
    have hzS := (Finset.mem_sdiff.mp hz).1
    have hzNot := (Finset.mem_sdiff.mp hz).2
    have hzQBad : z ∉ qBad S Q := by
      intro hbad
      exact hzNot (Finset.mem_union_left _ hbad)
    have hQz : triSpecializeZ Q z ≠ 0 := by
      intro hzero
      apply hzQBad
      exact Finset.mem_filter.mpr ⟨hzS, hzero⟩
    have hzOuter : z ∉ (outerFactors Q).biUnion (outerBad x₀) := by
      intro hbad
      exact hzNot (Finset.mem_union_right _ hbad)
    have hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
        0 < R.natDegree → triEval R z (Pz z) = 0 →
        biSpecializeZ (triSpecializeX R x₀) z ≠ 0 := by
      intro R hRQ hRpos hRroot
      have hRouter : R ∈ outerFactors Q :=
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hRQ, hRpos⟩
      have hzNotBad : z ∉ outerBad x₀ R := by
        intro hbad
        exact hzOuter (Finset.mem_biUnion.mpr ⟨R, hRouter, hbad⟩)
      have hzObs : Polynomial.eval z
          (Polynomial.eval (Polynomial.C x₀)
            (factorXObstruction R)) ≠ 0 := by
        intro hzero
        apply hzNotBad
        rw [outerBad, Multiset.mem_toFinset,
          Polynomial.mem_roots (hx R
            (by simpa [outerFactors] using hRouter)).2.1]
        exact hzero
      intro hzero
      apply hzObs
      have hcoeff := congrArg
        (fun B : Polynomial F ↦ B.coeff R.natDegree) hzero
      have hleadzero : Polynomial.eval z
          (Polynomial.eval (Polynomial.C x₀) R.leadingCoeff) = 0 := by
        simpa only [biSpecializeZ, triSpecializeX, Polynomial.coeff_map,
          Polynomial.coeff_zero, Polynomial.coe_evalRingHom,
          Polynomial.leadingCoeff] using hcoeff
      rw [factorXObstruction, Polynomial.eval_mul, Polynomial.eval_mul,
        hleadzero, zero_mul]
    obtain ⟨RH, hRHpairs, hRroot, hHroot⟩ :=
      exists_positive_normalizedFactorPair Q z (Pz z) x₀ hQz
        (hQeval z hzS) hsecond
    have hmem := pair_mem_facts Q x₀ RH (by simpa [pairs] using hRHpairs)
    refine ⟨RH, ?_, hRroot, hHroot, ?_, ?_⟩
    · simpa [pairs] using hRHpairs
    · have hRouter : RH.1 ∈ outerFactors Q :=
        Finset.mem_filter.mpr
          ⟨Multiset.mem_toFinset.mpr hmem.1, hmem.2.1⟩
      have hzNotBad : z ∉ outerBad x₀ RH.1 := by
        intro hbad
        exact hzOuter (Finset.mem_biUnion.mpr ⟨RH.1, hRouter, hbad⟩)
      intro hzero
      apply hzNotBad
      rw [outerBad, Multiset.mem_toFinset,
        Polynomial.mem_roots (hx RH.1
          (by simpa [outerFactors] using hRouter)).2.1]
      exact hzero
    · exact hsecond RH.1 hmem.1 hmem.2.1 hRroot
theorem exists_large_fresh_coordinates
    (T : Finset F) (Arow : F → Finset (Fin 241914))
    (resultantDegree : Nat)
    (hrow : ∀ z ∈ T, freshAgreement ≤ (Arow z).card)
    (hincidence : (freshLength - freshRootCap) * resultantDegree <
      (freshAgreement - freshRootCap) * T.card) :
    ∃ Coord : Finset (Fin 241914),
      freshRootCap + 1 ≤ Coord.card ∧
      ∀ i ∈ Coord, resultantDegree <
        (T.filter fun z ↦ i ∈ Arow z).card := by
  classical
  let Coord : Finset (Fin 241914) := Finset.univ.filter fun i ↦
    resultantDegree < (T.filter fun z ↦ i ∈ Arow z).card
  have hcard : freshRootCap + 1 ≤ Coord.card := by
    simpa [Coord, freshLength, freshAgreement, freshRootCap] using
      many_large_fibers T Arow freshLength (freshLength - freshAgreement)
        freshRootCap resultantDegree (by norm_num [freshLength])
        (by
          intro z hz
          norm_num [freshLength, freshAgreement]
          exact hrow z hz)
        (by
          norm_num [freshLength, freshAgreement, freshRootCap] at hincidence ⊢
          simpa [Nat.mul_comm] using hincidence)
  exact ⟨Coord, hcard, fun i hi ↦ (Finset.mem_filter.mp hi).2⟩
theorem exists_selected_pair_coordinate_divisibility
    (S : Finset F) (Pz : F → Polynomial F) (Q : TriPoly)
    (Arow : F → Finset (Fin 241914))
    (G : F → Pair → Fin 241914 → BiPoly)
    (hS : freshSelectorThreshold < S.card)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (Pz z) = 0)
    (hcaps : SupportCaps Q)
    (hrow : ∀ z ∈ S, freshAgreement ≤ (Arow z).card)
    (hGcaps : ∀ x₀ RH, RH ∈ pairs Q x₀ → ∀ i,
      (G x₀ RH i).natDegree ≤ freshExponent * RH.1.natDegree ∧
      Bivariate.degreeX (G x₀ RH i) ≤
        freshExponent * freshFactorZMass)
    (hGroot : ∀ x₀ z RH, RH ∈ pairs Q x₀ →
      (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree →
      z ∈ S → pairRel Pz x₀ z RH → ∀ i ∈ Arow z,
      biEval (G x₀ RH i) (Polynomial.eval x₀ (Pz z)) z = 0) :
    ∃ x₀ : F, ∃ RH : Pair, ∃ T : Finset F,
      ∃ Coord : Finset (Fin 241914),
      RH ∈ pairs Q x₀ ∧
      ((triSpecializeX RH.1 x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀)
          (factorXObstruction RH.1) ≠ 0 ∧
        triSpecializeX RH.1 x₀ ≠ 0 ∧
        (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree ∧
        Polynomial.eval (Polynomial.C x₀)
          (rawSepResultant RH.1) ≠ 0) ∧
      T ⊆ S ∧
      freshErrors + 1 < T.card ∧
      freshRootCap + 1 ≤ Coord.card ∧
      (∀ z ∈ T, pairRel Pz x₀ z RH) ∧
      (∀ i ∈ Coord, RH.2 ∣ G x₀ RH i) := by
  classical
  obtain ⟨x₀, hqBad, houterBad, hpairs, hx₀, hcover⟩ :=
    exists_outer_pair_cover S Pz Q hQ hQeval hcaps
  let rdeg : Pair → Nat := universalPairResultantCapacity
    freshExponent freshFactorZMass
  have hQdeg := natDegree_le_factorMass Q hQ hcaps
  have hBZ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      Bivariate.degreeX (triSpecializeX R x₀) ≤ freshFactorZMass := by
    intro R hRQ
    apply normalizedFactor_triSpecializeX_degreeX_le Q R x₀
      freshFactorZMass hQ hRQ
    intro j a hja
    have hz := (hcaps j a hja).2.2
    norm_num [freshFactorZMass] at hz ⊢
    exact hz
  have hsum : (∑ RH ∈ pairs Q x₀, rdeg RH) ≤
      freshRawResultantCap := by
    simpa [rdeg, pairs, freshRawResultantCap] using
      positiveNormalizedFactorPairs_universal_capacity_le
        Q hQ x₀ freshExponent freshFactorZMass freshFactorMass hQdeg hBZ
  obtain ⟨RH, hRH, hpLarge⟩ :=
    exists_pair_fiber_of_fused_resultant_ledger
      S (qBad S Q) (outerFactors Q) (outerBad x₀) (pairs Q x₀)
      (pairRel Pz x₀) rdeg
      (freshLength - freshRootCap) (freshAgreement - freshRootCap)
      freshErrors freshFactorZMass
      (2 * freshFactorZMass * freshFactorMass)
      freshRawResultantCap freshFactorMass freshFusedResultantCap
      hqBad houterBad hsum hpairs
      (by
        exact fresh_constants_exact.2.2.2)
      hcover
      (by simpa [freshSelectorThreshold] using hS)
  let T : Finset F :=
    (S \ (qBad S Q ∪ (outerFactors Q).biUnion (outerBad x₀))).filter
      fun z ↦ pairRel Pz x₀ z RH
  have hpLarge' :
      ((freshLength - freshRootCap) * rdeg RH) /
          (freshAgreement - freshRootCap) + (freshErrors + 1) < T.card := by
    simpa [T] using hpLarge
  have hgap : 0 < freshAgreement - freshRootCap := by
    norm_num [freshAgreement, freshRootCap]
  have hbounds := scaled_pair_capacity_implies_incidence
    (freshLength - freshRootCap) (freshAgreement - freshRootCap)
      (rdeg RH) freshErrors T.card hgap hpLarge'
  have hTsub : T ⊆ S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hrel : ∀ z ∈ T, pairRel Pz x₀ z RH := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hxSelected :
      (triSpecializeX RH.1 x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀)
          (factorXObstruction RH.1) ≠ 0 ∧
        triSpecializeX RH.1 x₀ ≠ 0 ∧
        (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree ∧
        Polynomial.eval (Polynomial.C x₀)
          (rawSepResultant RH.1) ≠ 0 := by
    have hm := pair_mem_facts Q x₀ RH hRH
    have houter : RH.1 ∈ outerFactors Q :=
      Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr hm.1, hm.2.1⟩
    exact hx₀ RH.1 houter
  have hrowT : ∀ z ∈ T, freshAgreement ≤ (Arow z).card := by
    intro z hz
    exact hrow z (hTsub hz)
  obtain ⟨Coord, hCoord, hlarge⟩ :=
    exists_large_fresh_coordinates T Arow (rdeg RH) hrowT (by
      simpa using hbounds.1)
  let Res : Fin 241914 → F[X] := fun i ↦
    Polynomial.resultant (G x₀ RH i) RH.2
      (G x₀ RH i).natDegree RH.2.natDegree
  have hResdeg : ∀ i ∈ Coord, (Res i).natDegree ≤ rdeg RH := by
    intro i hi
    have hg := hGcaps x₀ RH hRH i
    calc
      (Res i).natDegree ≤
          RH.2.natDegree * Bivariate.degreeX (G x₀ RH i) +
            (G x₀ RH i).natDegree * Bivariate.degreeX RH.2 :=
        bivariate_resultant_natDegree_le (G x₀ RH i) RH.2
          (G x₀ RH i).natDegree RH.2.natDegree
      _ ≤ RH.2.natDegree *
            (freshExponent * freshFactorZMass) +
          (freshExponent * RH.1.natDegree) *
            Bivariate.degreeX RH.2 := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left RH.2.natDegree hg.2)
          (Nat.mul_le_mul_right (Bivariate.degreeX RH.2) hg.1)
      _ = rdeg RH := rfl
  have hResroot : ∀ i ∈ Coord, ∀ z ∈ T, i ∈ Arow z →
      (Res i).eval z = 0 := by
    intro i hi z hzT hiz
    have hpair := hrel z hzT
    have hsize : 0 < (G x₀ RH i).natDegree + RH.2.natDegree := by
      have hfacts := pair_mem_facts Q x₀ RH hRH
      exact Nat.add_pos_right _ hfacts.2.2.2.1
    exact bivariate_resultant_eval_eq_zero_of_common_root
      (G x₀ RH i) RH.2 (G x₀ RH i).natDegree RH.2.natDegree
      z (Polynomial.eval x₀ (Pz z))
      Polynomial.natDegree_map_le Polynomial.natDegree_map_le hsize
      (hGroot x₀ z RH hRH hxSelected.2.2.2.1
        (hTsub hzT) hpair i hiz) hpair.2.1
  have hReszero : ∀ i ∈ Coord, Res i = 0 := by
    intro i hi
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (Res i) (T.filter fun z ↦ i ∈ Arow z)
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact hResroot i hi z hz'.1 hz'.2
    · exact (hResdeg i hi).trans_lt (hlarge i hi)
  have hdiv : ∀ i ∈ Coord, RH.2 ∣ G x₀ RH i := by
    intro i hi
    have hfacts := pair_mem_facts Q x₀ RH hRH
    have hHi :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor RH.2
        hfacts.2.2.1).irreducible
    apply irreducible_dvd_of_resultant_eq_zero_nonmonic
      (G x₀ RH i) RH.2 hHi hfacts.2.2.2.1
    simpa only [Res] using hReszero i hi
  exact ⟨x₀, RH, T, Coord, hRH, hxSelected, hTsub,
    hbounds.2, hCoord, hrel, hdiv⟩
theorem exists_concrete_fresh_selected_pair
    (omega : Fin 241914 ↪ F)
    (u₀ u₁ : Fin 241914 → F)
    (S : Finset F)
    (A : F → Finset (Fin 241914))
    (P : ↑S → Polynomial F)
    (Q : TriPoly)
    (hScard : freshSelectorThreshold < S.card)
    (hQ : Q ≠ 0)
    (hPdeg : ∀ z : ↑S, (P z).natDegree ≤ freshRootCap)
    (hAcard : ∀ z : ↑S, freshAgreement ≤ (A z.1).card)
    (hagree : ∀ z : ↑S, ∀ i ∈ A z,
      Polynomial.eval (omega i) (P z) = u₀ i + z.1 * u₁ i)
    (hQeval : ∀ z : ↑S, triEval Q z.1 (P z) = 0)
    (hcaps : SupportCaps Q) :
    ∃ x₀ : F, ∃ RH : Pair, ∃ T : Finset F,
      ∃ Coord : Finset (Fin 241914),
      RH ∈ pairs Q x₀ ∧
      ((triSpecializeX RH.1 x₀).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₀)
          (factorXObstruction RH.1) ≠ 0 ∧
        triSpecializeX RH.1 x₀ ≠ 0 ∧
        (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree ∧
        Polynomial.eval (Polynomial.C x₀)
          (rawSepResultant RH.1) ≠ 0) ∧
      T ⊆ S ∧
      freshErrors + 1 < T.card ∧
      freshRootCap + 1 ≤ Coord.card ∧
      (∀ z ∈ T,
        pairRel (fun w ↦ if hw : w ∈ S then P ⟨w, hw⟩ else 0)
          x₀ z RH) ∧
      (∀ i ∈ Coord, RH.2 ∣
        concreteUniversalAffineObstruction x₀ RH.1
          freshExponent freshRootCap
          (omega i - x₀) (u₀ i) (u₁ i)) := by
  classical
  let PE : F → Polynomial F := fun z ↦
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  let G : F → Pair → Fin 241914 → BiPoly := fun x₀ RH i ↦
    concreteUniversalAffineObstruction x₀ RH.1
      freshExponent freshRootCap (omega i - x₀) (u₀ i) (u₁ i)
  have hPEdeg : ∀ z ∈ S, (PE z).natDegree ≤ freshRootCap := by
    intro z hz
    simpa [PE, hz] using hPdeg ⟨z, hz⟩
  have hPEeval : ∀ z ∈ S, triEval Q z (PE z) = 0 := by
    intro z hz
    simpa [PE, hz] using hQeval ⟨z, hz⟩
  have hrow : ∀ z ∈ S, freshAgreement ≤ (A z).card := by
    intro z hz
    exact hAcard ⟨z, hz⟩
  have hGcaps : ∀ x₀ RH, RH ∈ pairs Q x₀ → ∀ i,
      (G x₀ RH i).natDegree ≤ freshExponent * RH.1.natDegree ∧
      Bivariate.degreeX (G x₀ RH i) ≤
        freshExponent * freshFactorZMass := by
    intro x₀ RH hRH i
    have hm := pair_mem_facts Q x₀ RH hRH
    have hRYZraw := YZFactorCap.normalizedFactor_YZ_cap
      Q RH.1 836 hQ hm.1 (fun j a ha ↦ (hcaps j a ha).2.2)
    have hRYZ : YZCap RH.1 freshFactorZMass := by
      intro j a ha
      have hh := hRYZraw j a ha
      norm_num [freshFactorZMass] at hh ⊢
      omega
    simpa [G] using
      concreteUniversalAffineObstruction_degree_bounds x₀ RH.1
        freshExponent freshRootCap RH.1.natDegree freshFactorZMass
        (omega i - x₀) (u₀ i) (u₁ i)
        (by norm_num [freshExponent, freshRootCap,
          FiniteHenselWeight.denominatorExponent])
        (by norm_num [freshRootCap]) (by exact hm.2.1)
        (by norm_num [freshFactorZMass]) hm.2.1 le_rfl hRYZ
  have hGroot : ∀ x₀ z RH, RH ∈ pairs Q x₀ →
      (triSpecializeX RH.1 x₀).natDegree = RH.1.natDegree →
      z ∈ S → pairRel PE x₀ z RH → ∀ i ∈ A z,
      biEval (G x₀ RH i) (Polynomial.eval x₀ (PE z)) z = 0 := by
    intro x₀ z RH hRH hdeg hzS hrel i hi
    have hm := pair_mem_facts Q x₀ RH hRH
    apply biEval_concreteUniversalAffineObstruction_eq_zero
      x₀ z (Polynomial.eval x₀ (PE z)) RH.1 (PE z)
      freshExponent freshRootCap (omega i - x₀) (u₀ i) (u₁ i)
    · norm_num [freshExponent, freshRootCap,
        FiniteHenselWeight.denominatorExponent]
    · exact hm.2.1
    · rfl
    · exact hPEdeg z hzS
    · exact hrel.1
    · exact simple_slope_of_pairRel PE x₀ z RH.1 RH.2
        hrel hdeg hm.2.1
    · have ha := hagree ⟨z, hzS⟩ i hi
      simpa [PE, hzS] using ha
  obtain ⟨x₀, RH, T, Coord, hRH, hx, hTS, hTcard, hCoord,
      hrel, hdiv⟩ :=
    exists_selected_pair_coordinate_divisibility
      S PE Q A G hScard hQ hPEeval hcaps hrow hGcaps hGroot
  exact ⟨x₀, RH, T, Coord, hRH, hx, hTS, hTcard, hCoord,
    by simpa [PE] using hrel, by simpa [G] using hdiv⟩
end BCHKSFreshQuotientUniversalSelector6400
end ProximityPrize.SubmissionLower
