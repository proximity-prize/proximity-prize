import ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact

/-! Packed from ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance. -/
section PackedLocator_LocatorTwoFactorAvoidance

/-!
# A shared high-band route for two regular factors

The one-factor power route pays for a high-band projection independently for
every regular factor.  For two factors the projection can be shared.  On the
resulting low subspace there are only four cases: neither divisibility
condition is universal, exactly one is universal, or both are universal.  In
the first case one vector avoids both divisors; in a one-universal case the
other factor is finished and the universal factor continues through the
one-factor route; in the both-universal case the product is divided out and
the shared route continues.

This file contains the linear-algebraic core.  It intentionally returns
weight bounds rather than coefficient-box membership: those are precisely
the data consumed by the derivative and unequal-pair arguments, and they are
stable when the other factor is multiplied back into a recursively produced
helper.
-/

namespace ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorDoubleSquareAvoidance LocatorArbitraryPowerAvoidance
  LocatorArbitraryPowerContact

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The budget for a shared two-factor route.  After the current common band
there are three possible continuations: only `F`, only `G`, or both.  Taking
their maximum is sound because the divisibility case split chooses only one
continuation. -/
def twoFactorBandBudget
    (delta fT fY fS gT gY gS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      delta * channelCount T YS S +
        max
          (powerBandBudget delta fT fY fS
            (T - fT) (YS - fY) (S - fS) n)
          (max
            (powerBandBudget delta gT gY gS
              (T - gT) (YS - gY) (S - gS) n)
            (twoFactorBandBudget delta fT fY fS gT gY gS
              (T - fT - gT) (YS - fY - gY) (S - fS - gS) n))

/-- A stage for one target factor.  `j` records how many copies have been
removed from the input family.  At a nonterminal stage the helper is coprime
to the target irreducible; at the last stage the consumer may instead use a
terminal weight inequality. -/
def HasFactorStage [AddCommMonoid V] [Module K V]
    (fuel Dlow w delta T YS S : ℕ)
    (q : V →ₗ[K] P4 K) (F : P4 K) : Prop :=
  ∃ (j : Fin fuel) (v : V) (J : P4 K),
    v ≠ 0 ∧ J ≠ 0 ∧ F ^ j.val * J = q v ∧
    wt residualTotalWeights J ≤ T - j.val * wt residualTotalWeights F ∧
    wt residualYSWeights J ≤ YS - j.val * wt residualYSWeights F ∧
    wt residualSWeights J ≤ S - j.val * wt residualSWeights F ∧
    wt (contactWeights w) J <
      Dlow - j.val * delta - j.val * wt (contactWeights w) F ∧
    (j.val + 1 < fuel → ¬ F ∣ J)

/-- Two proper divisibility subspaces cannot cover a vector space.  For two
subspaces this has a particularly cheap constructive proof: in the crossed
case `x + y` avoids both divisors. -/
theorem exists_not_dvd_both
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F G : P4 K)
    (hF : ¬ ∀ v, F ∣ q v) (hG : ¬ ∀ v, G ∣ q v) :
    ∃ v, ¬ F ∣ q v ∧ ¬ G ∣ q v := by
  classical
  push_neg at hF hG
  obtain ⟨x, hxF⟩ := hF
  obtain ⟨y, hyG⟩ := hG
  by_cases hxG : G ∣ q x
  · by_cases hyF : F ∣ q y
    · refine ⟨x + y, ?_, ?_⟩
      · intro hsum
        apply hxF
        have hd : F ∣ q (x + y) - q y := dvd_sub hsum hyF
        simpa only [map_add, add_sub_cancel_right] using hd
      · intro hsum
        apply hyG
        have hd : G ∣ q (x + y) - q x := dvd_sub hsum hxG
        simpa only [map_add, add_sub_cancel_left] using hd
    · exact ⟨y, hyF, hyG⟩
  · exact ⟨x, hxF, hxG⟩

/-- Package the four cases used by the shared recursion. -/
theorem two_divisor_cases
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F G : P4 K) :
    ((∀ v, F ∣ q v) ∧ (∀ v, G ∣ q v)) ∨
      ((∀ v, F ∣ q v) ∧ ∃ v, ¬ G ∣ q v) ∨
      ((∃ v, ¬ F ∣ q v) ∧ ∀ v, G ∣ q v) ∨
      ∃ v, ¬ F ∣ q v ∧ ¬ G ∣ q v := by
  classical
  by_cases hF : ∀ v, F ∣ q v
  · by_cases hG : ∀ v, G ∣ q v
    · exact Or.inl ⟨hF, hG⟩
    · right; left
      push_neg at hG
      exact ⟨hF, hG⟩
  · by_cases hG : ∀ v, G ∣ q v
    · right; right; left
      push_neg at hF
      exact ⟨hF, hG⟩
    · right; right; right
      exact exists_not_dvd_both q F G hF hG

private theorem regular_mem_normalizedFactors
    (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H := by
  have hactive : F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf : F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf

/-- Distinct regular indices are represented by distinct normalized prime
factors, hence are relatively prime. -/
theorem regularIndex_isRelPrime_of_ne
    (H : P4 K) (F G : RCN266.RegularIndex H) (hne : F.1 ≠ G.1) :
    IsRelPrime F.1 G.1 := by
  have hFs := RCN167.positiveRFactors_spec H F.1 F.2
  have hGs := RCN167.positiveRFactors_spec H G.1 G.2
  apply hFs.1.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hne
  apply UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
    (regular_mem_normalizedFactors H F) (regular_mem_normalizedFactors H G)
  exact (hFs.1.dvd_irreducible_iff_associated hGs.1).mp hd

/-- Universal divisibility by two relatively-prime factors is universal
divisibility by their product.  This is the entry point for quotienting an
`FG`-divisible source family before starting the shared bands. -/
theorem product_dvd_of_two_universal
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F G : P4 K) (hrel : IsRelPrime F G)
    (hF : ∀ v, F ∣ q v) (hG : ∀ v, G ∣ q v) :
    ∀ v, F * G ∣ q v := by
  intro v
  exact hrel.mul_dvd (hF v) (hG v)

/-- Dividing an injective nested-box family by a universal divisor preserves
injectivity and subtracts the four factor weights. -/
theorem quotientLinear_nested_data
    [AddCommGroup V] [Module K V]
    (D w T YS S : ℕ) (q : V →ₗ[K] P4 K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F : P4 K) (hF : F ≠ 0) (hdiv : ∀ v, F ∣ q v) :
    Function.Injective (quotientLinear q F hF hdiv) ∧
      (∀ v, q v = F * quotientLinear q F hF hdiv v) ∧
      ∀ v, quotientLinear q F hF hdiv v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F)
        (YS - wt residualYSWeights F)
        (S - wt residualSWeights F) := by
  classical
  let qF := quotientLinear q F hF hdiv
  have hqF : Function.Injective qF :=
    quotientLinear_injective q hq F hF hdiv
  have hprod (v : V) : q v = F * qF v :=
    recon_eq_mul_quotientPolynomial q F hdiv v
  refine ⟨hqF, hprod, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    rw [map_zero]
    exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
  · have hqv : q v ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    have hqFv : qF v ≠ 0 := by
      intro hz
      apply hqv
      rw [hprod v, hz, mul_zero]
    exact quotient_mem_nestedCoefficientBox_of_mul_eq
      (q v) F (qF v) D w T YS S hqv hF hqFv (hmem v) (hprod v)

/-- Quotient an `FG`-divisible source family by both factors while retaining
the separated weight decrements needed by the pair budget. -/
theorem exists_twoFactor_quotient_nested_data
    [AddCommGroup V] [Module K V]
    (D w T YS S : ℕ) (q : V →ₗ[K] P4 K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F G : P4 K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hrel : IsRelPrime F G)
    (hdivF : ∀ v, F ∣ q v) (hdivG : ∀ v, G ∣ q v) :
    ∃ qFG : V →ₗ[K] P4 K,
      Function.Injective qFG ∧
      (∀ v, q v = F * (G * qFG v)) ∧
      ∀ v, qFG v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F - wt (contactWeights w) G) w
        (T - wt residualTotalWeights F - wt residualTotalWeights G)
        (YS - wt residualYSWeights F - wt residualYSWeights G)
        (S - wt residualSWeights F - wt residualSWeights G) := by
  let qF := quotientLinear q F hF hdivF
  have hdataF := quotientLinear_nested_data D w T YS S q hq hmem F hF hdivF
  have hqF : Function.Injective qF := by
    simpa only [qF] using hdataF.1
  have hprodF : ∀ v, q v = F * qF v := by
    simpa only [qF] using hdataF.2.1
  have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
      (D - wt (contactWeights w) F) w
      (T - wt residualTotalWeights F)
      (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
    simpa only [qF] using hdataF.2.2
  have hdivG' : ∀ v, G ∣ qF v := by
    intro v
    apply hrel.symm.dvd_of_dvd_mul_left
    rw [← hprodF v]
    exact hdivG v
  let qFG := quotientLinear qF G hG hdivG'
  have hdataG := quotientLinear_nested_data
    (D - wt (contactWeights w) F) w
    (T - wt residualTotalWeights F)
    (YS - wt residualYSWeights F)
    (S - wt residualSWeights F)
    qF hqF hqFBox G hG hdivG'
  refine ⟨qFG, ?_, ?_, ?_⟩
  · simpa only [qFG] using hdataG.1
  · intro v
    calc
      q v = F * qF v := hprodF v
      _ = F * (G * qFG v) := by
        rw [hdataG.2.1 v]
  · simpa only [qFG] using hdataG.2.2

/-- Exact weighted degree of a nonzero power. -/
theorem wt_pow_eq (weights : Fin 4 → ℕ) (F : P4 K) (hF : F ≠ 0)
    (j : ℕ) : wt weights (F ^ j) = j * wt weights F := by
  unfold wt
  induction j with
  | zero => simp [pow_zero, MvPolynomial.weightedTotalDegree]
  | succ j ih =>
      rw [pow_succ', weightedTotalDegree_mul weights F (F ^ j) hF
        (pow_ne_zero j hF), ih]
      simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul]
      omega

/-- If a boxed polynomial is `F^j * J`, the three residual weights of `J`
are the ambient weights minus the corresponding factor weights. -/
theorem residual_bounds_of_power_identity
    (D w T YS S j : ℕ) (P F J : P4 K)
    (hP : P ≠ 0) (hF : F ≠ 0) (hJ : J ≠ 0)
    (hbox : P ∈ nestedCoefficientBox K D w T YS S)
    (heq : F ^ j * J = P) :
    wt residualTotalWeights J ≤ T - j * wt residualTotalWeights F ∧
      wt residualYSWeights J ≤ YS - j * wt residualYSWeights F ∧
      wt residualSWeights J ≤ S - j * wt residualSWeights F := by
  have hb := nested_mem_weights hbox hP
  have one (weights : Fin 4 → ℕ) (B : ℕ)
      (hPB : wt weights P ≤ B) :
      wt weights J ≤ B - j * wt weights F := by
    have hm := weightedTotalDegree_mul weights (F ^ j) J
      (pow_ne_zero j hF) hJ
    have hp := wt_pow_eq weights F hF j
    unfold wt at hPB ⊢ hp
    rw [hp, heq] at hm
    omega
  exact ⟨one residualTotalWeights T hb.1,
    one residualYSWeights YS hb.2.1,
    one residualSWeights S hb.2.2.1⟩

private theorem sub_one_then_mul (a b j : ℕ) :
    a - b - j * b = a - (j + 1) * b := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

private theorem sub_pair_then_mul (a x y j : ℕ) :
    a - x - y - j * x - j * y =
      a - (j + 1) * x - (j + 1) * y := by
  simp only [Nat.sub_sub, Nat.add_mul, one_mul]
  congr 1
  omega

/-- Arithmetic used when a recursively produced helper for one factor is
multiplied by the other factor.  Expanding `(j+1) * _` first keeps the proof
inside Presburger arithmetic. -/
private theorem cross_contact_lt
    (a delta cSelf cOther j x : ℕ)
    (h : x < a - delta - cSelf - cOther - j * delta - j * cSelf) :
    cOther + x < a - (j + 1) * delta - (j + 1) * cSelf := by
  simp only [Nat.add_mul, one_mul]
  omega

/-- A single high-band chain simultaneously supplies helpers for two coprime
factors.  Relative to two independent invocations, the first band is always
paid once; whenever both divisibility conditions remain universal, all later
bands are shared as well. -/
theorem exists_two_factor_stages_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F G : P4 K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hrel : IsRelPrime F G)
    (hsource :
      twoFactorBandBudget delta
          (wt residualTotalWeights F) (wt residualYSWeights F)
          (wt residualSWeights F)
          (wt residualTotalWeights G) (wt residualYSWeights G)
          (wt residualSWeights G) T YS S (steps + 1) <
        Module.finrank K V) :
    HasFactorStage (steps + 1) Dlow w delta T YS S q F ∧
      HasFactorStage (steps + 1) Dlow w delta T YS S q G := by
  classical
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      have hfirst : delta * channelCount T YS S < Module.finrank K V := by
        simpa [twoFactorBandBudget, powerBandBudget] using hsource
      obtain ⟨v, hv, hqv, hlow⟩ :=
        exists_nonzero_image_mem_low Dhigh Dlow w delta T YS S hwidth
          q hq hmem hfirst
      have hb := nested_mem_weights hlow hqv
      let j0 : Fin (0 + 1) := ⟨0, by omega⟩
      have one (A : P4 K) :
          HasFactorStage (0 + 1) Dlow w delta T YS S q A := by
        refine ⟨j0, v, q v, hv, hqv, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [j0, Fin.val_zero, pow_zero, one_mul]
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.2
        · intro hlt
          omega
      exact ⟨one F, one G⟩
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have htail :
          max
            (powerBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) (steps + 1))
            (max
              (powerBandBudget delta
                (wt residualTotalWeights G) (wt residualYSWeights G)
                (wt residualSWeights G)
                (T - wt residualTotalWeights G)
                (YS - wt residualYSWeights G)
                (S - wt residualSWeights G) (steps + 1))
              (twoFactorBandBudget delta
                (wt residualTotalWeights F) (wt residualYSWeights F)
                (wt residualSWeights F)
                (wt residualTotalWeights G) (wt residualYSWeights G)
                (wt residualSWeights G)
                (T - wt residualTotalWeights F - wt residualTotalWeights G)
                (YS - wt residualYSWeights F - wt residualYSWeights G)
                (S - wt residualSWeights F - wt residualSWeights G)
                (steps + 1))) < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget := hsource
        rw [twoFactorBandBudget] at hbudget
        have hrangeTail : Module.finrank K bandOne.range +
            max
              (powerBandBudget delta
                (wt residualTotalWeights F) (wt residualYSWeights F)
                (wt residualSWeights F)
                (T - wt residualTotalWeights F)
                (YS - wt residualYSWeights F)
                (S - wt residualSWeights F) (steps + 1))
              (max
                (powerBandBudget delta
                  (wt residualTotalWeights G) (wt residualYSWeights G)
                  (wt residualSWeights G)
                  (T - wt residualTotalWeights G)
                  (YS - wt residualYSWeights G)
                  (S - wt residualSWeights G) (steps + 1))
                (twoFactorBandBudget delta
                  (wt residualTotalWeights F) (wt residualYSWeights F)
                  (wt residualSWeights F)
                  (wt residualTotalWeights G) (wt residualYSWeights G)
                  (wt residualSWeights G)
                  (T - wt residualTotalWeights F - wt residualTotalWeights G)
                  (YS - wt residualYSWeights F - wt residualYSWeights G)
                  (S - wt residualSWeights F - wt residualSWeights G)
                  (steps + 1))) < Module.finrank K V := by
          exact (Nat.add_le_add_right hrangeOne _).trans_lt (by
            simpa only [Nat.succ_eq_add_one] using hbudget)
        rw [← hsum] at hrangeTail
        exact Nat.lt_of_add_lt_add_left hrangeTail
      have hsourceF :
          powerBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) (steps + 1) <
            Module.finrank K lowOne :=
        (Nat.le_max_left _ _).trans_lt htail
      have hsourceG :
          powerBandBudget delta
              (wt residualTotalWeights G) (wt residualYSWeights G)
              (wt residualSWeights G)
              (T - wt residualTotalWeights G)
              (YS - wt residualYSWeights G)
              (S - wt residualSWeights G) (steps + 1) <
            Module.finrank K lowOne :=
        ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans_lt htail
      have hsourceBoth :
          twoFactorBandBudget delta
              (wt residualTotalWeights F) (wt residualYSWeights F)
              (wt residualSWeights F)
              (wt residualTotalWeights G) (wt residualYSWeights G)
              (wt residualSWeights G)
              (T - wt residualTotalWeights F - wt residualTotalWeights G)
              (YS - wt residualYSWeights F - wt residualYSWeights G)
              (S - wt residualSWeights F - wt residualSWeights G)
              (steps + 1) < Module.finrank K lowOne :=
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans_lt htail
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      have immediate (A : P4 K) (v : lowOne) (hnot : ¬ A ∣ qOne v) :
          HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q A := by
        have hv : v.1 ≠ 0 := by
          intro hz
          apply hnot
          have hvzero : v = 0 := Subtype.ext hz
          rw [hvzero]
          simp only [map_zero]
          exact dvd_zero A
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hq
          simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype,
            map_zero] using hz
        have hb := nested_mem_weights (hqOneBox v) hqv
        let j0 : Fin (Nat.succ steps + 1) := ⟨0, by omega⟩
        refine ⟨j0, v.1, qOne v, hv, hqv, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [j0, Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.1
        · simpa only [j0, Fin.val_zero, zero_mul, Nat.sub_zero] using hb.2.2.2
        · intro _hlt
          exact hnot
      rcases two_divisor_cases qOne F G with hboth | honeF | honeG | hneither
      · rcases hboth with ⟨hdivF, hdivG⟩
        let qF := quotientLinear qOne F hF hdivF
        have hdataF := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox F hF hdivF
        have hqF : Function.Injective qF := by
          simpa only [qF] using hdataF.1
        have hprodF : ∀ v, qOne v = F * qF v := by
          simpa only [qF] using hdataF.2.1
        have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
          simpa only [qF] using hdataF.2.2
        have hdivG' : ∀ v, G ∣ qF v := by
          intro v
          apply hrel.symm.dvd_of_dvd_mul_left
          rw [← hprodF v]
          exact hdivG v
        let qFG := quotientLinear qF G hG hdivG'
        have hdataG := quotientLinear_nested_data
          (Dlow - wt (contactWeights w) F) w
          (T - wt residualTotalWeights F)
          (YS - wt residualYSWeights F)
          (S - wt residualSWeights F)
          qF hqF hqFBox G hG hdivG'
        have hqFG : Function.Injective qFG := by
          simpa only [qFG] using hdataG.1
        have hprodG : ∀ v, qF v = G * qFG v := by
          simpa only [qFG] using hdataG.2.1
        have hqFGBox : ∀ v, qFG v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F - wt (contactWeights w) G) w
            (T - wt residualTotalWeights F - wt residualTotalWeights G)
            (YS - wt residualYSWeights F - wt residualYSWeights G)
            (S - wt residualSWeights F - wt residualSWeights G) := by
          simpa only [qFG] using hdataG.2.2
        have hwidthRest :
            Dlow - wt (contactWeights w) F - wt (contactWeights w) G ≤
              (Dlow - delta - wt (contactWeights w) F -
                wt (contactWeights w) G) + delta := by
          omega
        obtain ⟨stageF, stageG⟩ := ih
          (Dlow - wt (contactWeights w) F - wt (contactWeights w) G)
          (Dlow - delta - wt (contactWeights w) F -
            wt (contactWeights w) G)
          (T - wt residualTotalWeights F - wt residualTotalWeights G)
          (YS - wt residualYSWeights F - wt residualYSWeights G)
          (S - wt residualSWeights F - wt residualSWeights G)
          hwidthRest qFG hqFG hqFGBox hsourceBoth
        have liftF :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q F := by
          rcases stageF with
            ⟨j, v, J, hv, hJ, heq, _hT, _hY, _hS, hC, hterminal⟩
          let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
          let JUp := G * J
          have hJUp : JUp ≠ 0 := mul_ne_zero hG hJ
          have hv' : v.1 ≠ 0 := by
            intro hz
            apply hv
            exact Subtype.ext hz
          have heqOne : F ^ (j.val + 1) * JUp = qOne v := by
            calc
              F ^ (j.val + 1) * JUp = F * (G * (F ^ j.val * J)) := by
                simp only [JUp, pow_succ']
                ring
              _ = F * (G * qFG v) := by rw [heq]
              _ = F * qF v := by rw [← hprodG v]
              _ = qOne v := (hprodF v).symm
          have hqOneV : qOne v ≠ 0 := by
            intro hz
            apply hv
            apply hqOne
            simpa only [map_zero] using hz
          have hb := residual_bounds_of_power_identity Dlow w T YS S
            (j.val + 1) (qOne v) F JUp hqOneV hF hJUp
            (hqOneBox v) heqOne
          refine ⟨jUp, v.1, JUp, hv', hJUp, ?_, hb.1, hb.2.1,
            hb.2.2, ?_, ?_⟩
          · simpa only [jUp, qOne, LinearMap.comp_apply,
              Submodule.coe_subtype] using heqOne
          · have hm : wt (contactWeights w) JUp ≤
                wt (contactWeights w) G + wt (contactWeights w) J := by
              simpa only [JUp] using wt_mul_le (contactWeights w) G J
            exact hm.trans_lt (by
              simpa only [jUp] using cross_contact_lt Dlow delta
                (wt (contactWeights w) F) (wt (contactWeights w) G)
                j.val (wt (contactWeights w) J) hC)
          · intro hlt
            have hn : ¬ F ∣ J := by
              apply hterminal
              change j.val + 1 < steps + 1
              change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
              omega
            intro hd
            exact hn (hrel.dvd_of_dvd_mul_left hd)
        have liftG :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q G := by
          rcases stageG with
            ⟨j, v, J, hv, hJ, heq, _hT, _hY, _hS, hC, hterminal⟩
          let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
          let JUp := F * J
          have hJUp : JUp ≠ 0 := mul_ne_zero hF hJ
          have hv' : v.1 ≠ 0 := by
            intro hz
            apply hv
            exact Subtype.ext hz
          have heqOne : G ^ (j.val + 1) * JUp = qOne v := by
            calc
              G ^ (j.val + 1) * JUp = F * (G * (G ^ j.val * J)) := by
                simp only [JUp, pow_succ']
                ring
              _ = F * (G * qFG v) := by rw [heq]
              _ = F * qF v := by rw [← hprodG v]
              _ = qOne v := (hprodF v).symm
          have hqOneV : qOne v ≠ 0 := by
            intro hz
            apply hv
            apply hqOne
            simpa only [map_zero] using hz
          have hb := residual_bounds_of_power_identity Dlow w T YS S
            (j.val + 1) (qOne v) G JUp hqOneV hG hJUp
            (hqOneBox v) heqOne
          refine ⟨jUp, v.1, JUp, hv', hJUp, ?_, hb.1, hb.2.1,
            hb.2.2, ?_, ?_⟩
          · simpa only [jUp, qOne, LinearMap.comp_apply,
              Submodule.coe_subtype] using heqOne
          · have hm : wt (contactWeights w) JUp ≤
                wt (contactWeights w) F + wt (contactWeights w) J := by
              simpa only [JUp] using wt_mul_le (contactWeights w) F J
            have hC' : wt (contactWeights w) J <
                Dlow - delta - wt (contactWeights w) G -
                  wt (contactWeights w) F - j.val * delta -
                    j.val * wt (contactWeights w) G := by
              simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using hC
            exact hm.trans_lt (by
              simpa only [jUp] using cross_contact_lt Dlow delta
                (wt (contactWeights w) G) (wt (contactWeights w) F)
                j.val (wt (contactWeights w) J) hC')
          · intro hlt
            have hn : ¬ G ∣ J := by
              apply hterminal
              change j.val + 1 < steps + 1
              change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
              omega
            intro hd
            exact hn (hrel.symm.dvd_of_dvd_mul_left hd)
        exact ⟨liftF, liftG⟩
      · rcases honeF with ⟨hdivF, ⟨vG, hvG⟩⟩
        let qF := quotientLinear qOne F hF hdivF
        have hdataF := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox F hF hdivF
        have hqF : Function.Injective qF := by
          simpa only [qF] using hdataF.1
        have hprodF : ∀ v, qOne v = F * qF v := by
          simpa only [qF] using hdataF.2.1
        have hqFBox : ∀ v, qF v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) F) w
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) := by
          simpa only [qF] using hdataF.2.2
        have hwidthRest : Dlow - wt (contactWeights w) F ≤
            (Dlow - delta - wt (contactWeights w) F) + delta := by
          omega
        obtain ⟨j, v, J, hv, hJ, heq, hbox, hterminal⟩ :=
          exists_power_stage_of_bandBudget_succ steps
            (Dlow - wt (contactWeights w) F)
            (Dlow - delta - wt (contactWeights w) F)
            w delta
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F)
            hwidthRest qF hqF hqFBox F hF hsourceF
        have hwts := nested_mem_weights hbox hJ
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        have hv' : v.1 ≠ 0 := by
          intro hz
          apply hv
          exact Subtype.ext hz
        have stageF :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q F := by
          refine ⟨jUp, v.1, J, hv', hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · change F ^ (j.val + 1) * J = q v.1
            calc
              F ^ (j.val + 1) * J = F * (F ^ j.val * J) := by
                rw [pow_succ']
                ring
              _ = F * qF v := by rw [heq]
              _ = qOne v := (hprodF v).symm
              _ = q v.1 := rfl
          · simpa only [jUp, sub_one_then_mul] using hwts.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.2.1
          · simpa only [jUp, sub_pair_then_mul] using hwts.2.2.2
          · intro hlt
            apply hterminal
            change j.val + 1 < steps + 1
            change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
            omega
        exact ⟨stageF, immediate G vG hvG⟩
      · rcases honeG with ⟨⟨vF, hvF⟩, hdivG⟩
        let qG := quotientLinear qOne G hG hdivG
        have hdataG := quotientLinear_nested_data Dlow w T YS S qOne hqOne
          hqOneBox G hG hdivG
        have hqG : Function.Injective qG := by
          simpa only [qG] using hdataG.1
        have hprodG : ∀ v, qOne v = G * qG v := by
          simpa only [qG] using hdataG.2.1
        have hqGBox : ∀ v, qG v ∈ nestedCoefficientBox K
            (Dlow - wt (contactWeights w) G) w
            (T - wt residualTotalWeights G)
            (YS - wt residualYSWeights G)
            (S - wt residualSWeights G) := by
          simpa only [qG] using hdataG.2.2
        have hwidthRest : Dlow - wt (contactWeights w) G ≤
            (Dlow - delta - wt (contactWeights w) G) + delta := by
          omega
        obtain ⟨j, v, J, hv, hJ, heq, hbox, hterminal⟩ :=
          exists_power_stage_of_bandBudget_succ steps
            (Dlow - wt (contactWeights w) G)
            (Dlow - delta - wt (contactWeights w) G)
            w delta
            (T - wt residualTotalWeights G)
            (YS - wt residualYSWeights G)
            (S - wt residualSWeights G)
            hwidthRest qG hqG hqGBox G hG hsourceG
        have hwts := nested_mem_weights hbox hJ
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        have hv' : v.1 ≠ 0 := by
          intro hz
          apply hv
          exact Subtype.ext hz
        have stageG :
            HasFactorStage (Nat.succ steps + 1) Dlow w delta T YS S q G := by
          refine ⟨jUp, v.1, J, hv', hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · change G ^ (j.val + 1) * J = q v.1
            calc
              G ^ (j.val + 1) * J = G * (G ^ j.val * J) := by
                rw [pow_succ']
                ring
              _ = G * qG v := by rw [heq]
              _ = qOne v := (hprodG v).symm
              _ = q v.1 := rfl
          · simpa only [jUp, sub_one_then_mul] using hwts.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.1
          · simpa only [jUp, sub_one_then_mul] using hwts.2.2.1
          · simpa only [jUp, sub_pair_then_mul] using hwts.2.2.2
          · intro hlt
            apply hterminal
            change j.val + 1 < steps + 1
            change j.val + 1 + 1 < Nat.succ steps + 1 at hlt
            omega
        exact ⟨immediate F vF hvF, stageG⟩
      · obtain ⟨v, hvF, hvG⟩ := hneither
        exact ⟨immediate F v hvF, immediate G v hvG⟩

/-- A directed helper after removing one outer copy of each factor.  For the
`F` direction the original source is `F^(j+1) * (G * J)`.  Consequently the
derivative argument makes `J` vanish on the `F`-regular seeds away from the
collision locus `G = 0`; the collision locus itself can use `G` as its cut.
-/
def HasDirectedOuterStage [AddCommMonoid V] [Module K V]
    (fuel D w delta T YS S : ℕ)
    (q : V →ₗ[K] P4 K) (F G : P4 K) : Prop :=
  ∃ (j : Fin fuel) (v : V) (J : P4 K),
    v ≠ 0 ∧ J ≠ 0 ∧ F ^ (j.val + 1) * (G * J) = q v ∧
    wt residualTotalWeights J ≤
      T - wt residualTotalWeights F - wt residualTotalWeights G -
        j.val * wt residualTotalWeights F ∧
    wt residualYSWeights J ≤
      YS - wt residualYSWeights F - wt residualYSWeights G -
        j.val * wt residualYSWeights F ∧
    wt residualSWeights J ≤
      S - wt residualSWeights F - wt residualSWeights G -
        j.val * wt residualSWeights F ∧
    wt (contactWeights w) J <
      D - delta - wt (contactWeights w) F - wt (contactWeights w) G -
        j.val * delta - j.val * wt (contactWeights w) F ∧
    (j.val + 1 < fuel → ¬ F ∣ J)

/-- Entry point from an original source family universally divisible by both
regular factors.  It exposes the residual directed helper `J`, not `G * J`,
so the consumer can split into the off-collision (`J`) and collision (`G`)
seed classes without inflating the common helper caps. -/
theorem exists_directed_outer_stages_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps D w delta T YS S : ℕ)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F G : P4 K) (hF : F ≠ 0) (hG : G ≠ 0)
    (hrel : IsRelPrime F G)
    (hdivF : ∀ v, F ∣ q v) (hdivG : ∀ v, G ∣ q v)
    (hsource :
      twoFactorBandBudget delta
          (wt residualTotalWeights F) (wt residualYSWeights F)
          (wt residualSWeights F)
          (wt residualTotalWeights G) (wt residualYSWeights G)
          (wt residualSWeights G)
          (T - wt residualTotalWeights F - wt residualTotalWeights G)
          (YS - wt residualYSWeights F - wt residualYSWeights G)
          (S - wt residualSWeights F - wt residualSWeights G)
          (steps + 1) < Module.finrank K V) :
    HasDirectedOuterStage (steps + 1) D w delta T YS S q F G ∧
      HasDirectedOuterStage (steps + 1) D w delta T YS S q G F := by
  classical
  obtain ⟨qFG, hqFG, hprod, hqFGBox⟩ :=
    exists_twoFactor_quotient_nested_data D w T YS S q hq hmem
      F G hF hG hrel hdivF hdivG
  have hwidth :
      D - wt (contactWeights w) F - wt (contactWeights w) G ≤
        (D - delta - wt (contactWeights w) F -
          wt (contactWeights w) G) + delta := by
    omega
  obtain ⟨stageF, stageG⟩ :=
    exists_two_factor_stages_of_bandBudget_succ steps
      (D - wt (contactWeights w) F - wt (contactWeights w) G)
      (D - delta - wt (contactWeights w) F - wt (contactWeights w) G)
      w delta
      (T - wt residualTotalWeights F - wt residualTotalWeights G)
      (YS - wt residualYSWeights F - wt residualYSWeights G)
      (S - wt residualSWeights F - wt residualSWeights G)
      hwidth qFG hqFG hqFGBox F G hF hG hrel hsource
  have directedF :
      HasDirectedOuterStage (steps + 1) D w delta T YS S q F G := by
    rcases stageF with
      ⟨j, v, J, hv, hJ, heq, hT, hY, hS, hC, hterminal⟩
    refine ⟨j, v, J, hv, hJ, ?_, hT, hY, hS, hC, hterminal⟩
    calc
      F ^ (j.val + 1) * (G * J) = F * (G * (F ^ j.val * J)) := by
        rw [pow_succ']
        ring
      _ = F * (G * qFG v) := by rw [heq]
      _ = q v := (hprod v).symm
  have directedG :
      HasDirectedOuterStage (steps + 1) D w delta T YS S q G F := by
    rcases stageG with
      ⟨j, v, J, hv, hJ, heq, hT, hY, hS, hC, hterminal⟩
    refine ⟨j, v, J, hv, hJ, ?_, ?_, ?_, ?_, ?_, hterminal⟩
    · calc
        G ^ (j.val + 1) * (F * J) = F * (G * (G ^ j.val * J)) := by
          rw [pow_succ']
          ring
        _ = F * (G * qFG v) := by rw [heq]
        _ = q v := (hprod v).symm
    · simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hT
    · simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hY
    · simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hS
    · simpa only [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hC
  exact ⟨directedF, directedG⟩

/-- After extracting the `F`-power term, the residual helper vanishes away
from the collision with `G`.  This is the exact soundness interface needed by
the directed consumer: collision seeds are charged using `G`, and every other
`F`-regular seed is charged using `J`. -/
theorem specialization_eq_zero_of_iteratePderivR_twoFactor_offCollision
    (j : ℕ) (P : Polynomial K) (gamma : K) (F G J : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGnonzero : RCN319.specialization K P gamma G ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (F ^ j * (G * J))) = 0) :
    RCN319.specialization K P gamma J = 0 := by
  have hGJ := specialization_eq_zero_of_iteratePderivR_power_product
    j P gamma F (G * J) hfactorial hFzero hregular hpower
  have hmul : RCN319.specialization K P gamma G *
      RCN319.specialization K P gamma J = 0 := by
    simpa only [map_mul] using hGJ
  exact (mul_eq_zero.mp hmul).resolve_left hGnonzero

private theorem reconstruct_mem_low_of_directed_power
    {I : Type} [Fintype I]
    (D w L S m delta j : ℕ) (nodes : I → K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L S m nodes u0 u1)
    (F G J : P4 K)
    (heq : F ^ (j + 1) * (G * J) =
      reconstruct K D w L S v.1)
    (hD : 0 < D) (hlowpos : 0 < D - (j + 1) * delta)
    (hcontact : wt (contactWeights w) J <
      D - delta - wt (contactWeights w) F - wt (contactWeights w) G -
        j * delta - j * wt (contactWeights w) F) :
    reconstruct K D w L S v.1 ∈
      globalCoefficientBox K (D - (j + 1) * delta) w L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D w L S v.1) D w L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D w L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D w L S v.1) (D - (j + 1) * delta) w L S
      hlowpos).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [← heq]
  have houter := wt_mul_le (contactWeights w) (F ^ (j + 1)) (G * J)
  have hpow := wt_pow_le (contactWeights w) F (j + 1)
  have hinner := wt_mul_le (contactWeights w) G J
  simp only [Nat.add_mul, one_mul] at hpow ⊢
  omega

/-- Turn one directed outer stage into a concrete helper vanishing on every
`F`-regular seed outside the `F/G` collision locus.  The returned derivative
order is `j+1`, while the low contact cutoff is `D-(j+1)*delta`; keeping these
two quantities together avoids the common off-by-one error in the outer-FG
route. -/
theorem exists_directed_helper_zero_offCollision
    {I : Type} [Fintype I] [DecidableEq I]
    (fuel D w L S m delta T YS agreements p : ℕ)
    [CharP K p] (hp : p.Prime)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (H : P4 K) (F G : RCN266.RegularIndex H)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hD : 0 < D) (hw : 1 ≤ w) (hfuelChar : fuel < p)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)).card)
    (hcapacity : ∀ a, 1 ≤ a → a ≤ fuel →
      D - a * delta ≤ (m - a) * agreements + a * (w - 1))
    (hlowpos : ∀ a, 1 ≤ a → a ≤ fuel → 0 < D - a * delta)
    (hstage : HasDirectedOuterStage fuel D w delta T YS S
      (kernelReconstructLinear (K := K) D w L S m nodes u0 u1)
      F.1 G.1) :
    ∃ (j : Fin fuel)
        (v : ConstraintKernel (K := K) D w L S m nodes u0 u1)
        (J : P4 K),
      v ≠ 0 ∧ J ≠ 0 ∧
      F.1 ^ (j.val + 1) * (G.1 * J) = reconstruct K D w L S v.1 ∧
      wt residualTotalWeights J ≤
        T - wt residualTotalWeights F.1 - wt residualTotalWeights G.1 -
          j.val * wt residualTotalWeights F.1 ∧
      wt residualYSWeights J ≤
        YS - wt residualYSWeights F.1 - wt residualYSWeights G.1 -
          j.val * wt residualYSWeights F.1 ∧
      wt residualSWeights J ≤
        S - wt residualSWeights F.1 - wt residualSWeights G.1 -
          j.val * wt residualSWeights F.1 ∧
      (j.val + 1 < fuel → ¬ F.1 ∣ J) ∧
      ∀ gamma ∈ regularSeeds H selected Gamma F,
        RCN319.specialization K (selected gamma) gamma G.1 ≠ 0 →
          RCN319.specialization K (selected gamma) gamma J = 0 := by
  classical
  rcases hstage with
    ⟨j, v, J, hv, hJ, heq, hT, hY, hS, hcontact, hterminal⟩
  have heq' : F.1 ^ (j.val + 1) * (G.1 * J) =
      reconstruct K D w L S v.1 := by
    simpa only [kernelReconstructLinear_apply] using heq
  have hjpos : 1 ≤ j.val + 1 := by omega
  have hjle : j.val + 1 ≤ fuel := by omega
  have hlow : reconstruct K D w L S v.1 ∈
      globalCoefficientBox K (D - (j.val + 1) * delta) w L S :=
    reconstruct_mem_low_of_directed_power D w L S m delta j.val
      nodes u0 u1 v F.1 G.1 J heq' hD (hlowpos _ hjpos hjle) hcontact
  refine ⟨j, v, J, hv, hJ, heq', hT, hY, hS, hterminal, ?_⟩
  intro gamma hgamma hGnonzero
  have hgammaG := regularSeeds_subset H selected Gamma F hgamma
  let support := (Finset.univ : Finset I).filter (fun i ↦
    (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
  have hcard : agreements ≤ support.card := hagreement gamma hgammaG
  have hcap : D - (j.val + 1) * delta ≤
      (m - (j.val + 1)) * support.card + (j.val + 1) * (w - 1) :=
    (hcapacity _ hjpos hjle).trans
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left (m - (j.val + 1)) hcard) _)
  have hvalues : ∀ i ∈ support,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hder := specialization_iteratePderivR_eq_zero_of_kernel_low_box
    (j.val + 1) D (D - (j.val + 1) * delta) w L S m
    nodes u0 u1 v hlow (selected gamma) gamma support hjpos
    hw (hdegree gamma hgammaG) hcap hvalues
  rw [← heq'] at hder
  obtain ⟨hFzero, hregular⟩ := (Finset.mem_filter.mp hgamma).2
  exact specialization_eq_zero_of_iteratePderivR_twoFactor_offCollision
    (j.val + 1) (selected gamma) gamma F.1 G.1 J
    (factorial_ne_zero_of_lt_char p (j.val + 1) hp
      (hjle.trans_lt hfuelChar))
    hFzero hregular hGnonzero hder

end

end ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance
end PackedLocator_LocatorTwoFactorAvoidance

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier08 : True := by trivial
end ProximityPrize.SubmissionLower

