/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# The affine-pencil branch after linear-R elimination

The accepted lower `67.77` proof eliminates a carrier that is linear in its
residual `R` coordinate without a mixed-degree characteristic hypothesis.  If
the resulting bivariate resultant vanishes identically, interpolation on the
identity nodes forces the selected row polynomials onto a pencil

`P gamma = P0 + gamma * P1`.

This file reverses that exceptional branch for an upper attack.  Suppose a
fixed received line `u0 + gamma * u1` agrees with this polynomial pencil on at
least `n - e` coordinates for every challenge.  More than `e + 1` challenges
force one agreement support on which both `u0` and `u1` equal the two pencil
directions separately.  The corresponding two-row instance is then not
violating.  Thus the identity branch has an intrinsic cap of `e + 1`, with no
dependence on the characteristic or on the resultant degree.

At the first prospective `116.12` endpoint this cap is `122363`, versus the
inclusive challenge threshold `274980728111395088`.  Consequently the new
linear-`R` elimination is useful as an upper rejection gate, but it does not
provide a threshold-sized fixed-center construction.  A surviving attack must
use a genuinely nonlinear challenge reparameterization, an irregular carrier,
or a nonidentity resultant branch.
-/

namespace ProximityPrize.SubmissionUpper.LinearRAffinePencilGate

open scoped BigOperators

section AffineSupport

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [DecidableEq F]

/-- If more than `e + 1` affine parameters have supports of size at least
`|ι| - e`, one support separates the affine identity into its two coefficient
identities.  This is the exact combinatorial obstruction behind the
large-pencil alternative; it does not use a degree or characteristic bound. -/
theorem exists_support_with_both_rows
    (u p : Fin 2 → ι → F) (Gamma : Finset F) (support : F → Finset ι) (e : ℕ)
    (hGamma : e + 1 < Gamma.card)
    (hsupport : ∀ gamma ∈ Gamma,
      Fintype.card ι - e ≤ (support gamma).card)
    (haffine : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      u 0 i + gamma * u 1 i = p 0 i + gamma * p 1 i) :
    ∃ gamma ∈ Gamma, ∀ i ∈ support gamma,
      u 0 i = p 0 i ∧ u 1 i = p 1 i := by
  classical
  let bad : Finset ι := Finset.univ.filter fun i =>
    u 0 i ≠ p 0 i ∨ u 1 i ≠ p 1 i
  let residual : F → Finset ι := fun gamma => support gamma ∩ bad
  have hresidual_sub (gamma : F) : residual gamma ⊆ bad := by
    intro i hi
    exact (Finset.mem_inter.mp hi).2
  have hpairwise : (↑Gamma : Set F).PairwiseDisjoint residual := by
    rintro gamma hgamma eta heta hne
    change Disjoint (residual gamma) (residual eta)
    rw [Finset.disjoint_left]
    intro i hiGamma hiEta
    have hiSupportGamma : i ∈ support gamma := (Finset.mem_inter.mp hiGamma).1
    have hiSupportEta : i ∈ support eta := (Finset.mem_inter.mp hiEta).1
    have hgammaEq := haffine gamma hgamma i hiSupportGamma
    have hetaEq := haffine eta heta i hiSupportEta
    have hmul : (gamma - eta) * (u 1 i - p 1 i) = 0 := by
      linear_combination hgammaEq - hetaEq
    have hgammaEta : gamma - eta ≠ 0 := sub_ne_zero.mpr hne
    have hrowOne : u 1 i = p 1 i := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hgammaEta)
    have hrowZero : u 0 i = p 0 i := by
      rw [hrowOne] at hgammaEq
      exact add_right_cancel hgammaEq
    have hiBad : i ∈ bad := (Finset.mem_inter.mp hiGamma).2
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hiBad
    exact hiBad.elim (fun h => h hrowZero) (fun h => h hrowOne)
  have hresidual_lower (gamma : F) (hgamma : gamma ∈ Gamma) :
      bad.card ≤ (residual gamma).card + e := by
    have hsplit := Finset.card_inter_add_card_sdiff (support gamma) bad
    have hdiff : (support gamma \ bad).card ≤ badᶜ.card := by
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_compl]
      exact (Finset.mem_sdiff.mp hi).2
    rw [Finset.card_compl] at hdiff
    have hlarge := hsupport gamma hgamma
    have hbadCard : bad.card ≤ Fintype.card ι := Finset.card_le_univ bad
    dsimp only [residual]
    omega
  have hbad : bad.card ≤ e := by
    by_contra hnot
    have heBad : e < bad.card := Nat.lt_of_not_ge hnot
    have hsumLower : Gamma.card * (bad.card - e) ≤
        ∑ gamma ∈ Gamma, (residual gamma).card := by
      calc
        Gamma.card * (bad.card - e) =
            ∑ _gamma ∈ Gamma, (bad.card - e) := by
          exact (Finset.sum_const_nat (fun _ _ => rfl)).symm
        _ ≤ ∑ gamma ∈ Gamma, (residual gamma).card := by
          exact Finset.sum_le_sum fun gamma hgamma => by
            have := hresidual_lower gamma hgamma
            omega
    have hunionSub : (Gamma.biUnion residual).card ≤ bad.card := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨gamma, _hgamma, hiResidual⟩ := Finset.mem_biUnion.mp hi
      exact hresidual_sub gamma hiResidual
    have hunionCard : (Gamma.biUnion residual).card =
        ∑ gamma ∈ Gamma, (residual gamma).card :=
      Finset.card_biUnion hpairwise
    rw [hunionCard] at hunionSub
    have hproduct : Gamma.card * (bad.card - e) ≤ bad.card :=
      hsumLower.trans hunionSub
    have hpositive : 0 < bad.card - e := Nat.sub_pos_of_lt heBad
    have hGammaLower : e + 2 ≤ Gamma.card := by omega
    have heMul : e ≤ e * (bad.card - e) :=
      Nat.le_mul_of_pos_right e hpositive
    have hstrict : bad.card < (e + 2) * (bad.card - e) := by
      calc
        bad.card = e + (bad.card - e) := (Nat.add_sub_of_le heBad.le).symm
        _ ≤ e * (bad.card - e) + (bad.card - e) :=
          Nat.add_le_add_right heMul _
        _ < e * (bad.card - e) + 2 * (bad.card - e) := by omega
        _ = (e + 2) * (bad.card - e) := by ring
    have hproductLower : (e + 2) * (bad.card - e) ≤
        Gamma.card * (bad.card - e) :=
      Nat.mul_le_mul_right _ hGammaLower
    omega
  by_contra hno
  push Not at hno
  have hresidual_pos : ∀ gamma ∈ Gamma, 1 ≤ (residual gamma).card := by
    intro gamma hgamma
    obtain ⟨i, hiSupport, hiNotBoth⟩ := hno gamma hgamma
    apply Finset.card_pos.mpr
    refine ⟨i, Finset.mem_inter.mpr ⟨hiSupport, ?_⟩⟩
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hzero : u 0 i = p 0 i
    · exact Or.inr (hiNotBoth hzero)
    · exact Or.inl hzero
  have hGammaSum : Gamma.card ≤ ∑ gamma ∈ Gamma, (residual gamma).card := by
    calc
      Gamma.card = ∑ _gamma ∈ Gamma, 1 := by simp
      _ ≤ ∑ gamma ∈ Gamma, (residual gamma).card :=
        Finset.sum_le_sum hresidual_pos
  have hunionSub : (Gamma.biUnion residual).card ≤ bad.card := by
    apply Finset.card_le_card
    intro i hi
    obtain ⟨gamma, _hgamma, hiResidual⟩ := Finset.mem_biUnion.mp hi
    exact hresidual_sub gamma hiResidual
  rw [Finset.card_biUnion hpairwise] at hunionSub
  have hGammaBad : Gamma.card ≤ bad.card := hGammaSum.trans hunionSub
  omega

/-- Polynomial form of the gate.  If the selected rows are exactly
`P0 + gamma * P1`, a fixed received center cannot support more than `e + 1`
challenges while remaining genuinely violating on every selected support. -/
theorem fixed_center_affine_polynomial_pencil_card_le
    (domain : ι → F) (u0 u1 : ι → F) (P0 P1 : Polynomial F)
    (Gamma : Finset F) (support : F → Finset ι) (e : ℕ)
    (hsupport : ∀ gamma ∈ Gamma,
      Fintype.card ι - e ≤ (support gamma).card)
    (hagreement : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      (P0 + Polynomial.C gamma * P1).eval (domain i) =
        u0 i + gamma * u1 i)
    (hviolating : ∀ gamma ∈ Gamma,
      ¬∀ i ∈ support gamma,
        u0 i = P0.eval (domain i) ∧ u1 i = P1.eval (domain i)) :
    Gamma.card ≤ e + 1 := by
  by_contra hnot
  have hlarge : e + 1 < Gamma.card := Nat.lt_of_not_ge hnot
  let u : Fin 2 → ι → F := ![u0, u1]
  let p : Fin 2 → ι → F :=
    ![fun i => P0.eval (domain i), fun i => P1.eval (domain i)]
  have haffine : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      u 0 i + gamma * u 1 i = p 0 i + gamma * p 1 i := by
    intro gamma hgamma i hi
    have h := (hagreement gamma hgamma i hi).symm
    simpa [u, p, Polynomial.eval_add, Polynomial.eval_mul] using h
  obtain ⟨gamma, hgamma, hboth⟩ :=
    exists_support_with_both_rows u p Gamma support e hlarge hsupport haffine
  exact hviolating gamma hgamma (by
    intro i hi
    simpa [u, p] using hboth i hi)

/-- Double counting for a nonlinear escape from the identity branch.  After
removing at most `w` identity coordinates, if every remaining coordinate can
serve at most `fiberCap` challenges, then the whole challenge family obeys
the sharp incidence inequality below. -/
theorem bounded_nonidentity_incidence
    {Seed Node : Type*} [DecidableEq Seed] [DecidableEq Node]
    (relation : Seed → Node → Prop)
    [∀ seed node, Decidable (relation seed node)]
    (seeds : Finset Seed) (nodes identities : Finset Node)
    (agreement w fiberCap : ℕ)
    (hidentities : identities ⊆ nodes)
    (hidentityCard : identities.card ≤ w)
    (hgap : w < agreement) (hagreementCard : agreement ≤ nodes.card)
    (hagreement : ∀ seed ∈ seeds,
      agreement ≤ (nodes.filter (relation seed)).card)
    (hfiber : ∀ node ∈ nodes \ identities,
      (seeds.filter fun seed => relation seed node).card ≤ fiberCap) :
    seeds.card * (agreement - w) ≤ (nodes.card - w) * fiberCap := by
  have hremaining (seed : Seed) (hseed : seed ∈ seeds) :
      agreement - identities.card ≤
        ((nodes \ identities).filter (relation seed)).card := by
    have hsub : (nodes.filter (relation seed)) \ identities ⊆
        (nodes \ identities).filter (relation seed) := by
      intro node hnode
      obtain ⟨hfiltered, hnotIdentity⟩ := Finset.mem_sdiff.mp hnode
      obtain ⟨hnodes, hrel⟩ := Finset.mem_filter.mp hfiltered
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hnodes, hnotIdentity⟩, hrel⟩
    calc
      agreement - identities.card ≤
          (nodes.filter (relation seed)).card - identities.card :=
        Nat.sub_le_sub_right (hagreement seed hseed) identities.card
      _ ≤ ((nodes.filter (relation seed)) \ identities).card :=
        Finset.le_card_sdiff identities (nodes.filter (relation seed))
      _ ≤ ((nodes \ identities).filter (relation seed)).card :=
        Finset.card_le_card hsub
  have hraw : seeds.card * (agreement - identities.card) ≤
      (nodes.card - identities.card) * fiberCap := by
    calc
      seeds.card * (agreement - identities.card) =
          ∑ _seed ∈ seeds, (agreement - identities.card) := by simp
      _ ≤ ∑ seed ∈ seeds,
          ((nodes \ identities).filter (relation seed)).card :=
        Finset.sum_le_sum hremaining
      _ = ∑ node ∈ nodes \ identities,
          (seeds.filter fun seed => relation seed node).card := by
        simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      _ ≤ ∑ _node ∈ nodes \ identities, fiberCap :=
        Finset.sum_le_sum hfiber
      _ = (nodes.card - identities.card) * fiberCap := by
        simp [Finset.card_sdiff_of_subset hidentities]
  by_cases hseedCap : seeds.card ≤ fiberCap
  · calc
      seeds.card * (agreement - w) ≤ fiberCap * (agreement - w) :=
        Nat.mul_le_mul_right _ hseedCap
      _ ≤ fiberCap * (nodes.card - w) :=
        Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hagreementCard w)
      _ = (nodes.card - w) * fiberCap := Nat.mul_comm _ _
  · have hfiberSeed : fiberCap ≤ seeds.card := (Nat.lt_of_not_ge hseedCap).le
    have hagreementSplit : agreement - identities.card =
        (agreement - w) + (w - identities.card) := by omega
    have hnodesSplit : nodes.card - identities.card =
        (nodes.card - w) + (w - identities.card) := by omega
    have hraw' :
        seeds.card * (agreement - w) +
            seeds.card * (w - identities.card) ≤
          (nodes.card - w) * fiberCap +
            (w - identities.card) * fiberCap := by
      simpa only [hagreementSplit, hnodesSplit, Nat.mul_add, Nat.add_mul] using hraw
    have hcancel : (w - identities.card) * fiberCap ≤
        seeds.card * (w - identities.card) := by
      calc
        (w - identities.card) * fiberCap ≤
            (w - identities.card) * seeds.card :=
          Nat.mul_le_mul_left _ hfiberSeed
        _ = seeds.card * (w - identities.card) := Nat.mul_comm _ _
    omega

end AffineSupport

/-! ## Exact benchmark-scale consequences -/

def domainSize : ℕ := 262144
def challengeThreshold : ℕ := 274980728111395088

def currentAgreement : ℕ := 139775
def currentErrors : ℕ := domainSize - currentAgreement
def currentAffinePencilCap : ℕ := currentErrors + 1

def improvementAgreement : ℕ := 139782
def improvementErrors : ℕ := domainSize - improvementAgreement
def improvementAffinePencilCap : ℕ := improvementErrors + 1

def rowDegree : ℕ := 131071
def improvementAgreementGap : ℕ := improvementAgreement - rowDegree
def movingCoordinateCount : ℕ := domainSize - rowDegree

/-- Least per-coordinate nonlinear fibre cap that is not immediately rejected
by sharp incidence at the first score-improving agreement. -/
def minimumNonlinearFiberCap : ℕ := 18274985104318683

def acceptedLower6777Agreement : ℕ := 181618
def acceptedLower6777Errors : ℕ := domainSize - acceptedLower6777Agreement
def acceptedLower6777AffinePencilCap : ℕ := acceptedLower6777Errors + 1

theorem exact_affine_pencil_caps :
    currentErrors = 122369 ∧ currentAffinePencilCap = 122370 ∧
      improvementErrors = 122362 ∧ improvementAffinePencilCap = 122363 ∧
      acceptedLower6777Errors = 80526 ∧
      acceptedLower6777AffinePencilCap = 80527 := by
  norm_num [currentErrors, currentAffinePencilCap, improvementErrors,
    improvementAffinePencilCap, acceptedLower6777Errors,
    acceptedLower6777AffinePencilCap, domainSize, currentAgreement,
    improvementAgreement, acceptedLower6777Agreement]

/-- The affine-pencil exception is already more than twelve orders of
magnitude too small at the first score-improving agreement. -/
theorem improvement_affine_pencil_cap_below_threshold :
    improvementAffinePencilCap < challengeThreshold := by
  norm_num [improvementAffinePencilCap, improvementErrors, domainSize,
    improvementAgreement, challengeThreshold]

/-- A nonlinear reparameterization can avoid the affine identity conclusion
only by presenting an enormous coordinate fibre: the first arithmetically
possible cap is `18274985104318683`. -/
theorem nonlinear_fiber_cap_boundary :
    movingCoordinateCount * (minimumNonlinearFiberCap - 1) <
        challengeThreshold * improvementAgreementGap ∧
      challengeThreshold * improvementAgreementGap ≤
        movingCoordinateCount * minimumNonlinearFiberCap := by
  norm_num [movingCoordinateCount, minimumNonlinearFiberCap,
    challengeThreshold, improvementAgreementGap, improvementAgreement,
    rowDegree, domainSize]

theorem minimum_nonlinear_fiber_cap_of_threshold_incidence
    (fiberCap : ℕ)
    (hincidence : challengeThreshold * improvementAgreementGap ≤
      movingCoordinateCount * fiberCap) :
    minimumNonlinearFiberCap ≤ fiberCap := by
  norm_num [challengeThreshold, improvementAgreementGap, improvementAgreement,
    rowDegree, movingCoordinateCount, domainSize,
    minimumNonlinearFiberCap] at hincidence ⊢
  omega

/-- The quadratic seed graph appearing in the simplest nonlinear triangular
core can carry at most thirty challenges in its nonidentity branch. -/
theorem quadratic_nonidentity_card_le
    (card : ℕ)
    (hincidence : card * improvementAgreementGap ≤
      movingCoordinateCount * 2) :
    card ≤ 30 := by
  norm_num [improvementAgreementGap, improvementAgreement, rowDegree,
    movingCoordinateCount, domainSize] at hincidence ⊢
  omega

/-- A threshold-sized challenge family and the affine-pencil cap are
incompatible. -/
theorem no_threshold_sized_improvement_affine_pencil
    (card : ℕ) (hthreshold : challengeThreshold ≤ card)
    (hpencil : card ≤ improvementAffinePencilCap) : False := by
  exact (not_lt_of_ge hthreshold)
    (hpencil.trans_lt improvement_affine_pencil_cap_below_threshold)

#print axioms exists_support_with_both_rows
#print axioms fixed_center_affine_polynomial_pencil_card_le
#print axioms bounded_nonidentity_incidence
#print axioms exact_affine_pencil_caps
#print axioms minimum_nonlinear_fiber_cap_of_threshold_incidence
#print axioms quadratic_nonidentity_card_le
#print axioms no_threshold_sized_improvement_affine_pencil

end ProximityPrize.SubmissionUpper.LinearRAffinePencilGate
