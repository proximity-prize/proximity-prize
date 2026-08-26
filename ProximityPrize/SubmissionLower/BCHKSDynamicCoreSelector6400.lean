import ProximityPrize.SubmissionLower.BCHKSUniversalSelectedPairCore
import ProximityPrize.SubmissionLower.BCHKSUniversalSelection6399
import ProximityPrize.SubmissionLower.BCHKSCoreVandermonde6400
import ProximityPrize.SubmissionLower.BCHKSFullCoreOwnerBridge6400
import ProximityPrize.SubmissionLower.BCHKSCanonicalGammaCoreQuotient6400
import ProximityPrize.SubmissionLower.BCHKSExplicitCoreInnerTransport6400
import ProximityPrize.SubmissionLower.BCHKSFreshQuotientInterpolation6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSDynamicCoreSelector6400

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-!
The dynamic-core variant of the universal selector.

The usual universal proof drives the row-to-column double count all the way
to `k+1` common coordinates and immediately interpolates an affine line.
There is no need to do that.  Stopping at an arbitrary `q+1` common
coordinates gives a genuine common agreement core for the selected Hensel
pair.  The remaining degree is then `k-q`, so a separate quotient-incidence
bound can finish the selected fibre.

This file proves the two non-arithmetic interfaces needed by that switch:

* the row-to-column extraction at an arbitrary target `q+1`; and
* specialization of a zero universal obstruction back to an actual owner
  agreement at every extracted coordinate.
-/

/-- Ambient-restricted row/column extraction.  This is the form needed for
a recursive pass: after the first common core is removed, both the universe
and every agreement row are restricted to its complement. -/
theorem exists_large_coordinates_in_ambient
    {I Challenge : Type} [DecidableEq I] [DecidableEq Challenge]
    (U : Finset I) (T : Finset Challenge)
    (Arow : Challenge → Finset I)
    (rowLower q resultantDegree : ℕ)
    (hrowLower : rowLower ≤ U.card)
    (hrow : ∀ z ∈ T, rowLower ≤
      (U.attach.filter fun i : U ↦ (i : I) ∈ Arow z).card)
    (hincidence : (U.card - q) * resultantDegree <
      (rowLower - q) * T.card) :
    ∃ Coord : Finset U,
      q + 1 ≤ Coord.card ∧
      ∀ i ∈ Coord, resultantDegree <
        (T.filter fun z ↦ (i : I) ∈ Arow z).card := by
  classical
  let ArowU : Challenge → Finset U := fun z ↦
    U.attach.filter fun i : U ↦ (i : I) ∈ Arow z
  let Coord : Finset U := Finset.univ.filter fun i ↦
    resultantDegree < (T.filter fun z ↦ (i : I) ∈ Arow z).card
  have hcard : q + 1 ≤ Coord.card := by
    have hbase : U.card - (U.card - rowLower) = rowLower :=
      Nat.sub_sub_self hrowLower
    have hrow' : ∀ z ∈ T,
        U.card - (U.card - rowLower) ≤ (ArowU z).card := by
      intro z hz
      rw [hbase]
      exact hrow z hz
    have hcount' :
        (U.card - (U.card - rowLower) - q) * T.card >
          (U.card - q) * resultantDegree := by
      rw [hbase]
      exact hincidence
    have hlarge := many_large_fibers
      (ι := {i : I // i ∈ U}) (ζ := Challenge)
      T ArowU U.card (U.card - rowLower) q resultantDegree
        (Fintype.card_coe U) hrow' hcount'
    simpa [Coord, ArowU] using hlarge
  refine ⟨Coord, hcard, ?_⟩
  intro i hi
  exact (Finset.mem_filter.mp hi).2

/-- Root-counting finish for an ambient-restricted recursive pass.  The
returned coordinates live in the complement supplied as `U`, so they are
automatically disjoint from every core removed in earlier passes. -/
theorem exists_zero_obstruction_core_in_ambient
    {I F : Type} [DecidableEq I] [Field F] [DecidableEq F]
    (U : Finset I) (T : Finset F) (Arow : F → Finset I)
    (rowLower q resultantDegree : ℕ)
    (obstruction : I → F[X])
    (hrowLower : rowLower ≤ U.card)
    (hrow : ∀ z ∈ T, rowLower ≤
      (U.attach.filter fun i : U ↦ (i : I) ∈ Arow z).card)
    (hincidence : (U.card - q) * resultantDegree <
      (rowLower - q) * T.card)
    (hdegree : ∀ i ∈ U, (obstruction i).natDegree ≤ resultantDegree)
    (hroot : ∀ i ∈ U, ∀ z ∈ T, i ∈ Arow z →
      (obstruction i).eval z = 0) :
    ∃ Coord : Finset U,
      q + 1 ≤ Coord.card ∧
      ∀ i ∈ Coord, obstruction (i : I) = 0 := by
  obtain ⟨Coord, hCoord, hlarge⟩ :=
    exists_large_coordinates_in_ambient U T Arow
      rowLower q resultantDegree hrowLower hrow hincidence
  refine ⟨Coord, hCoord, ?_⟩
  intro i hi
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (obstruction (i : I))
      (T.filter fun z ↦ (i : I) ∈ Arow z)
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact hroot (i : I) i.property z hz'.1 hz'.2
  · exact (hdegree (i : I) i.property).trans_lt (hlarge i hi)

/-- Arbitrary-target version of the universal coordinate double count. -/
theorem exists_large_universal_coordinates_dynamic6400
    (T : Finset IRSProfile.Field)
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (resultantDegree q : ℕ)
    (hrow : ∀ z ∈ T,
      262144 - bchksErrors6400 ≤ (Arow z).card)
    (hincidence : (262144 - q) * resultantDegree <
      (262144 - bchksErrors6400 - q) * T.card) :
    ∃ Coord : Finset IRSProfile.Index,
      q + 1 ≤ Coord.card ∧
      ∀ i ∈ Coord, resultantDegree <
        (T.filter fun z ↦ i ∈ Arow z).card := by
  classical
  let Coord : Finset IRSProfile.Index := Finset.univ.filter fun i ↦
    resultantDegree < (T.filter fun z ↦ i ∈ Arow z).card
  have hcard : q + 1 ≤ Coord.card := by
    simpa [Coord] using many_large_fibers T Arow 262144 bchksErrors6400
      q resultantDegree (by norm_num [IRSProfile.Index]) hrow
      (by simpa [Nat.mul_comm] using hincidence)
  refine ⟨Coord, hcard, ?_⟩
  intro i hi
  exact (Finset.mem_filter.mp hi).2

/-- A single floor capacity simultaneously gives the structural-fibre
threshold and enough large coordinate columns for a target `q+1` core. -/
theorem dynamic_capacity_implies_common_coordinates6400
    (T : Finset IRSProfile.Field)
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (resultantDegree q ownerCap : ℕ)
    (hgap : 0 < 262144 - bchksErrors6400 - q)
    (hrow : ∀ z ∈ T,
      262144 - bchksErrors6400 ≤ (Arow z).card)
    (hcapacity :
      ((262144 - q) * resultantDegree) /
          (262144 - bchksErrors6400 - q) + (ownerCap + 1) < T.card) :
    ownerCap + 1 < T.card ∧
      ∃ Coord : Finset IRSProfile.Index,
        q + 1 ≤ Coord.card ∧
        ∀ i ∈ Coord, resultantDegree <
          (T.filter fun z ↦ i ∈ Arow z).card := by
  have hbounds := scaled_pair_capacity_implies_incidence
    (262144 - q) (262144 - bchksErrors6400 - q)
      resultantDegree ownerCap T.card hgap hcapacity
  refine ⟨hbounds.2, ?_⟩
  exact exists_large_universal_coordinates_dynamic6400
    T Arow resultantDegree q hrow hbounds.1

/-- Complete arbitrary-`q` row/column selector: once the coordinate
obstructions have the advertised degree and vanish at every owner agreement,
the large columns supplied above are identically zero.  In particular, this
step performs no second selection of the owner fibre. -/
theorem dynamic_capacity_implies_zero_obstruction_core6400
    (T : Finset IRSProfile.Field)
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (resultantDegree q ownerCap : ℕ)
    (obstruction : IRSProfile.Index → IRSProfile.Field[X])
    (hgap : 0 < 262144 - bchksErrors6400 - q)
    (hrow : ∀ z ∈ T,
      262144 - bchksErrors6400 ≤ (Arow z).card)
    (hcapacity :
      ((262144 - q) * resultantDegree) /
          (262144 - bchksErrors6400 - q) + (ownerCap + 1) < T.card)
    (hdegree : ∀ i, (obstruction i).natDegree ≤ resultantDegree)
    (hroot : ∀ i, ∀ z ∈ T, i ∈ Arow z →
      (obstruction i).eval z = 0) :
    ownerCap + 1 < T.card ∧
      ∃ Coord : Finset IRSProfile.Index,
        q + 1 ≤ Coord.card ∧
        ∀ i ∈ Coord, obstruction i = 0 := by
  obtain ⟨howner, Coord, hCoord, hlarge⟩ :=
    dynamic_capacity_implies_common_coordinates6400
      T Arow resultantDegree q ownerCap hgap hrow hcapacity
  refine ⟨howner, Coord, hCoord, ?_⟩
  apply universal_coordinate_obstructions_eq_zero
    T Arow Coord resultantDegree obstruction hlarge
  · intro i _hi
    exact hdegree i
  · intro i _hi z hzT hiz
    exact hroot i z hzT hiz

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A zero branch-independent universal obstruction at one coordinate
specializes to the claimed received-value agreement for every owner in the
selected Hensel fibre.  Unlike the final alignment theorem, this statement
does not require `k+1` coordinates. -/
theorem universal_selected_pair_owner_matches_of_obstruction_zero
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : ℕ) (hkDX : k < DX)
    (T : Finset F) (P : T → F[X])
    (S : UniversalSelectedHenselData x₀ R H hHyp hzeta
      D d k DX T P)
    (hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp (z : F)
      (S.root z) x₀ ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (x u₀ u₁ : F)
    (num : ℕ → F[X][Y]) (s : F[X][Y]) (E : ℕ)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hs : Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) s = HenselNumerators.zeta R x₀ H)
    (hnum : ∀ i, i ≤ k →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (num i) =
        finiteAlpha (R := R) (H := H) x₀ DX i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i)
    (hzero : Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H))
        (universalAffineObstruction num s E k
          (x - x₀) u₀ u₁) = 0) :
    ∀ z : T, (P z).eval x = u₀ + (z : F) * u₁ := by
  have hspecializes : ∀ z : T, ∀ n, n ≤ DX →
      concreteSpecializedAlpha x₀ R hHyp hzeta DX (z : F)
          (S.root z) n = FiniteHensel.TaylorCoeff (P z) x₀ n := by
    intro z n hn
    apply concreteSpecializedAlpha_eq_TaylorCoeff x₀ R hHyp hzeta DX
      (z : F) (S.root z) x₀ ((P z).eval x₀) (P z)
      (S.hx z) (S.hy z) S.hsL (S.hsimple z) rfl
      ((hPdeg z).trans (Nat.le_of_lt hkDX)) (S.hExact z)
      (S.hslope z) (S.hW z) (S.hxi z) n hn
  have hgamma := gamma_eval_eq_affine_of_universalAffineObstruction_eq_zero
    x₀ x u₀ u₁ R hHyp hzeta DX k (Nat.le_of_lt hkDX)
      num s E hE hs hnum hzero
  intro z
  let beta := explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
    u₀ u₁ R hHyp hzeta DX k (Nat.le_of_lt hkDX)
  have hbetaEmbedding : embeddingOf𝒪Into𝕃 H beta = 0 := by
    rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
      u₀ u₁ R hHyp hzeta DX k (Nat.le_of_lt hkDX)]
    change (canonicalFunctionFieldGamma H x₀ R DX k).eval
      (fieldTo𝕃 (H := H) x) = _ at hgamma
    rw [canonicalFunctionFieldGamma_eval] at hgamma
    rw [hgamma]
    ring
  have hbeta : beta = 0 := by
    apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
    simpa using hbetaEmbedding
  have hpiz : piZ (z : F) (S.root z) beta = 0 := by
    rw [hbeta]
    simp
  rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
    x₀ (x - x₀) u₀ u₁ (z : F) (S.root z)
    R hHyp hzeta DX k (Nat.le_of_lt hkDX)
    (P z) (hPdeg z)] at hpiz
  · simpa [sub_eq_add_neg, add_assoc] using hpiz
  · intro i hi
    exact hspecializes z i (hi.trans (Nat.le_of_lt hkDX))
  · intro i _hi
    exact (hNP z).hden i

/-- Finset form: every zero obstruction coordinate becomes a simultaneous
received-value core for the whole selected fibre. -/
theorem universal_selected_pair_commonCore_matches
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : ℕ) (hkDX : k < DX)
    (T : Finset F) (P : T → F[X])
    (S : UniversalSelectedHenselData x₀ R H hHyp hzeta
      D d k DX T P)
    (hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp (z : F)
      (S.root z) x₀ ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (Core : Finset F) (U₀ U₁ : F → F)
    (num : ℕ → F[X][Y]) (slope : F[X][Y]) (E : ℕ)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hs : Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) slope = HenselNumerators.zeta R x₀ H)
    (hnum : ∀ i, i ≤ k →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (num i) =
        finiteAlpha (R := R) (H := H) x₀ DX i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i)
    (hzero : ∀ x ∈ Core,
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H))
          (universalAffineObstruction num slope E k
            (x - x₀) (U₀ x) (U₁ x)) = 0) :
    ∀ z : T, ∀ x ∈ Core,
      (P z).eval x = U₀ x + (z : F) * U₁ x := by
  intro z x hx
  exact universal_selected_pair_owner_matches_of_obstruction_zero
    x₀ R hHyp hzeta D d k DX hkDX T P S hNP hPdeg
      x (U₀ x) (U₁ x) num slope E hE hs hnum (hzero x hx) z

/-- Once the dynamic obstruction core has been specialized back to owner
agreements, locator division leaves exactly the complementary number of
polynomial degrees.  This is the algebraic hand-off from the universal
selector to the quotient-incidence lane. -/
theorem exists_bounded_dynamicCoreQuotient_family
    (Core : Finset F) (U₀ U₁ : F → F)
    (k s : ℕ) (hcard : Core.card + s = k)
    (T : Finset F) (P : T → F[X])
    (hPdegree : ∀ z : T, (P z).natDegree ≤ k)
    (hcoreMatch : ∀ z : T, ∀ x ∈ Core,
      Polynomial.eval x (P z) = U₀ x + (z : F) * U₁ x) :
    ∃ B₀ B₁ : F[X], ∃ Q : T → F[X],
      B₀.natDegree ≤ k ∧ B₁.natDegree ≤ k ∧
      (∀ x ∈ Core, B₀.eval x = U₀ x) ∧
      (∀ x ∈ Core, B₁.eval x = U₁ x) ∧
      (∀ z : T, (Q z).natDegree ≤ s) ∧
      (∀ z : T,
        P z = B₀ + Polynomial.C (z : F) * B₁ +
          BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z) := by
  classical
  let B₀ : F[X] :=
    BCHKSFullCoreOwnerBridge6400.coreBasePolynomial Core U₀
  let B₁ : F[X] :=
    BCHKSFullCoreOwnerBridge6400.coreBasePolynomial Core U₁
  have hB₀degree : B₀.natDegree ≤ k :=
    BCHKSFullCoreOwnerBridge6400.coreBasePolynomial_natDegree_le
      Core U₀ k s hcard
  have hB₁degree : B₁.natDegree ≤ k :=
    BCHKSFullCoreOwnerBridge6400.coreBasePolynomial_natDegree_le
      Core U₁ k s hcard
  have hB₀eval : ∀ x ∈ Core, B₀.eval x = U₀ x := by
    intro x hx
    exact BCHKSFullCoreOwnerBridge6400.coreBasePolynomial_eval
      Core U₀ x hx
  have hB₁eval : ∀ x ∈ Core, B₁.eval x = U₁ x := by
    intro x hx
    exact BCHKSFullCoreOwnerBridge6400.coreBasePolynomial_eval
      Core U₁ x hx
  have hexists : ∀ z : T, ∃ q : F[X],
      q.natDegree ≤ s ∧
        P z = B₀ + Polynomial.C (z : F) * B₁ +
          BCHKSFullCoreLineArrangement6400.coreLocator Core * q := by
    intro z
    have hbaseDegree :
        (B₀ + Polynomial.C (z : F) * B₁).natDegree ≤ k :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le hB₀degree
          ((Polynomial.natDegree_C_mul_le (z : F) B₁).trans hB₁degree))
    have heval : ∀ x ∈ Core,
        (P z).eval x =
          (B₀ + Polynomial.C (z : F) * B₁).eval x := by
      intro x hx
      rw [hcoreMatch z x hx]
      simp [hB₀eval x hx, hB₁eval x hx]
    obtain ⟨q, hqdegree, hqshape⟩ :=
      BCHKSCoreVandermonde6400.exists_coreQuotient_natDegree_le
        Core (P z) (B₀ + Polynomial.C (z : F) * B₁)
          k s hcard (hPdegree z) hbaseDegree heval
    exact ⟨q, hqdegree, by simpa [add_assoc] using hqshape⟩
  choose Q hQdegree hQshape using hexists
  exact ⟨B₀, B₁, Q, hB₀degree, hB₁degree,
    hB₀eval, hB₁eval, hQdegree, hQshape⟩

/-! ## The algebraic first-stage hand-off

The next theorem joins the two previously separate consequences of a zero
universal-obstruction core.  The same interpolated base polynomials divide
both

* every specialized owner polynomial, over the ground field; and
* the canonical generic Hensel branch, over the function field.

Thus the recursive branch is not merely a numerical analogy: it has one
canonical generic quotient and the owner quotients are its specializations.
Division is by the mapped monic locator, so this step adds no denominator.
-/

theorem exists_dynamicCore_owner_and_canonical_quotients
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : ℕ) (hkDX : k < DX)
    (T : Finset F) (P : T → F[X])
    (S : UniversalSelectedHenselData x₀ R H hHyp hzeta
      D d k DX T P)
    (hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp (z : F)
      (S.root z) x₀ ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (Core : Finset F) (U₀ U₁ : F → F) (s : ℕ)
    (hcard : Core.card + s = k)
    (num : ℕ → F[X][Y]) (slope : F[X][Y]) (E : ℕ)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hslopeNum : Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) slope = HenselNumerators.zeta R x₀ H)
    (hnum : ∀ i, i ≤ k →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (num i) =
        finiteAlpha (R := R) (H := H) x₀ DX i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i)
    (hzero : ∀ x ∈ Core,
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H))
          (universalAffineObstruction num slope E k
            (x - x₀) (U₀ x) (U₁ x)) = 0) :
    ∃ B₀ B₁ : F[X], ∃ Q : T → F[X], ∃ gammaQ : (𝕃 H)[X],
      B₀.natDegree ≤ k ∧ B₁.natDegree ≤ k ∧
      (∀ x ∈ Core, B₀.eval x = U₀ x) ∧
      (∀ x ∈ Core, B₁.eval x = U₁ x) ∧
      (∀ z : T, (Q z).natDegree ≤ s) ∧
      (∀ z : T, P z = B₀ + Polynomial.C (z : F) * B₁ +
        BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z) ∧
      gammaQ.natDegree ≤ s ∧
      canonicalFunctionFieldGamma H x₀ R DX k =
        B₀.map (groundToFunctionField H) +
          Polynomial.C (liftToFunctionField (H := H) Polynomial.X) *
            B₁.map (groundToFunctionField H) +
          (BCHKSFullCoreLineArrangement6400.coreLocator Core).map
              (groundToFunctionField H) * gammaQ := by
  have hcoreMatch : ∀ z : T, ∀ x ∈ Core,
      (P z).eval x = U₀ x + (z : F) * U₁ x :=
    universal_selected_pair_commonCore_matches
      x₀ R hHyp hzeta D d k DX hkDX T P S hNP hPdeg
        Core U₀ U₁ num slope E hE hslopeNum hnum hzero
  obtain ⟨B₀, B₁, Q, hB₀, hB₁, hB₀eval, hB₁eval,
      hQdegree, hQshape⟩ :=
    exists_bounded_dynamicCoreQuotient_family
      Core U₀ U₁ k s hcard T P hPdeg hcoreMatch
  have hgammaEval : ∀ x ∈ Core,
      (canonicalFunctionFieldGamma H x₀ R DX k).eval
          (fieldTo𝕃 (H := H) x) =
        fieldTo𝕃 (H := H) (U₀ x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (U₁ x) := by
    intro x hx
    exact gamma_eval_eq_affine_of_universalAffineObstruction_eq_zero
      x₀ x (U₀ x) (U₁ x) R hHyp hzeta DX k
        (Nat.le_of_lt hkDX) num slope E hE hslopeNum hnum (hzero x hx)
  obtain ⟨gammaQ, hgammaQdegree, hgammaShape⟩ :=
    BCHKSCanonicalGammaCoreQuotient6400.exists_canonicalGamma_coreQuotient_of_core_evaluations
        x₀ R DX k s Core hcard U₀ U₁ B₀ B₁ hB₀ hB₁
          hB₀eval hB₁eval hgammaEval
  exact ⟨B₀, B₁, Q, gammaQ, hB₀, hB₁, hB₀eval, hB₁eval,
    hQdegree, hQshape, hgammaQdegree, hgammaShape⟩

/-! ## The fresh quotient received word

Outside the extracted core, its locator is nonzero.  Consequently every
remaining agreement of an owner descends, by literal cancellation, to an
agreement of its quotient with another affine received word.  This is the
exact semantic bridge needed to run a fresh interpolation/list-recovery
instance on the complement; no probabilistic or generic-specialization
assumption is involved here.
-/

noncomputable def quotientReceived0
    (Core : Finset F) (B₀ : F[X]) (U₀ : F → F) (x : F) : F :=
  (U₀ x - B₀.eval x) /
    (BCHKSFullCoreLineArrangement6400.coreLocator Core).eval x

noncomputable def quotientReceived1
    (Core : Finset F) (B₁ : F[X]) (U₁ : F → F) (x : F) : F :=
  (U₁ x - B₁.eval x) /
    (BCHKSFullCoreLineArrangement6400.coreLocator Core).eval x

theorem dynamicCoreQuotient_eval_eq_affine_of_owner_match
    (Core : Finset F) (B₀ B₁ P Q : F[X]) (U₀ U₁ : F → F)
    (z x : F) (hx : x ∉ Core)
    (hshape : P = B₀ + Polynomial.C z * B₁ +
      BCHKSFullCoreLineArrangement6400.coreLocator Core * Q)
    (hmatch : P.eval x = U₀ x + z * U₁ x) :
    Q.eval x = quotientReceived0 Core B₀ U₀ x +
      z * quotientReceived1 Core B₁ U₁ x := by
  have hGx :
      (BCHKSFullCoreLineArrangement6400.coreLocator Core).eval x ≠ 0 :=
    BCHKSFullCoreLineArrangement6400.coreLocator_eval_ne_zero_of_not_mem
      Core x hx
  have hshapeEval := congrArg (Polynomial.eval x) hshape
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      at hshapeEval
  rw [hmatch] at hshapeEval
  dsimp [quotientReceived0, quotientReceived1]
  field_simp
  linear_combination -1 * hshapeEval

/-- Finset-family form of the same bridge.  The original agreement rows may
be arbitrary; restricting them to the complement produces quotient rows of
the same cardinality after the common-core coordinates are removed. -/
theorem dynamicCoreQuotient_family_matches_on_complement
    (Core : Finset F) (B₀ B₁ : F[X]) (U₀ U₁ : F → F)
    (T : Finset F) (P Q : T → F[X])
    (Arow : T → Finset F)
    (hshape : ∀ z : T, P z = B₀ + Polynomial.C (z : F) * B₁ +
      BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z)
    (hmatch : ∀ z : T, ∀ x ∈ Arow z,
      (P z).eval x = U₀ x + (z : F) * U₁ x) :
    ∀ z : T, ∀ x ∈ Arow z \ Core,
      (Q z).eval x = quotientReceived0 Core B₀ U₀ x +
        (z : F) * quotientReceived1 Core B₁ U₁ x := by
  intro z x hx
  have hx' := Finset.mem_sdiff.mp hx
  exact dynamicCoreQuotient_eval_eq_affine_of_owner_match
    Core B₀ B₁ (P z) (Q z) U₀ U₁ (z : F) x hx'.2
      (hshape z) (hmatch z x hx'.1)

/-- Concrete fresh-GS hand-off at the audited `q = 20230` schedule.  Once an
embedding enumerating the complement and the inherited agreement rows are
supplied, the quotient affine-word identity above feeds directly into the
compiled `m=28` interpolant.  In particular, interpolation existence,
nonzeroness, support caps, and substitution vanishing are conclusions, not
hypotheses. -/
theorem exists_freshQuotient_interpolant_of_dynamicCore6400
    (Core : Finset F) (B₀ B₁ : F[X]) (U₀ U₁ : F → F)
    (omega : Fin 241914 ↪ F) (houtside : ∀ i, omega i ∉ Core)
    (T : Finset F) (P Q : T → F[X])
    (Arow : T → Finset (Fin 241914))
    (hQdegree : ∀ z : T, (Q z).natDegree ≤ 110841)
    (hrow : ∀ z : T, 165134 ≤ (Arow z).card)
    (hshape : ∀ z : T,
      P z = B₀ + Polynomial.C (z : F) * B₁ +
        BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z)
    (hmatch : ∀ z : T, ∀ i ∈ Arow z,
      (P z).eval (omega i) = U₀ (omega i) +
        (z : F) * U₁ (omega i)) :
    ∃ Qfresh : Polynomial (Polynomial (Polynomial F)),
      Qfresh ≠ 0 ∧
      (∀ z : T,
        BCHKSSubstitutionVanish.triEval Qfresh (z : F) (Q z) = 0) ∧
      (∀ j a, (Qfresh.coeff j).coeff a ≠ 0 →
        j < 42 ∧ a + 110841 * j < 4623752 ∧
          ((Qfresh.coeff j).coeff a).natDegree + j < 836) := by
  let u₀q : Fin 241914 → F := fun i ↦
    quotientReceived0 Core B₀ U₀ (omega i)
  let u₁q : Fin 241914 → F := fun i ↦
    quotientReceived1 Core B₁ U₁ (omega i)
  apply BCHKSFreshQuotientInterpolation6400.exists_freshQuotient_interpolant_vanishing6400
      omega u₀q u₁q T Q Arow hQdegree hrow
  intro z i hi
  exact dynamicCoreQuotient_eval_eq_affine_of_owner_match
    Core B₀ B₁ (P z) (Q z) U₀ U₁ (z : F) (omega i)
      (houtside i) (hshape z) (hmatch z i hi)

/-! ## Choice-free transport of the selected inner factor

The first selector has already paid to choose `H`.  Re-factoring the
core-transformed fibre would lose that work and introduce a second pair
pigeonhole.  Instead the affine image `H'` below is explicit.  The compiled
transport theorem proves irreducibility, divisibility, the complete Hensel
hypotheses, and all three owner-local predicates without deleting any new
challenge values.
-/

theorem dynamicCore_transportedInnerFactor_setup
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (D d k DX : ℕ) (T : Finset F) (P : T → F[X])
    {hzeta : HenselNumerators.zeta R x₀ H ≠ 0}
    (S : UniversalSelectedHenselData x₀ R H hHyp hzeta
      D d k DX T P)
    (Core : Finset F) (B₀ B₁ : F[X]) (Q : T → F[X])
    (hshape : ∀ z : T,
      P z = B₀ + Polynomial.C (z : F) * B₁ +
        BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z)
    (hHroot : ∀ z : T, biEval H ((P z).eval x₀) (z : F) = 0)
    (hprimitive : (triSpecializeX R x₀).IsPrimitive)
    (hGx : (BCHKSFullCoreLineArrangement6400.coreLocator Core).eval x₀ ≠ 0) :
    let G := BCHKSFullCoreLineArrangement6400.coreLocator Core
    let H' := BCHKSExplicitCoreInnerTransport6400.transportedInnerFactor
      H B₀ B₁ G x₀
    Irreducible H' ∧ 0 < H'.natDegree ∧
      H' ∣ triSpecializeX
        (BCHKSCoreQuotientHenselAudit6400.coreRootTransform R B₀ B₁ G) x₀ ∧
      HenselNumerators.Hypotheses x₀
        (BCHKSCoreQuotientHenselAudit6400.coreRootTransform R B₀ B₁ G) H' ∧
      ∀ z : T,
        biEval H' ((Q z).eval x₀) (z : F) = 0 ∧
        H'.leadingCoeff.eval (z : F) ≠ 0 ∧
        FiniteHensel.IsSimpleRootAt
          (triSpecializeZ
            (BCHKSCoreQuotientHenselAudit6400.coreRootTransform R B₀ B₁ G)
            (z : F)) x₀ ((Q z).eval x₀) := by
  dsimp only
  let G := BCHKSFullCoreLineArrangement6400.coreLocator Core
  let H' := BCHKSExplicitCoreInnerTransport6400.transportedInnerFactor
    H B₀ B₁ G x₀
  have hHdvd : H ∣ triSpecializeX R x₀ := by
    simpa [triSpecializeX, Polynomial.Bivariate.evalX_eq_map] using
      hHyp.dvd_evalX
  have hsetup :=
    BCHKSExplicitCoreInnerTransport6400.transportedInnerFactor_henselSetup
      R H B₀ B₁ G x₀ Fact.out Fact.out hHdvd hprimitive hGx
  refine ⟨hsetup.1, hsetup.2.1, hsetup.2.2.1, hsetup.2.2.2, ?_⟩
  intro z
  exact BCHKSExplicitCoreInnerTransport6400.transported_owner_predicates
    R H B₀ B₁ G (P z) (Q z) x₀ (z : F) hGx
      (hshape z) (hHroot z) (S.hW z) (S.hsimple z)

end BCHKSDynamicCoreSelector6400
end ProximityPrize.SubmissionLower
