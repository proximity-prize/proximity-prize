import ProximityPrize.SubmissionLower.BCHKSFreshQuotientUniversalSelector6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSFreshQuotientChain6400
open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open BCHKSDynamicCoreSelector6400
open BCHKSFreshQuotientUniversalSelector6400
open UniversalNumerator
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
abbrev F := IRSProfile.Field
theorem exists_concrete_fresh_selected_pair_of_dynamicCore_family
    (Core : Finset F) (B₀ B₁ : F[X]) (U₀ U₁ : F → F)
    (omega : Fin 241914 ↪ F) (houtside : ∀ i, omega i ∉ Core)
    (T : Finset F) (P Q : T → F[X])
    (Arow : T → Finset (Fin 241914))
    (hTcard : freshSelectorThreshold < T.card)
    (hQdegree : ∀ z : T, (Q z).natDegree ≤ freshRootCap)
    (hrow : ∀ z : T, freshAgreement ≤ (Arow z).card)
    (hshape : ∀ z : T,
      P z = B₀ + Polynomial.C (z : F) * B₁ +
        BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z)
    (hmatch : ∀ z : T, ∀ i ∈ Arow z,
      (P z).eval (omega i) = U₀ (omega i) +
        (z : F) * U₁ (omega i)) :
    ∃ Qfresh : F[X][X][Y], ∃ x₁ : F,
      ∃ RH : BCHKSFreshQuotientUniversalSelector6400.Pair,
      ∃ T₁ : Finset F, ∃ Coord : Finset (Fin 241914),
      Qfresh ≠ 0 ∧
      (∀ z : T, triEval Qfresh (z : F) (Q z) = 0) ∧
      BCHKSFreshQuotientUniversalSelector6400.SupportCaps Qfresh ∧
      RH ∈ UniversalOuterCover6399.pairs Qfresh x₁ ∧
      ((triSpecializeX RH.1 x₁).IsPrimitive ∧
        Polynomial.eval (Polynomial.C x₁)
          (factorXObstruction RH.1) ≠ 0 ∧
        triSpecializeX RH.1 x₁ ≠ 0 ∧
        (triSpecializeX RH.1 x₁).natDegree = RH.1.natDegree ∧
        Polynomial.eval (Polynomial.C x₁)
          (rawSepResultant RH.1) ≠ 0) ∧
      T₁ ⊆ T ∧
      freshErrors + 1 < T₁.card ∧
      freshRootCap + 1 ≤ Coord.card ∧
      (∀ z ∈ T₁,
        UniversalOuterCover6399.pairRel
          (fun w ↦ if hw : w ∈ T then Q ⟨w, hw⟩ else 0)
          x₁ z RH) ∧
      (∀ i ∈ Coord, RH.2 ∣
        concreteUniversalAffineObstruction x₁ RH.1
          freshExponent freshRootCap (omega i - x₁)
          (quotientReceived0 Core B₀ U₀ (omega i))
          (quotientReceived1 Core B₁ U₁ (omega i))) := by
  classical
  let u₀q : Fin 241914 → F := fun i ↦
    quotientReceived0 Core B₀ U₀ (omega i)
  let u₁q : Fin 241914 → F := fun i ↦
    quotientReceived1 Core B₁ U₁ (omega i)
  let AE : F → Finset (Fin 241914) := fun z ↦
    if hz : z ∈ T then Arow ⟨z, hz⟩ else ∅
  obtain ⟨Qfresh, hQfresh, hQeval, hcaps⟩ :=
    exists_freshQuotient_interpolant_of_dynamicCore6400
      Core B₀ B₁ U₀ U₁ omega houtside T P Q Arow
        hQdegree hrow hshape hmatch
  have hAcard : ∀ z : T, freshAgreement ≤ (AE z).card := by
    intro z
    simpa [AE, z.property] using hrow z
  have hagree : ∀ z : T, ∀ i ∈ AE z,
      (Q z).eval (omega i) = u₀q i + (z : F) * u₁q i := by
    intro z i hi
    have hi' : i ∈ Arow z := by simpa [AE, z.property] using hi
    exact dynamicCoreQuotient_eval_eq_affine_of_owner_match
      Core B₀ B₁ (P z) (Q z) U₀ U₁ (z : F) (omega i)
        (houtside i) (hshape z) (hmatch z i hi')
  obtain ⟨x₁, RH, T₁, Coord, hRH, hx, hTsub, hT₁card,
      hCoord, hrel, hdiv⟩ :=
    exists_concrete_fresh_selected_pair
      omega u₀q u₁q T AE Q Qfresh hTcard hQfresh
        hQdegree hAcard hagree hQeval hcaps
  exact ⟨Qfresh, x₁, RH, T₁, Coord, hQfresh, hQeval, hcaps,
    hRH, hx, hTsub, hT₁card, hCoord, hrel,
    by simpa [u₀q, u₁q] using hdiv⟩
theorem exists_concrete_fresh_selected_pair_of_zeroCore
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX : Nat) (hkDX : k < DX)
    (T : Finset F) (P : T → F[X])
    (Sel : UniversalSelectedHenselData x₀ R H hHyp hzeta
      D d k DX T P)
    (hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp (z : F)
      (Sel.root z) x₀ ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (Core : Finset F) (U₀ U₁ : F → F) (s : Nat)
    (hcard : Core.card + s = k) (hs : s = freshRootCap)
    (num : Nat → F[X][Y]) (slope : F[X][Y]) (E : Nat)
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
            (x - x₀) (U₀ x) (U₁ x)) = 0)
    (omega : Fin 241914 ↪ F) (houtside : ∀ i, omega i ∉ Core)
    (Arow : T → Finset (Fin 241914))
    (hTcard : freshSelectorThreshold < T.card)
    (hrow : ∀ z : T, freshAgreement ≤ (Arow z).card)
    (hmatch : ∀ z : T, ∀ i ∈ Arow z,
      (P z).eval (omega i) = U₀ (omega i) +
        (z : F) * U₁ (omega i)) :
    ∃ B₀ B₁ : F[X], ∃ Q : T → F[X], ∃ gammaQ : (𝕃 H)[X],
      B₀.natDegree ≤ k ∧ B₁.natDegree ≤ k ∧
      (∀ z : T, (Q z).natDegree ≤ freshRootCap) ∧
      (∀ z : T, P z = B₀ + Polynomial.C (z : F) * B₁ +
        BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z) ∧
      gammaQ.natDegree ≤ freshRootCap ∧
      canonicalFunctionFieldGamma H x₀ R DX k =
        B₀.map (groundToFunctionField H) +
          Polynomial.C (liftToFunctionField (H := H) Polynomial.X) *
            B₁.map (groundToFunctionField H) +
          (BCHKSFullCoreLineArrangement6400.coreLocator Core).map
              (groundToFunctionField H) * gammaQ ∧
      ∃ Qfresh : F[X][X][Y], ∃ x₁ : F,
        ∃ RH : BCHKSFreshQuotientUniversalSelector6400.Pair,
        ∃ T₁ : Finset F, ∃ Coord : Finset (Fin 241914),
        Qfresh ≠ 0 ∧
        (∀ z : T, triEval Qfresh (z : F) (Q z) = 0) ∧
        BCHKSFreshQuotientUniversalSelector6400.SupportCaps Qfresh ∧
        RH ∈ UniversalOuterCover6399.pairs Qfresh x₁ ∧
        ((triSpecializeX RH.1 x₁).IsPrimitive ∧
          Polynomial.eval (Polynomial.C x₁)
            (factorXObstruction RH.1) ≠ 0 ∧
          triSpecializeX RH.1 x₁ ≠ 0 ∧
          (triSpecializeX RH.1 x₁).natDegree = RH.1.natDegree ∧
          Polynomial.eval (Polynomial.C x₁)
            (rawSepResultant RH.1) ≠ 0) ∧
        T₁ ⊆ T ∧ freshErrors + 1 < T₁.card ∧
        freshRootCap + 1 ≤ Coord.card ∧
        (∀ z ∈ T₁,
          UniversalOuterCover6399.pairRel
            (fun w ↦ if hw : w ∈ T then Q ⟨w, hw⟩ else 0)
            x₁ z RH) ∧
        (∀ i ∈ Coord, RH.2 ∣
          concreteUniversalAffineObstruction x₁ RH.1
            freshExponent freshRootCap (omega i - x₁)
            (quotientReceived0 Core B₀ U₀ (omega i))
            (quotientReceived1 Core B₁ U₁ (omega i))) := by
  obtain ⟨B₀, B₁, Q, gammaQ, hB₀, hB₁, hB₀eval, hB₁eval,
      hQdegree, hQshape, hgammaDegree, hgammaShape⟩ :=
    exists_dynamicCore_owner_and_canonical_quotients
      x₀ R hHyp hzeta D d k DX hkDX T P Sel hNP hPdeg
        Core U₀ U₁ s hcard num slope E hE hslopeNum hnum hzero
  have hQdegreeFresh : ∀ z : T, (Q z).natDegree ≤ freshRootCap := by
    intro z
    simpa [hs] using hQdegree z
  have hgammaDegreeFresh : gammaQ.natDegree ≤ freshRootCap := by
    simpa [hs] using hgammaDegree
  obtain ⟨Qfresh, x₁, RH, T₁, Coord, hQfresh, hQeval, hcaps,
      hRH, hx, hTsub, hT₁card, hCoord, hrel, hdiv⟩ :=
    exists_concrete_fresh_selected_pair_of_dynamicCore_family
      Core B₀ B₁ U₀ U₁ omega houtside T P Q Arow
        hTcard hQdegreeFresh hrow hQshape hmatch
  exact ⟨B₀, B₁, Q, gammaQ, hB₀, hB₁, hQdegreeFresh, hQshape,
    hgammaDegreeFresh, hgammaShape, Qfresh, x₁, RH, T₁, Coord,
    hQfresh, hQeval, hcaps, hRH, hx, hTsub, hT₁card, hCoord, hrel,
    hdiv⟩
end BCHKSFreshQuotientChain6400
end ProximityPrize.SubmissionLower
