import ProximityPrize.SubmissionLower.BCHKSFreshQuotientChain6400
import ProximityPrize.SubmissionLower.BCHKSExplicitPairAlignment6400
import ProximityPrize.SubmissionLower.BCHKSDynamicCoreArithmetic6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSFreshQuotientFirstStage6400

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open BCHKSDynamicCoreSelector6400
open BCHKSDynamicCoreArithmetic6400
open BCHKSExplicitMixedInnerPairs6400
open BCHKSExplicitPairAlignment6400
open BCHKSFreshQuotientUniversalSelector6400
open BCHKSFreshQuotientChain6400
open UniversalNumerator

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000

/-!
The first dynamic selector and the fresh quotient selector use the same
selected owner fibre.  Charging `freshSelectorThreshold` as the first
selector's owner cap has two consequences at once:

* enough owners remain to run the complete fresh selector; and
* the first row/column count can stop at the `20230`-coordinate core.

This file packages that hand-off without changing the global solution.
-/

theorem selectedExplicitPairFiber_freshSelectorThreshold_lt_card
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq A]
    {G : GlobalSelectorData F A}
    (W : SelectedExplicitPairFiber G)
    (herrors : G.errors = freshSelectorThreshold) :
    freshSelectorThreshold < W.fiber.card := by
  have hcap := W.common_capacity
  rw [herrors] at hcap
  exact ((Nat.lt_succ_self freshSelectorThreshold).trans_le
    (Nat.le_add_left (freshSelectorThreshold + 1) _)).trans hcap

/-- Global-selector form of the same strict threshold.  No second
pigeonhole is used: this is the fibre already returned by the first pair
selection. -/
theorem GlobalSelectorData.exists_selectedFiber_above_freshThreshold
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq A]
    (G : GlobalSelectorData F A)
    (herrors : G.errors = freshSelectorThreshold) :
    ∃ W : SelectedExplicitPairFiber G,
      freshSelectorThreshold < W.fiber.card := by
  let W := Classical.choice G.exists_selectedExplicitPairFiber
  exact ⟨W,
    selectedExplicitPairFiber_freshSelectorThreshold_lt_card W herrors⟩

/-! ## Coordinate data for a dynamic core below the root degree -/

/-- Coordinate/agreement data needed by the first dynamic-core extraction.

This is intentionally weaker than `GlobalAlignmentData`: ordinary affine
alignment stops at the full stored-root degree and therefore includes the
condition `rootDegreeCap ≤ commonTarget`.  A dynamic core stops strictly
earlier (`20230 < 131071`), so importing that condition here would make the
benchmark instance contradictory. -/
structure DynamicCoreCoordinateData
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq A]
    {G : GlobalSelectorData F A} (W : SelectedExplicitPairFiber G)
    (I : Type) [Fintype I]
    [DecidableEq I] where
  coords : Finset I
  domain : I ↪ F
  lift : AffineRootLift (G.tag W.pair.1)
  agreementRows : F → Finset I
  received0 : I → F
  received1 : I → F
  rowLower : Nat
  row_large : ∀ z ∈ W.fiber, rowLower ≤
    (coords.attach.filter fun i : coords ↦
      (i : I) ∈ agreementRows z).card
  support_cap : 0 < (G.data W.pair.1).supportCap
  locator_nonzero : ∀ i ∈ coords,
    lift.locator.eval (domain i) ≠ 0
  original_agrees : ∀ z ∈ W.fiber, ∀ i ∈ agreementRows (z : F),
      (lift.originalRoot (z : F)).eval (domain i) =
        received0 i + z * received1 i

/-! ## Enumerating the complement of an exact dynamic core -/

/-- An exact `20230`-subset of a `262144`-coordinate universe has a
canonical (noncomputable) `Fin 241914` enumeration.  Agreement rows lose at
most the removed `20230` positions, so `185364` agreements leave `165134`.
The returned index map records the link back to the original coordinates. -/
theorem exists_freshComplement_enumeration_of_gaps
    {I F Challenge : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq Challenge]
    (coords : Finset I) (CoreIdx : Finset coords)
    (hOutsideCard : coords.card - CoreIdx.card = 241914)
    (rowLower : Nat) (hrowGap : 165134 + CoreIdx.card <= rowLower)
    (domain : I ↪ F)
    (T : Finset Challenge) (Arow : Challenge -> Finset I)
    (hrow : ∀ z ∈ T, rowLower <=
      (coords.attach.filter fun i : coords => (i : I) ∈ Arow z).card) :
    ∃ idx : Fin 241914 ↪ coords, ∃ omega : Fin 241914 ↪ F,
      ∃ FreshRow : Challenge -> Finset (Fin 241914),
        (∀ j, idx j ∉ CoreIdx) ∧
        (∀ j, omega j = domain (idx j : I)) ∧
        (∀ z ∈ T, 165134 <= (FreshRow z).card) ∧
        (∀ z ∈ T, ∀ j ∈ FreshRow z, (idx j : I) ∈ Arow z) := by
  classical
  let Outside : Finset coords := Finset.univ \ CoreIdx
  have hOutside : Outside.card = 241914 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ CoreIdx)]
    simp only [Finset.card_univ, Fintype.card_coe]
    exact hOutsideCard
  let e : Fin 241914 ≃ Outside :=
    (Finset.equivFinOfCardEq hOutside).symm
  let idx : Fin 241914 ↪ coords := {
    toFun := fun j => (e j : Outside)
    inj' := by
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact hij
  }
  let omega : Fin 241914 ↪ F := {
    toFun := fun j => domain (idx j : I)
    inj' := fun _ _ h => idx.injective (Subtype.ext (domain.injective h))
  }
  let rowU : Challenge -> Finset coords := fun z =>
    coords.attach.filter fun i : coords => (i : I) ∈ Arow z
  let rowOutside : Challenge -> Finset coords := fun z => rowU z \ CoreIdx
  let FreshRow : Challenge -> Finset (Fin 241914) := fun z =>
    (rowOutside z).attach.image fun i =>
      Finset.equivFinOfCardEq hOutside
        ⟨i.1, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ i.1, (Finset.mem_sdiff.mp i.2).2⟩⟩
  have hidxOutside : ∀ j, idx j ∉ CoreIdx := by
    intro j
    have hj := (e j).property
    exact (Finset.mem_sdiff.mp hj).2
  have hFreshCard : ∀ z, (FreshRow z).card = (rowOutside z).card := by
    intro z
    change ((rowOutside z).attach.image _).card = (rowOutside z).card
    calc
      ((rowOutside z).attach.image _).card = (rowOutside z).attach.card :=
        Finset.card_image_iff.mpr (by
          intro a ha b hb hab
          have heq := (Finset.equivFinOfCardEq hOutside).injective hab
          exact Subtype.ext
            (congrArg (fun x : Outside => (x : coords)) heq))
      _ = (rowOutside z).card := by simp
  have hFreshRow : ∀ z, ∀ j ∈ FreshRow z, (idx j : I) ∈ Arow z := by
    intro z j hj
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
    have hirow : i.1 ∈ rowU z := (Finset.mem_sdiff.mp i.2).1
    have hieval : (idx j : I) = (i.1 : I) := by
      have heq := congrArg
        (fun t : Fin 241914 => (e t : Outside).1.1) hij.symm
      simpa [idx, e] using heq
    rw [hieval]
    exact (Finset.mem_filter.mp hirow).2
  refine ⟨idx, omega, FreshRow, hidxOutside, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro z hz
    rw [hFreshCard]
    have hloss : (rowU z).card ≤
        (rowU z \ CoreIdx).card + CoreIdx.card :=
      Finset.card_le_card_sdiff_add_card
    have hr := hrow z hz
    change (rowU z).card ≤ (rowOutside z).card + CoreIdx.card at hloss
    change rowLower ≤ (rowU z).card at hr
    omega
  · intro z hz
    exact hFreshRow z

/-- Benchmark specialization of the gap-form complement enumeration. -/
theorem exists_freshComplement_enumeration
    {I F Challenge : Type} [Fintype I] [DecidableEq I]
    [Field F] [DecidableEq Challenge]
    (coords : Finset I) (hcoords : coords.card = 262144)
    (CoreIdx : Finset coords) (hcore : CoreIdx.card = 20230)
    (domain : I ↪ F)
    (T : Finset Challenge) (Arow : Challenge -> Finset I)
    (hrow : ∀ z ∈ T, 185364 <=
      (coords.attach.filter fun i : coords => (i : I) ∈ Arow z).card) :
    ∃ idx : Fin 241914 ↪ coords, ∃ omega : Fin 241914 ↪ F,
      ∃ FreshRow : Challenge -> Finset (Fin 241914),
        (∀ j, idx j ∉ CoreIdx) ∧
        (∀ j, omega j = domain (idx j : I)) ∧
        (∀ z ∈ T, 165134 <= (FreshRow z).card) ∧
        (∀ z ∈ T, ∀ j ∈ FreshRow z, (idx j : I) ∈ Arow z) := by
  apply exists_freshComplement_enumeration_of_gaps
    coords CoreIdx (rowLower := 185364) (domain := domain)
      (T := T) (Arow := Arow)
  · omega
  · omega
  · exact hrow

/-! ## The selected first pair produces the exact zero core -/

/-- The first selected explicit pair is stopped at target `20230`.  Its
capacity was charged with the whole fresh-selector threshold, so the same
fibre both yields an exact zero-obstruction core and remains large enough
for the second selector. -/
theorem SelectedExplicitPairFiber.exists_zeroCoreUpTo20230
    {F I A : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I] [DecidableEq A]
    {G : GlobalSelectorData F A}
    (W : SelectedExplicitPairFiber G)
    [Fact (Irreducible (G.data W.pair.1).inner)]
    [Fact (0 < (G.data W.pair.1).inner.natDegree)]
    (C : DynamicCoreCoordinateData W I)
    (hcoordinateCount : G.coordinateCount = 262144)
    (hrowLower : G.rowLower = 185364)
    (hcommonTarget : G.commonTarget = 20230)
    (herrors : G.errors = freshSelectorThreshold)
    (q : Nat)
    (hcoordinateGap : C.coords.card - q = 241914)
    (hactualRowGap : C.rowLower - q = 165134)
    (hrootCapPos : 0 < (G.tag W.pair.1).rootDegreeCap) :
    let a := W.pair.1
    let tag := G.tag a
    let D := G.data a
    let L := C.lift
    let E := FiniteHenselWeight.denominatorExponent tag.rootDegreeCap
    ∃ CoreIdx : Finset C.coords, ∃ Core : Finset F,
      ∃ U0 U1 : F -> F,
        CoreIdx.card = q ∧
        Core = CoreIdx.image (fun i : C.coords => C.domain (i : I)) ∧
        Core.card = q ∧
        freshSelectorThreshold < W.fiber.card ∧
        (∀ i : I,
          U0 (C.domain i) = L.quotientReceived0 C.domain C.received0 i ∧
          U1 (C.domain i) = L.quotientReceived1 C.domain C.received1 i) ∧
        ∀ x ∈ Core,
          Polynomial.eval₂ (liftToFunctionField (H := D.inner))
            (initialValue (H := D.inner))
              (universalAffineObstruction
                (universalRootedNumerators tag.center tag.transformed)
                (universalSlope tag.center tag.transformed) E
                tag.rootDegreeCap (x - tag.center) (U0 x) (U1 x)) = 0 := by
  classical
  dsimp only
  let a := W.pair.1
  let tag := G.tag a
  let D := G.data a
  let L := C.lift
  let qu0 : I -> F := fun i =>
    L.quotientReceived0 C.domain C.received0 i
  let qu1 : I -> F := fun i =>
    L.quotientReceived1 C.domain C.received1 i
  let E := FiniteHenselWeight.denominatorExponent tag.rootDegreeCap
  let cap := ExplicitInnerData.resultantCapacity D E
  let B : I -> F[X][Y] := fun i =>
    concreteUniversalAffineObstruction tag.center tag.transformed
      E tag.rootDegreeCap (C.domain i - tag.center) (qu0 i) (qu1 i)
  let Res : I -> F[X] := fun i =>
    Polynomial.resultant (B i) D.inner (B i).natDegree D.inner.natDegree
  have ha : a ∈ G.outer := by
    simpa only [a] using
      explicitInnerPairs_fst_mem G.outer G.tag G.data W.pair W.pair_mem
  have hrootCapPos' : 0 < tag.rootDegreeCap := by
    simpa only [tag, a] using hrootCapPos
  have hsupportPos : 0 < D.supportCap := by
    simpa only [D, a] using C.support_cap
  have hpairEq : W.pair = (a, D.inner) := by
    apply Prod.ext
    · rfl
    · simpa only [a, D] using
        explicitInnerPairs_snd_eq G.outer G.tag G.data W.pair W.pair_mem
  have hcapEq :
      explicitPairResultantCapacity G.tag G.data G.exponent
          (a, D.inner) = cap := by
    dsimp only [cap]
    unfold explicitPairResultantCapacity
    unfold BCHKSExplicitPairAlignment6400.ExplicitInnerData.resultantCapacity
    rw [G.exponent_eq]
  have hcapacity :
      ((C.coords.card - q) * cap) / (C.rowLower - q) +
          (freshSelectorThreshold + 1) < W.fiber.card := by
    have hW := W.common_capacity
    rw [hpairEq, hcapEq] at hW
    rw [hcoordinateCount, hcommonTarget, hrowLower, herrors] at hW
    rw [hcoordinateGap, hactualRowGap]
    norm_num at hW ⊢
    exact hW
  have hscaled :
      (C.coords.card - q) * cap <
          (C.rowLower - q) * W.fiber.card ∧
        freshSelectorThreshold + 1 < W.fiber.card := by
    apply scaled_pair_capacity_implies_incidence
      (C.coords.card - q) (C.rowLower - q) cap
        freshSelectorThreshold W.fiber.card
    · omega
    · exact hcapacity
  have hrow : ∀ z ∈ W.fiber, C.rowLower <=
      (C.coords.attach.filter fun i : C.coords =>
        (i : I) ∈ C.agreementRows z).card := by
    intro z hz
    exact C.row_large z hz
  have hagree : ∀ z ∈ W.fiber, ∀ i ∈ C.coords,
      i ∈ C.agreementRows z ->
      (tag.root z).eval (C.domain i) = qu0 i + z * qu1 i := by
    intro z hz i hiC hirow
    exact L.storedRoot_agree_of_original
      C.domain C.received0 C.received1 z i (W.owns z hz)
      (C.locator_nonzero i hiC)
      (C.original_agrees z hz i hirow)
  have hResdegree : ∀ i ∈ C.coords, (Res i).natDegree <= cap := by
    intro i hi
    simpa [Res, B, cap, E] using
      BCHKSExplicitPairAlignment6400.ExplicitInnerData.concrete_resultant_natDegree_le
        D hrootCapPos' hsupportPos (C.domain i - tag.center) (qu0 i) (qu1 i)
  have hBroot : ∀ i ∈ C.coords, ∀ z ∈ W.fiber,
      i ∈ C.agreementRows z ->
      biEval (B i) ((tag.root z).eval tag.center) z = 0 := by
    intro i hi z hz hirow
    apply biEval_concreteUniversalAffineObstruction_eq_zero
      tag.center z ((tag.root z).eval tag.center)
      tag.transformed (tag.root z) E tag.rootDegreeCap
      (C.domain i - tag.center) (qu0 i) (qu1 i)
    · rfl
    · have hsourcePos : 0 < tag.source.natDegree :=
        D.inner_degree_pos.trans_le
          ((Polynomial.natDegree_le_of_dvd D.inner_dvd
            tag.primitive.ne_zero).trans tag.specializeDegree_le_source)
      rw [tag.outerDegree_preserved]
      exact hsourcePos
    · rfl
    · exact tag.root_degree_le z (W.owns z hz)
    · simpa [triEval_eq_eval_triSpecializeZ] using
        tag.exact_root z (W.owns z hz)
    · exact (tag.simple_root z (W.owns z hz)).2
    · rw [show tag.center + (C.domain i - tag.center) = C.domain i by ring]
      exact hagree z hz i hi hirow
  have hResroot : ∀ i ∈ C.coords, ∀ z ∈ W.fiber,
      i ∈ C.agreementRows z -> (Res i).eval z = 0 := by
    intro i hi z hz hirow
    have hsize : 0 < (B i).natDegree + D.inner.natDegree :=
      Nat.add_pos_right _ D.inner_degree_pos
    exact bivariate_resultant_eval_eq_zero_of_common_root
      (B i) D.inner (B i).natDegree D.inner.natDegree z
      ((tag.root z).eval tag.center)
      Polynomial.natDegree_map_le Polynomial.natDegree_map_le hsize
      (hBroot i hi z hz hirow) (D.owner_root z (W.owns z hz))
  obtain ⟨Coord, hCoordCard, hReszero⟩ :=
    exists_zero_obstruction_core_in_ambient
      C.coords W.fiber C.agreementRows C.rowLower q cap Res
      (by omega) hrow hscaled.1 hResdegree hResroot
  have hqCoord : q <= Coord.card := by omega
  obtain ⟨CoreIdx, hCoreCoord, hCoreIdxCard⟩ :=
    Finset.exists_subset_card_eq hqCoord
  let embedCoord : C.coords -> F := fun i => C.domain (i : I)
  let Core : Finset F := CoreIdx.image embedCoord
  have hCoreCard : Core.card = q := by
    rw [show Core.card = CoreIdx.card by
      exact Finset.card_image_of_injOn (fun _ _ _ _ h =>
        Subtype.ext (C.domain.injective h))]
    exact hCoreIdxCard
  let idx : Core -> C.coords := fun x =>
    Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x : Core) : idx x ∈ CoreIdx ∧
      C.domain (idx x : I) = (x : F) :=
    Classical.choose_spec (Finset.mem_image.mp x.property)
  let U0 : F -> F := Function.extend C.domain qu0 0
  let U1 : F -> F := Function.extend C.domain qu1 0
  have hUcoords : ∀ i : I,
      U0 (C.domain i) = qu0 i ∧ U1 (C.domain i) = qu1 i := by
    intro i
    exact ⟨C.domain.injective.extend_apply qu0 0 i,
      C.domain.injective.extend_apply qu1 0 i⟩
  have hdiv : ∀ i ∈ CoreIdx, D.inner ∣ B (i : I) := by
    intro i hi
    apply irreducible_dvd_of_resultant_eq_zero_nonmonic
      (B (i : I)) D.inner D.inner_irreducible D.inner_degree_pos
    simpa [Res] using hReszero i (hCoreCoord hi)
  have hzero : ∀ x ∈ Core,
      Polynomial.eval₂ (liftToFunctionField (H := D.inner))
        (initialValue (H := D.inner))
          (universalAffineObstruction
            (universalRootedNumerators tag.center tag.transformed)
            (universalSlope tag.center tag.transformed) E
            tag.rootDegreeCap (x - tag.center) (U0 x) (U1 x)) = 0 := by
    intro x hx
    let xx : Core := ⟨x, hx⟩
    have hdvd := hdiv (idx xx) (hidx xx).1
    have heval := eval₂_lift_initialValue_eq_zero_of_dvd
      (B (idx xx : I)) D.inner hdvd
    have hxeq : C.domain (idx xx : I) = x := (hidx xx).2
    rw [← hxeq, (hUcoords (idx xx : I)).1,
      (hUcoords (idx xx : I)).2]
    simpa [B, concreteUniversalAffineObstruction, E] using heval
  refine ⟨CoreIdx, Core, U0, U1, hCoreIdxCard, rfl, hCoreCard,
    (Nat.lt_succ_self freshSelectorThreshold).trans hscaled.2,
    hUcoords, hzero⟩

/-- Exact-`20230` specialization used when the selected stored root still has
the full benchmark degree `131071`. -/
theorem SelectedExplicitPairFiber.exists_zeroCore20230
    {F I A : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I] [DecidableEq A]
    {G : GlobalSelectorData F A}
    (W : SelectedExplicitPairFiber G)
    [Fact (Irreducible (G.data W.pair.1).inner)]
    [Fact (0 < (G.data W.pair.1).inner.natDegree)]
    (C : DynamicCoreCoordinateData W I)
    (hcoordinateCount : G.coordinateCount = 262144)
    (hrowLower : G.rowLower = 185364)
    (hcommonTarget : G.commonTarget = 20230)
    (herrors : G.errors = freshSelectorThreshold)
    (hcoords : C.coords.card = 262144)
    (hactualRow : C.rowLower = 185364)
    (hrootCap : (G.tag W.pair.1).rootDegreeCap = 131071) :
    let a := W.pair.1
    let tag := G.tag a
    let D := G.data a
    let L := C.lift
    let E := FiniteHenselWeight.denominatorExponent tag.rootDegreeCap
    ∃ CoreIdx : Finset C.coords, ∃ Core : Finset F,
      ∃ U0 U1 : F -> F,
        CoreIdx.card = 20230 ∧
        Core = CoreIdx.image (fun i : C.coords => C.domain (i : I)) ∧
        Core.card = 20230 ∧
        freshSelectorThreshold < W.fiber.card ∧
        (∀ i : I,
          U0 (C.domain i) = L.quotientReceived0 C.domain C.received0 i ∧
          U1 (C.domain i) = L.quotientReceived1 C.domain C.received1 i) ∧
        ∀ x ∈ Core,
          Polynomial.eval₂ (liftToFunctionField (H := D.inner))
            (initialValue (H := D.inner))
              (universalAffineObstruction
                (universalRootedNumerators tag.center tag.transformed)
                (universalSlope tag.center tag.transformed) E
                tag.rootDegreeCap (x - tag.center) (U0 x) (U1 x)) = 0 := by
  have hpos : 0 < (G.tag W.pair.1).rootDegreeCap := by
    rw [hrootCap]
    norm_num
  exact SelectedExplicitPairFiber.exists_zeroCoreUpTo20230 W C
    hcoordinateCount hrowLower hcommonTarget herrors 20230
      (by omega) (by omega) hpos

/-! ## Complete first-stage to fresh-quotient composition -/

/-- Any pre-existing common-core codimension at most `20230` leaves enough
stored-root degree for the fixed `110841` fresh quotient.  The formerly
problematic `c ≤ 390` strip is a tiny subinterval of this range. -/
theorem rootCap_interval_of_codim_le20230
    (rootCap codim : Nat) (hsum : rootCap + codim = 131071)
    (hcodim : codim <= 20230) :
    freshRootCap <= rootCap ∧ rootCap <= 131071 := by
  norm_num [freshRootCap]
  omega

/-- Exact invariant geometry of the selected tag's off-core profile.  Removing
its existing codimension and then the dynamic zero core always leaves the
same `241914` coordinates and `165134` agreements consumed by the fresh
selector. -/
theorem dynamic_profile_gaps_of_codim_le20230
    (rootCap codim coordCard rowLower : Nat)
    (hroot : rootCap + codim = 131071)
    (hcoord : coordCard + codim = 262144)
    (hrow : rowLower + codim = 185364)
    (hcodim : codim <= 20230) :
    freshRootCap <= rootCap ∧
      coordCard - (rootCap - freshRootCap) = 241914 ∧
      rowLower - (rootCap - freshRootCap) = 165134 := by
  norm_num [freshRootCap]
  omega

/-- The exact arithmetic/geometric endpoint consumed by the composed
selector: all source degrees through `209` fit the residual numerator, and
every profile codimension through `20230` has the fixed fresh gaps. -/
theorem degree209_profile_budget_and_gaps
    (d rootCap codim coordCard rowLower : Nat) (hd : d <= 209)
    (hroot : rootCap + codim = 131071)
    (hcoord : coordCard + codim = 262144)
    (hrow : rowLower + codim = 185364)
    (hcodim : codim <= 20230) :
    freshNestedTotalCorrected6400 d < bchksResidualNumerator6400 ∧
      freshRootCap <= rootCap ∧
      coordCard - (rootCap - freshRootCap) = 241914 ∧
      rowLower - (rootCap - freshRootCap) = 165134 := by
  exact ⟨freshNested_corrected_fits_of_degree_le2096400 d hd,
    dynamic_profile_gaps_of_codim_le20230 rootCap codim coordCard rowLower
      hroot hcoord hrow hcodim⟩

/-- Set-difference form used by the benchmark adapter.  Deleting the
selected tag's existing core from both the domain and an agreement row
simultaneously supplies the exact profile gaps and the required row lower
bound. -/
theorem selected_profile_complement_gaps
    {I : Type} [DecidableEq I]
    (Domain ExistingCore Agree : Finset I)
    (rootCap codim : Nat)
    (hDomain : Domain.card = 262144)
    (hCoreSub : ExistingCore ⊆ Domain)
    (hCoreCard : ExistingCore.card = codim)
    (hAgree : 185364 <= Agree.card)
    (hroot : rootCap + codim = 131071)
    (hcodim : codim <= 20230) :
    (Domain \ ExistingCore).card -
        (rootCap - freshRootCap) = 241914 ∧
      (185364 - codim) -
        (rootCap - freshRootCap) = 165134 ∧
      185364 - codim <= (Agree \ ExistingCore).card := by
  have hDomainDiff : (Domain \ ExistingCore).card = 262144 - codim := by
    rw [Finset.card_sdiff_of_subset hCoreSub, hDomain, hCoreCard]
  have hAgreeDiff := Finset.le_card_sdiff ExistingCore Agree
  rw [hCoreCard] at hAgreeDiff
  have hgaps := dynamic_profile_gaps_of_codim_le20230
    rootCap codim (262144 - codim) (185364 - codim)
    hroot (by omega) (by omega) hcodim
  rw [hDomainDiff]
  exact ⟨hgaps.2.1, hgaps.2.2, by omega⟩

/-- The selected first pair, stopped at exactly `20230` common obstruction
identities, feeds the complete fresh quotient interpolation and universal
inner-pair selector on the *same* owner fibre.  In particular there is no
second incidence or owner-cap loss between the two stages. -/
theorem SelectedExplicitPairFiber.exists_completeFreshQuotientChain20230
    {I A : Type} [Fintype I] [DecidableEq I] [DecidableEq A]
    {G : GlobalSelectorData IRSProfile.Field A}
    (W : SelectedExplicitPairFiber G)
    (C : DynamicCoreCoordinateData W I)
    (hcoordinateCount : G.coordinateCount = 262144)
    (hrowLower : G.rowLower = 185364)
    (hcommonTarget : G.commonTarget = 20230)
    (herrors : G.errors = freshSelectorThreshold)
    (hrootCapLower : freshRootCap <=
      (G.tag W.pair.1).rootDegreeCap)
    (hcoordinateGap : C.coords.card -
      ((G.tag W.pair.1).rootDegreeCap - freshRootCap) = 241914)
    (hactualRowGap : C.rowLower -
      ((G.tag W.pair.1).rootDegreeCap - freshRootCap) = 165134) :
    let a := W.pair.1
    let tag := G.tag a
    ∃ Core : Finset IRSProfile.Field,
      ∃ U0 U1 : IRSProfile.Field → IRSProfile.Field,
      ∃ omega : Fin 241914 ↪ IRSProfile.Field,
      ∃ B0 B1 : IRSProfile.Field[X],
      ∃ Q : W.fiber → IRSProfile.Field[X],
      ∃ Qfresh : IRSProfile.Field[X][X][Y],
      ∃ x1 : IRSProfile.Field,
      ∃ RH : BCHKSFreshQuotientUniversalSelector6400.Pair,
      ∃ T1 : Finset IRSProfile.Field,
      ∃ Coord : Finset (Fin 241914),
        Core.card + freshRootCap = tag.rootDegreeCap ∧
        (∀ i, omega i ∉ Core) ∧
        B0.natDegree ≤ tag.rootDegreeCap ∧
        B1.natDegree ≤ tag.rootDegreeCap ∧
        (∀ z : W.fiber, (Q z).natDegree ≤ freshRootCap) ∧
        (∀ z : W.fiber,
          tag.root z = B0 + Polynomial.C (z : IRSProfile.Field) * B1 +
            BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z) ∧
        Qfresh ≠ 0 ∧
        (∀ z : W.fiber,
          triEval Qfresh (z : IRSProfile.Field) (Q z) = 0) ∧
        BCHKSFreshQuotientUniversalSelector6400.SupportCaps Qfresh ∧
        RH ∈ UniversalOuterCover6399.pairs Qfresh x1 ∧
        ((triSpecializeX RH.1 x1).IsPrimitive ∧
          Polynomial.eval (Polynomial.C x1)
            (factorXObstruction RH.1) ≠ 0 ∧
          triSpecializeX RH.1 x1 ≠ 0 ∧
          (triSpecializeX RH.1 x1).natDegree = RH.1.natDegree ∧
          Polynomial.eval (Polynomial.C x1)
            (rawSepResultant RH.1) ≠ 0) ∧
        T1 ⊆ W.fiber ∧
        freshErrors + 1 < T1.card ∧
        freshRootCap + 1 ≤ Coord.card ∧
        (∀ z ∈ T1,
          UniversalOuterCover6399.pairRel
            (fun w ↦ if hw : w ∈ W.fiber then Q ⟨w, hw⟩ else 0)
            x1 z RH) ∧
        (∀ i ∈ Coord, RH.2 ∣
          concreteUniversalAffineObstruction x1 RH.1
            freshExponent freshRootCap
            (omega i - x1)
            (quotientReceived0 Core B0 U0 (omega i))
            (quotientReceived1 Core B1 U1 (omega i))) := by
  classical
  dsimp only
  let a := W.pair.1
  let tag := G.tag a
  let D := G.data a
  let L := C.lift
  let q := tag.rootDegreeCap - freshRootCap
  letI : Fact (Irreducible D.inner) := ⟨D.inner_irreducible⟩
  letI : Fact (0 < D.inner.natDegree) := ⟨D.inner_degree_pos⟩
  have ha : a ∈ G.outer := by
    simpa only [a] using
      explicitInnerPairs_fst_mem G.outer G.tag G.data W.pair W.pair_mem
  have hrootCapLower' : freshRootCap <= tag.rootDegreeCap := by
    simpa only [tag, a] using hrootCapLower
  have hrootCapPos : 0 < (G.tag W.pair.1).rootDegreeCap := by
    exact (by norm_num [freshRootCap] : 0 < freshRootCap).trans_le
      hrootCapLower
  obtain ⟨CoreIdx, Core, U0, U1, hCoreIdxCard, hCoreEq,
      hCoreCard, hTcard, hUcoords, hzero⟩ :=
    BCHKSFreshQuotientFirstStage6400.SelectedExplicitPairFiber.exists_zeroCoreUpTo20230
      W C hcoordinateCount hrowLower hcommonTarget herrors q
        (by simpa only [q, tag, a] using hcoordinateGap)
        (by simpa only [q, tag, a] using hactualRowGap) hrootCapPos
  have hOutsideGap : C.coords.card - CoreIdx.card = 241914 := by
    rw [hCoreIdxCard]
    simpa only [q, tag, a] using hcoordinateGap
  have hFreshRowGap : 165134 + CoreIdx.card <= C.rowLower := by
    rw [hCoreIdxCard]
    have hgap : C.rowLower - q = 165134 := by
      simpa only [q, tag, a] using hactualRowGap
    omega
  obtain ⟨idx, omega, FreshRow, hidxOutside, homega,
      hFreshCard, hFreshRow⟩ :=
    exists_freshComplement_enumeration_of_gaps C.coords CoreIdx
      hOutsideGap C.rowLower hFreshRowGap C.domain W.fiber
        C.agreementRows C.row_large
  have houtside : ∀ j, omega j ∉ Core := by
    intro j hj
    rw [hCoreEq] at hj
    obtain ⟨i, hiCore, hiEq⟩ := Finset.mem_image.mp hj
    have hij : i = idx j := by
      apply Subtype.ext
      apply C.domain.injective
      exact hiEq.trans (homega j)
    exact hidxOutside j (by simpa [hij] using hiCore)
  let Arow : W.fiber → Finset (Fin 241914) := fun z => FreshRow (z : _)
  have hrowFresh : ∀ z : W.fiber,
      freshAgreement ≤ (Arow z).card := by
    intro z
    simpa [Arow, freshAgreement] using hFreshCard (z : _) z.property
  have hmatch : ∀ z : W.fiber, ∀ j ∈ Arow z,
      (tag.root z).eval (omega j) =
        U0 (omega j) + (z : IRSProfile.Field) * U1 (omega j) := by
    intro z j hj
    have hjrow : (idx j : I) ∈ C.agreementRows (z : _) :=
      hFreshRow (z : _) z.property j (by simpa [Arow] using hj)
    have hagree := L.storedRoot_agree_of_original
      C.domain C.received0 C.received1 (z : _) (idx j : I)
      (W.owns (z : _) z.property)
      (C.locator_nonzero (idx j) (idx j).property)
      (C.original_agrees (z : _) z.property (idx j : I) hjrow)
    rw [homega j, (hUcoords (idx j : I)).1,
      (hUcoords (idx j : I)).2]
    exact hagree
  have hTnonempty : W.fiber.Nonempty :=
    Finset.card_pos.mp (Nat.zero_lt_of_lt hTcard)
  obtain ⟨hzeta, Sel, hNP⟩ :=
    BCHKSExplicitPairAlignment6400.ExplicitInnerData.exists_universalSelectedData
      D W.fiber hTnonempty W.owns (tag.rootDegreeCap + 1)
  have hslope : Polynomial.eval₂ (liftToFunctionField (H := D.inner))
      (initialValue (H := D.inner))
        (universalSlope tag.center tag.transformed) =
      HenselNumerators.zeta tag.transformed tag.center D.inner := by
    change evalUniversal (liftToFunctionField (H := D.inner))
      (initialValue (H := D.inner))
        (universalSlope tag.center tag.transformed) = _
    rw [universalSlope_evalUniversal]
    simpa [liftedR, fieldTo𝕃] using
      (ySlope_liftedR_eq_zeta
        (R := tag.transformed) (H := D.inner) tag.center)
  have hnum : ∀ n, n ≤ tag.rootDegreeCap →
      Polynomial.eval₂ (liftToFunctionField (H := D.inner))
          (initialValue (H := D.inner))
          (universalRootedNumerators tag.center tag.transformed n) =
        finiteAlpha (R := tag.transformed) (H := D.inner)
            tag.center (tag.rootDegreeCap + 1) n *
          HenselNumerators.zeta tag.transformed tag.center D.inner ^
            FiniteHenselWeight.denominatorExponent n := by
    intro n hn
    exact eval₂_universalRootedNumerators_eq_finiteAlpha_mul_zeta_pow
      tag.center tag.transformed D.henselSetup hzeta
        (tag.rootDegreeCap + 1) n (hn.trans (Nat.le_add_right _ _))
  have hcard : Core.card + freshRootCap = tag.rootDegreeCap := by
    rw [hCoreCard]
    dsimp only [q]
    exact Nat.sub_add_cancel hrootCapLower'
  obtain ⟨B0, B1, Q, _gammaQ, hB0degree, hB1degree, hQdegree, hshape,
      _hgammaDegree, _hgammaShape, Qfresh, x1, RH, T1, Coord,
      hQfresh, hQeval, hcaps, hRH, hx, hTsub, hT1card, hCoord,
      hrel, hdiv⟩ :=
    exists_concrete_fresh_selected_pair_of_zeroCore
      tag.center tag.transformed D.henselSetup hzeta
      D.supportCap tag.transformed.natDegree tag.rootDegreeCap
      (tag.rootDegreeCap + 1) (Nat.lt_succ_self _)
      W.fiber (fun z : W.fiber => tag.root z) Sel hNP
      (fun z => tag.root_degree_le (z : _) (W.owns (z : _) z.property))
      Core U0 U1 freshRootCap hcard rfl
      (universalRootedNumerators tag.center tag.transformed)
      (universalSlope tag.center tag.transformed)
      (FiniteHenselWeight.denominatorExponent tag.rootDegreeCap)
      rfl hslope hnum hzero omega houtside Arow hTcard hrowFresh hmatch
  exact ⟨Core, U0, U1, omega, B0, B1, Q, Qfresh, x1, RH, T1,
    Coord, hcard, houtside, hB0degree, hB1degree, hQdegree, hshape,
    hQfresh, hQeval,
    hcaps, hRH, hx, hTsub, hT1card, hCoord, hrel, hdiv⟩

end BCHKSFreshQuotientFirstStage6400
end ProximityPrize.SubmissionLower
