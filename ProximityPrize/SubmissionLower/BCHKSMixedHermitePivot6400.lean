import ProximityPrize.SubmissionLower.BCHKSMixedJetRankBridge6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSMixedHermitePivot6400

open Polynomial
open BCHKSMixedJetRankBridge6400

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 200000

/-!
Finite confluent-Hermite pivots for the mixed-jet lane.

This file proves the rank statement which is independent of Gao's generic
rank theorem.  At one fixed `Y`-Hasse layer, the selected mixed jets restrict
to the usual confluent-Hermite evaluation map in `X`.  Root multiplicity
shows that this square map is an equivalence.  Layers are then stacked by a
recursive block-triangular argument, from low `Y` order to high `Y` order.

Nothing here asserts that a particular Gao source contains these pivots;
that source-membership and generic-specialization statement remains a
separate obligation.
-/

/-- The finite row type containing the first `mu i` Hasse jets at point `i`. -/
abbrev HermiteIndex (I : Type*) (mu : I -> Nat) :=
  Sigma fun i : I => Fin (mu i)

@[simp]
theorem hermiteIndex_card
    {I : Type*} [Fintype I] (mu : I -> Nat) :
    Fintype.card (HermiteIndex I mu) = ∑ i : I, mu i := by
  classical
  simp [HermiteIndex]

/-- Vanishing of the first `m` Hasse coefficients at `x` forces root
multiplicity at least `m`, in every characteristic. -/
theorem le_rootMultiplicity_of_eval_hasseDeriv_eq_zero
    {K : Type*} [Field K] (P : Polynomial K) (x : K) (m : Nat)
    (hP : P ≠ 0)
    (hvan : forall s, s < m ->
      Polynomial.eval x (Polynomial.hasseDeriv s P) = 0) :
    m <= P.rootMultiplicity x := by
  rw [Polynomial.le_rootMultiplicity_iff hP]
  have htaylor : Polynomial.X ^ m ∣ Polynomial.taylor x P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro s hs
    rw [Polynomial.taylor_coeff]
    exact hvan s hs
  obtain ⟨Q, hQ⟩ := htaylor
  refine ⟨Q.comp (Polynomial.X - Polynomial.C x), ?_⟩
  calc
    P = (Polynomial.taylor x P).comp
        (Polynomial.X - Polynomial.C x) := by
      simp [Polynomial.taylor_apply, Polynomial.comp_assoc]
    _ = (Polynomial.X ^ m * Q).comp
        (Polynomial.X - Polynomial.C x) := by rw [hQ]
    _ = (Polynomial.X - Polynomial.C x) ^ m *
        Q.comp (Polynomial.X - Polynomial.C x) := by
      simp

/-- The square confluent-Hermite evaluation map on polynomials of degree
strictly below the total selected jet mass. -/
noncomputable def hermiteJetMap
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) :
    Polynomial.degreeLT K (∑ i : I, mu i) →ₗ[K]
      (HermiteIndex I mu -> K) where
  toFun P j := Polynomial.eval (omega j.1)
    (Polynomial.hasseDeriv j.2 P.1)
  map_add' P Q := by
    funext j
    simp
  map_smul' c P := by
    funext j
    simp

@[simp]
theorem hermiteJetMap_apply
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat)
    (P : Polynomial.degreeLT K (∑ i : I, mu i))
    (j : HermiteIndex I mu) :
    hermiteJetMap omega mu P j =
      Polynomial.eval (omega j.1)
        (Polynomial.hasseDeriv j.2 P.1) := rfl

/-- Root counting makes the square confluent-Hermite map injective. -/
theorem hermiteJetMap_injective
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) :
    Function.Injective (hermiteJetMap omega mu) := by
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq I := Classical.decEq I
  intro P Q hPQ
  have hPjets : hermiteJetMap omega mu (P - Q) = 0 := by
    rw [LinearMap.map_sub, hPQ, sub_self]
  have hzero : P - Q = 0 := by
    apply Subtype.ext
    by_contra hP
    have hjet : forall i : I, forall s, s < mu i ->
        Polynomial.eval (omega i)
          (Polynomial.hasseDeriv s (P - Q).1) = 0 := by
      intro i s hs
      let j : HermiteIndex I mu := ⟨i, ⟨s, hs⟩⟩
      have hj := congrFun hPjets j
      simpa [j] using hj
    have hmult : forall i, i ∈ (Finset.univ : Finset I) ->
        mu i <= (P - Q).1.rootMultiplicity (omega i) := by
      intro i hi
      exact le_rootMultiplicity_of_eval_hasseDeriv_eq_zero
        (P - Q).1 (omega i) (mu i) hP (hjet i)
    have hroots :=
      BCHKSWeightedSubstitution.sum_le_natDegree_of_rootMultiplicity
        (F := K) (ι := I)
        (P - Q).1 omega (Finset.univ : Finset I) mu hmult
    have hdegree := (P - Q).2
    rw [Polynomial.mem_degreeLT,
      Polynomial.degree_eq_natDegree hP] at hdegree
    have hdegree' : (P - Q).1.natDegree < ∑ i : I, mu i := by
      exact_mod_cast hdegree
    exact (not_lt_of_ge hroots hdegree')
  exact sub_eq_zero.mp hzero

/-- Domain and target of `hermiteJetMap` have the same dimension. -/
theorem hermiteJetMap_finrank_eq
    {K I : Type*} [Field K] [Fintype I] (mu : I -> Nat) :
    Module.finrank K (Polynomial.degreeLT K (∑ i : I, mu i)) =
      Module.finrank K (HermiteIndex I mu -> K) := by
  classical
  rw [Module.finrank_eq_card_basis
    (Polynomial.degreeLT.basis K (∑ i : I, mu i))]
  simp [HermiteIndex]

/-- Confluent Hermite interpolation as a genuine linear equivalence. -/
noncomputable def hermiteJetEquiv
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) :
    Polynomial.degreeLT K (∑ i : I, mu i) ≃ₗ[K]
      (HermiteIndex I mu -> K) :=
  (hermiteJetMap omega mu).linearEquivOfInjective
    (hermiteJetMap_injective omega mu)
    (hermiteJetMap_finrank_eq mu)

/-- The explicit interpolant with prescribed selected jets. -/
noncomputable def hermiteInterpolate
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) :
    (HermiteIndex I mu -> K) →ₗ[K]
      Polynomial.degreeLT K (∑ i : I, mu i) :=
  (hermiteJetEquiv omega mu).symm.toLinearMap

@[simp]
theorem hermiteJetMap_hermiteInterpolate
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat)
    (v : HermiteIndex I mu -> K) :
    hermiteJetMap omega mu (hermiteInterpolate omega mu v) = v := by
  exact (hermiteJetEquiv omega mu).apply_symm_apply v

@[simp]
theorem hermiteInterpolate_hermiteJetMap
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat)
    (P : Polynomial.degreeLT K (∑ i : I, mu i)) :
    hermiteInterpolate omega mu (hermiteJetMap omega mu P) = P := by
  exact (hermiteJetEquiv omega mu).symm_apply_apply P

/-- Coordinate functionals of the square Hermite map. -/
noncomputable def selectedHermiteFunctional
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) (j : HermiteIndex I mu) :
    Module.Dual K
      (Polynomial.degreeLT K (∑ i : I, mu i)) where
  toFun P := hermiteJetMap omega mu P j
  map_add' P Q := by simp
  map_smul' c P := by simp

@[simp]
theorem selectedHermiteFunctional_apply
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) (j : HermiteIndex I mu)
    (P : Polynomial.degreeLT K (∑ i : I, mu i)) :
    selectedHermiteFunctional omega mu j P =
      Polynomial.eval (omega j.1)
        (Polynomial.hasseDeriv j.2 P.1) := by
  rfl

/-- The selected univariate Hasse-Hermite rows are linearly independent. -/
theorem selectedHermiteFunctional_linearIndependent
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (mu : I -> Nat) :
    LinearIndependent K (selectedHermiteFunctional omega mu) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hrelation j
  let e : HermiteIndex I mu -> K := Pi.single j 1
  let P := hermiteInterpolate omega mu e
  have happly := congrArg
    (fun f : Module.Dual K
      (Polynomial.degreeLT K (∑ i : I, mu i)) => f P)
    hrelation
  have hjet : hermiteJetMap omega mu P = e := by
    exact hermiteJetMap_hermiteInterpolate omega mu e
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.zero_apply] at happly
  simp only [selectedHermiteFunctional_apply, ← hermiteJetMap_apply,
    hjet, e, Pi.single_apply] at happly
  simpa using happly

/-- A mixed Hasse coefficient, regarded as a linear functional on
bivariate polynomials. -/
noncomputable def mixedHasseJetLinear
    {K : Type*} [Field K] (omega u : K) (s b : Nat) :
    Module.Dual K (Polynomial (Polynomial K)) where
  toFun T := mixedHasseJet omega u s b T
  map_add' T U := by
    simp [mixedHasseJet]
  map_smul' c T := by
    simp [mixedHasseJet]

/-- The finite mixed-Hasse family selected in one `Y` layer. -/
noncomputable def selectedMixedHasseLayer
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (u : I -> K) (mu : I -> Nat) (b : Nat) :
    HermiteIndex I mu -> Module.Dual K (Polynomial (Polynomial K)) :=
  fun j => mixedHasseJetLinear (omega j.1) (u j.1) j.2 b

/-- Embed a bounded univariate polynomial as the pure `Y^b` layer. -/
noncomputable def pureYLayerMap
    {K : Type*} [Field K] (b N : Nat) :
    Polynomial.degreeLT K N →ₗ[K] Polynomial (Polynomial K) where
  toFun A := Polynomial.monomial b A.1
  map_add' A B := by
    simp
  map_smul' c A := by
    simp

/-- Restrict a bivariate functional to the pure `Y^b` layer. -/
noncomputable def restrictToPureYLayer
    {K : Type*} [Field K] (b N : Nat) :
    Module.Dual K (Polynomial (Polynomial K)) →ₗ[K]
      Module.Dual K (Polynomial.degreeLT K N) :=
  (pureYLayerMap b N).dualMap

@[simp]
theorem restrict_selectedMixedHasseLayer_same
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (u : I -> K) (mu : I -> Nat) (b : Nat)
    (j : HermiteIndex I mu) :
    restrictToPureYLayer b (∑ i : I, mu i)
        (selectedMixedHasseLayer omega u mu b j) =
      selectedHermiteFunctional omega mu j := by
  ext A
  simp [restrictToPureYLayer, selectedMixedHasseLayer,
    mixedHasseJetLinear, pureYLayerMap,
    selectedHermiteFunctional_apply,
    mixedHasseJet_pureLayer_same]

/-- One selected mixed-Hasse layer is independent, with no characteristic
restriction and no hypothesis on the received values `u`. -/
theorem selectedMixedHasseLayer_linearIndependent
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (u : I -> K) (mu : I -> Nat) (b : Nat) :
    LinearIndependent K (selectedMixedHasseLayer omega u mu b) := by
  classical
  apply LinearIndependent.of_comp
    (restrictToPureYLayer b (∑ i : I, mu i))
  simpa [Function.comp_def] using
    selectedHermiteFunctional_linearIndependent omega mu

@[simp]
theorem restrict_selectedMixedHasseLayer_higher_zero
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (u : I -> K)
    (muLow muHigh : I -> Nat) (b c : Nat) (hbc : b < c)
    (j : HermiteIndex I muHigh) :
    restrictToPureYLayer b (∑ i : I, muLow i)
        (selectedMixedHasseLayer omega u muHigh c j) = 0 := by
  ext A
  simp [restrictToPureYLayer, selectedMixedHasseLayer,
    mixedHasseJetLinear, pureYLayerMap,
    mixedHasseJet_pureLayer_higher_zero, hbc]

/-! A recursive finite index for consecutive layers.  `LayerTower I s n`
contains the blocks `I s, I (s+1), ..., I (s+n-1)`. -/
universe u v

def LayerTower (J : Nat -> Type u) : Nat -> Nat -> Type u
  | _, 0 => PEmpty
  | s, n + 1 => Sum (J s) (LayerTower J (s + 1) n)

noncomputable instance layerTowerFintype
    (J : Nat -> Type u) [forall b, Fintype (J b)] (s n : Nat) :
    Fintype (LayerTower J s n) := by
  induction n generalizing s with
  | zero =>
      simp [LayerTower]
      infer_instance
  | succ n ih =>
      simp only [LayerTower]
      letI : Fintype (LayerTower J (s + 1) n) := ih (s + 1)
      infer_instance

/-- The flattened index has exactly the sum of the block sizes. -/
theorem layerTower_card
    (J : Nat -> Type u) [forall b, Fintype (J b)] (s n : Nat) :
    Fintype.card (LayerTower J s n) =
      ∑ t ∈ Finset.range n, Fintype.card (J (s + t)) := by
  induction n generalizing s with
  | zero => simp [LayerTower]
  | succ n ih =>
      letI : Fintype (LayerTower J (s + 1) n) :=
        layerTowerFintype J (s + 1) n
      have hsplit : Fintype.card (LayerTower J s (n + 1)) =
          Fintype.card (J s ⊕ LayerTower J (s + 1) n) :=
        Fintype.card_congr (Equiv.refl _)
      rw [hsplit, Fintype.card_sum, ih (s + 1),
        Finset.sum_range_succ']
      have htail :
          (∑ t ∈ Finset.range n,
              Fintype.card (J (s + 1 + t))) =
            ∑ t ∈ Finset.range n,
              Fintype.card (J (s + (t + 1))) := by
        apply Finset.sum_congr rfl
        intro t ht
        have hindex : s + 1 + t = s + (t + 1) := by omega
        rw [hindex]
      rw [htail]
      simp [Nat.add_comm]

/-- Flatten consecutive vector blocks into one family. -/
def layerTowerFamily
    {M : Type v} (J : Nat -> Type u)
    (block : forall b, J b -> M) :
    forall s n, LayerTower J s n -> M
  | _, 0 => PEmpty.elim
  | s, n + 1 => Sum.elim (block s)
      (layerTowerFamily J block (s + 1) n)

private theorem restriction_layerTower_zero
    {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    (J : Nat -> Type*) (block : forall b, J b -> M)
    (L : M →ₗ[K] N)
    (b : Nat) (hzero : forall c, b < c -> forall j, L (block c j) = 0)
    (s n : Nat) (hbs : b < s) :
    forall j : LayerTower J s n,
      L (layerTowerFamily J block s n j) = 0 := by
  induction n generalizing s with
  | zero =>
      intro j
      exact PEmpty.elim j
  | succ n ih =>
      intro j
      cases j with
      | inl j => exact hzero s hbs j
      | inr j =>
          exact ih (s + 1) (by omega) j

/-- General finite block-triangular independence theorem for consecutive
layers.  The restriction target may vary with the layer.  The proof repeatedly
uses `linearIndependent_sum_of_triangular_restriction`. -/
theorem linearIndependent_layerTower_of_triangular_restriction
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (J : Nat -> Type*) [forall b, Fintype (J b)]
    (N : Nat -> Type*)
    [forall b, AddCommGroup (N b)] [forall b, Module K (N b)]
    (block : forall b, J b -> M)
    (L : forall b, M →ₗ[K] N b)
    (hdiag : forall b, LinearIndependent K (fun j => L b (block b j)))
    (hzero : forall b c, b < c -> forall j, L b (block c j) = 0) :
    forall s n,
      LinearIndependent K (layerTowerFamily J block s n) := by
  intro s n
  induction n generalizing s with
  | zero =>
      simp only [LayerTower, layerTowerFamily]
      exact linearIndependent_empty_type
  | succ n ih =>
      letI : Fintype (LayerTower J (s + 1) n) :=
        layerTowerFintype J (s + 1) n
      have htailZero : forall j : LayerTower J (s + 1) n,
          L s (layerTowerFamily J block (s + 1) n j) = 0 := by
        exact restriction_layerTower_zero J block (L s) s
          (fun c hsc j => hzero s c hsc j)
          (s + 1) n (by omega)
      simpa only [LayerTower, layerTowerFamily] using
        linearIndependent_sum_of_triangular_restriction
          (block s) (layerTowerFamily J block (s + 1) n) (L s)
          (hdiag s) (ih (s + 1)) htailZero

/-- The benchmark-relevant selected count at layer `b`: a point of local
order `nu i` contributes `nu i - 1 - b` rows. -/
def predecessorLayerCount
    {I : Type*} (nu : I -> Nat) (b : Nat) (i : I) : Nat :=
  nu i - 1 - b

/-- All selected mixed-Hasse rows in consecutive layers are independent.
Taking `s=0`, `n=52`, and local orders bounded by `53` is the canonical
degree-53 Hermite pivot family. -/
theorem selectedMixedHasseTower_linearIndependent
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (u : I -> K) (nu : I -> Nat) (s n : Nat) :
    LinearIndependent K
      (layerTowerFamily
        (fun b => HermiteIndex I (predecessorLayerCount nu b))
        (fun b => selectedMixedHasseLayer omega u
          (predecessorLayerCount nu b) b) s n) := by
  classical
  apply linearIndependent_layerTower_of_triangular_restriction
    (J := fun b => HermiteIndex I (predecessorLayerCount nu b))
    (N := fun b => Module.Dual K
      (Polynomial.degreeLT K
        (∑ i : I, predecessorLayerCount nu b i)))
    (block := fun b => selectedMixedHasseLayer omega u
      (predecessorLayerCount nu b) b)
    (L := fun b => restrictToPureYLayer b
      (∑ i : I, predecessorLayerCount nu b i))
  · intro b
    simpa [Function.comp_def] using
      selectedHermiteFunctional_linearIndependent omega
        (predecessorLayerCount nu b)
  · intro b c hbc j
    exact restrict_selectedMixedHasseLayer_higher_zero
      omega u (predecessorLayerCount nu b)
      (predecessorLayerCount nu c) b c hbc j

/-- Named degree-53 specialization: layers `0,...,51`. -/
theorem selectedMixedHasseTower_degree53_linearIndependent
    {K I : Type*} [Field K] [Fintype I]
    (omega : I ↪ K) (u : I -> K) (nu : I -> Nat) :
    LinearIndependent K
      (layerTowerFamily
        (fun b => HermiteIndex I (predecessorLayerCount nu b))
        (fun b => selectedMixedHasseLayer omega u
          (predecessorLayerCount nu b) b) 0 52) :=
  selectedMixedHasseTower_linearIndependent omega u nu 0 52

/-- The degree-53 pivot family has exactly the layer-sensitive mixed-jet
mass used in the endpoint ledger. -/
theorem selectedMixedHasseTower_degree53_card
    {I : Type*} [Fintype I] (nu : I -> Nat) :
    Fintype.card
        (LayerTower
          (fun b => HermiteIndex I (predecessorLayerCount nu b)) 0 52) =
      ∑ b ∈ Finset.range 52,
        ∑ i : I, (nu i - 1 - b) := by
  classical
  rw [layerTower_card]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hermiteIndex_card]
  simp [predecessorLayerCount]

end BCHKSMixedHermitePivot6400
end ProximityPrize.SubmissionLower
