import ProximityPrize.SubmissionLower.BCHKSExplicitMixedInnerPairs6400
import ProximityPrize.SubmissionLower.BCHKSDynamicCoreSelector6400
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteObstruction
import ProximityPrize.SubmissionLower.BCHKSUniversalNumeratorFunctionField
import ProximityPrize.SubmissionLower.BCHKSUniversalResultantSelection
namespace ProximityPrize.SubmissionLower
namespace BCHKSExplicitPairAlignment6400
open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open BCHKSTransformedUniversalTag6400
open BCHKSCoreTransformedUniversalTag6400
open BCHKSMixedUniversalTag6400
open BCHKSExplicitCoreInnerTransport6400
open BCHKSExplicitMixedInnerPairs6400
open BCHKSCoreQuotientHenselAudit6400
open BCHKSDynamicCoreSelector6400
open UniversalNumerator
set_option maxHeartbeats 200000
set_option maxRecDepth 1000000
structure AffineRootLift
    {F : Type} [Field F]
    (tag : TransformedUniversalTag F) where
  originalRoot : F → F[X]
  degreeCap : Nat
  base0 : F[X]
  base1 : F[X]
  locator : F[X]
  base0_degree_le : base0.natDegree ≤ degreeCap
  base1_degree_le : base1.natDegree ≤ degreeCap
  locator_degree_add_rootCap :
    locator.natDegree + tag.rootDegreeCap ≤ degreeCap
  root_shape : ∀ z, tag.owns z →
    originalRoot z = base0 + Polynomial.C z * base1 + locator * tag.root z
theorem AffineRootLift.lift_alignment
    {F : Type} [Field F]
    {tag : TransformedUniversalTag F}
    (L : AffineRootLift tag)
    (T : Finset F) (q0 q1 : F[X])
    (hq0 : q0.natDegree ≤ tag.rootDegreeCap)
    (hq1 : q1.natDegree ≤ tag.rootDegreeCap)
    (howns : ∀ z ∈ T, tag.owns z)
    (halign : ∀ z ∈ T,
      tag.root z = q0 + Polynomial.C z * q1) :
    ∃ p0 p1 : F[X],
      p0.natDegree ≤ L.degreeCap ∧
      p1.natDegree ≤ L.degreeCap ∧
      ∀ z ∈ T, L.originalRoot z = p0 + Polynomial.C z * p1 := by
  let p0 := L.base0 + L.locator * q0
  let p1 := L.base1 + L.locator * q1
  have hloc0 : (L.locator * q0).natDegree ≤ L.degreeCap :=
    Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add_left hq0 L.locator.natDegree).trans
        L.locator_degree_add_rootCap)
  have hloc1 : (L.locator * q1).natDegree ≤ L.degreeCap :=
    Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add_left hq1 L.locator.natDegree).trans
        L.locator_degree_add_rootCap)
  have hp0 : p0.natDegree ≤ L.degreeCap :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le L.base0_degree_le hloc0)
  have hp1 : p1.natDegree ≤ L.degreeCap :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le L.base1_degree_le hloc1)
  refine ⟨p0, p1, hp0, hp1, ?_⟩
  intro z hz
  rw [L.root_shape z (howns z hz), halign z hz]
  dsimp [p0, p1]
  ring
noncomputable def CoreTransformedTagInput.affineRootLift
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) : AffineRootLift D.toTag := {
  originalRoot := D.originalRoot
  degreeCap := 131071
  base0 := D.base0
  base1 := D.base1
  locator := D.locator
  base0_degree_le := D.base0_degree_le
  base1_degree_le := D.base1_degree_le
  locator_degree_add_rootCap := D.locator_degree_add_cap
  root_shape := fun z hz ↦ D.quotient_shape D.center z hz
}
noncomputable def OrdinaryTagInput.affineRootLift
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) : AffineRootLift D.toTag := {
  originalRoot := D.root
  degreeCap := 131071
  base0 := 0
  base1 := 0
  locator := 1
  base0_degree_le := by simp
  base1_degree_le := by simp
  locator_degree_add_rootCap := by
    change (1 : F[X]).natDegree + 131071 ≤ 131071
    simp
  root_shape := by simp
}
noncomputable def mixedAffineRootLift
    {F A B : Type} [Field F] [Fintype F]
    (high : A → CoreTransformedTagInput F)
    (low : B → OrdinaryTagInput F) :
    ∀ i, AffineRootLift (mixedUniversalTag high low i)
  | Sum.inl a => CoreTransformedTagInput.affineRootLift (high a)
  | Sum.inr b => OrdinaryTagInput.affineRootLift (low b)
noncomputable def AffineRootLift.quotientReceived0
    {F I : Type} [Field F]
    {tag : TransformedUniversalTag F}
    (L : AffineRootLift tag) (domain : I → F) (u0 : I → F)
    (i : I) : F :=
  (u0 i - L.base0.eval (domain i)) / L.locator.eval (domain i)
noncomputable def AffineRootLift.quotientReceived1
    {F I : Type} [Field F]
    {tag : TransformedUniversalTag F}
    (L : AffineRootLift tag) (domain : I → F) (u1 : I → F)
    (i : I) : F :=
  (u1 i - L.base1.eval (domain i)) / L.locator.eval (domain i)
theorem AffineRootLift.storedRoot_agree_of_original
    {F I : Type} [Field F]
    {tag : TransformedUniversalTag F}
    (L : AffineRootLift tag) (domain : I → F)
    (u0 u1 : I → F) (z : F) (i : I)
    (hz : tag.owns z) (hlocator : L.locator.eval (domain i) ≠ 0)
    (hagree : (L.originalRoot z).eval (domain i) = u0 i + z * u1 i) :
    (tag.root z).eval (domain i) =
      L.quotientReceived0 domain u0 i +
        z * L.quotientReceived1 domain u1 i := by
  have hshape := congrArg (Polynomial.eval (domain i)) (L.root_shape z hz)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      at hshape
  rw [hagree] at hshape
  dsimp [AffineRootLift.quotientReceived0,
    AffineRootLift.quotientReceived1]
  field_simp
  linear_combination -1 * hshape
theorem ExplicitInnerData.exists_universalSelectedData
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag)
    [Fact (Irreducible D.inner)] [Fact (0 < D.inner.natDegree)]
    (T : Finset F) (hT : T.Nonempty)
    (howns : ∀ z ∈ T, tag.owns z)
    (DX : Nat) :
    ∃ hzeta : HenselNumerators.zeta
        tag.transformed tag.center D.inner ≠ 0,
      ∃ S : UniversalSelectedHenselData
        tag.center tag.transformed D.inner D.henselSetup hzeta
        D.supportCap tag.transformed.natDegree tag.rootDegreeCap DX
        T (fun z : T ↦ tag.root z),
        ∀ z : T, SelectedNonpoleData tag.center tag.transformed D.inner
          D.henselSetup (z : F) (S.root z) tag.center
            ((tag.root z).eval tag.center) := by
  let P : T → F[X] := fun z ↦ tag.root z
  have hfactor : ∀ z : T,
      Polynomial.evalEval (z : F) ((P z).eval tag.center) D.inner = 0 := by
    intro z
    exact (eval_map_eval_eq_eval_eval_C D.inner
      ((P z).eval tag.center) (z : F)).symm.trans
        (D.owner_root (z : F) (howns z z.property))
  let root : ∀ z : T, rationalRoot (monicize D.inner) (z : F) :=
    fun z ↦ rationalRootOfPair D.inner (Fact.out : 0 < D.inner.natDegree)
      (z : F) ((P z).eval tag.center) (hfactor z)
  have hx : ∀ z : T, GoodAt (z : F) (root z)
      (fieldTo𝕃 (H := D.inner) tag.center) tag.center := fun z ↦
    GoodAt.fieldTo𝕃 (H := D.inner) (z : F) (root z) tag.center
  have hy : ∀ z : T, GoodAt (z : F) (root z)
      (initialValue (H := D.inner)) ((P z).eval tag.center) := by
    intro z
    have hTval : GoodAt (z : F) (root z)
        (functionFieldT (H := D.inner))
        (D.inner.leadingCoeff.eval (z : F) * (P z).eval tag.center) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize D.inner}) Polynomial.X,
        1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using
          (piZ_mk_X_rationalRootOfPair D.inner
            (Fact.out : 0 < D.inner.natDegree) (z : F)
            ((P z).eval tag.center) (hfactor z)).symm
    have hWgood := GoodAt.liftToFunctionField (H := D.inner)
      (z : F) (root z) D.inner.leadingCoeff
    simpa [initialValue,
      mul_div_cancel_left₀ _ (D.owner_leadingCoeff_ne_zero
        (z : F) (howns z z.property))] using
      GoodAt.div hTval hWgood
        (D.owner_leadingCoeff_ne_zero (z : F) (howns z z.property))
  let z0 : T := ⟨Classical.choose hT, Classical.choose_spec hT⟩
  have hzeta : HenselNumerators.zeta
      tag.transformed tag.center D.inner ≠ 0 :=
    zeta_ne_zero_of_selected_slope tag.center tag.transformed (z0 : F)
      (root z0) tag.center ((P z0).eval tag.center)
      (hx z0) (hy z0) (tag.simple_root (z0 : F) (howns z0 z0.property)).2
  have hNP : ∀ z : T, SelectedNonpoleData
      tag.center tag.transformed D.inner D.henselSetup
        (z : F) (root z) tag.center ((P z).eval tag.center) := by
    intro z
    exact selectedNonpoleData tag.center tag.transformed D.henselSetup hzeta
      (z : F) (root z) tag.center ((P z).eval tag.center)
      (hx z) (hy z)
      (D.owner_leadingCoeff_ne_zero (z : F) (howns z z.property))
      (tag.simple_root (z : F) (howns z z.property)).2
  have hExact : ∀ z : T,
      (triSpecializeZ tag.transformed (z : F)).eval (P z) = 0 := by
    intro z
    simpa [P, triEval_eq_eval_triSpecializeZ] using
      tag.exact_root (z : F) (howns z z.property)
  let S : UniversalSelectedHenselData
      tag.center tag.transformed D.inner D.henselSetup hzeta
      D.supportCap tag.transformed.natDegree tag.rootDegreeCap DX
      T P := {
    root := root
    hx := hx
    hy := hy
    hsL := (hNP z0).hsL
    hsimple := fun z ↦ tag.simple_root (z : F) (howns z z.property)
    hExact := hExact
    hslope := fun z ↦ (hNP z).hslope
    hW := fun z ↦
      D.owner_leadingCoeff_ne_zero (z : F) (howns z z.property)
    hxi := fun z ↦ (hNP z).hxi }
  exact ⟨hzeta, S, hNP⟩
noncomputable def ExplicitInnerData.resultantCapacity
    {F : Type} [Field F]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag) (E : Nat) : Nat :=
  D.inner.natDegree * (E * D.supportCap) +
    (E * tag.source.natDegree) * Polynomial.Bivariate.degreeX D.inner
theorem ExplicitInnerData.concrete_resultant_natDegree_le
    {F : Type} [Field F]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag)
    (hk : 0 < tag.rootDegreeCap) (hD : 0 < D.supportCap)
    (dx u0 u1 : F) :
    let E := FiniteHenselWeight.denominatorExponent tag.rootDegreeCap
    (Polynomial.resultant
      (concreteUniversalAffineObstruction tag.center tag.transformed
        E tag.rootDegreeCap dx u0 u1)
      D.inner
      (concreteUniversalAffineObstruction tag.center tag.transformed
        E tag.rootDegreeCap dx u0 u1).natDegree
      D.inner.natDegree).natDegree ≤
        ExplicitInnerData.resultantCapacity D E := by
  dsimp only
  let E := FiniteHenselWeight.denominatorExponent tag.rootDegreeCap
  let B := concreteUniversalAffineObstruction tag.center tag.transformed
    E tag.rootDegreeCap dx u0 u1
  have hsourcePos : 0 < tag.source.natDegree :=
    D.inner_degree_pos.trans_le
      ((Polynomial.natDegree_le_of_dvd D.inner_dvd tag.primitive.ne_zero).trans
        tag.specializeDegree_le_source)
  have htransformedPos : 0 < tag.transformed.natDegree := by
    rw [tag.outerDegree_preserved]
    exact hsourcePos
  have hcaps : B.natDegree ≤ E * tag.source.natDegree ∧
      Polynomial.Bivariate.degreeX B ≤ E * D.supportCap := by
    exact concreteUniversalAffineObstruction_degree_bounds
      tag.center tag.transformed E tag.rootDegreeCap
        tag.source.natDegree D.supportCap dx u0 u1 rfl hk hsourcePos hD
        htransformedPos (by rw [tag.outerDegree_preserved])
        D.transformed_YZCap
  calc
    (Polynomial.resultant B D.inner B.natDegree D.inner.natDegree).natDegree
        ≤ D.inner.natDegree * Polynomial.Bivariate.degreeX B +
          B.natDegree * Polynomial.Bivariate.degreeX D.inner :=
      bivariate_resultant_natDegree_le B D.inner
        B.natDegree D.inner.natDegree
    _ ≤ D.inner.natDegree * (E * D.supportCap) +
        (E * tag.source.natDegree) *
          Polynomial.Bivariate.degreeX D.inner := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left D.inner.natDegree hcaps.2)
        (Nat.mul_le_mul_right
          (Polynomial.Bivariate.degreeX D.inner) hcaps.1)
    _ = ExplicitInnerData.resultantCapacity D E := rfl
theorem ExplicitInnerData.exists_storedRoot_affine_alignment
    {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag)
    [Fact (Irreducible D.inner)] [Fact (0 < D.inner.natDegree)]
    (U : Finset I) (domain : I → F) (hdomain : Function.Injective domain)
    (T : Finset F) (Arow : F → Finset I)
    (u0 u1 : I → F) (rowLower errors : Nat)
    (hk : 0 < tag.rootDegreeCap) (hD : 0 < D.supportCap)
    (hkF : tag.rootDegreeCap < Fintype.card F)
    (hrowLower : rowLower ≤ U.card)
    (hgap : 0 < rowLower - tag.rootDegreeCap)
    (hrow : ∀ z ∈ T, rowLower ≤
      (U.attach.filter fun i : U ↦ (i : I) ∈ Arow z).card)
    (howns : ∀ z ∈ T, tag.owns z)
    (hagree : ∀ z ∈ T, ∀ i ∈ U, i ∈ Arow z →
      (tag.root z).eval (domain i) = u0 i + z * u1 i)
    (hcapacity :
      ((U.card - tag.rootDegreeCap) *
          ExplicitInnerData.resultantCapacity D
            (FiniteHenselWeight.denominatorExponent tag.rootDegreeCap)) /
          (rowLower - tag.rootDegreeCap) + (errors + 1) < T.card) :
    ∃ q0 q1 : F[X],
      q0.natDegree ≤ tag.rootDegreeCap ∧
      q1.natDegree ≤ tag.rootDegreeCap ∧
      ∀ z ∈ T, tag.root z = q0 + Polynomial.C z * q1 := by
  classical
  let E := FiniteHenselWeight.denominatorExponent tag.rootDegreeCap
  let cap := ExplicitInnerData.resultantCapacity D E
  let B : I → F[X][Y] := fun i ↦
    concreteUniversalAffineObstruction tag.center tag.transformed
      E tag.rootDegreeCap (domain i - tag.center) (u0 i) (u1 i)
  let Res : I → F[X] := fun i ↦
    Polynomial.resultant (B i) D.inner (B i).natDegree D.inner.natDegree
  have hscaled :
      (U.card - tag.rootDegreeCap) * cap <
          (rowLower - tag.rootDegreeCap) * T.card ∧
        errors + 1 < T.card := by
    exact scaled_pair_capacity_implies_incidence
      (U.card - tag.rootDegreeCap) (rowLower - tag.rootDegreeCap)
      cap errors T.card hgap (by simpa [cap, E] using hcapacity)
  have hResdegree : ∀ i ∈ U, (Res i).natDegree ≤ cap := by
    intro i hi
    simpa [Res, B, cap, E] using
      ExplicitInnerData.concrete_resultant_natDegree_le D hk hD
        (domain i - tag.center) (u0 i) (u1 i)
  have hBroot : ∀ i ∈ U, ∀ z ∈ T, i ∈ Arow z →
      biEval (B i) ((tag.root z).eval tag.center) z = 0 := by
    intro i hi z hzT hirow
    apply biEval_concreteUniversalAffineObstruction_eq_zero
      tag.center z ((tag.root z).eval tag.center)
      tag.transformed (tag.root z) E tag.rootDegreeCap
      (domain i - tag.center) (u0 i) (u1 i)
    · rfl
    · have hsourcePos : 0 < tag.source.natDegree :=
        D.inner_degree_pos.trans_le
          ((Polynomial.natDegree_le_of_dvd
            D.inner_dvd tag.primitive.ne_zero).trans
              tag.specializeDegree_le_source)
      rw [tag.outerDegree_preserved]
      exact hsourcePos
    · rfl
    · exact tag.root_degree_le z (howns z hzT)
    · simpa [triEval_eq_eval_triSpecializeZ] using
        tag.exact_root z (howns z hzT)
    · exact (tag.simple_root z (howns z hzT)).2
    · rw [show tag.center + (domain i - tag.center) = domain i by ring]
      exact hagree z hzT i hi hirow
  have hResroot : ∀ i ∈ U, ∀ z ∈ T, i ∈ Arow z →
      (Res i).eval z = 0 := by
    intro i hi z hzT hirow
    have hsize : 0 < (B i).natDegree + D.inner.natDegree :=
      Nat.add_pos_right _ D.inner_degree_pos
    exact bivariate_resultant_eval_eq_zero_of_common_root
      (B i) D.inner (B i).natDegree D.inner.natDegree z
      ((tag.root z).eval tag.center)
      Polynomial.natDegree_map_le Polynomial.natDegree_map_le hsize
      (hBroot i hi z hzT hirow) (D.owner_root z (howns z hzT))
  obtain ⟨Coord, hCoordCard, hReszero⟩ :=
    exists_zero_obstruction_core_in_ambient
      U T Arow rowLower tag.rootDegreeCap cap Res hrowLower hrow
      hscaled.1 hResdegree hResroot
  have hdiv : ∀ i ∈ Coord, D.inner ∣ B (i : I) := by
    intro i hi
    apply irreducible_dvd_of_resultant_eq_zero_nonmonic
      (B (i : I)) D.inner (Fact.out : Irreducible D.inner)
        (Fact.out : 0 < D.inner.natDegree)
    simpa [Res] using hReszero i hi
  have hTnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hzeta, Sel, hNP⟩ :=
    ExplicitInnerData.exists_universalSelectedData D T hTnonempty howns
      (tag.rootDegreeCap + 1)
  let embedCoord : U → F := fun i ↦ domain (i : I)
  let Afield : Finset F := Coord.image embedCoord
  have hAfield : tag.rootDegreeCap + 1 ≤ Afield.card := by
    have hinj : Set.InjOn embedCoord
        (↑Coord : Set U) := by
      intro i _hi j _hj hij
      exact Subtype.ext (hdomain hij)
    rw [show Afield.card = Coord.card by
      exact Finset.card_image_of_injOn hinj]
    exact hCoordCard
  let idx : Afield → U := fun x ↦
    Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x : Afield) : idx x ∈ Coord ∧
      domain (idx x : I) = (x : F) :=
    Classical.choose_spec (Finset.mem_image.mp x.property)
  let U0 : F → F := fun x ↦
    if hxA : x ∈ Afield then u0 (idx ⟨x, hxA⟩ : I) else 0
  let U1 : F → F := fun x ↦
    if hxA : x ∈ Afield then u1 (idx ⟨x, hxA⟩ : I) else 0
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
  have hzero : ∀ x ∈ Afield,
      Polynomial.eval₂ (liftToFunctionField (H := D.inner))
        (initialValue (H := D.inner))
          (universalAffineObstruction
            (universalRootedNumerators tag.center tag.transformed)
            (universalSlope tag.center tag.transformed) E
            tag.rootDegreeCap (x - tag.center) (U0 x) (U1 x)) = 0 := by
    intro x hxA
    let xx : Afield := ⟨x, hxA⟩
    have hdvd := hdiv (idx xx) (hidx xx).1
    have heval := eval₂_lift_initialValue_eq_zero_of_dvd
      (B (idx xx : I)) D.inner hdvd
    have hxeq : domain (idx xx : I) = x := (hidx xx).2
    simpa [B, concreteUniversalAffineObstruction, U0, U1, hxA, xx,
      hxeq, E] using heval
  obtain ⟨q0, q1, hq0, hq1, halign⟩ :=
    universal_selected_pair_alignment_core_light
      tag.center tag.transformed D.henselSetup hzeta
      D.supportCap tag.transformed.natDegree tag.rootDegreeCap
      (tag.rootDegreeCap + 1) (Nat.lt_succ_self _)
      T (fun z : T ↦ tag.root z) Sel hNP
      (fun z ↦ tag.root_degree_le (z : F) (howns z z.property))
      hkF Afield hAfield U0 U1
      (universalRootedNumerators tag.center tag.transformed)
      (universalSlope tag.center tag.transformed) E rfl hslope hnum hzero
  refine ⟨q0, q1, hq0, hq1, ?_⟩
  intro z hz
  exact halign ⟨z, hz⟩
theorem ExplicitInnerData.exists_originalRoot_affine_alignment
    {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag) (L : AffineRootLift tag)
    [Fact (Irreducible D.inner)] [Fact (0 < D.inner.natDegree)]
    (U : Finset I) (domain : I → F) (hdomain : Function.Injective domain)
    (T : Finset F) (Arow : F → Finset I)
    (u0 u1 : I → F) (rowLower errors : Nat)
    (hk : 0 < tag.rootDegreeCap) (hD : 0 < D.supportCap)
    (hkF : tag.rootDegreeCap < Fintype.card F)
    (hrowLower : rowLower ≤ U.card)
    (hgap : 0 < rowLower - tag.rootDegreeCap)
    (hrow : ∀ z ∈ T, rowLower ≤
      (U.attach.filter fun i : U ↦ (i : I) ∈ Arow z).card)
    (howns : ∀ z ∈ T, tag.owns z)
    (hagree : ∀ z ∈ T, ∀ i ∈ U, i ∈ Arow z →
      (tag.root z).eval (domain i) = u0 i + z * u1 i)
    (hcapacity :
      ((U.card - tag.rootDegreeCap) *
          ExplicitInnerData.resultantCapacity D
            (FiniteHenselWeight.denominatorExponent tag.rootDegreeCap)) /
          (rowLower - tag.rootDegreeCap) + (errors + 1) < T.card) :
    ∃ p0 p1 : F[X],
      p0.natDegree ≤ L.degreeCap ∧
      p1.natDegree ≤ L.degreeCap ∧
      ∀ z ∈ T, L.originalRoot z = p0 + Polynomial.C z * p1 := by
  obtain ⟨q0, q1, hq0, hq1, halign⟩ :=
    ExplicitInnerData.exists_storedRoot_affine_alignment
      D U domain hdomain T Arow u0 u1 rowLower errors hk hD hkF
        hrowLower hgap hrow howns hagree hcapacity
  exact L.lift_alignment T q0 q1 hq0 hq1 howns halign
theorem scaledFloor_mono_target
    (ambient row small large cap : Nat)
    (hsmall : small ≤ large) (hlarge : large < row)
    (hrow : row ≤ ambient) :
    ((ambient - small) * cap) / (row - small) ≤
      ((ambient - large) * cap) / (row - large) := by
  have hsmallRow : small < row := hsmall.trans_lt hlarge
  have hsmallDen : 0 < row - small := Nat.sub_pos_of_lt hsmallRow
  have hlargeDen : 0 < row - large := Nat.sub_pos_of_lt hlarge
  let q := ((ambient - small) * cap) / (row - small)
  have hqmul : q * (row - small) ≤ (ambient - small) * cap := by
    exact Nat.div_mul_le_self _ _
  have hcross :
      ((ambient - small) * cap) * (row - large) ≤
        ((ambient - large) * cap) * (row - small) := by
    have hUs : ambient - small =
        (ambient - large) + (large - small) := by omega
    have hRs : row - small = (row - large) + (large - small) := by omega
    have hUl : ambient - large =
        (row - large) + (ambient - row) := by omega
    rw [hUs, hRs, hUl]
    calc
      ((row - large + (ambient - row) + (large - small)) * cap) *
            (row - large) ≤
          ((row - large + (ambient - row) + (large - small)) * cap) *
              (row - large) +
            (ambient - row) * (large - small) * cap :=
        Nat.le_add_right _ _
      _ = ((row - large + (ambient - row)) * cap) *
          (row - large + (large - small)) := by ring
  have hqcross :
      (q * (row - large)) * (row - small) ≤
        (((ambient - large) * cap) * (row - small)) := by
    calc
      (q * (row - large)) * (row - small) =
          (q * (row - small)) * (row - large) := by ring
      _ ≤ ((ambient - small) * cap) * (row - large) :=
        Nat.mul_le_mul_right (row - large) hqmul
      _ ≤ ((ambient - large) * cap) * (row - small) := hcross
  have hqle : q * (row - large) ≤ (ambient - large) * cap :=
    Nat.le_of_mul_le_mul_right hqcross hsmallDen
  exact (Nat.le_div_iff_mul_le hlargeDen).2 hqle
theorem explicitInnerPairs_fst_mem
    {F A : Type} [Field F] [DecidableEq A]
    (Outer : Finset A) (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a))
    (p : A × F[X][Y])
    (hp : p ∈ explicitInnerPairs Outer tag data) : p.1 ∈ Outer := by
  classical
  change p ∈ Outer.image (fun a ↦ (a, (data a).inner)) at hp
  obtain ⟨a, ha, hpair⟩ :=
    (@Finset.mem_image A (A × F[X][Y]) inferInstance
      (fun a ↦ (a, (data a).inner)) Outer p).mp hp
  have hfst : a = p.1 := congrArg Prod.fst hpair
  simpa only [hfst] using ha
theorem explicitInnerPairs_snd_eq
    {F A : Type} [Field F] [DecidableEq A]
    (Outer : Finset A) (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a))
    (p : A × F[X][Y])
    (hp : p ∈ explicitInnerPairs Outer tag data) :
    p.2 = (data p.1).inner := by
  classical
  change p ∈ Outer.image (fun a ↦ (a, (data a).inner)) at hp
  obtain ⟨a, _ha, hpair⟩ :=
    (@Finset.mem_image A (A × F[X][Y]) inferInstance
      (fun a ↦ (a, (data a).inner)) Outer p).mp hp
  have hfst : a = p.1 := congrArg Prod.fst hpair
  have hsnd : (data a).inner = p.2 := congrArg Prod.snd hpair
  rw [hfst] at hsnd
  exact hsnd.symm
structure GlobalSelectorData
    (F A : Type) [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq A] where
  S : Finset F
  quotientBad : Finset F
  outer : Finset A
  outerBad : A → Finset F
  tag : A → TransformedUniversalTag F
  data : ∀ a, ExplicitInnerData (tag a)
  exponent : A → Nat
  exponent_eq : ∀ a, exponent a =
    FiniteHenselWeight.denominatorExponent (tag a).rootDegreeCap
  coordinateCount : Nat
  commonTarget : Nat
  rowLower : Nat
  errors : Nat
  quotientBadCap : Nat
  outerBadCap : Nat
  resultCap : Nat
  pairCap : Nat
  fusedCap : Nat
  quotientBad_card : quotientBad.card ≤ quotientBadCap
  outerBad_sum : (∑ a ∈ outer, (outerBad a).card) ≤ outerBadCap
  tagCharge :
    (∑ a ∈ outer,
      2 * exponent a * (tag a).source.natDegree *
        (data a).supportCap) ≤ resultCap
  sourceMass : (∑ a ∈ outer, (tag a).source.natDegree) ≤ pairCap
  fused : (coordinateCount - commonTarget) * resultCap ≤
    (rowLower - commonTarget) * fusedCap
  cover : ∀ z ∈ S \ (quotientBad ∪ outer.biUnion outerBad),
    ∃ a ∈ outer, (tag a).owns z
  large : quotientBadCap + outerBadCap +
    (fusedCap + (errors + 1) * pairCap) < S.card
structure SelectedExplicitPairFiber
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq A]
    (G : GlobalSelectorData F A) where
  pair : A × F[X][Y]
  pair_mem : pair ∈ explicitInnerPairs G.outer G.tag G.data
  fiber : Finset F
  fiber_subset : fiber ⊆ G.S
  pair_relation : ∀ z ∈ fiber, pairRel G.tag z pair
  common_capacity :
    ((G.coordinateCount - G.commonTarget) *
        explicitPairResultantCapacity G.tag G.data G.exponent pair) /
        (G.rowLower - G.commonTarget) + (G.errors + 1) < fiber.card
theorem SelectedExplicitPairFiber.owns
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq A] {G : GlobalSelectorData F A}
    (W : SelectedExplicitPairFiber G) (z : F) (hz : z ∈ W.fiber) :
    (G.tag W.pair.1).owns z := by
  have hrel := (W.pair_relation z hz).1
  exact hrel
theorem GlobalSelectorData.exists_selectedExplicitPairFiber
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq A]
    (G : GlobalSelectorData F A) :
    Nonempty (SelectedExplicitPairFiber G) := by
  classical
  letI : DecidableRel (pairRel G.tag) :=
    fun _z _p ↦ Classical.propDecidable _
  obtain ⟨p, hp, hpfiber⟩ :=
    exists_explicit_pair_fiber_of_self_capacity_ledger
      G.S G.quotientBad G.outer G.outerBad G.tag G.data G.exponent
      (G.coordinateCount - G.commonTarget)
      (G.rowLower - G.commonTarget) G.errors
      G.quotientBadCap G.outerBadCap G.resultCap G.pairCap G.fusedCap
      G.quotientBad_card G.outerBad_sum G.tagCharge G.sourceMass G.fused
      G.cover G.large
  let T : Finset F :=
    (G.S \ (G.quotientBad ∪ G.outer.biUnion G.outerBad)).filter
      fun z ↦ pairRel G.tag z p
  have hTsub : T ⊆ G.S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hrel : ∀ z ∈ T, pairRel G.tag z p := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hcapacity :
      ((G.coordinateCount - G.commonTarget) *
          explicitPairResultantCapacity G.tag G.data G.exponent p) /
          (G.rowLower - G.commonTarget) + (G.errors + 1) < T.card := by
    simpa only [T] using hpfiber
  exact ⟨⟨p, hp, T, hTsub, hrel, hcapacity⟩⟩
structure GlobalAlignmentData
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq A]
    (G : GlobalSelectorData F A)
    (I : Type) [Fintype I] [DecidableEq I] where
  lift : ∀ a, AffineRootLift (G.tag a)
  coords : Finset I
  domain : I → F
  domain_injective : Function.Injective domain
  agreementRows : F → Finset I
  received0 : I → F
  received1 : I → F
  coordinate_card : G.coordinateCount = coords.card
  rowLower_le : G.rowLower ≤ coords.card
  commonTarget_lt : G.commonTarget < G.rowLower
  row_large : ∀ z ∈ G.S, G.rowLower ≤
    (coords.attach.filter fun i : coords ↦
      (i : I) ∈ agreementRows z).card
  root_caps : ∀ a ∈ G.outer,
    0 < (G.tag a).rootDegreeCap ∧
    (G.tag a).rootDegreeCap ≤ G.commonTarget ∧
    (G.tag a).rootDegreeCap < Fintype.card F
  support_caps : ∀ a ∈ G.outer, 0 < (G.data a).supportCap
  locator_nonzero : ∀ a ∈ G.outer, ∀ i ∈ coords,
    (lift a).locator.eval (domain i) ≠ 0
  original_agrees : ∀ a ∈ G.outer, ∀ z ∈ G.S,
    (G.tag a).owns z → ∀ i ∈ agreementRows z,
      ((lift a).originalRoot z).eval (domain i) =
        received0 i + z * received1 i
theorem SelectedExplicitPairFiber.exists_originalRoot_affine_alignment
    {F I A : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I] [DecidableEq A]
    {G : GlobalSelectorData F A}
    (W : SelectedExplicitPairFiber G)
    (C : GlobalAlignmentData G I) :
    ∃ p0 p1 : F[X],
      p0.natDegree ≤ (C.lift W.pair.1).degreeCap ∧
      p1.natDegree ≤ (C.lift W.pair.1).degreeCap ∧
      ∀ z ∈ W.fiber,
        (C.lift W.pair.1).originalRoot z =
          p0 + Polynomial.C z * p1 := by
  classical
  let a := W.pair.1
  let tag := G.tag a
  let D := G.data a
  let L := C.lift a
  let qu0 : I → F := fun i ↦ L.quotientReceived0 C.domain C.received0 i
  let qu1 : I → F := fun i ↦ L.quotientReceived1 C.domain C.received1 i
  have ha : a ∈ G.outer := by
    simpa only [a] using
      explicitInnerPairs_fst_mem G.outer G.tag G.data W.pair W.pair_mem
  have hinner : W.pair.2 = (G.data a).inner := by
    simpa only [a] using
      explicitInnerPairs_snd_eq G.outer G.tag G.data W.pair W.pair_mem
  have hlocalFloor :
      ((C.coords.card - tag.rootDegreeCap) *
          ExplicitInnerData.resultantCapacity D
            (FiniteHenselWeight.denominatorExponent tag.rootDegreeCap)) /
          (G.rowLower - tag.rootDegreeCap) ≤
        ((C.coords.card - G.commonTarget) *
          ExplicitInnerData.resultantCapacity D
            (FiniteHenselWeight.denominatorExponent tag.rootDegreeCap)) /
          (G.rowLower - G.commonTarget) := by
    exact scaledFloor_mono_target C.coords.card G.rowLower
      tag.rootDegreeCap G.commonTarget
      (ExplicitInnerData.resultantCapacity D
        (FiniteHenselWeight.denominatorExponent tag.rootDegreeCap))
      (C.root_caps a ha).2.1 C.commonTarget_lt C.rowLower_le
  have hcommonCapacity :
      ((C.coords.card - G.commonTarget) *
          ExplicitInnerData.resultantCapacity D
            (FiniteHenselWeight.denominatorExponent tag.rootDegreeCap)) /
          (G.rowLower - G.commonTarget) + (G.errors + 1) < W.fiber.card := by
    have hcapEq :
        explicitPairResultantCapacity G.tag G.data G.exponent
            (a, (G.data a).inner) =
          ExplicitInnerData.resultantCapacity (G.data a)
            (FiniteHenselWeight.denominatorExponent
              (G.tag a).rootDegreeCap) := by
      unfold explicitPairResultantCapacity
      unfold ExplicitInnerData.resultantCapacity
      rw [G.exponent_eq]
    have hpairEq : W.pair = (a, (G.data a).inner) := by
      apply Prod.ext
      · rfl
      · exact hinner
    have hW := W.common_capacity
    rw [hpairEq, C.coordinate_card, hcapEq] at hW
    simpa only [a, tag, D] using hW
  have hlocalCapacity :
      ((C.coords.card - tag.rootDegreeCap) *
          ExplicitInnerData.resultantCapacity D
            (FiniteHenselWeight.denominatorExponent tag.rootDegreeCap)) /
          (G.rowLower - tag.rootDegreeCap) + (G.errors + 1) < W.fiber.card :=
    (Nat.add_le_add_right hlocalFloor (G.errors + 1)).trans_lt
      hcommonCapacity
  have hquotientAgree : ∀ z ∈ W.fiber, ∀ i ∈ C.coords,
      i ∈ C.agreementRows z →
      (tag.root z).eval (C.domain i) = qu0 i + z * qu1 i := by
    intro z hz i hiU hi
    exact L.storedRoot_agree_of_original
      C.domain C.received0 C.received1 z i (W.owns z hz)
      (C.locator_nonzero a ha i hiU)
      (C.original_agrees a ha z (W.fiber_subset hz)
        (W.owns z hz) i hi)
  have hrow : ∀ z ∈ W.fiber, G.rowLower ≤
      (C.coords.attach.filter fun i : C.coords ↦
        (i : I) ∈ C.agreementRows z).card := by
    intro z hz
    exact C.row_large z (W.fiber_subset hz)
  letI : Fact (Irreducible D.inner) := ⟨D.inner_irreducible⟩
  letI : Fact (0 < D.inner.natDegree) := ⟨D.inner_degree_pos⟩
  exact ExplicitInnerData.exists_originalRoot_affine_alignment
    D L C.coords C.domain C.domain_injective W.fiber C.agreementRows
    qu0 qu1 G.rowLower G.errors
    (C.root_caps a ha).1 (C.support_caps a ha)
    (C.root_caps a ha).2.2 C.rowLower_le
    (Nat.sub_pos_of_lt
      ((C.root_caps a ha).2.1.trans_lt C.commonTarget_lt))
    hrow W.owns hquotientAgree hlocalCapacity
theorem exists_originalRoot_affine_alignment_of_global_selector
    {F I A : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I] [DecidableEq A]
    (G : GlobalSelectorData F A) (C : GlobalAlignmentData G I) :
    ∃ a ∈ G.outer, ∃ T : Finset F,
      T ⊆ G.S ∧ G.errors + 1 < T.card ∧
      ∃ p0 p1 : F[X],
        p0.natDegree ≤ (C.lift a).degreeCap ∧
        p1.natDegree ≤ (C.lift a).degreeCap ∧
        ∀ z ∈ T,
          (C.lift a).originalRoot z = p0 + Polynomial.C z * p1 := by
  classical
  let W := Classical.choice G.exists_selectedExplicitPairFiber
  obtain ⟨p0, p1, hp0, hp1, halign⟩ :=
    W.exists_originalRoot_affine_alignment C
  have hcard : G.errors + 1 < W.fiber.card :=
    (Nat.le_add_left (G.errors + 1) _).trans_lt W.common_capacity
  have ha : W.pair.1 ∈ G.outer :=
    explicitInnerPairs_fst_mem G.outer G.tag G.data W.pair W.pair_mem
  exact ⟨W.pair.1, ha, W.fiber, W.fiber_subset, hcard,
    p0, p1, hp0, hp1, halign⟩
end BCHKSExplicitPairAlignment6400
end ProximityPrize.SubmissionLower
