import ProximityPrize.SubmissionLower.BCHKSLocatorRankOneResultantFibers6400

/-!
# Recursive two-axis factor descent

Once a positive factor is common to the homogeneous and affine lanes, it can
be divided out.  Fibres where that factor specializes to zero are discarded.
The number discarded is paid for exactly by the degree removed, yielding
stable owner- and coordinate-cardinality invariants for recursion.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRecursiveTwoAxisDescent6400

open Polynomial
open Polynomial.Bivariate
open BCHKSResultantMultiplicity6400
open BCHKSTwoAxisResultant6400
open BCHKSCommonFactorDescent6400
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

def recursiveOwnerBase : Nat := ownerFloor - affineChallengeCap
def recursiveCoordinateBase : Nat :=
  coordinateCount - homogeneousLocatorCap

/-- The production inequality retains its large strict margin after all
possible recursive specialization losses have been charged. -/
theorem recursive_reverse_elimination
    (d n u : Nat)
    (hd : d ≤ homogeneousLocatorCap)
    (hn : n ≤ affineLocatorCap)
    (hu : u ≤ affineChallengeCap) :
    u * (n + d) <
      recursiveOwnerBase * (recursiveCoordinateBase - n) := by
  have hleft : u * (n + d) ≤
      affineChallengeCap * (affineLocatorCap + homogeneousLocatorCap) :=
    Nat.mul_le_mul hu (Nat.add_le_add hn hd)
  have hfixed :
      affineChallengeCap * (affineLocatorCap + homogeneousLocatorCap) <
        recursiveOwnerBase *
          (recursiveCoordinateBase - affineLocatorCap) := by
    norm_num [recursiveOwnerBase, recursiveCoordinateBase, ownerFloor,
      affineChallengeCap, affineLocatorCap, coordinateCount,
      homogeneousLocatorCap]
  have hright :
      recursiveOwnerBase *
          (recursiveCoordinateBase - affineLocatorCap) ≤
        recursiveOwnerBase * (recursiveCoordinateBase - n) := by
    apply Nat.mul_le_mul_left
    norm_num [recursiveCoordinateBase, affineLocatorCap,
      coordinateCount, homogeneousLocatorCap] at hn ⊢
    omega
  exact hleft.trans_lt (hfixed.trans_le hright)

/-- Dynamic-cardinality form of the production resultant dichotomy.  The
cardinality hypotheses are precisely the invariants preserved by quotienting
and filtering zero specializations. -/
theorem recursive_resultant_zero_dichotomy
    {F ι κ : Type} [Field F]
    [DecidableEq F] [DecidableEq ι] [DecidableEq κ]
    (H C : F[X][X])
    (Owners : Finset ι) (owner : ι ↪ F)
    (Coords : Finset κ) (coord : κ ↪ F)
    (d t n u : Nat)
    (hH : H ≠ 0)
    (hHY : H.natDegree = d)
    (hHX : degreeX H = t)
    (hCY : C.natDegree = n)
    (hCX : degreeX C = u)
    (hd : 0 < d)
    (hdcap : d ≤ homogeneousLocatorCap)
    (hncap : n ≤ affineLocatorCap)
    (hucap : u ≤ affineChallengeCap)
    (hOwners : recursiveOwnerBase + u ≤ Owners.card)
    (hCoords : recursiveCoordinateBase + d ≤ Coords.card)
    (howner : ∀ i ∈ Owners,
      H.map (Polynomial.evalRingHom (owner i)) ∣
        C.map (Polynomial.evalRingHom (owner i)))
    (hcoord : ∀ i ∈ Coords,
      (swap H).map (Polynomial.evalRingHom (coord i)) ∣
        (swap C).map (Polynomial.evalRingHom (coord i))) :
    Polynomial.resultant H C d n = 0 ∨
      Polynomial.resultant (swap H) (swap C) t u = 0 := by
  by_contra hboth
  push Not at hboth
  have hbounds := twoAxis_multiplicity_bounds
    H C Owners owner Coords coord d t n u
    hH hHY hHX hCY.le hCX.le howner hcoord hboth.1 hboth.2
  have hownerBound :
      d * (recursiveOwnerBase + u) ≤
        n * t + d * u + d * t :=
    (Nat.mul_le_mul_left d hOwners).trans hbounds.1
  have hcoordBound :
      t * (recursiveCoordinateBase + d) ≤
        u * d + t * n + t * d :=
    (Nat.mul_le_mul_left t hCoords).trans hbounds.2
  have huG : u ≤ recursiveOwnerBase + u := Nat.le_add_left _ _
  have hnI : n + d ≤ recursiveCoordinateBase + d := by
    apply Nat.add_le_add_right
    norm_num [recursiveCoordinateBase, coordinateCount,
      homogeneousLocatorCap, affineLocatorCap] at hncap ⊢
    omega
  have heliminated := eliminate_transverse_degree
    d t n u (recursiveOwnerBase + u) (recursiveCoordinateBase + d)
    hd huG hnI hownerBound hcoordBound
  have hownerSub : recursiveOwnerBase + u - u = recursiveOwnerBase := by
    omega
  have hcoordSub :
      recursiveCoordinateBase + d - (n + d) =
        recursiveCoordinateBase - n := by
    omega
  rw [hownerSub, hcoordSub] at heliminated
  exact (Nat.not_lt_of_ge heliminated)
    (recursive_reverse_elimination d n u hdcap hncap hucap)

/-- Recursive-scale fibres still force a positive common locator factor. -/
theorem recursive_exists_positiveLocatorCommonFactor
    {F ι κ : Type} [Field F]
    [DecidableEq F] [DecidableEq ι] [DecidableEq κ]
    (H C : F[X][X])
    (Owners : Finset ι) (owner : ι ↪ F)
    (Coords : Finset κ) (coord : κ ↪ F)
    (hHprimitive : H.IsPrimitive)
    (hd : 0 < H.natDegree)
    (hdcap : H.natDegree ≤ homogeneousLocatorCap)
    (hncap : C.natDegree ≤ affineLocatorCap)
    (hucap : degreeX C ≤ affineChallengeCap)
    (hOwners : recursiveOwnerBase + degreeX C ≤ Owners.card)
    (hCoords : recursiveCoordinateBase + H.natDegree ≤ Coords.card)
    (howner : ∀ i ∈ Owners,
      H.map (Polynomial.evalRingHom (owner i)) ∣
        C.map (Polynomial.evalRingHom (owner i)))
    (hcoord : ∀ i ∈ Coords,
      (swap H).map (Polynomial.evalRingHom (coord i)) ∣
        (swap C).map (Polynomial.evalRingHom (coord i))) :
    ∃ D : F[X][X],
      D.IsPrimitive ∧ 0 < D.natDegree ∧ D ∣ H ∧ D ∣ C := by
  rcases recursive_resultant_zero_dichotomy
      H C Owners owner Coords coord
      H.natDegree (degreeX H) C.natDegree (degreeX C)
      hHprimitive.ne_zero rfl rfl rfl rfl hd hdcap hncap hucap
      hOwners hCoords howner hcoord with hOwnerZero | hCoordZero
  · exact exists_integralPrimitiveCommonFactor_of_fixed_resultant_eq_zero
      H C H.natDegree C.natDegree
      hHprimitive.ne_zero rfl le_rfl hOwnerZero
  · exact exists_positiveLocatorCommonFactor_of_swapped_fixed_resultant_eq_zero
      H C (degreeX H) (degreeX C)
      hHprimitive rfl le_rfl hCoordZero

/-- Removing all zero coefficient-specializations of a nonzero bivariate
polynomial costs at most its transverse degree. -/
theorem card_le_filter_bivariate_map_ne_zero_add_degreeX
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    (S : Finset ι) (owner : ι ↪ F)
    (D : F[X][X]) (hD : D ≠ 0) :
    S.card ≤
      (S.filter fun i ↦
        D.map (Polynomial.evalRingHom (owner i)) ≠ 0).card +
          degreeX D := by
  let a : F[X] := D.leadingCoeff
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact Polynomial.leadingCoeff_ne_zero.mpr hD
  let LeadGood : Finset ι := S.filter fun i ↦ a.eval (owner i) ≠ 0
  let Good : Finset ι := S.filter fun i ↦
    D.map (Polynomial.evalRingHom (owner i)) ≠ 0
  have hraw := card_le_filter_eval_ne_zero_add_natDegree S owner a ha
  change S.card ≤ LeadGood.card + a.natDegree at hraw
  have hsubset : LeadGood ⊆ Good := by
    intro i hi
    have hlead : (Polynomial.evalRingHom (owner i)) D.leadingCoeff ≠ 0 := by
      simpa only [Polynomial.coe_evalRingHom, a] using
        (Finset.mem_filter.mp hi).2
    have hmap : D.map (Polynomial.evalRingHom (owner i)) ≠ 0 := by
      rw [← Polynomial.leadingCoeff_ne_zero,
        Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlead]
      exact hlead
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hmap⟩
  have hcard : LeadGood.card ≤ Good.card := Finset.card_le_card hsubset
  have hadegree : a.natDegree ≤ degreeX D := by
    dsimp only [a]
    exact coeff_natDegree_le_degreeX D D.natDegree
  exact hraw.trans (Nat.add_le_add hcard hadegree)

/-- Iterating the recursive dichotomy exhausts the locator degree.  Hence a
primitive factor that divides on every sufficiently numerous owner and
coordinate fibre already divides the affine lane globally. -/
theorem dvd_of_recursive_twoAxis_fibers
    {F ι κ : Type} [Field F]
    [DecidableEq F] [DecidableEq ι] [DecidableEq κ]
    (H C : F[X][X])
    (Owners : Finset ι) (owner : ι ↪ F)
    (Coords : Finset κ) (coord : κ ↪ F)
    (hHprimitive : H.IsPrimitive)
    (hd : 0 < H.natDegree)
    (hdcap : H.natDegree ≤ homogeneousLocatorCap)
    (hncap : C.natDegree ≤ affineLocatorCap)
    (hucap : degreeX C ≤ affineChallengeCap)
    (hOwners : recursiveOwnerBase + degreeX C ≤ Owners.card)
    (hCoords : recursiveCoordinateBase + H.natDegree ≤ Coords.card)
    (howner : ∀ i ∈ Owners,
      H.map (Polynomial.evalRingHom (owner i)) ∣
        C.map (Polynomial.evalRingHom (owner i)))
    (hcoord : ∀ i ∈ Coords,
      (swap H).map (Polynomial.evalRingHom (coord i)) ∣
        (swap C).map (Polynomial.evalRingHom (coord i))) :
    H ∣ C := by
  classical
  by_cases hCzero : C = 0
  · simp only [hCzero, dvd_zero]
  let rec descend
      (H C : F[X][X])
      (Owners : Finset ι) (Coords : Finset κ)
      (hHprimitive : H.IsPrimitive)
      (hd : 0 < H.natDegree)
      (hCne : C ≠ 0)
      (hdcap : H.natDegree ≤ homogeneousLocatorCap)
      (hncap : C.natDegree ≤ affineLocatorCap)
      (hucap : degreeX C ≤ affineChallengeCap)
      (hOwners : recursiveOwnerBase + degreeX C ≤ Owners.card)
      (hCoords : recursiveCoordinateBase + H.natDegree ≤ Coords.card)
      (howner : ∀ i ∈ Owners,
        H.map (Polynomial.evalRingHom (owner i)) ∣
          C.map (Polynomial.evalRingHom (owner i)))
      (hcoord : ∀ i ∈ Coords,
        (swap H).map (Polynomial.evalRingHom (coord i)) ∣
          (swap C).map (Polynomial.evalRingHom (coord i))) :
      H ∣ C := by
    obtain ⟨D, hDprimitive, hDpositive, hDdivH, hDdivC⟩ :=
      recursive_exists_positiveLocatorCommonFactor
        H C Owners owner Coords coord hHprimitive hd hdcap hncap hucap
        hOwners hCoords howner hcoord
    let H₁ : F[X][X] := Classical.choose hDdivH
    let C₁ : F[X][X] := Classical.choose hDdivC
    have hHfactor : H = D * H₁ := Classical.choose_spec hDdivH
    have hCfactor : C = D * C₁ := Classical.choose_spec hDdivC
    have hDne : D ≠ 0 := by
      intro hzero
      rw [hzero, Polynomial.natDegree_zero] at hDpositive
      omega
    have hHne : H ≠ 0 := hHprimitive.ne_zero
    have hH₁ne : H₁ ≠ 0 := by
      intro hzero
      apply hHne
      rw [hHfactor, hzero, mul_zero]
    have hC₁ne : C₁ ≠ 0 := by
      intro hzero
      apply hCne
      rw [hCfactor, hzero, mul_zero]
    have hH₁divH : H₁ ∣ H := by
      refine ⟨D, ?_⟩
      rw [hHfactor, mul_comm]
    have hH₁primitive : H₁.IsPrimitive :=
      Polynomial.isPrimitive_of_dvd hHprimitive hH₁divH
    by_cases hH₁degree : H₁.natDegree = 0
    · have hH₁const : H₁ = Polynomial.C (H₁.coeff 0) :=
        Polynomial.eq_C_of_natDegree_le_zero hH₁degree.le
      have hCdivH₁ : Polynomial.C (H₁.coeff 0) ∣ H₁ := by
        refine ⟨1, ?_⟩
        simpa only [mul_one] using hH₁const
      have hcoeffUnit : IsUnit (H₁.coeff 0) :=
        (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hH₁primitive)
          (H₁.coeff 0) hCdivH₁
      have hH₁unit : IsUnit H₁ := by
        rw [hH₁const]
        exact Polynomial.isUnit_C.mpr hcoeffUnit
      have hassociated : Associated H D := by
        rw [hHfactor]
        exact associated_mul_unit_left D H₁ hH₁unit
      exact hassociated.dvd_iff_dvd_left.mpr hDdivC
    · have hH₁positive : 0 < H₁.natDegree :=
        Nat.pos_of_ne_zero hH₁degree
      let Owners₁ : Finset ι := Owners.filter fun i ↦
        D.map (Polynomial.evalRingHom (owner i)) ≠ 0
      let Coords₁ : Finset κ := Coords.filter fun i ↦
        (swap D).map (Polynomial.evalRingHom (coord i)) ≠ 0
      have hHdegree : H.natDegree = D.natDegree + H₁.natDegree := by
        rw [hHfactor, Polynomial.natDegree_mul hDne hH₁ne]
      have hCdegree : C.natDegree = D.natDegree + C₁.natDegree := by
        rw [hCfactor, Polynomial.natDegree_mul hDne hC₁ne]
      have hCXdegree : degreeX C = degreeX D + degreeX C₁ := by
        rw [hCfactor, Polynomial.Bivariate.degreeX_mul D C₁ hDne hC₁ne]
      have hH₁cap : H₁.natDegree ≤ homogeneousLocatorCap := by
        omega
      have hC₁ncap : C₁.natDegree ≤ affineLocatorCap := by
        omega
      have hC₁ucap : degreeX C₁ ≤ affineChallengeCap := by
        omega
      have hOwnersRaw :=
        card_le_filter_bivariate_map_ne_zero_add_degreeX
          Owners owner D hDne
      have hOwnersRaw' :
          Owners.card ≤ Owners₁.card + degreeX D := by
        simpa only [Owners₁] using hOwnersRaw
      have hOwners₁ :
          recursiveOwnerBase + degreeX C₁ ≤ Owners₁.card := by
        omega
      have hswapDne : swap D ≠ 0 := by
        simpa using swap.injective.ne hDne
      have hCoordsRaw :=
        card_le_filter_bivariate_map_ne_zero_add_degreeX
          Coords coord (swap D) hswapDne
      have hswapDegree : degreeX (swap D) = D.natDegree := by
        exact degreeX_swap D
      have hCoordsRaw' :
          Coords.card ≤ Coords₁.card + degreeX (swap D) := by
        simpa only [Coords₁] using hCoordsRaw
      rw [hswapDegree] at hCoordsRaw'
      have hCoords₁ :
          recursiveCoordinateBase + H₁.natDegree ≤ Coords₁.card := by
        omega
      have howner₁ : ∀ i ∈ Owners₁,
          H₁.map (Polynomial.evalRingHom (owner i)) ∣
            C₁.map (Polynomial.evalRingHom (owner i)) := by
        intro i hi
        have hiOwners : i ∈ Owners := (Finset.mem_filter.mp hi).1
        have hDmap : D.map (Polynomial.evalRingHom (owner i)) ≠ 0 :=
          (Finset.mem_filter.mp hi).2
        obtain ⟨W, hW⟩ := howner i hiOwners
        refine ⟨W, ?_⟩
        apply mul_left_cancel₀ hDmap
        calc
          D.map (Polynomial.evalRingHom (owner i)) *
                C₁.map (Polynomial.evalRingHom (owner i)) =
              C.map (Polynomial.evalRingHom (owner i)) := by
                rw [hCfactor, Polynomial.map_mul]
          _ = H.map (Polynomial.evalRingHom (owner i)) * W := hW
          _ = (D.map (Polynomial.evalRingHom (owner i)) *
                H₁.map (Polynomial.evalRingHom (owner i))) * W := by
                rw [hHfactor, Polynomial.map_mul]
          _ = D.map (Polynomial.evalRingHom (owner i)) *
                (H₁.map (Polynomial.evalRingHom (owner i)) * W) := by
                ring
      have hcoord₁ : ∀ i ∈ Coords₁,
          (swap H₁).map (Polynomial.evalRingHom (coord i)) ∣
            (swap C₁).map (Polynomial.evalRingHom (coord i)) := by
        intro i hi
        have hiCoords : i ∈ Coords := (Finset.mem_filter.mp hi).1
        have hDmap : (swap D).map
            (Polynomial.evalRingHom (coord i)) ≠ 0 :=
          (Finset.mem_filter.mp hi).2
        obtain ⟨W, hW⟩ := hcoord i hiCoords
        refine ⟨W, ?_⟩
        apply mul_left_cancel₀ hDmap
        calc
          (swap D).map (Polynomial.evalRingHom (coord i)) *
                (swap C₁).map (Polynomial.evalRingHom (coord i)) =
              (swap C).map (Polynomial.evalRingHom (coord i)) := by
                rw [hCfactor, map_mul, Polynomial.map_mul]
          _ = (swap H).map (Polynomial.evalRingHom (coord i)) * W := hW
          _ = ((swap D).map (Polynomial.evalRingHom (coord i)) *
                (swap H₁).map (Polynomial.evalRingHom (coord i))) * W := by
                rw [hHfactor, map_mul, Polynomial.map_mul]
          _ = (swap D).map (Polynomial.evalRingHom (coord i)) *
                ((swap H₁).map (Polynomial.evalRingHom (coord i)) * W) := by
                ring
      have hrec := descend H₁ C₁ Owners₁ Coords₁
        hH₁primitive hH₁positive hC₁ne hH₁cap hC₁ncap
        hC₁ucap hOwners₁ hCoords₁ howner₁ hcoord₁
      rcases hrec with ⟨Q, hQ⟩
      refine ⟨Q, ?_⟩
      calc
        C = D * C₁ := hCfactor
        _ = D * (H₁ * Q) := by rw [hQ]
        _ = (D * H₁) * Q := by ring
        _ = H * Q := by rw [← hHfactor]
    termination_by H.natDegree
    decreasing_by
      change H₁.natDegree < H.natDegree
      rw [hHdegree]
      omega
  exact descend H C Owners Coords hHprimitive hd hCzero hdcap hncap
    hucap hOwners hCoords howner hcoord

/-- Production consequence: in every retained rational-rank-one branch with
`L ≥ 2`, one honest Cramer relation has a positive primitive full gcd of
the homogeneous lanes that also divides the global affine lane.  The chosen
homogeneous quotients remain coprime over the challenge fraction field. -/
theorem exists_score6400_rankOne_globalTripleCoprimeFactor
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
      ∃ H A' B' : IRSProfile.Field[X][X],
        q ∈ LinearMap.ker
            (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin ∧
        (∀ n, (q n).natDegree ≤ 76779 * 2130706433) ∧
        H.IsPrimitive ∧ 0 < H.natDegree ∧
        (score6400PolynomialLocatorRelationPair q).1.1 = H * A' ∧
        (score6400PolynomialLocatorRelationPair q).2.1 = H * B' ∧
        IsCoprime
          (A'.map (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])))
          (B'.map (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))) ∧
        ((score6400PolynomialLocatorRelationPair q).1.1 ≠ 0 ∨
          (score6400PolynomialLocatorRelationPair q).2.1 ≠ 0) ∧
        H.natDegree ≤ homogeneousLocatorCap ∧
        H ∣ score6400PolynomialLocatorPairToCode f₀ f₁ q := by
  classical
  obtain ⟨q, H, A', B', hqker, hqdegree, hHprimitive, hHpositive,
      hAfactor, hBfactor, hcoprime, hpairNe, hHcap⟩ :=
    exists_score6400_rankOne_Cramer_coprimeQuotient
      f₀ f₁ L hkernelRank hLtwo hrankOne
  have hHdivA : H ∣ (score6400PolynomialLocatorRelationPair q).1.1 :=
    ⟨A', hAfactor⟩
  have hHdivB : H ∣ (score6400PolynomialLocatorRelationPair q).2.1 :=
    ⟨B', hBfactor⟩
  let C := score6400PolynomialLocatorPairToCode f₀ f₁ q
  have hfield :
      76779 * 2130706433 + 2130706433 <
        Fintype.card IRSProfile.Field := by
    rw [CompPoly.Extension.Ext.card_ext]
    norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]
  have hCYlt : C.natDegree < 185363 :=
    score6400PolynomialLocatorPairToCode_natDegree_lt
      f₀ f₁ q hqker (76779 * 2130706433) hqdegree hfield
  have hCY : C.natDegree ≤ affineLocatorCap := by
    norm_num [affineLocatorCap] at hCYlt ⊢
    omega
  have hCX : degreeX C ≤ affineChallengeCap := by
    apply degreeX_le_of_coeff_natDegree_le
    intro n
    have hcoeff := score6400PolynomialLocatorPairToCode_coeff_natDegree_le
      f₀ f₁ q (76779 * 2130706433) hqdegree n
    have hcoeffC : (C.coeff n).natDegree ≤
        76779 * 2130706433 + 2130706433 := by
      simpa only [C] using hcoeff
    norm_num [affineChallengeCap] at hcoeffC ⊢
    omega
  have hOwners : recursiveOwnerBase + degreeX C ≤ T.card := by
    apply le_trans (Nat.add_le_add_left hCX recursiveOwnerBase)
    norm_num [recursiveOwnerBase, ownerFloor, affineChallengeCap] at hTcard ⊢
    exact hTcard
  have hCoords : recursiveCoordinateBase + H.natDegree ≤
      (Finset.univ : Finset IRSProfile.Index).card := by
    apply le_trans (Nat.add_le_add_left hHcap recursiveCoordinateBase)
    norm_num [recursiveCoordinateBase, coordinateCount,
      homogeneousLocatorCap, IRSProfile.Index]
  have hownerFiber : ∀ z ∈ T,
      H.map (Polynomial.evalRingHom ((Function.Embedding.refl _) z)) ∣
        C.map (Polynomial.evalRingHom ((Function.Embedding.refl _) z)) := by
    intro z hz
    exact score6400_commonFactor_retained_owner_fiber
      f₀ f₁ q hqker H hHdivA hHdivB z
        (hbad z hz) (hnotOld z hz)
  have hcoordFiber : ∀ i ∈ (Finset.univ : Finset IRSProfile.Index),
      (swap H).map (Polynomial.evalRingHom (IRSProfile.domain i)) ∣
        (swap C).map (Polynomial.evalRingHom (IRSProfile.domain i)) := by
    intro i _hi
    exact score6400_commonFactor_coordinate_fiber
      f₀ f₁ q H hHdivA hHdivB i
  have hHdivC := dvd_of_recursive_twoAxis_fibers
    H C T (Function.Embedding.refl IRSProfile.Field)
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
    hHprimitive hHpositive hHcap hCY hCX hOwners hCoords
    hownerFiber hcoordFiber
  exact ⟨q, H, A', B', hqker, hqdegree, hHprimitive, hHpositive,
    hAfactor, hBfactor, hcoprime, hpairNe, hHcap,
    by simpa only [C] using hHdivC⟩

/-- Compatibility endpoint retaining only global triple divisibility. -/
theorem exists_score6400_rankOne_globalTripleFactor
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
      ∃ H : IRSProfile.Field[X][X],
        q ∈ LinearMap.ker
            (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin ∧
        (∀ n, (q n).natDegree ≤ 76779 * 2130706433) ∧
        H.IsPrimitive ∧ 0 < H.natDegree ∧
        H ∣ (score6400PolynomialLocatorRelationPair q).1.1 ∧
        H ∣ (score6400PolynomialLocatorRelationPair q).2.1 ∧
        ((score6400PolynomialLocatorRelationPair q).1.1 ≠ 0 ∨
          (score6400PolynomialLocatorRelationPair q).2.1 ≠ 0) ∧
        H.natDegree ≤ homogeneousLocatorCap ∧
        H ∣ score6400PolynomialLocatorPairToCode f₀ f₁ q := by
  obtain ⟨q, H, A', B', hqker, hqdegree, hHprimitive, hHpositive,
      hAfactor, hBfactor, _hcoprime, hpairNe, hHcap, hHdivC⟩ :=
    exists_score6400_rankOne_globalTripleCoprimeFactor
      f₀ f₁ L hkernelRank hLtwo hrankOne T hTcard hbad hnotOld
  exact ⟨q, H, hqker, hqdegree, hHprimitive, hHpositive,
    ⟨A', hAfactor⟩, ⟨B', hBfactor⟩, hpairNe, hHcap, hHdivC⟩

end BCHKSRecursiveTwoAxisDescent6400
end ProximityPrize.SubmissionLower
