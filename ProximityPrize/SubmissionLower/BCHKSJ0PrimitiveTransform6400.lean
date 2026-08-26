import ProximityPrize.SubmissionLower.BCHKSPrimitiveSpanLift
import ProximityPrize.SubmissionLower.BCHKSPrimitiveEffective
import ProximityPrize.SubmissionLower.BCHKSHybridHighDegreeAudit6400
import ProximityPrize.SubmissionLower.BCHKSFactorXDegree
import ProximityPrize.SubmissionLower.BCHKSFullCoreTransformedTagBridge6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSJ0PrimitiveTransform6400

open Polynomial Polynomial.Bivariate
open BCHKSHybridHighDegreeAudit6400
open BCHKSCoreTransformedUniversalTag6400
open BCHKSFullCoreTransformedTagBridge6400
open BCHKSTransformedUniversalTag6400

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-! ## Cap-generic effective primitive obstruction -/

private theorem span_caps
    {F J : Type} [Field F]
    (c : J → F[X][Y]) (DZ DX : Nat)
    (hZ : ∀ j, (c j).natDegree ≤ DZ)
    (hX : ∀ j, Polynomial.Bivariate.degreeX (c j) ≤ DX)
    {p : F[X][Y]} (hp : p ∈ Submodule.span F (Set.range c)) :
    p.natDegree ≤ DZ ∧ Polynomial.Bivariate.degreeX p ≤ DX := by
  induction hp using Submodule.span_induction with
  | mem p hp => rcases hp with ⟨j, rfl⟩; exact ⟨hZ j, hX j⟩
  | zero => simp [Polynomial.Bivariate.degreeX]
  | add p q hp hq ihp ihq =>
      constructor
      · exact (Polynomial.natDegree_add_le p q).trans (max_le ihp.1 ihq.1)
      · unfold Polynomial.Bivariate.degreeX at *
        apply Finset.sup_le
        intro i hi
        exact (Polynomial.natDegree_add_le _ _).trans
          (max_le
            ((Polynomial.Bivariate.coeff_natDegree_le_degreeX p i).trans ihp.2)
            ((Polynomial.Bivariate.coeff_natDegree_le_degreeX q i).trans ihq.2))
  | smul a p hp ih =>
      constructor
      · exact (Polynomial.natDegree_smul_le a p).trans ih.1
      · unfold Polynomial.Bivariate.degreeX at *
        apply Finset.sup_le
        intro i hi
        simpa [smul_eq_C_mul] using
          (Polynomial.natDegree_smul_le a (p.coeff i)).trans
            ((Polynomial.Bivariate.coeff_natDegree_le_degreeX p i).trans ih.2)

private theorem map_swap_eval
    {F : Type} [Field F] (q : F[X][Y]) (x : F) :
    (Polynomial.Bivariate.swap q).map (Polynomial.evalRingHom x) =
      Polynomial.eval (Polynomial.C x) q := by
  rw [← Polynomial.Bivariate.evalX_eq_map]
  exact (Polynomial.Bivariate.evalY_eq_evalX_swap x q).symm

private theorem span_map_dvd
    {F J : Type} [Field F] (c : J → F[X][Y])
    (x : F) (a : F[X])
    (hc : ∀ j, a ∣ (c j).map (Polynomial.evalRingHom x))
    {p : F[X][Y]} (hp : p ∈ Submodule.span F (Set.range c)) :
    a ∣ p.map (Polynomial.evalRingHom x) := by
  induction hp using Submodule.span_induction with
  | mem p hp => rcases hp with ⟨j, rfl⟩; exact hc j
  | zero => simp
  | add p q hp hq ihp ihq =>
      rw [Polynomial.map_add]
      exact dvd_add ihp ihq
  | smul b p hp ih =>
      have heq : (b • p).map (Polynomial.evalRingHom x) =
          Polynomial.C b * p.map (Polynomial.evalRingHom x) := by
        ext n
        simp
      rw [heq]
      exact dvd_mul_of_dvd_right ih _

/-- The effective-resultant construction with the support caps exposed.
This is the same argument as the older fixed-cap theorem, but it can be
instantiated at the much larger J0 rectangle. -/
theorem effectivePrimitiveObstruction_of_irreducible_caps
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (R : F[X][X][Y]) (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (DZ DX : Nat) (hfield : DZ + 1 < Fintype.card F)
    (hZ : ∀ j, (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤ DZ)
    (hX : ∀ j, Polynomial.Bivariate.degreeX
      (Polynomial.Bivariate.swap (R.coeff j)) ≤ DX) :
    ∃ w : EffectivePrimitiveObstruction F R,
      w.obstruction.natDegree ≤ 2 * (DZ + 1) * DX := by
  classical
  let c0 : Nat → F[X][Y] := fun j =>
    Polynomial.Bivariate.swap (R.coeff j)
  let L := polynomialRatFuncLinearMap F
  let c : Nat → (RatFunc F)[X] := fun j => L (c0 j)
  have hc : c = (localizedSwapY R).coeff := by
    funext j
    simp [c, c0, L, polynomialRatFuncLinearMap, localizedSwapY]
  have hi := localizedSwapY_irreducible_of_irreducible hR hpos
  have hloc0 : localizedSwapY R ≠ 0 := hi.ne_zero
  have hinj : Function.Injective
      (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) :=
    Polynomial.map_injective _ (IsFractionRing.injective F[X] (RatFunc F))
  have hlocpos : 0 < (localizedSwapY R).natDegree := by
    rw [localizedSwapY, Polynomial.natDegree_map_eq_of_injective hinj]
    have heq :
        (R.map Polynomial.Bivariate.swap.toRingEquiv.toRingHom).natDegree =
          R.natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        Polynomial.Bivariate.swap.toRingEquiv.injective R
    omega
  let j0 := (localizedSwapY R).natDegree
  have hf : c j0 ≠ 0 := by
    rw [hc, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hloc0
  have htop : Ideal.span (Set.range c) = ⊤ := by
    rw [hc]
    exact span_range_coeff_eq_top_of_isPrimitive
      (hi.isPrimitive hlocpos.ne')
  obtain ⟨hraw, hhraw, hcopraw⟩ := exists_primitive_localized_selection
    c j0 (DZ + 1) hf htop
    (lt_of_le_of_lt (by
      rw [show (c j0).natDegree = (c0 j0).natDegree by
        exact Polynomial.natDegree_map_eq_of_injective
          (IsFractionRing.injective F[X] (RatFunc F)) (c0 j0)]
      exact hZ j0) (Nat.lt_succ_self _)) hfield
  let h := if hraw = 0 then c j0 else hraw
  have hhspan : h ∈ Submodule.span F (Set.range c) := by
    by_cases hz : hraw = 0
    · simp only [h, hz, if_true]
      exact Submodule.subset_span (Set.mem_range_self j0)
    · simp only [h, hz, if_false]
      exact hhraw
  have hne : h ≠ 0 := by
    by_cases hz : hraw = 0
    · simpa only [h, hz, if_true] using hf
    · simpa only [h, hz, if_false]
  have hcop : IsCoprime (c j0) h := by
    by_cases hz : hraw = 0
    · rcases hcopraw with ⟨u, v, huv⟩
      refine ⟨u, 0, ?_⟩
      rw [zero_mul, add_zero]
      simpa only [hz, mul_zero, add_zero] using huv
    · simpa only [h, hz, if_false] using hcopraw
  have hccomp : c = L ∘ c0 := rfl
  obtain ⟨h0, hh0, hmaph⟩ := exists_span_lift L c0 c hccomp hhspan
  let f0 := c0 j0
  have hfcaps := span_caps c0 DZ DX
    (by simpa [c0] using hZ) (by simpa [c0] using hX)
    (Submodule.subset_span (Set.mem_range_self j0))
  have hhcaps := span_caps c0 DZ DX
    (by simpa [c0] using hZ) (by simpa [c0] using hX) hh0
  let P : F[X] := f0.leadingCoeff * h0.leadingCoeff *
    Polynomial.resultant f0 h0
  have hP : P ≠ 0 := by
    have hfmap : L f0 = c j0 := rfl
    have hfne : L f0 ≠ 0 := by simpa [hfmap] using hf
    have hf0ne : f0 ≠ 0 := by
      intro hz
      apply hfne
      rw [hz]
      simp
    have hdegreef : (L f0).natDegree = f0.natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective F[X] (RatFunc F)) f0
    have hdegreeh : (L h0).natDegree = h0.natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective F[X] (RatFunc F)) h0
    have hr : Polynomial.resultant (L f0) (L h0) ≠ 0 := by
      rw [hmaph]
      simpa [hfmap] using Polynomial.resultant_ne_zero (c j0) h hcop
    have hhne : L h0 ≠ 0 := by
      rw [hmaph]
      exact hne
    have hh0ne : h0 ≠ 0 := by
      intro hz
      apply hhne
      rw [hz]
      simp
    have hr0 : Polynomial.resultant f0 h0 ≠ 0 := by
      intro hz
      apply hr
      change Polynomial.resultant (L f0) (L h0)
        (L f0).natDegree (L h0).natDegree = 0
      rw [hdegreef, hdegreeh]
      change Polynomial.resultant
        (f0.map (algebraMap F[X] (RatFunc F)))
        (h0.map (algebraMap F[X] (RatFunc F)))
        f0.natDegree h0.natDegree = 0
      rw [Polynomial.resultant_map_map, hz]
      simp
    exact mul_ne_zero (mul_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr hf0ne)
      (Polynomial.leadingCoeff_ne_zero.mpr hh0ne)) hr0
  let w : EffectivePrimitiveObstruction F R := {
    obstruction := P
    ne := hP
    property := by
      intro x hx
      rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
      intro a ha
      have hac : ∀ j, a ∣ (triSpecializeX R x).coeff j :=
        (Polynomial.C_dvd_iff_dvd_coeff a _).mp ha
      have hdiv0 : ∀ j, a ∣
          (c0 j).map (Polynomial.evalRingHom x) := by
        intro j
        rw [show c0 j = Polynomial.Bivariate.swap (R.coeff j) by rfl,
          map_swap_eval]
        simpa [triSpecializeX] using hac j
      have hdivh : a ∣ h0.map (Polynomial.evalRingHom x) :=
        span_map_dvd c0 x a hdiv0 hh0
      have hdivf : a ∣ f0.map (Polynomial.evalRingHom x) := hdiv0 j0
      have hxe : Polynomial.eval x P =
          Polynomial.eval x f0.leadingCoeff *
          Polynomial.eval x h0.leadingCoeff *
          Polynomial.eval x (Polynomial.resultant f0 h0) := by
        simp [P]
      have hlf : Polynomial.eval x f0.leadingCoeff ≠ 0 := by
        intro hz
        apply hx
        rw [hxe, hz, zero_mul, zero_mul]
      have hlh : Polynomial.eval x h0.leadingCoeff ≠ 0 := by
        intro hz
        apply hx
        rw [hxe, hz, mul_zero, zero_mul]
      have hres : Polynomial.eval x (Polynomial.resultant f0 h0) ≠ 0 := by
        intro hz
        apply hx
        rw [hxe, hz, mul_zero]
      have hfcoeff :
          (f0.map (Polynomial.evalRingHom x)).coeff f0.natDegree ≠ 0 := by
        rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
        exact hlf
      have hhcoeff :
          (h0.map (Polynomial.evalRingHom x)).coeff h0.natDegree ≠ 0 := by
        rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
        exact hlh
      have hdf : (f0.map (Polynomial.evalRingHom x)).natDegree =
          f0.natDegree :=
        le_antisymm Polynomial.natDegree_map_le
          (Polynomial.le_natDegree_of_ne_zero hfcoeff)
      have hdh : (h0.map (Polynomial.evalRingHom x)).natDegree =
          h0.natDegree :=
        le_antisymm Polynomial.natDegree_map_le
          (Polynomial.le_natDegree_of_ne_zero hhcoeff)
      have hresspec : Polynomial.resultant
          (f0.map (Polynomial.evalRingHom x))
          (h0.map (Polynomial.evalRingHom x)) ≠ 0 := by
        change Polynomial.resultant
          (f0.map (Polynomial.evalRingHom x))
          (h0.map (Polynomial.evalRingHom x))
          (f0.map (Polynomial.evalRingHom x)).natDegree
          (h0.map (Polynomial.evalRingHom x)).natDegree ≠ 0
        rw [hdf, hdh, Polynomial.resultant_map_map]
        exact hres
      have hcopSpec : IsCoprime
          (f0.map (Polynomial.evalRingHom x))
          (h0.map (Polynomial.evalRingHom x)) := by
        by_contra hn
        exact hresspec ((Polynomial.resultant_eq_zero_iff).2
          ⟨Or.inl (by
            intro hz
            exact hfcoeff (by rw [hz]; simp)), hn⟩)
      rcases hcopSpec with ⟨u, v, huv⟩
      have hca : a ∣ (1 : F[X]) := by
        rw [← huv]
        exact dvd_add (dvd_mul_of_dvd_right hdivf u)
          (dvd_mul_of_dvd_right hdivh v)
      exact isUnit_iff_dvd_one.mpr hca
  }
  refine ⟨w, ?_⟩
  change P.natDegree ≤ _
  have hlfcap : f0.leadingCoeff.natDegree ≤ DX := by
    rw [← Polynomial.coeff_natDegree]
    exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX
      f0 f0.natDegree).trans hfcaps.2
  have hlhcap : h0.leadingCoeff.natDegree ≤ DX := by
    rw [← Polynomial.coeff_natDegree]
    exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX
      h0 h0.natDegree).trans hhcaps.2
  have hfzcaps : f0.natDegree ≤ DZ ∧
      Polynomial.Bivariate.degreeX f0 ≤ DX := by
    simpa [f0] using hfcaps
  have hrCap := bivariate_resultant_natDegree_le
    f0 h0 f0.natDegree h0.natDegree
  refine Polynomial.natDegree_mul_le.trans ?_
  refine (Nat.add_le_add Polynomial.natDegree_mul_le hrCap).trans ?_
  nlinarith

/-! ## J0 factor instantiation -/

def bchksJ0PrimitiveZCap6400 : Nat := 1688975428
def bchksJ0PrimitiveXCap6400 : Nat := 11089586662
def bchksJ0PrimitiveObstructionCap6400 : Nat :=
  2 * (bchksJ0PrimitiveZCap6400 + 1) * bchksJ0PrimitiveXCap6400

theorem bchksJ0Primitive_caps_lt_field6400 :
    bchksJ0PrimitiveZCap6400 + 1 <
      Fintype.card ProximityPrize.Benchmark.IRSProfile.Field ∧
    bchksJ0PrimitiveObstructionCap6400 + 131071 +
        (2 * 84607 + 2) * bchksJ0PrimitiveXCap6400 <
      Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
  constructor <;>
    norm_num [bchksJ0PrimitiveZCap6400, bchksJ0PrimitiveXCap6400,
      bchksJ0PrimitiveObstructionCap6400,
      ProximityPrize.Benchmark.IRSProfile.Field,
      KoalaBear.Ext6, KoalaBear.fieldSize]

/-- Every positive irreducible J0 factor has an explicit effective
primitive obstruction at the sharp J0 support caps. -/
theorem exists_j0_effectivePrimitiveObstruction
    (Q R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hRpos : 0 < R.natDegree)
    (hYZ : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 1688975429)
    (hweighted : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      a + 131071 * j < 11089586663) :
    ∃ w : EffectivePrimitiveObstruction
        ProximityPrize.Benchmark.IRSProfile.Field R,
      w.obstruction.natDegree ≤ bchksJ0PrimitiveObstructionCap6400 := by
  have hRYZ := YZFactorCap.normalizedFactor_YZ_cap
    Q R 1688975429 hQ hRQ hYZ
  have hRW := WeightedFactorCaps.coeff_cap_of_dvd
    Q R 131071 11089586663 hQ
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hweighted
  have hZ : ∀ j,
      (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤
        bchksJ0PrimitiveZCap6400 := by
    intro j
    rw [show (Polynomial.Bivariate.swap (R.coeff j)).natDegree =
      Polynomial.Bivariate.natDegreeY
        (Polynomial.Bivariate.swap (R.coeff j)) from rfl,
      Polynomial.Bivariate.natDegreeY_swap]
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have hne : (R.coeff j).coeff a ≠ 0 :=
      Polynomial.mem_support_iff.mp ha
    have hc := hRYZ j a hne
    simp only [bchksJ0PrimitiveZCap6400]
    omega
  have hX : ∀ j, Polynomial.Bivariate.degreeX
      (Polynomial.Bivariate.swap (R.coeff j)) ≤
        bchksJ0PrimitiveXCap6400 := by
    intro j
    rw [Polynomial.Bivariate.degreeX_swap]
    change (R.coeff j).natDegree ≤ bchksJ0PrimitiveXCap6400
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hc := hRW j (R.coeff j).natDegree (by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz)
      simp only [bchksJ0PrimitiveXCap6400]
      omega
  obtain ⟨w, hw⟩ := effectivePrimitiveObstruction_of_irreducible_caps
    R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
      hRpos bchksJ0PrimitiveZCap6400 bchksJ0PrimitiveXCap6400
      bchksJ0Primitive_caps_lt_field6400.1 hZ hX
  exact ⟨w, by simpa [bchksJ0PrimitiveObstructionCap6400] using hw⟩

/-! ## Factor-local center and simple-root survivor set -/

private theorem specialization_ne_zero_of_ratFunc_eval
    {F : Type} [Field F] (P : F[X][Y]) (x : F)
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

/-- Simultaneously avoid the primitive obstruction, an arbitrary nonzero
locator, and the factor's leading/separability obstruction.  The returned
bad `Z` set is exactly the root set of the specialized factor obstruction. -/
theorem exists_primitive_locator_factorGood
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (p : Nat) [CharP F p]
    (R : F[X][X][Y]) (G : F[X])
    (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (hchar : R.natDegree < p)
    (w : EffectivePrimitiveObstruction F R) (hG0 : G ≠ 0)
    (d DZ : Nat)
    (hcenter : w.obstruction.natDegree + G.natDegree +
      (factorXObstruction R).natDegree < Fintype.card F)
    (hzcap : ∀ x : F,
      (Polynomial.eval (Polynomial.C x)
        (factorXObstruction R)).natDegree ≤ 2 * d * DZ) :
    ∃ x0 : F, ∃ Bad : Finset F,
      G.eval x0 ≠ 0 ∧ Bad.card ≤ 2 * d * DZ ∧
      (triSpecializeX R x0).IsPrimitive ∧
      (triSpecializeX R x0).natDegree = R.natDegree ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y
          (biSpecializeZ (triSpecializeX R x0) z) = 0 →
        Polynomial.eval y
          (biSpecializeZ (triSpecializeX R.derivative x0) z) ≠ 0) := by
  classical
  let g : F[X] →+* RatFunc F := algebraMap _ _
  let primRat : (RatFunc F)[X] :=
    w.obstruction.map (algebraMap F (RatFunc F))
  let locatorRat : (RatFunc F)[X] :=
    G.map (algebraMap F (RatFunc F))
  let factorRat : (RatFunc F)[X] := (factorXObstruction R).map g
  let combined : (RatFunc F)[X] := primRat * locatorRat * factorRat
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hf : Function.Injective (algebraMap F (RatFunc F)) :=
    FaithfulSMul.algebraMap_injective F (RatFunc F)
  have hfactor0 : factorXObstruction R ≠ 0 := mul_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr hR.ne_zero)
    (rawSepResultant_ne_zero_of_irreducible p
      R hR hpos hchar)
  have hcombined0 : combined ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        ((Polynomial.map_ne_zero_iff hf).mpr w.ne)
        ((Polynomial.map_ne_zero_iff hf).mpr hG0))
      ((Polynomial.map_ne_zero_iff hg).mpr hfactor0)
  have hcombinedDegree : combined.natDegree < Fintype.card F := by
    have hle : combined.natDegree ≤
        w.obstruction.natDegree + G.natDegree +
          (factorXObstruction R).natDegree := by
      calc
        combined.natDegree ≤ primRat.natDegree + locatorRat.natDegree +
            factorRat.natDegree := by
          exact Polynomial.natDegree_mul_le.trans
            (Nat.add_le_add Polynomial.natDegree_mul_le le_rfl)
        _ = w.obstruction.natDegree + G.natDegree +
            (factorXObstruction R).natDegree := by
          rw [show primRat.natDegree = w.obstruction.natDegree by
              exact Polynomial.natDegree_map_eq_of_injective hf _,
            show locatorRat.natDegree = G.natDegree by
              exact Polynomial.natDegree_map_eq_of_injective hf _,
            show factorRat.natDegree = (factorXObstruction R).natDegree by
              exact Polynomial.natDegree_map_eq_of_injective hg _]
    exact hle.trans_lt hcenter
  obtain ⟨x0, hx⟩ := exists_base_point_avoiding_ratfunc_polynomials
    ({()} : Finset Unit) (fun _ => combined)
      (by intro i hi; exact hcombined0)
      (by simpa using hcombinedDegree)
  have hcombinedEval := hx () (by simp)
  have hprod :
      Polynomial.eval (algebraMap F (RatFunc F) x0) primRat *
          Polynomial.eval (algebraMap F (RatFunc F) x0) locatorRat *
        Polynomial.eval (algebraMap F (RatFunc F) x0) factorRat ≠ 0 := by
    simpa [combined, Polynomial.eval_mul] using hcombinedEval
  have hprimRat :
      Polynomial.eval (algebraMap F (RatFunc F) x0) primRat ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have hlocatorRat :
      Polynomial.eval (algebraMap F (RatFunc F) x0) locatorRat ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have hfactorRat :
      Polynomial.eval (algebraMap F (RatFunc F) x0) factorRat ≠ 0 :=
    right_ne_zero_of_mul hprod
  have hprim : Polynomial.eval x0 w.obstruction ≠ 0 := by
    intro hz
    apply hprimRat
    simp [primRat, Polynomial.eval_map, hz]
  have hGx : G.eval x0 ≠ 0 := by
    intro hz
    apply hlocatorRat
    simp [locatorRat, Polynomial.eval_map, hz]
  have hfactorX :
      Polynomial.eval (Polynomial.C x0) (factorXObstruction R) ≠ 0 :=
    specialization_ne_zero_of_ratFunc_eval
      (factorXObstruction R) x0 (by
        change Polynomial.eval (algebraMap F (RatFunc F) x0)
          ((factorXObstruction R).map g) ≠ 0
        simpa [factorRat] using hfactorRat)
  let zObs : F[X] :=
    Polynomial.eval (Polynomial.C x0) (factorXObstruction R)
  let Bad : Finset F := zObs.roots.toFinset
  have hzObs : zObs ≠ 0 := hfactorX
  have hBad : Bad.card ≤ 2 * d * DZ := by
    dsimp [Bad]
    exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' zObs).trans (hzcap x0))
  have hlead : Polynomial.eval (Polynomial.C x0) R.leadingCoeff ≠ 0 := by
    intro hz
    apply hfactorX
    rw [factorXObstruction, Polynomial.eval_mul, hz, zero_mul]
  have hdegree : (triSpecializeX R x0).natDegree = R.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Polynomial.evalRingHom (Polynomial.C x0)) hlead
  refine ⟨x0, Bad, hGx, hBad, w.property x0 hprim, hdegree, ?_⟩
  intro z hzBad y hy
  have hzO : Polynomial.eval z zObs ≠ 0 := by
    intro hz
    apply hzBad
    dsimp [Bad]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hzObs]
    exact hz
  have hresEval : Polynomial.eval z
      (Polynomial.eval (Polynomial.C x0) (rawSepResultant R)) ≠ 0 := by
    intro hzres
    apply hzO
    dsimp [zObs]
    rw [factorXObstruction, Polynomial.eval_mul,
      Polynomial.eval_mul, hzres, mul_zero]
  have hresX : Polynomial.eval (Polynomial.C x0) (rawSepResultant R) =
      Polynomial.resultant (triSpecializeX R x0)
        (triSpecializeX R.derivative x0)
        R.natDegree (R.natDegree - 1) := by
    simp [rawSepResultant, triSpecializeX]
  have hder : triSpecializeX R.derivative x0 =
      (triSpecializeX R x0).derivative := by
    simp [triSpecializeX, Polynomial.derivative_map]
  have hresB : Polynomial.eval z
      (Polynomial.resultant (triSpecializeX R x0)
        (triSpecializeX R x0).derivative
        (triSpecializeX R x0).natDegree
        ((triSpecializeX R x0).natDegree - 1)) ≠ 0 := by
    rw [hdegree, ← hder, ← hresX]
    exact hresEval
  have hs := simple_root_of_fixed_resultant_eval_ne_zero
    (triSpecializeX R x0) z y (by rw [hdegree]; exact hpos) hresB hy
  rw [← hder] at hs
  exact hs

local instance j0ConcreteChar :
    CharP ProximityPrize.Benchmark.IRSProfile.Field 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- The strict J0 outer support cap gives the factor degree bound used by
the center and bad-fiber ledgers. -/
theorem j0_normalizedFactor_natDegree_le
    (Q R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hY : ∀ j a, (Q.coeff j).coeff a ≠ 0 → j < 84608) :
    R.natDegree ≤ 84607 := by
  have hleadQ : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQ
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hleadQ
  have hca : (Q.coeff Q.natDegree).coeff a ≠ 0 := by
    simpa only [Polynomial.leadingCoeff] using
      Polynomial.mem_support_iff.mp ha
  have hQdegree : Q.natDegree ≤ 84607 := by
    have := hY Q.natDegree a hca
    omega
  exact (Polynomial.natDegree_le_of_dvd
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hQ).trans
      hQdegree

/-- J0 weighted support controls the center-variable degree of the whole
factor obstruction. -/
theorem j0_factorXObstruction_natDegree_le
    (Q R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hweighted : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      a + 131071 * j < 11089586663) :
    (factorXObstruction R).natDegree ≤
      (2 * R.natDegree + 2) * bchksJ0PrimitiveXCap6400 := by
  have hRW := WeightedFactorCaps.coeff_cap_of_dvd
    Q R 131071 11089586663 hQ
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hweighted
  have hmapX : Polynomial.Bivariate.degreeX (mapZToRatFunc R) ≤
      bchksJ0PrimitiveXCap6400 := by
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro j hj
    simp only [mapZToRatFunc, Polynomial.coeff_map]
    exact Polynomial.natDegree_map_le.trans (by
      by_cases hz : R.coeff j = 0
      · simp [hz]
      · have hc := hRW j (R.coeff j).natDegree (by
          rw [Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr hz)
        simp only [bchksJ0PrimitiveXCap6400]
        omega)
  have hlead : R.leadingCoeff.natDegree ≤
      bchksJ0PrimitiveXCap6400 := by
    by_cases hz : R.leadingCoeff = 0
    · simp [hz]
    · have hc := hRW R.natDegree R.leadingCoeff.natDegree (by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz)
      simp only [bchksJ0PrimitiveXCap6400]
      omega
  exact factorXObstruction_natDegree_le
    R bchksJ0PrimitiveXCap6400 hmapX hlead

/-- At every center, the specialized factor obstruction has the sharp J0
`Z`-degree bound `2*d*1688975428`. -/
theorem j0_factorXObstruction_eval_natDegree_le
    (Q R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hRpos : 0 < R.natDegree)
    (hYZ : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 1688975429)
    (x : ProximityPrize.Benchmark.IRSProfile.Field) :
    (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
      2 * R.natDegree * bchksJ0PrimitiveZCap6400 := by
  have hRYZ := YZFactorCap.normalizedFactor_YZ_cap
    Q R 1688975429 hQ hRQ hYZ
  have hcoeffCap : ∀ j, Polynomial.Bivariate.degreeX (R.coeff j) ≤
      bchksJ0PrimitiveZCap6400 := by
    intro j
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have hc := hRYZ j a (Polynomial.mem_support_iff.mp ha)
    simp only [bchksJ0PrimitiveZCap6400]
    omega
  have hevalCap : ∀ p : Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field),
      Polynomial.Bivariate.degreeX p ≤ bchksJ0PrimitiveZCap6400 →
      (Polynomial.eval (Polynomial.C x) p).natDegree ≤
        bchksJ0PrimitiveZCap6400 := by
    intro q hq
    have heq : (Polynomial.Bivariate.swap q).map
        (Polynomial.evalRingHom x) = Polynomial.eval (Polynomial.C x) q := by
      rw [← Polynomial.Bivariate.evalX_eq_map]
      exact (Polynomial.Bivariate.evalY_eq_evalX_swap x q).symm
    rw [← heq]
    exact Polynomial.natDegree_map_le.trans (by
      rw [show (Polynomial.Bivariate.swap q).natDegree =
        Polynomial.Bivariate.natDegreeY
          (Polynomial.Bivariate.swap q) from rfl,
        Polynomial.Bivariate.natDegreeY_swap]
      exact hq)
  apply factorXObstruction_eval_natDegree_le
    R x R.natDegree bchksJ0PrimitiveZCap6400 hRpos le_rfl
  · unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro j hj
    simp only [triSpecializeX, Polynomial.coeff_map]
    exact hevalCap (R.coeff j) (hcoeffCap j)
  · exact hevalCap R.leadingCoeff (by
      rw [← Polynomial.coeff_natDegree]
      exact hcoeffCap R.natDegree)

/-- Fully concrete J0 factor-local center.  It avoids the primitive
obstruction, core locator, and factor obstruction, and returns a simple-root
survivor set with its exact factorwise cardinality cost. -/
theorem exists_j0_primitive_locator_factorGood
    (Q R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (G : Polynomial ProximityPrize.Benchmark.IRSProfile.Field)
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hRpos : 0 < R.natDegree)
    (hG0 : G ≠ 0) (hGdegree : G.natDegree ≤ 131071)
    (hY : ∀ j a, (Q.coeff j).coeff a ≠ 0 → j < 84608)
    (hweighted : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      a + 131071 * j < 11089586663)
    (hYZ : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 1688975429) :
    ∃ w : EffectivePrimitiveObstruction
        ProximityPrize.Benchmark.IRSProfile.Field R,
      w.obstruction.natDegree ≤ bchksJ0PrimitiveObstructionCap6400 ∧
      ∃ x0 : ProximityPrize.Benchmark.IRSProfile.Field,
        ∃ Bad : Finset ProximityPrize.Benchmark.IRSProfile.Field,
          G.eval x0 ≠ 0 ∧
          Bad.card ≤ 2 * R.natDegree * bchksJ0PrimitiveZCap6400 ∧
          (triSpecializeX R x0).IsPrimitive ∧
          (triSpecializeX R x0).natDegree = R.natDegree ∧
          (∀ z ∉ Bad, ∀ y,
            Polynomial.eval y
              (biSpecializeZ (triSpecializeX R x0) z) = 0 →
            Polynomial.eval y
              (biSpecializeZ (triSpecializeX R.derivative x0) z) ≠ 0) := by
  obtain ⟨w, hw⟩ := exists_j0_effectivePrimitiveObstruction
    Q R hQ hRQ hRpos hYZ hweighted
  have hRdegree := j0_normalizedFactor_natDegree_le Q R hQ hRQ hY
  have hfactorDegree := j0_factorXObstruction_natDegree_le
    Q R hQ hRQ hweighted
  have hcenter : w.obstruction.natDegree + G.natDegree +
      (factorXObstruction R).natDegree <
        Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
    apply lt_of_le_of_lt (b := bchksJ0PrimitiveObstructionCap6400 + 131071 +
      (2 * 84607 + 2) * bchksJ0PrimitiveXCap6400)
    · exact Nat.add_le_add (Nat.add_le_add hw hGdegree)
        (hfactorDegree.trans
          (Nat.mul_le_mul_right bchksJ0PrimitiveXCap6400 (by omega)))
    · exact bchksJ0Primitive_caps_lt_field6400.2
  obtain ⟨x0, Bad, hGx, hBad, hprimitive, hdegree, hsimple⟩ :=
    exists_primitive_locator_factorGood 2130706433 R G
      (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
      hRpos (lt_of_le_of_lt hRdegree (by norm_num)) w hG0
      R.natDegree bchksJ0PrimitiveZCap6400 hcenter
      (fun x => j0_factorXObstruction_eval_natDegree_le
        Q R hQ hRQ hRpos hYZ x)
  exact ⟨w, hw, x0, Bad, hGx, hBad, hprimitive, hdegree, hsimple⟩

/-- The factor-local simple-root bad cost aggregates to the existing J0
radical ledger; it is not multiplied by the number of factors. -/
theorem j0_factorBad_sum_le
    {A : Type} [DecidableEq A]
    (Outer : Finset A) (degree zDegree badCard : A → Nat)
    (hbad : ∀ a ∈ Outer, badCard a ≤ 2 * degree a * zDegree a)
    (hdegree : ∀ a ∈ Outer, degree a ≤ 84607)
    (hzMass : (∑ a ∈ Outer, zDegree a) ≤ bchksHybridZMass6400) :
    (∑ a ∈ Outer, badCard a) ≤ bchksHybridRadicalCover6400 := by
  calc
    (∑ a ∈ Outer, badCard a) ≤
        ∑ a ∈ Outer, 2 * degree a * zDegree a :=
      Finset.sum_le_sum hbad
    _ ≤ ∑ a ∈ Outer, 2 * 84607 * zDegree a := by
      apply Finset.sum_le_sum
      intro a ha
      exact Nat.mul_le_mul_right (zDegree a)
        (Nat.mul_le_mul_left 2 (hdegree a ha))
    _ = 2 * 84607 * (∑ a ∈ Outer, zDegree a) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * 84607 * bchksHybridZMass6400 :=
      Nat.mul_le_mul_left _ hzMass
    _ = bchksHybridRadicalCover6400 := by
      norm_num [bchksHybridZMass6400, bchksHybridRadicalCover6400]

/-- Removing the union of factor-local bad sets preserves pointwise factor
coverage.  This is the exact input expected by
`exists_mixedPositiveInnerFactorPair`. -/
theorem factorCoverage_of_not_mem_badUnion
    {F A : Type} [DecidableEq F] [DecidableEq A]
    (Outer : Finset A) (Owner Bad : A → Finset F)
    (z : F) (hzOwner : ∃ a ∈ Outer, z ∈ Owner a)
    (hzBad : z ∉ Outer.biUnion Bad) :
    ∃ a ∈ Outer, z ∈ Owner a ∧ z ∉ Bad a := by
  obtain ⟨a, ha, hza⟩ := hzOwner
  refine ⟨a, ha, hza, ?_⟩
  intro hbad
  exact hzBad (Finset.mem_biUnion.mpr ⟨a, ha, hbad⟩)

/-- The union removed before the heterogeneous selector costs at most the
sum of the factor-local simple-root bad caps. -/
theorem badUnion_card_le_sum
    {F A : Type} [DecidableEq F] [DecidableEq A]
    (Outer : Finset A) (Bad : A → Finset F) :
    (Outer.biUnion Bad).card ≤ ∑ a ∈ Outer, (Bad a).card :=
  Finset.card_biUnion_le

/-! ## End-to-end full-core transformed tag -/

/-- The J0 factor caps, full-core quotient, effective primitive obstruction,
factor-local center, and simple-root bad set assemble into the exact tag
consumed by the heterogeneous selector. -/
theorem exists_j0_fullCore_transformedUniversalTag
    (Qglobal R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (E S : Finset ProximityPrize.Benchmark.IRSProfile.Field)
    (P : ProximityPrize.Benchmark.IRSProfile.Field →
      Polynomial ProximityPrize.Benchmark.IRSProfile.Field)
    (U0 U1 : ProximityPrize.Benchmark.IRSProfile.Field →
      ProximityPrize.Benchmark.IRSProfile.Field)
    (s : Nat)
    (hQ : Qglobal ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Qglobal)
    (hRpos : 0 < R.natDegree)
    (hY : ∀ j a, (Qglobal.coeff j).coeff a ≠ 0 → j < 84608)
    (hweighted : ∀ j a, (Qglobal.coeff j).coeff a ≠ 0 →
      a + 131071 * j < 11089586663)
    (hYZ : ∀ j a, (Qglobal.coeff j).coeff a ≠ 0 →
      ((Qglobal.coeff j).coeff a).natDegree + j < 1688975429)
    (hcard : E.card + s = 131071)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ 131071)
    (hcoreMatch : ∀ z ∈ S, ∀ x ∈ E,
      Polynomial.eval x (P z) = U0 x + z * U1 x)
    (hroot : ∀ z ∈ S, triEval R z (P z) = 0) :
    ∃ x0 : ProximityPrize.Benchmark.IRSProfile.Field,
      ∃ Bad : Finset ProximityPrize.Benchmark.IRSProfile.Field,
        ∃ tag : TransformedUniversalTag
          ProximityPrize.Benchmark.IRSProfile.Field,
          Bad.card ≤ 2 * R.natDegree * bchksJ0PrimitiveZCap6400 ∧
          tag.source = R ∧ tag.center = x0 ∧
          tag.rootDegreeCap = s ∧
          tag.owns = (fun z => z ∈ S ∧ z ∉ Bad) ∧
          tag.transformed ≠ 0 := by
  classical
  obtain ⟨B0, B1, Qroot, hB0, hB1, _hB0eval, _hB1eval,
      hQrootDegree, hshape⟩ :=
    BCHKSFullCoreOwnerBridge6400.exists_bounded_coreQuotient_family
      E S P U0 U1 131071 s hcard hPdegree hcoreMatch
  let G := BCHKSFullCoreLineArrangement6400.coreLocator E
  have hG0 : G ≠ 0 :=
    (BCHKSFullCoreLineArrangement6400.coreLocator_monic E).ne_zero
  have hGdegree : G.natDegree ≤ 131071 := by
    rw [show G.natDegree = E.card by
      exact BCHKSFullCoreLineArrangement6400.coreLocator_natDegree E]
    omega
  obtain ⟨w, hw, x0, Bad, hGx, hBad, hprimitive, _hdegree,
      hsimpleSlope⟩ :=
    exists_j0_primitive_locator_factorGood Qglobal R G hQ hRQ hRpos
      hG0 hGdegree hY hweighted hYZ
  let owns : ProximityPrize.Benchmark.IRSProfile.Field → Prop :=
    fun z => z ∈ S ∧ z ∉ Bad
  have hsimpleAt : ∀ z, owns z →
      FiniteHensel.IsSimpleRootAt (triSpecializeZ R z) x0
        ((P z).eval x0) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have hzroot := congrArg (Polynomial.eval x0) (hroot z hz.1)
      calc
        (triSpecializeZ R z).eval₂ (Polynomial.evalRingHom x0)
            ((P z).eval x0) =
            (Polynomial.evalRingHom x0)
              ((triSpecializeZ R z).eval (P z)) := by
          exact (Polynomial.hom_eval₂ (triSpecializeZ R z)
            (RingHom.id _) (Polynomial.evalRingHom x0) (P z)).symm
        _ = 0 := by simpa [triEval_eq_eval_triSpecializeZ] using hzroot
    · rw [ySlope_triSpecializeZ_eq_eval_biSpecializeZ_derivative]
      apply hsimpleSlope z hz.2 ((P z).eval x0)
      have hpoint : biEval (triSpecializeX R x0)
          ((P z).eval x0) z = 0 := by
        rw [← eval_triEval_eq_biEval_triSpecializeX]
        rw [hroot z hz.1]
        simp
      simpa [biEval, biSpecializeZ] using hpoint
  let tag := BCHKSCoreTransformedUniversalTag6400.coreTransformedUniversalTag
    R P Qroot B0 B1 G x0 s owns hG0 hGx hprimitive
    (fun z hz => hQrootDegree z hz.1)
    (fun z hz => hshape z hz.1)
    (fun z hz => hroot z hz.1)
    hsimpleAt hB0 hB1 (by
      rw [show G.natDegree = E.card by
        exact BCHKSFullCoreLineArrangement6400.coreLocator_natDegree E]
      omega)
  have htag0 : tag.transformed ≠ 0 := by
    change BCHKSCoreQuotientHenselAudit6400.coreRootTransform
      R B0 B1 G ≠ 0
    intro hzero
    have hdegree :=
      BCHKSCoreQuotientHenselAudit6400.coreRootTransform_natDegree
        R B0 B1 G hG0
    rw [hzero] at hdegree
    simp at hdegree
    omega
  exact ⟨x0, Bad, tag, hBad, rfl, rfl, rfl, rfl, htag0⟩

end BCHKSJ0PrimitiveTransform6400
end ProximityPrize.SubmissionLower
