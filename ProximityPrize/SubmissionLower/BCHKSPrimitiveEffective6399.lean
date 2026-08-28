import ProximityPrize.SubmissionLower.BCHKSPrimitiveSpanLift
import ProximityPrize.SubmissionLower.BCHKSPrimitiveEffective
import ProximityPrize.SubmissionLower.BCHKSParameters6399

namespace ProximityPrize.SubmissionLower
open Polynomial

private abbrev F := ProximityPrize.Benchmark.IRSProfile.Field

private theorem span_caps
    {F J : Type*} [Field F]
    (c : J → Polynomial (Polynomial F)) (DZ DX : ℕ)
    (hZ : ∀ j, (c j).natDegree ≤ DZ)
    (hX : ∀ j, Polynomial.Bivariate.degreeX (c j) ≤ DX)
    {p : Polynomial (Polynomial F)}
    (hp : p ∈ Submodule.span F (Set.range c)) :
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
          (max_le ((Polynomial.Bivariate.coeff_natDegree_le_degreeX p i).trans ihp.2)
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
    {F : Type*} [Field F] (q : Polynomial (Polynomial F)) (x : F) :
    (Polynomial.Bivariate.swap q).map (Polynomial.evalRingHom x) =
      Polynomial.eval (Polynomial.C x) q := by
  rw [← Polynomial.Bivariate.evalX_eq_map]
  exact (Polynomial.Bivariate.evalY_eq_evalX_swap x q).symm

private theorem span_map_dvd
    {F J : Type*} [Field F] (c : J → Polynomial (Polynomial F))
    (x : F) (a : Polynomial F)
    (hc : ∀ j, a ∣ (c j).map (Polynomial.evalRingHom x))
    {p : Polynomial (Polynomial F)}
    (hp : p ∈ Submodule.span F (Set.range c)) :
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


theorem effectivePrimitiveObstruction_of_irreducible6399
    (R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (hZ : ∀ j, (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤
      bchksZCap6399)
    (hX : ∀ j, Polynomial.Bivariate.degreeX
      (Polynomial.Bivariate.swap (R.coeff j)) ≤ bchksXCap6399) :
    ∃ w : EffectivePrimitiveObstruction
        ProximityPrize.Benchmark.IRSProfile.Field R,
      w.obstruction.natDegree ≤
        2 * (bchksZCap6399 + 1) * bchksXCap6399 := by
  classical
  let c₀ : ℕ → Polynomial (Polynomial F) := fun j =>
    Polynomial.Bivariate.swap (R.coeff j)
  let L := polynomialRatFuncLinearMap F
  let c : ℕ → Polynomial (RatFunc F) := fun j => L (c₀ j)
  have hc : c = (localizedSwapY R).coeff := by
    funext j
    simp [c, c₀, L, polynomialRatFuncLinearMap, localizedSwapY]
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
  let j₀ := (localizedSwapY R).natDegree
  have hf : c j₀ ≠ 0 := by
    rw [hc]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hloc0
  have htop : Ideal.span (Set.range c) = ⊤ := by
    rw [hc]
    exact span_range_coeff_eq_top_of_isPrimitive (hi.isPrimitive (by
      omega))
  obtain ⟨hraw, hhraw, hcopraw⟩ := exists_primitive_localized_selection
    c j₀ (bchksZCap6399 + 1) hf htop
    (lt_of_le_of_lt (by
      rw [show (c j₀).natDegree = (c₀ j₀).natDegree by
        exact Polynomial.natDegree_map_eq_of_injective
          (IsFractionRing.injective F[X] (RatFunc F)) (c₀ j₀)]
      exact hZ j₀) (Nat.lt_succ_self _))
    (by norm_num [bchksZCap6399, F,
      ProximityPrize.Benchmark.IRSProfile.Field])
  let h := if hraw = 0 then c j₀ else hraw
  have hhspan : h ∈ Submodule.span F (Set.range c) := by
    by_cases hz : hraw = 0
    · simp only [h, hz, if_true]
      exact Submodule.subset_span (Set.mem_range_self j₀)
    · simp only [h, hz, if_false]
      exact hhraw
  have hne : h ≠ 0 := by
    by_cases hz : hraw = 0
    · simpa only [h, hz, if_true] using hf
    · simpa only [h, hz, if_false]
  have hcop : IsCoprime (c j₀) h := by
    by_cases hz : hraw = 0
    · rcases hcopraw with ⟨u, v, huv⟩
      refine ⟨u, 0, ?_⟩
      rw [zero_mul, add_zero]
      simpa only [hz, mul_zero, add_zero] using huv
    · simpa only [h, hz, if_false] using hcopraw
  have hccomp : c = L ∘ c₀ := rfl
  obtain ⟨h₀, hh₀, hmaph⟩ := exists_span_lift L c₀ c hccomp hhspan
  let f₀ := c₀ j₀
  have hfcaps := span_caps c₀ bchksZCap6399 bchksXCap6399
    (by simpa [c₀] using hZ) (by simpa [c₀] using hX)
    (Submodule.subset_span (Set.mem_range_self j₀))
  have hhcaps := span_caps c₀ bchksZCap6399 bchksXCap6399
    (by simpa [c₀] using hZ) (by simpa [c₀] using hX) hh₀
  let P : Polynomial F := f₀.leadingCoeff * h₀.leadingCoeff *
    Polynomial.resultant f₀ h₀
  have hP : P ≠ 0 := by
    have hfmap : L f₀ = c j₀ := rfl
    have hfne : L f₀ ≠ 0 := by simpa [hfmap] using hf
    have hf₀ne : f₀ ≠ 0 := by
      intro hz
      apply hfne
      rw [hz]
      simp
    have hdegreef : (L f₀).natDegree = f₀.natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective F[X] (RatFunc F)) f₀
    have hdegreeh : (L h₀).natDegree = h₀.natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective F[X] (RatFunc F)) h₀
    have hr : Polynomial.resultant (L f₀) (L h₀) ≠ 0 := by
      rw [hmaph]
      simpa [hfmap] using Polynomial.resultant_ne_zero (c j₀) h hcop
    have hhne : L h₀ ≠ 0 := by
      rw [hmaph]
      exact hne
    have hh₀ne : h₀ ≠ 0 := by
      intro hz
      apply hhne
      rw [hz]
      simp
    have hr₀ : Polynomial.resultant f₀ h₀ ≠ 0 := by
      intro hz
      apply hr
      change Polynomial.resultant (L f₀) (L h₀)
        (L f₀).natDegree (L h₀).natDegree = 0
      rw [hdegreef, hdegreeh]
      change Polynomial.resultant
        (f₀.map (algebraMap F[X] (RatFunc F)))
        (h₀.map (algebraMap F[X] (RatFunc F)))
        f₀.natDegree h₀.natDegree = 0
      rw [Polynomial.resultant_map_map, hz]
      simp
    exact mul_ne_zero (mul_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr hf₀ne)
      (Polynomial.leadingCoeff_ne_zero.mpr hh₀ne)) hr₀
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
          (c₀ j).map (Polynomial.evalRingHom x) := by
        intro j
        rw [show c₀ j = Polynomial.Bivariate.swap (R.coeff j) by rfl,
          map_swap_eval]
        simpa [triSpecializeX] using hac j
      have hdivh : a ∣ h₀.map (Polynomial.evalRingHom x) :=
        span_map_dvd c₀ x a hdiv0 hh₀
      have hdivf : a ∣ f₀.map (Polynomial.evalRingHom x) := hdiv0 j₀
      have hxe : Polynomial.eval x P =
          Polynomial.eval x f₀.leadingCoeff *
          Polynomial.eval x h₀.leadingCoeff *
          Polynomial.eval x (Polynomial.resultant f₀ h₀) := by simp [P]
      have hlf : Polynomial.eval x f₀.leadingCoeff ≠ 0 := by
        intro hz; apply hx; rw [hxe, hz, zero_mul, zero_mul]
      have hlh : Polynomial.eval x h₀.leadingCoeff ≠ 0 := by
        intro hz; apply hx; rw [hxe, hz, mul_zero, zero_mul]
      have hres : Polynomial.eval x (Polynomial.resultant f₀ h₀) ≠ 0 := by
        intro hz; apply hx; rw [hxe, hz, mul_zero]
      have hfcoeff :
          (f₀.map (Polynomial.evalRingHom x)).coeff f₀.natDegree ≠ 0 := by
        rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
        exact hlf
      have hhcoeff :
          (h₀.map (Polynomial.evalRingHom x)).coeff h₀.natDegree ≠ 0 := by
        rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
        exact hlh
      have hdf : (f₀.map (Polynomial.evalRingHom x)).natDegree = f₀.natDegree :=
        le_antisymm Polynomial.natDegree_map_le
          (Polynomial.le_natDegree_of_ne_zero hfcoeff)
      have hdh : (h₀.map (Polynomial.evalRingHom x)).natDegree = h₀.natDegree :=
        le_antisymm Polynomial.natDegree_map_le
          (Polynomial.le_natDegree_of_ne_zero hhcoeff)
      have hresspec : Polynomial.resultant
          (f₀.map (Polynomial.evalRingHom x))
          (h₀.map (Polynomial.evalRingHom x)) ≠ 0 := by
        change Polynomial.resultant
          (f₀.map (Polynomial.evalRingHom x))
          (h₀.map (Polynomial.evalRingHom x))
          (f₀.map (Polynomial.evalRingHom x)).natDegree
          (h₀.map (Polynomial.evalRingHom x)).natDegree ≠ 0
        rw [hdf, hdh, Polynomial.resultant_map_map]
        exact hres
      have hcopSpec : IsCoprime
          (f₀.map (Polynomial.evalRingHom x))
          (h₀.map (Polynomial.evalRingHom x)) := by
        by_contra hn
        exact hresspec ((Polynomial.resultant_eq_zero_iff).2
          ⟨Or.inl (by
            intro hz
            exact hfcoeff (by rw [hz]; simp)), hn⟩)
      rcases hcopSpec with ⟨u, v, huv⟩
      have hca : a ∣ (1 : Polynomial F) := by
        rw [← huv]
        exact dvd_add (dvd_mul_of_dvd_right hdivf u)
          (dvd_mul_of_dvd_right hdivh v)
      exact isUnit_iff_dvd_one.mpr hca
  }
  refine ⟨w, ?_⟩
  change P.natDegree ≤ _
  have hlfcap : f₀.leadingCoeff.natDegree ≤ bchksXCap6399 := by
    rw [← Polynomial.coeff_natDegree]
    exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX f₀ f₀.natDegree).trans
      hfcaps.2
  have hlhcap : h₀.leadingCoeff.natDegree ≤ bchksXCap6399 := by
    rw [← Polynomial.coeff_natDegree]
    exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX h₀ h₀.natDegree).trans
      hhcaps.2
  have hfzcaps : f₀.natDegree ≤ bchksZCap6399 ∧
      Polynomial.Bivariate.degreeX f₀ ≤ bchksXCap6399 := by
    simpa [f₀] using hfcaps
  have hrCap := bivariate_resultant_natDegree_le
    f₀ h₀ f₀.natDegree h₀.natDegree
  refine Polynomial.natDegree_mul_le.trans ?_
  refine (Nat.add_le_add Polynomial.natDegree_mul_le hrCap).trans ?_
  nlinarith

end ProximityPrize.SubmissionLower
