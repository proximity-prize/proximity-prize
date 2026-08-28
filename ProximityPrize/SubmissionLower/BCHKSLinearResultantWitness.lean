import ProximityPrize.SubmissionLower.BCHKSLinearDegreeOneFinal
import ProximityPrize.SubmissionLower.BCHKSPrimitiveEffectiveResultant
import ProximityPrize.SubmissionLower.BCHKSConcreteNumerators

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private abbrev F := ProximityPrize.Benchmark.IRSProfile.Field

structure EffectivePrimitiveObstructionZ
    (F : Type) [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) where
  obstruction : Polynomial F
  ne : obstruction ≠ 0
  property : ∀ z : F, Polynomial.eval z obstruction ≠ 0 →
    (triSpecializeZ R z).IsPrimitive

noncomputable def localizedY {F : Type} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial (RatFunc F)) :=
  R.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

private theorem localizedY_irreducible_of_irreducible
    {F : Type} [Field F]
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : Irreducible R) (hpos : 0 < R.natDegree) :
    Irreducible (localizedY R) := by
  let A := Polynomial (Polynomial F)
  let K := RatFunc F
  let S := Polynomial K
  let M0 : Submonoid (Polynomial F) := nonZeroDivisors (Polynomial F)
  let M : Submonoid A := M0.map Polynomial.C
  letI : Algebra A S :=
    (Polynomial.mapRingHom (algebraMap (Polynomial F) K)).toAlgebra
  letI : IsLocalization M S := Polynomial.isLocalization M0 K
  have hM0 : ∀ m : M, (m : A) ≠ 0 := by
    intro m
    rcases m.property with ⟨p, hp, hpm⟩
    have hp0 : p ≠ 0 := by simpa [M0] using hp
    rw [← hpm]
    exact Polynomial.C_ne_zero.mpr hp0
  have hi := irreducible_map_of_isLocalization_of_natDegree_pos
    (S := S) M hM0 hR hpos
  simpa [localizedY, A, S, K] using hi

private theorem span_capsZ
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


private theorem span_map_dvdZ
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


private theorem coeff_one_isUnit_of_primitive_root
    {F : Type*} [Field F] (S : Polynomial (Polynomial F)) (P : Polynomial F)
    (hprim : S.IsPrimitive) (hdeg : S.natDegree ≤ 1)
    (hroot : Polynomial.eval P S = 0) : IsUnit (S.coeff 1) := by
  apply (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprim)
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro j
  rcases j with _ | j
  · have hshape : S = Polynomial.C (S.coeff 0) +
        Polynomial.C (S.coeff 1) * Polynomial.X := by
      ext n
      rcases n with _ | n
      · simp
      rcases n with _ | n
      · simp
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt hdeg (by omega))]
        simp
    rw [hshape] at hroot
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X] at hroot
    refine ⟨-P, ?_⟩
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left hroot
  rcases j with _ | j
  · exact dvd_rfl
  · have hz : S.coeff (Nat.succ (Nat.succ j)) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
    rw [hz]
    exact dvd_zero _

private theorem effectivePrimitiveObstructionZ_of_irreducible
    (R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (DZ DX k : ℕ) (hcard : DX + 1 < Fintype.card F)
    (hRdeg : R.natDegree = 1)
    (hZ : ∀ j, (R.coeff j).natDegree ≤ DX)
    (hZone : (R.coeff 1).natDegree + k ≤ DX)
    (hX : ∀ j, Polynomial.Bivariate.degreeX (R.coeff j) ≤ DZ) :
    ∃ w : EffectivePrimitiveObstructionZ
        ProximityPrize.Benchmark.IRSProfile.Field R,
      w.obstruction.natDegree ≤
        (2 * DX + 2 - k) * DZ := by
  classical
  let c₀ : ℕ → Polynomial (Polynomial F) := fun j =>
    R.coeff j
  let L := polynomialRatFuncLinearMap F
  let c : ℕ → Polynomial (RatFunc F) := fun j => L (c₀ j)
  have hc : c = (localizedY R).coeff := by
    funext j
    simp [c, c₀, L, polynomialRatFuncLinearMap, localizedY]
  have hi := localizedY_irreducible_of_irreducible hR hpos
  have hloc0 : localizedY R ≠ 0 := hi.ne_zero
  have hinj : Function.Injective
      (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) :=
    Polynomial.map_injective _ (IsFractionRing.injective F[X] (RatFunc F))
  have hlocpos : 0 < (localizedY R).natDegree := by
    rw [localizedY, Polynomial.natDegree_map_eq_of_injective hinj]
    omega
  let j₀ := (localizedY R).natDegree
  have hj₀ : j₀ = 1 := by
    dsimp [j₀]
    rw [localizedY, Polynomial.natDegree_map_eq_of_injective hinj, hRdeg]
  have hf : c j₀ ≠ 0 := by
    rw [hc]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hloc0
  have htop : Ideal.span (Set.range c) = ⊤ := by
    rw [hc]
    exact span_range_coeff_eq_top_of_isPrimitive (hi.isPrimitive (by
      omega))
  obtain ⟨hraw, hhraw, hcopraw⟩ := exists_primitive_localized_selection
    c j₀ (DX + 1) hf htop
    (lt_of_le_of_lt (by
      rw [show (c j₀).natDegree = (c₀ j₀).natDegree by
        exact Polynomial.natDegree_map_eq_of_injective
          (IsFractionRing.injective F[X] (RatFunc F)) (c₀ j₀)]
      exact hZ j₀) (Nat.lt_succ_self _))
    hcard
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
  have hfcaps := span_capsZ c₀ DX DZ
    (by simpa [c₀] using hZ) (by simpa [c₀] using hX)
    (Submodule.subset_span (Set.mem_range_self j₀))
  have hhcaps := span_capsZ c₀ DX DZ
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
  let w : EffectivePrimitiveObstructionZ F R := {
    obstruction := P
    ne := hP
    property := by
      intro x hx
      rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
      intro a ha
      have hac : ∀ j, a ∣ (triSpecializeZ R x).coeff j :=
        (Polynomial.C_dvd_iff_dvd_coeff a _).mp ha
      have hdiv0 : ∀ j, a ∣
          (c₀ j).map (Polynomial.evalRingHom x) := by
        intro j
        simpa [c₀, triSpecializeZ] using hac j
      have hdivh : a ∣ h₀.map (Polynomial.evalRingHom x) :=
        span_map_dvdZ c₀ x a hdiv0 hh₀
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
  have hlfcap : f₀.leadingCoeff.natDegree ≤ DZ := by
    rw [← Polynomial.coeff_natDegree]
    exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX f₀ f₀.natDegree).trans
      hfcaps.2
  have hlhcap : h₀.leadingCoeff.natDegree ≤ DZ := by
    rw [← Polynomial.coeff_natDegree]
    exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX h₀ h₀.natDegree).trans
      hhcaps.2
  have hfzcaps : f₀.natDegree ≤ DX ∧
      Polynomial.Bivariate.degreeX f₀ ≤ DZ := by
    simpa [f₀] using hfcaps
  have hfzsharp : f₀.natDegree + k ≤ DX := by
    simpa [f₀, c₀, hj₀] using hZone
  have hrCap := bivariate_resultant_natDegree_le
    f₀ h₀ f₀.natDegree h₀.natDegree
  refine Polynomial.natDegree_mul_le.trans ?_
  refine (Nat.add_le_add Polynomial.natDegree_mul_le hrCap).trans ?_
  have hsum : h₀.natDegree + f₀.natDegree + 2 ≤ 2 * DX + 2 - k := by
    omega
  have hfx : Polynomial.Bivariate.degreeX f₀ ≤ DZ := hfzcaps.2
  have hhx : Polynomial.Bivariate.degreeX h₀ ≤ DZ := hhcaps.2
  calc
    f₀.leadingCoeff.natDegree + h₀.leadingCoeff.natDegree +
        (h₀.natDegree * Polynomial.Bivariate.degreeX f₀ +
          f₀.natDegree * Polynomial.Bivariate.degreeX h₀) ≤
        DZ + DZ + (h₀.natDegree * DZ + f₀.natDegree * DZ) := by
          gcongr
    _ = (h₀.natDegree + f₀.natDegree + 2) * DZ := by ring
    _ ≤ (2 * DX + 2 - k) * DZ := Nat.mul_le_mul_right DZ hsum


/-- A single resultant obstruction for the linear-in-Y branch. -/
theorem exists_linear_resultant_witness
    (R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hRi : Irreducible R) (hRdeg : R.natDegree = 1)
    (hYZ : YZCap R 519142)
    (hWeighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 111624646)
    (T : Finset ProximityPrize.Benchmark.IRSProfile.Field)
    (P : ProximityPrize.Benchmark.IRSProfile.Field →
      Polynomial ProximityPrize.Benchmark.IRSProfile.Field)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0) :
    ∃ Res : Polynomial ProximityPrize.Benchmark.IRSProfile.Field,
      Res ≠ 0 ∧ Res.natDegree ≤ (2 * 111624646 - 131071) * 519142 ∧
      ∀ z ∈ T, Res.eval z ≠ 0 → ∀ x,
        (linearHSpecialization R z x).natDegree = 1 := by
  classical
  have hOuter : ∀ j, (R.coeff j).natDegree ≤ 111624645 := by
    intro j
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hne : (R.coeff j).coeff (R.coeff j).natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hz
      have hw := hWeighted j (R.coeff j).natDegree hne
      omega
  have hInner : ∀ j, Polynomial.Bivariate.degreeX (R.coeff j) ≤ 519142 := by
    intro j
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    by_cases hz : (R.coeff j).coeff a = 0
    · simp [hz]
    · exact (Nat.le_add_right _ _).trans (hYZ j a hz)
  have hCoeffOne : R.coeff 1 ≠ 0 := by
    rw [← hRdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hRi.ne_zero
  have hOuterOne : (R.coeff 1).natDegree + 131071 ≤ 111624645 := by
    have hne : (R.coeff 1).coeff (R.coeff 1).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hCoeffOne
    have hw := hWeighted 1 (R.coeff 1).natDegree hne
    omega
  obtain ⟨w, hwdeg⟩ := effectivePrimitiveObstructionZ_of_irreducible
    R hRi (by omega) 519142 111624645 131071 (by norm_num [F,
      ProximityPrize.Benchmark.IRSProfile.Field]) hRdeg hOuter hOuterOne hInner
  refine ⟨w.obstruction, w.ne, ?_, ?_⟩
  · exact hwdeg.trans (by norm_num)
  intro z hzT hzRes x
  have hprim := w.property z hzRes
  have hdeg : (triSpecializeZ R z).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_map_le).trans (by omega)
  have hroot : Polynomial.eval (P z) (triSpecializeZ R z) = 0 := by
    simpa [triEval, triSpecializeZ] using hvan z hzT
  have hu : IsUnit ((triSpecializeZ R z).coeff 1) :=
    coeff_one_isUnit_of_primitive_root _ _ hprim hdeg hroot
  have hcoeff : (linearHSpecialization R z x).coeff 1 ≠ 0 := by
    have he : Polynomial.eval x ((triSpecializeZ R z).coeff 1) ≠ 0 :=
      (hu.map (Polynomial.evalRingHom x)).ne_zero
    simpa [linearHSpecialization, triSpecializeZ] using he
  apply le_antisymm
  · exact Polynomial.natDegree_map_le.trans (by omega)
  · exact Polynomial.le_natDegree_of_ne_zero hcoeff

end ProximityPrize.SubmissionLower
