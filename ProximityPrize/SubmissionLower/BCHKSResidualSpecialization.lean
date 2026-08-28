import ProximityPrize.SubmissionLower.BCHKSPartialSpecializationFunctor
import ProximityPrize.SubmissionLower.BCHKSFactorPigeon

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

lemma PolyGoodAt.sum {z : F} {root : rationalRoot (monicize H) z}
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → (𝕃 H)[X]) (q : ι → F[X])
    (h : ∀ i ∈ s, PolyGoodAt z root (p i) (q i)) :
    PolyGoodAt z root (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  induction s using Finset.induction_on with
  | empty =>
      intro n; simp
      exact GoodAt.zero (H:=H) z root
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact PolyGoodAt.add (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Composition of synchronously specialized polynomials. -/
theorem PolyGoodAt.comp {z : F} {root : rationalRoot (monicize H) z}
    {p u : (𝕃 H)[X]} {q v : F[X]}
    (hp : PolyGoodAt z root p q) (hu : PolyGoodAt z root u v) :
    PolyGoodAt z root (p.comp u) (q.comp v) := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.comp_eq_sum_left]
  have hsub : q.support ⊆ p.support := by
    intro i hiq
    contrapose! hiq
    have ha : p.coeff i=0 := by simpa [Polynomial.mem_support_iff] using hiq
    have hg := hp i
    rw [ha] at hg
    obtain ⟨b,d,hb,hd,hval⟩ := hg
    have hb0 : b=0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using hb
    subst b
    simp at hval
    simpa [Polynomial.mem_support_iff] using hval
  change PolyGoodAt z root
    (∑ i ∈ p.support, Polynomial.C (p.coeff i) * u^i)
    (∑ i ∈ q.support, Polynomial.C (q.coeff i) * v^i)
  have hqsum : (∑ i ∈ q.support, Polynomial.C (q.coeff i) * v^i) =
      ∑ i ∈ p.support, Polynomial.C (q.coeff i) * v^i := by
    apply Finset.sum_subset hsub
    intro i _ hi
    have hz : q.coeff i=0 := by simpa [Polynomial.mem_support_iff] using hi
    simp [hz]
  rw [hqsum]
  apply PolyGoodAt.sum
  intro i hi
  exact PolyGoodAt.mul (PolyGoodAt.C (hp i)) (PolyGoodAt.pow hu i)

/-- Coefficientwise relation for bivariate polynomials. -/
def BiPolyGoodAt (z : F) (root : rationalRoot (monicize H) z)
    (R : (𝕃 H)[X][Y]) (S : F[X][Y]) : Prop :=
  ∀ j, PolyGoodAt z root (R.coeff j) (S.coeff j)

lemma BiPolyGoodAt.eval {z : F} {root : rationalRoot (monicize H) z}
    {R : (𝕃 H)[X][Y]} {S : F[X][Y]} {p : (𝕃 H)[X]} {q : F[X]}
    (hR : BiPolyGoodAt z root R S) (hp : PolyGoodAt z root p q) :
    PolyGoodAt z root (R.eval p) (S.eval q) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  have hsub : S.support ⊆ R.support := by
    intro i hiS
    contrapose! hiS
    have hz : R.coeff i=0 := by simpa [Polynomial.mem_support_iff] using hiS
    have hg := hR i
    rw [hz] at hg
    have : S.coeff i=0 := by
      ext n
      have hn := hg n
      simp at hn
      obtain ⟨b,d,hb,hd,hv⟩ := hn
      have hb0 : b=0 := by
        apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
        simpa using hb
      subst b; simp at hv
      exact hv
    simpa [Polynomial.mem_support_iff] using this
  have hsum : (∑ i ∈ S.support, S.coeff i * q^i) =
      ∑ i ∈ R.support, S.coeff i * q^i := by
    apply Finset.sum_subset hsub
    intro i _ hi
    have hz : S.coeff i=0 := by simpa [Polynomial.mem_support_iff] using hi
    simp [hz]
  change PolyGoodAt z root
    (∑ i ∈ R.support, R.coeff i * p^i)
    (∑ i ∈ S.support, S.coeff i * q^i)
  rw [hsum]
  apply PolyGoodAt.sum
  intro i hi
  exact PolyGoodAt.mul (hR i) (PolyGoodAt.pow hp i)

lemma PolyGoodAt.truncSeries {z : F} {root : rationalRoot (monicize H) z}
    (a : ℕ → 𝕃 H) (b : ℕ → F) (N : ℕ)
    (h : ∀ i, i ≤ N → GoodAt z root (a i) (b i)) :
    PolyGoodAt z root (FiniteHensel.truncSeries a N)
      (FiniteHensel.truncSeries b N) := by
  unfold FiniteHensel.truncSeries
  apply PolyGoodAt.sum
  intro i hi
  rw [Finset.mem_range] at hi
  exact PolyGoodAt.monomial (h i (by omega)) i

/-- The lifted trivariate polynomial specializes coefficientwise to fixing Z. -/
theorem liftedR_goodAt_triSpecializeZ
    (R₀ : F[X][X][Y]) (z : F) (root : rationalRoot (monicize H) z) :
    BiPolyGoodAt z root (liftedR (R:=R₀) (H:=H)) (triSpecializeZ R₀ z) := by
  intro j i
  simp [liftedR, triSpecializeZ, Polynomial.coeff_map]
  exact GoodAt.liftToFunctionField (H:=H) z root ((R₀.coeff j).coeff i)

/-- Shift maps preserve the synchronized coefficient specialization. -/
theorem shifted_liftedR_goodAt
    (R₀ : F[X][X][Y]) (z : F) (root : rationalRoot (monicize H) z)
    (xL : 𝕃 H) (x : F) (hx : GoodAt z root xL x) :
    BiPolyGoodAt z root
      ((liftedR (R:=R₀) (H:=H)).map (FiniteHensel.shiftMap xL))
      ((triSpecializeZ R₀ z).map (FiniteHensel.shiftMap x)) := by
  intro j
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  simp only [FiniteHensel.shiftMap_apply]
  apply PolyGoodAt.comp (liftedR_goodAt_triSpecializeZ R₀ z root j)
  exact PolyGoodAt.add (PolyGoodAt.C hx) (PolyGoodAt.X (H:=H) z root)

/-- Fully automatic residual coefficient specialization. -/
theorem residual_goodAt
    (R₀ : F[X][X][Y]) (z : F) (root : rationalRoot (monicize H) z)
    (xL : 𝕃 H) (x : F) (hx : GoodAt z root xL x)
    (a : ℕ → 𝕃 H) (b : ℕ → F) (N : ℕ)
    (hab : ∀ i, i ≤ N → GoodAt z root (a i) (b i)) :
    PolyGoodAt z root
      (FiniteHensel.residual (liftedR (R:=R₀) (H:=H)) xL a N)
      (FiniteHensel.residual (triSpecializeZ R₀ z) x b N) := by
  unfold FiniteHensel.residual
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map]
  exact BiPolyGoodAt.eval (shifted_liftedR_goodAt R₀ z root xL x hx)
    (PolyGoodAt.truncSeries a b N hab)


/-- The concrete regular fraction specializes automatically to the ordinary
Taylor coefficient of an exact simple-root polynomial.  No coefficientwise
`hspecializes` hypothesis remains. -/
theorem concreteSpecializedAlpha_eq_TaylorCoeff
    (x₀ : F) (R₀ : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R₀ H)
    (hzeta : HenselNumerators.zeta R₀ x₀ H ≠ 0)
    (N : ℕ) (z : F) (root : rationalRoot (monicize H) z)
    (x y : F) (P : F[X])
    (hx : GoodAt z root (fieldTo𝕃 (H:=H) x₀) x)
    (hy : GoodAt z root (initialValue (H:=H)) y)
    (hsL : FiniteHensel.ySlope (liftedR (R:=R₀) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0)
    (hsimple : FiniteHensel.IsSimpleRootAt (triSpecializeZ R₀ z) x y)
    (hPy : P.eval x = y)
    (hPdeg : P.natDegree ≤ N)
    (hPexact : (triSpecializeZ R₀ z).eval P = 0)
    (hslope : GoodAt z root
      (FiniteHensel.ySlope (liftedR (R:=R₀) (H:=H))
        (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
      (FiniteHensel.ySlope (triSpecializeZ R₀ z) x y))
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : Polynomial.evalEval z root.1 (HenselNumerators.xiPre x₀ R₀ H) ≠ 0)
    (n : ℕ) (hn : n ≤ N) :
    concreteSpecializedAlpha x₀ R₀ hHyp hzeta N z root n =
      FiniteHensel.TaylorCoeff P x n := by
  have halpha : concreteSpecializedAlpha x₀ R₀ hHyp hzeta N z root n =
      FiniteHensel.liftCoeff (triSpecializeZ R₀ z) x y N n := by
    apply concreteSpecializedAlpha_eq_liftCoeff_of_residual_specializes
      x₀ R₀ hHyp hzeta N z root (triSpecializeZ R₀ z) x y hx hy hsL
      hsimple.2 hslope
    · intro m hm hstage
      exact residual_goodAt R₀ z root (fieldTo𝕃 (H:=H) x₀) x hx
        (fun i => (FiniteHensel.liftPoly (liftedR (R:=R₀) (H:=H))
          (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) N m).coeff i)
        (fun i => (FiniteHensel.liftPoly (triSpecializeZ R₀ z) x y N m).coeff i)
        N (fun i hi => hstage i) (m+1)
    · exact hW
    · exact hxi
    · exact hn
  rw [halpha]
  apply FiniteHensel.simpleRoot_unique_of_vanishesThrough
    (triSpecializeZ R₀ z) x y
    (FiniteHensel.liftCoeff (triSpecializeZ R₀ z) x y N)
    (FiniteHensel.TaylorCoeff P x) N hsimple
  · exact FiniteHensel.liftCoeff_zero _ _ _ _
  · rw [FiniteHensel.TaylorCoeff_zero]
    exact hPy
  · exact FiniteHensel.liftCoeff_vanishesThrough _ _ _ _ hsimple
  · exact FiniteHensel.TaylorCoeff_vanishesThrough _ _ _ _ hPdeg hPexact
  · exact hn

end ProximityPrize.SubmissionLower
