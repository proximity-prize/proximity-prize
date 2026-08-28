import ProximityPrize.SubmissionLower.BCHKSPartialSpecialization

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

lemma GoodAt.sum {z : F} {root : rationalRoot (monicize H) z}
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → 𝕃 H) (v : ι → F)
    (h : ∀ i ∈ s, GoodAt z root (a i) (v i)) :
    GoodAt z root (∑ i ∈ s, a i) (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty => simpa using GoodAt.zero (H:=H) z root
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact GoodAt.add (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma GoodAt.pow {z : F} {root : rationalRoot (monicize H) z}
    {a : 𝕃 H} {v : F} (h : GoodAt z root a v) :
    ∀ n, GoodAt z root (a^n) (v^n)
  | 0 => by
      refine ⟨1,1,by simp,by simp,by simp⟩
  | n+1 => by simpa [pow_succ] using GoodAt.mul (GoodAt.pow h n) h

/-- Base coefficient polynomials have their expected good specialization. -/
theorem GoodAt.liftToFunctionField (z : F)
    (root : rationalRoot (monicize H) z) (c : F[X]) :
    GoodAt z root (RationalFunctions.liftToFunctionField (H:=H) c) (c.eval z) := by
  refine ⟨(Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C c) : 𝒪 H),
    1, ?_, by simp, ?_⟩
  · rw [embeddingOf𝒪Into𝕃_mk]
    simp [liftBivariate_C]
  · simp [piZ_mk_C]

lemma GoodAt.fieldTo𝕃 (z : F) (root : rationalRoot (monicize H) z) (x : F) :
    GoodAt z root (RationalFunctions.fieldTo𝕃 (H:=H) x) x := by
  have h := GoodAt.liftToFunctionField (H:=H) z root (Polynomial.C x)
  simpa [RationalFunctions.fieldTo𝕃] using h

lemma PolyGoodAt.mul {z : F} {root : rationalRoot (monicize H) z}
    {p r : (𝕃 H)[X]} {q s : F[X]}
    (hp : PolyGoodAt z root p q) (hr : PolyGoodAt z root r s) :
    PolyGoodAt z root (p*r) (q*s) := by
  intro n
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply GoodAt.sum
  intro ij hij
  exact GoodAt.mul (hp ij.1) (hr ij.2)

lemma PolyGoodAt.pow {z : F} {root : rationalRoot (monicize H) z}
    {p : (𝕃 H)[X]} {q : F[X]} (hp : PolyGoodAt z root p q) :
    ∀ n, PolyGoodAt z root (p^n) (q^n)
  | 0 => by
      intro i
      by_cases hi : i=0
      · subst i; refine ⟨1,1,by simp,by simp,by simp⟩
      · simp [Polynomial.coeff_one, hi, GoodAt.zero]
  | n+1 => by simpa [pow_succ] using PolyGoodAt.mul (PolyGoodAt.pow hp n) hp

lemma PolyGoodAt.C {z : F} {root : rationalRoot (monicize H) z}
    {a : 𝕃 H} {v : F} (h : GoodAt z root a v) :
    PolyGoodAt z root (Polynomial.C a) (Polynomial.C v) := by
  intro i
  by_cases hi : i=0
  · subst i; simpa using h
  · simp [Polynomial.coeff_C, hi, GoodAt.zero]

lemma PolyGoodAt.X (z : F) (root : rationalRoot (monicize H) z) :
    PolyGoodAt z root (Polynomial.X : (𝕃 H)[X]) (Polynomial.X : F[X]) := by
  intro i
  by_cases hi : i=1
  · subst i; refine ⟨1,1,by simp,by simp,by simp⟩
  · have hi' : 1 ≠ i := Ne.symm hi
    simp [Polynomial.coeff_X, hi', GoodAt.zero]

/-- Synchronously built polynomial expressions preserve good specialization. -/
theorem PolyGoodAt.eval₂_of_induction
    (z : F) (root : rationalRoot (monicize H) z)
    (p : (𝕃 H)[X]) (q : F[X]) (xL : 𝕃 H) (x : F)
    (hp : PolyGoodAt z root p q) (hx : GoodAt z root xL x) :
    GoodAt z root (p.eval xL) (q.eval x) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  have hsub : q.support ⊆ p.support := by
    intro i hiq
    contrapose! hiq
    have hz := hp i
    have ha : p.coeff i = 0 := by simpa [Polynomial.mem_support_iff] using hiq
    rw [ha] at hz
    obtain ⟨b,d,hb,hd,hv⟩ := hz
    have hb0 : b=0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using hb
    subst b
    simp at hv
    simpa [Polynomial.mem_support_iff] using hv
  change GoodAt z root
    (∑ i ∈ p.support, p.coeff i * xL^i)
    (∑ i ∈ q.support, q.coeff i * x^i)
  have hqsum : (∑ i ∈ q.support, q.coeff i * x^i) =
      ∑ i ∈ p.support, q.coeff i * x^i := by
    apply Finset.sum_subset hsub
    intro i hip hiq
    have hz : q.coeff i = 0 := by
      simpa [Polynomial.mem_support_iff] using hiq
    simp [hz]
  rw [hqsum]
  apply GoodAt.sum
  intro i hi
  exact GoodAt.mul (hp i) (GoodAt.pow hx i)

end ProximityPrize.SubmissionLower
