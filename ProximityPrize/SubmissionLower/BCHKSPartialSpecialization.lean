import ProximityPrize.SubmissionLower.BCHKSRegularDenSpecialization

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- A function-field value is good at a pair when it has a regular fraction
presentation whose denominator does not vanish there. -/
def GoodAt (z : F) (root : rationalRoot (monicize H) z) (a : 𝕃 H) (v : F) : Prop :=
  ∃ b d : 𝒪 H, embeddingOf𝒪Into𝕃 H b = a * embeddingOf𝒪Into𝕃 H d ∧
    piZ z root d ≠ 0 ∧ v = piZ z root b / piZ z root d

lemma GoodAt.zero (z : F) (root : rationalRoot (monicize H) z) :
    GoodAt z root (0 : 𝕃 H) 0 := by
  refine ⟨0, 1, by simp, by simp, by simp⟩

lemma GoodAt.neg {z : F} {root : rationalRoot (monicize H) z} {a : 𝕃 H} {v : F}
    (h : GoodAt z root a v) : GoodAt z root (-a) (-v) := by
  obtain ⟨b,d,he,hd,hv⟩ := h
  refine ⟨-b,d,?_,hd,?_⟩
  · rw [map_neg, he]; ring
  · rw [map_neg, hv]; ring

lemma GoodAt.add {z : F} {root : rationalRoot (monicize H) z}
    {a c : 𝕃 H} {v w : F} (ha : GoodAt z root a v) (hc : GoodAt z root c w) :
    GoodAt z root (a+c) (v+w) := by
  obtain ⟨b,d,hb,hd,hv⟩ := ha
  obtain ⟨e,f,he,hf,hw⟩ := hc
  refine ⟨b*f+e*d,d*f,?_,(by simpa using mul_ne_zero hd hf),?_⟩
  · simp only [map_add,map_mul,hb,he]; ring
  · simp only [map_add,map_mul,hv,hw]; field_simp

lemma GoodAt.mul {z : F} {root : rationalRoot (monicize H) z}
    {a c : 𝕃 H} {v w : F} (ha : GoodAt z root a v) (hc : GoodAt z root c w) :
    GoodAt z root (a*c) (v*w) := by
  obtain ⟨b,d,hb,hd,hv⟩ := ha
  obtain ⟨e,f,he,hf,hw⟩ := hc
  refine ⟨b*e,d*f,?_,(by simpa using mul_ne_zero hd hf),?_⟩
  · simp only [map_mul,hb,he]; ring
  · simp only [map_mul,hv,hw]; field_simp

lemma GoodAt.div {z : F} {root : rationalRoot (monicize H) z}
    {a c : 𝕃 H} {v w : F} (ha : GoodAt z root a v) (hc : GoodAt z root c w)
    (hw0 : w ≠ 0) : GoodAt z root (a/c) (v/w) := by
  obtain ⟨b,d,hb,hd,hv⟩ := ha
  obtain ⟨e,f,he,hf,hw⟩ := hc
  have hepi : piZ z root e ≠ 0 := by
    intro he0
    rw [he0, zero_div] at hw
    exact hw0 hw
  have heemb : embeddingOf𝒪Into𝕃 H e ≠ 0 := by
    intro h
    have : e = 0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using h
    subst e
    simp at hepi
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at he
    exact heemb he
  refine ⟨b*f,d*e,?_,(by simpa using mul_ne_zero hd hepi),?_⟩
  · simp only [map_mul,hb,he]
    field_simp [hc0, heemb]
    <;> ring
  · simp only [map_mul,hv,hw]
    field_simp

/-- Two good presentations of the same function-field value have the same
pair value. -/
lemma GoodAt.value_unique {z : F} {root : rationalRoot (monicize H) z}
    {a : 𝕃 H} {v w : F} (hv : GoodAt z root a v) (hw : GoodAt z root a w) : v=w := by
  obtain ⟨b,d,hb,hd,rfl⟩ := hv
  obtain ⟨e,f,he,hf,rfl⟩ := hw
  have hcross : b*f=e*d := by
    apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
    simp only [map_mul,hb,he]
    ring
  have hp := congrArg (piZ z root) hcross
  simp only [map_mul] at hp
  field_simp [hd,hf]
  calc
    _ = (piZ z root b) * (piZ z root f) := by ring
    _ = (piZ z root e) * (piZ z root d) := hp
    _ = _ := by ring

/-- Coefficientwise good specialization of polynomials. -/
def PolyGoodAt (z : F) (root : rationalRoot (monicize H) z)
    (p : (𝕃 H)[X]) (q : F[X]) : Prop :=
  ∀ i, GoodAt z root (p.coeff i) (q.coeff i)

lemma PolyGoodAt.add {z : F} {root : rationalRoot (monicize H) z}
    {p r : (𝕃 H)[X]} {q s : F[X]}
    (hp : PolyGoodAt z root p q) (hr : PolyGoodAt z root r s) :
    PolyGoodAt z root (p+r) (q+s) := by
  intro i
  simpa [Polynomial.coeff_add] using GoodAt.add (hp i) (hr i)

lemma PolyGoodAt.monomial {z : F} {root : rationalRoot (monicize H) z}
    {a : 𝕃 H} {v : F} (h : GoodAt z root a v) (n : ℕ) :
    PolyGoodAt z root (Polynomial.C a * (Polynomial.X : (𝕃 H)[X])^n)
      (Polynomial.C v * (Polynomial.X : F[X])^n) := by
  intro i
  by_cases hi : i=n
  · subst i; simpa using h
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hi, GoodAt.zero]

/-- Naturality of the finite lift algorithm under a good partial
specialization. The only structural premise is specialization of each residual
coefficient; it follows mechanically from coefficient specialization of `R`
using closure of `GoodAt` under polynomial sums and products. -/
theorem liftPoly_goodAt_induction
    (z : F) (root : rationalRoot (monicize H) z)
    (RL : (𝕃 H)[X][Y]) (RF : F[X][Y])
    (xL yL : 𝕃 H) (x y : F) (N : ℕ)
    (hx : GoodAt z root xL x) (hy : GoodAt z root yL y)
    (hsL : FiniteHensel.ySlope RL xL yL ≠ 0)
    (hsF : FiniteHensel.ySlope RF x y ≠ 0)
    (hslope : GoodAt z root (FiniteHensel.ySlope RL xL yL)
      (FiniteHensel.ySlope RF x y))
    (hres : ∀ m, m < N →
      PolyGoodAt z root (FiniteHensel.liftPoly RL xL yL N m)
        (FiniteHensel.liftPoly RF x y N m) →
      GoodAt z root
        ((FiniteHensel.residual RL xL
          (fun i => (FiniteHensel.liftPoly RL xL yL N m).coeff i) N).coeff (m+1))
        ((FiniteHensel.residual RF x
          (fun i => (FiniteHensel.liftPoly RF x y N m).coeff i) N).coeff (m+1))) :
    ∀ m, m ≤ N → PolyGoodAt z root
      (FiniteHensel.liftPoly RL xL yL N m)
      (FiniteHensel.liftPoly RF x y N m) := by
  intro m hm
  induction m with
  | zero =>
      intro i
      simp [FiniteHensel.liftPoly]
      by_cases hi : i=0
      · subst i; simpa using hy
      · simp [Polynomial.coeff_C, hi, GoodAt.zero]
  | succ m ih =>
      have hmN : m ≤ N := by omega
      have hold := ih hmN
      rw [FiniteHensel.liftPoly, FiniteHensel.liftPoly]
      apply PolyGoodAt.add hold
      apply PolyGoodAt.monomial
      apply GoodAt.div (GoodAt.neg (hres m (by omega) hold)) hslope hsF

/-- Consequently the concrete regular fraction is automatically the
specialized finite-lift coefficient; no per-coefficient equality hypothesis is
needed. -/
theorem concreteSpecializedAlpha_eq_liftCoeff_of_residual_specializes
    (x₀ : F) (R₀ : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R₀ H)
    (hzeta : HenselNumerators.zeta R₀ x₀ H ≠ 0)
    (N : ℕ) (z : F) (root : rationalRoot (monicize H) z)
    (RF : F[X][Y]) (x y : F)
    (hx : GoodAt z root (fieldTo𝕃 (H:=H) x₀) x)
    (hy : GoodAt z root (initialValue (H:=H)) y)
    (hsL : FiniteHensel.ySlope (liftedR (R:=R₀) (H:=H))
      (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) ≠ 0)
    (hsF : FiniteHensel.ySlope RF x y ≠ 0)
    (hslope : GoodAt z root
      (FiniteHensel.ySlope (liftedR (R:=R₀) (H:=H))
        (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)))
      (FiniteHensel.ySlope RF x y))
    (hres : ∀ m, m < N →
      PolyGoodAt z root
        (FiniteHensel.liftPoly (liftedR (R:=R₀) (H:=H))
          (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) N m)
        (FiniteHensel.liftPoly RF x y N m) →
      GoodAt z root
        ((FiniteHensel.residual (liftedR (R:=R₀) (H:=H))
          (fieldTo𝕃 (H:=H) x₀)
          (fun i => (FiniteHensel.liftPoly (liftedR (R:=R₀) (H:=H))
            (fieldTo𝕃 (H:=H) x₀) (initialValue (H:=H)) N m).coeff i) N).coeff (m+1))
        ((FiniteHensel.residual RF x
          (fun i => (FiniteHensel.liftPoly RF x y N m).coeff i) N).coeff (m+1)))
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : Polynomial.evalEval z root.1 (HenselNumerators.xiPre x₀ R₀ H) ≠ 0)
    (n : ℕ) (hn : n ≤ N) :
    concreteSpecializedAlpha x₀ R₀ hHyp hzeta N z root n =
      FiniteHensel.liftCoeff RF x y N n := by
  have hpoly := liftPoly_goodAt_induction z root
    (liftedR (R:=R₀) (H:=H)) RF (fieldTo𝕃 (H:=H) x₀)
    (initialValue (H:=H)) x y N hx hy hsL hsF hslope hres N (le_refl N)
  have ha : GoodAt z root (finiteAlpha (R:=R₀) (H:=H) x₀ N n)
      (FiniteHensel.liftCoeff RF x y N n) := by
    exact hpoly n
  have ht : n ≤ N := hn
  have hrep : GoodAt z root (finiteAlpha (R:=R₀) (H:=H) x₀ N n)
      (concreteSpecializedAlpha x₀ R₀ hHyp hzeta N z root n) := by
    refine ⟨concreteBetaUpTo x₀ R₀ hHyp hzeta N n,
      concreteDenRegularBridge x₀ R₀ hHyp n, ?_, ?_, rfl⟩
    · rw [concreteBetaUpTo_eq_betaRegular x₀ R₀ hHyp hzeta N n hn]
      exact embedding_betaRegular_eq_finiteAlpha_mul_denRegularBridge x₀ R₀ hHyp hzeta N n hn
    · unfold concreteDenRegularBridge
      rw [map_mul, map_pow, map_pow, piZ_mk_C,
        piZ_xi_eq_evalEval x₀ R₀ hHyp z root]
      exact mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hxi)
  exact GoodAt.value_unique hrep ha

end ProximityPrize.SubmissionLower
