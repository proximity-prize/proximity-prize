import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.Koala6831MovingTaylorDivision
import ProximityPrize.SubmissionLower.Koala6831MovingShortening

namespace ProximityPrize.SubmissionLower.Koala6831MovingShortenedCut

open scoped BigOperators
open RCN002 RCN047 RCN065 RCN077 RCN095 RCN136 RCN139 RCN156 RCN229 RCN231 RCN233 RCN238 RCN319
open RCN262 RCN263 RCN269
open RCN275 RCN313 RCN347

noncomputable section

variable {K E : Type} {L : Type*} [Field K] [Field E] [Field L]

private def jetBasis (φ : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (s u j : ℕ) : MvPolynomial (Fin 3) E :=
  surfaceMap φ (reducedAgreementNumerator F s u (fun k => if k = j then 1 else 0) 0 0 0)

private theorem jetBasis_eq (φ : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (s u j : ℕ) (hj : j ≤ u) :
    jetBasis φ F s u j = surfaceMap φ (reducedNumerator F s j) *
      surfaceMap φ (polyH K F) ^ (2 * (u - j)) * MvPolynomial.C ((-φ Polynomial.X) ^ j) := by
  unfold jetBasis reducedAgreementNumerator reducedClearedTaylorNumerator
  simp only [reducedCommonNumeratorTerm, affineSeedPolynomial, map_zero, zero_mul, add_zero,
    sub_zero, mul_zero]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))]
  · simp only [ite_eq_left True.intro, map_one, one_mul, map_mul, map_pow, zero_sub, map_neg,
      surfaceMap_X_zero]
  · intro k _ hk
    simp only [ite_eq_right hk, map_zero, zero_mul]

private def targetBasis (φ : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (s u : ℕ) (a b : K) : MvPolynomial (Fin 3) E :=
  surfaceMap φ (reducedAgreementNumerator F s u (fun _ => 0) 0 a b)

private theorem targetBasis_eq (φ : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (s u : ℕ) (a b : K) :
    targetBasis φ F s u a b =
      -(MvPolynomial.C (φ (Polynomial.C a)) + MvPolynomial.X (2 : Fin 3) *
        MvPolynomial.C (φ (Polynomial.C b))) * surfaceMap φ (polyH K F) ^ (2 * u) := by
  have hZ : surfaceMap φ (MvPolynomial.X (3 : Fin 4)) = MvPolynomial.X (2 : Fin 3) :=
    surfaceMap_X_succ φ (2 : Fin 3)
  simp only [targetBasis, reducedAgreementNumerator, reducedClearedTaylorNumerator,
    reducedCommonNumeratorTerm, map_zero, zero_mul, Finset.sum_const_zero, zero_sub, map_neg,
    map_mul, map_pow, affineSeedPolynomial, map_add, surfaceMap_C, hZ, neg_mul]

def linearCut (φ : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (s u : ℕ) (weights : ℕ → E) (a b : E) : MvPolynomial (Fin 3) E :=
  (∑ j ∈ Finset.range (u + 1),
    (weights j / (j.factorial : E) / ((-φ Polynomial.X) ^ j)) • jetBasis φ F s u j) +
    a • targetBasis φ F s u 1 0 + b • targetBasis φ F s u 0 1

theorem linearCut_in_flag (φ : Polynomial K →+* E) (P : ResidualSupportParameters)
    {F : MvPolynomial (Fin 4) K} (hF : ResidualSupportData P F)
    (u : ℕ) (weights : ℕ → E) (a b : E) :
    PolynomialInFlag (reducedResidualAgreementFlag P u) (linearCut φ F P.s u weights a b) := by
  classical
  let box := MvPolynomial.restrictSupport E {d | InFlag (reducedResidualAgreementFlag P u) d}
  change linearCut φ F P.s u weights a b ∈ box
  apply box.add_mem (box.add_mem ?_ ?_) ?_
  · apply Submodule.sum_mem
    intro j _
    apply box.smul_mem
    exact surfaceMap_reducedAgreement_in_flag φ P hF u _ _ _ _
  · exact box.smul_mem _ (surfaceMap_reducedAgreement_in_flag φ P hF u _ _ _ _)
  · exact box.smul_mem _ (surfaceMap_reducedAgreement_in_flag φ P hF u _ _ _ _)

abbrev coefficientMap (φ : Polynomial K →+* E) (ι : E →+* L) : K →+* L :=
  ι.comp (φ.comp Polynomial.C)

abbrev fullPoint (φ : Polynomial K →+* E) (ι : E →+* L) (v : Fin 3 → L) : Fin 4 → L :=
  Fin.cases (ι (φ Polynomial.X)) v

theorem evaluate_surface (φ : Polynomial K →+* E) (ι : E →+* L) (v : Fin 3 → L)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval₂Hom ι v (surfaceMap φ F) =
      MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι v) F := by
  have heq : (MvPolynomial.eval₂Hom ι v).comp (surfaceMap φ) =
      MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  exact DFunLike.congr_fun heq F

theorem taylor_globalPolynomial_coeff (κ : K →+* L) (v : Fin 4 → L)
    (F : MvPolynomial (Fin 4) K)
    (hF : MvPolynomial.eval₂Hom κ v F = 0)
    (hreg : MvPolynomial.eval₂Hom κ v (polyH K F) ≠ 0)
    (s w j : ℕ) (hj : j ≤ w) :
    (Polynomial.taylor (v 0) (globalPolynomial κ F v hF hreg w)).coeff j =
      MvPolynomial.eval₂Hom κ v (reducedNumerator F s j) *
        (MvPolynomial.eval₂Hom κ v (polyH K F))⁻¹ ^ (2 * j) / (j.factorial : L) := by
  have hred : MvPolynomial.eval₂Hom κ v (numerator K F j - reducedNumerator F s j) = 0 := by
    obtain ⟨Q, hQ⟩ := numerator_sub_reduced_dvd F s j
    rw [hQ, map_mul, hF, zero_mul]
  have heq : MvPolynomial.eval₂Hom κ v (numerator K F j) =
      MvPolynomial.eval₂Hom κ v (reducedNumerator F s j) := by
    rw [map_sub] at hred
    exact sub_eq_zero.mp hred
  simp only [globalPolynomial, Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero,
    reconstructedPolynomial, jetPolynomial_coeff, ite_eq_left (by omega : j < w + 1)]
  exact (jetCoefficient_eq_evaluated_numerator κ F v hF hreg j).trans (by rw [heq])

theorem linearCut_evaluate (φ : Polynomial K →+* E) (hφ : Function.Injective φ)
    (ι : E →+* L) (v : Fin 3 → L) (F : MvPolynomial (Fin 4) K)
    (hF : MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι v) F = 0)
    (hreg : MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι v) (polyH K F) ≠ 0)
    (s u w : ℕ) (hu : u ≤ w) (weights : ℕ → E) (a b : E) :
    let Φ := globalPolynomial (coefficientMap φ ι) F (fullPoint φ ι v) hF hreg w
    let S := MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι v) (polyH K F)
    MvPolynomial.eval₂Hom ι v (linearCut φ F s u weights a b) = S ^ (2 * u) *
      ((∑ j ∈ Finset.range (u + 1), ι (weights j) *
        (Polynomial.taylor (ι (φ Polynomial.X)) Φ).coeff j) - (ι a + v 2 * ι b)) := by
  classical
  let f := MvPolynomial.eval₂Hom ι v
  let evalFull := MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι v)
  let S := evalFull (polyH K F)
  let Φ := globalPolynomial (coefficientMap φ ι) F (fullPoint φ ι v) hF hreg w
  have hS : S ≠ 0 := hreg
  have hξ : φ Polynomial.X ≠ 0 := fun h => Polynomial.X_ne_zero (hφ (h.trans (map_zero φ).symm))
  have hshift (j : ℕ) : ι ((-φ Polynomial.X) ^ j) ≠ 0 := by
    rw [map_pow, map_neg]
    exact pow_ne_zero _ (neg_ne_zero.mpr ((map_ne_zero ι).mpr hξ))
  have hterm (j : ℕ) (hj : j ∈ Finset.range (u + 1)) :
      f ((weights j / (j.factorial : E) / ((-φ Polynomial.X) ^ j)) • jetBasis φ F s u j) =
        ι (weights j / (j.factorial : E)) * evalFull (reducedNumerator F s j) * S ^ (2 * (u - j)) := by
    rw [jetBasis_eq φ F s u j (by have := Finset.mem_range.mp hj; omega)]
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, evaluate_surface, f, evalFull, S,
      MvPolynomial.eval₂Hom_C]
    rw [map_pow, evaluate_surface]
    rw [map_div₀]
    calc
      _ = (ι (weights j / (j.factorial : E)) / ι ((-φ Polynomial.X) ^ j) *
          ι ((-φ Polynomial.X) ^ j)) * evalFull (reducedNumerator F s j) * S ^ (2 * (u - j)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ (hshift j)]
  have hsum : (∑ j ∈ Finset.range (u + 1), ι (weights j / (j.factorial : E)) *
        evalFull (reducedNumerator F s j) * S ^ (2 * (u - j))) =
      S ^ (2 * u) * ∑ j ∈ Finset.range (u + 1), ι (weights j) *
        (Polynomial.taylor (ι (φ Polynomial.X)) Φ).coeff j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjU : j ≤ u := by have := Finset.mem_range.mp hj; omega
    have hjW := hjU.trans hu
    have hc := taylor_globalPolynomial_coeff (coefficientMap φ ι) (fullPoint φ ι v)
      F hF hreg s w j hjW
    change (Polynomial.taylor (ι (φ Polynomial.X)) Φ).coeff j = _ at hc
    rw [hc, map_div₀, map_natCast, div_eq_mul_inv, div_eq_mul_inv]
    change _ = S ^ (2 * u) *
      (ι (weights j) * (evalFull (reducedNumerator F s j) * S⁻¹ ^ (2 * j) * (j.factorial : L)⁻¹))
    rw [show S ^ (2 * u) * (ι (weights j) *
        (evalFull (reducedNumerator F s j) * S⁻¹ ^ (2 * j) * (j.factorial : L)⁻¹)) =
        (S ^ (2 * u) * S⁻¹ ^ (2 * j)) *
        (ι (weights j) * (j.factorial : L)⁻¹ * evalFull (reducedNumerator F s j)) by ring,
      common_denominator_power S S⁻¹ (mul_inv_cancel₀ hS) u j hjU]
    ring
  change f (linearCut φ F s u weights a b) = _
  unfold linearCut
  rw [map_add, map_add, map_sum, Finset.sum_congr rfl hterm, hsum]
  rw [targetBasis_eq, targetBasis_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_neg, map_pow,
    f, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', map_one, map_zero,
    mul_zero, mul_one, add_zero, zero_add,
    evaluate_surface, evalFull, S]
  ring

universe v

theorem exists_shortened_cut (φ : Polynomial K →+* E) (hφ : Function.Injective φ)
    (P : ResidualSupportParameters) {F : MvPolynomial (Fin 4) K} (hData : ResidualSupportData P F)
    (locator baseline₀ baseline₁ : Polynomial E) (target target₀ target₁ : E)
    (u w : ℕ) (hu : u ≤ w) (hcenter : locator.eval (φ Polynomial.X) ≠ 0) :
    ∃ A : MvPolynomial (Fin 3) E,
      PolynomialInFlag (reducedResidualAgreementFlag P u) A ∧
      ∀ {M : Type v} [Field M] (ι : E →+* M) (q : Fin 3 → M)
        (hF : MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι q) F = 0)
        (hreg : MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι q) (polyH K F) ≠ 0)
        (Q : Polynomial M),
        let Φ := globalPolynomial (coefficientMap φ ι) F (fullPoint φ ι q) hF hreg w
        let S := MvPolynomial.eval₂Hom (coefficientMap φ ι) (fullPoint φ ι q) (polyH K F)
        Q.natDegree ≤ u →
        Φ = baseline₀.map ι + Polynomial.C (q 2) * baseline₁.map ι + locator.map ι * Q →
        MvPolynomial.eval₂Hom ι q A = S ^ (2 * u) *
          (Φ.eval (ι target) - (ι target₀ + q 2 * ι target₁)) := by
  obtain ⟨weights, a, b, hweights⟩ := Koala6831Moving.exists_shortened_affine_weights.{v}
    locator baseline₀ baseline₁ (φ Polynomial.X) target target₀ target₁ u hcenter
  refine ⟨linearCut φ F P.s u weights a b, linearCut_in_flag φ P hData u weights a b, ?_⟩
  intro M _ ι q hF hreg Q Φ S hQ hΦ
  have h := linearCut_evaluate φ hφ ι q F hF hreg P.s u w hu weights a b
  change MvPolynomial.eval₂Hom ι q (linearCut φ F P.s u weights a b) = S ^ (2 * u) *
      ((∑ j ∈ Finset.range (u + 1), ι (weights j) *
        (Polynomial.taylor (ι (φ Polynomial.X)) Φ).coeff j) - (ι a + q 2 * ι b)) at h
  rw [h, hweights ι (q 2) Φ Q hQ hΦ]

private theorem selected_fullPoint (φ : Polynomial K →+* E)
    (selected : K → Polynomial K) (γ : K) :
    fullPoint φ (RingHom.id E) (selectedPoint φ selected γ) =
      polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) := by
  funext i
  fin_cases i <;> rfl

theorem exists_prime_shortened_cut (φ : Polynomial K →+* E) (hφ : Function.Injective φ)
    (P : Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime]
    (support : ResidualSupportParameters) {F : MvPolynomial (Fin 4) K}
    (hData : ResidualSupportData support F) (hF : surfaceMap φ F ∈ P)
    (hH : surfaceMap φ (polyH K F) ∉ P)
    (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (p w : ℕ) [CharP E p] (hchar : w < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) (polyH K F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (hshort : (identityNodes φ P F nodes x u₀ u₁ w).card ≤ w)
    (i : Node) (hi : i ∈ nodes) (hiI : i ∉ identityNodes φ P F nodes x u₀ u₁ w) :
    ∃ A : MvPolynomial (Fin 3) E,
      PolynomialInFlag (reducedResidualAgreementFlag support
        (w - (identityNodes φ P F nodes x u₀ u₁ w).card)) A ∧ A ∉ P ∧
      ∀ γ ∈ Γ, (selected γ).eval (x i) = u₀ i + γ * u₁ i →
        MvPolynomial.aeval (selectedPoint φ selected γ) A = 0 := by
  classical
  let I := identityNodes φ P F nodes x u₀ u₁ w
  let u := w - I.card
  let κ := φ.comp (Polynomial.C : K →+* Polynomial K)
  let H := (Lagrange.nodal I x).map κ
  let B₀ := (Lagrange.interpolate I x u₀).map κ
  let B₁ := (Lagrange.interpolate I x u₁).map κ
  let jE := algebraMap E (CoordinateField E P)
  have hI : Set.InjOn x I := hx.mono (identityNodes_subset φ P F nodes x u₀ u₁ w)
  have hX (j : Node) : φ Polynomial.X ≠ κ (x j) := by
    intro heq
    have h := congrArg (fun T : Polynomial K => T.coeff 1) (hφ heq)
    simp at h
  have hcenter : H.eval (φ Polynomial.X) ≠ 0 := by
    simp only [H, Lagrange.nodal, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hX j)
  obtain ⟨A, hflag, hcut⟩ := exists_shortened_cut.{0} φ hφ support hData H B₀ B₁
    (κ (x i)) (κ (u₀ i)) (κ (u₁ i)) u w (Nat.sub_le _ _) hcenter
  refine ⟨A, hflag, ?_, ?_⟩
  · let Φ := truncatedPolynomial φ P F hF hH w
    have hident (j : Node) (hj : j ∈ I) :
        Φ.eval (componentCoefficients φ P (x j)) = componentCoefficients φ P (u₀ j) +
          coordinate E P 2 * componentCoefficients φ P (u₁ j) :=
      (agreement_mem_iff_truncated_value φ P F hF hH w (x j) (u₀ j) (u₁ j)).mp
        (Finset.mem_filter.mp hj).2
    obtain ⟨Q, hQ, hform, _⟩ := Koala6831Moving.exists_identity_shortened_tail
      (componentCoefficients φ P) I x u₀ u₁ hI w hshort (coordinate E P 2) Φ
      (truncatedPolynomial_natDegree_le φ P F hF hH w) hident
    have hΦ : Φ = B₀.map jE + Polynomial.C (coordinate E P 2) * B₁.map jE + H.map jE * Q := by
      simpa only [B₀, B₁, H, Polynomial.map_map, componentCoefficients, κ, jE] using hform
    have hne : Φ.eval (jE (κ (x i))) ≠ jE (κ (u₀ i)) + coordinate E P 2 * jE (κ (u₁ i)) := by
      intro heq
      apply hiI
      refine Finset.mem_filter.mpr ⟨hi, ?_⟩
      exact (agreement_mem_iff_truncated_value φ P F hF hH w (x i) (u₀ i) (u₁ i)).mpr heq
    have hcutEval := hcut jE (coordinate E P) (component_relation φ P F hF)
      (component_regular φ P F hH) Q hQ hΦ
    have hEval : MvPolynomial.eval₂Hom jE (coordinate E P) A ≠ 0 := by
      rw [hcutEval]
      exact mul_ne_zero (pow_ne_zero _ (component_regular φ P F hH)) (sub_ne_zero.mpr hne)
    intro hA
    apply hEval
    have hker : A ∈ RingHom.ker (MvPolynomial.aeval (coordinate E P)).toRingHom := by
      rwa [aeval_coordinate_ker]
    exact hker
  · intro γ hγ hagree
    let q := selectedPoint φ selected γ
    have hrel : MvPolynomial.eval₂Hom (coefficientMap φ (RingHom.id E))
        (fullPoint φ (RingHom.id E) q) F = 0 := by
      rw [show q = selectedPoint φ selected γ by rfl, selected_fullPoint]
      exact polynomialPoint_relation κ F (selected γ) γ (φ Polynomial.X) (hsolution γ hγ)
    have hreg : MvPolynomial.eval₂Hom (coefficientMap φ (RingHom.id E))
        (fullPoint φ (RingHom.id E) q) (polyH K F) ≠ 0 := by
      rw [show q = selectedPoint φ selected γ by rfl, selected_fullPoint]
      exact hregular γ hγ
    let Φ := globalPolynomial (coefficientMap φ (RingHom.id E)) F
      (fullPoint φ (RingHom.id E) q) hrel hreg w
    have hΦmap : Φ = (selected γ).map κ := by
      simpa only [Φ, q, selected_fullPoint, coefficientMap, RingHom.id_comp, κ] using
        (globalPolynomial_eq_map_of_solution κ F (selected γ) γ (φ Polynomial.X)
          (hsolution γ hγ) (hregular γ hγ) p w hchar (hdegree γ hγ))
    have hident (j : Node) (hj : j ∈ I) : Φ.eval (κ (x j)) = κ (u₀ j) + q 2 * κ (u₁ j) := by
      have h := selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
        (selected γ) γ (hdegree γ hγ) (hsolution γ hγ) (hregular γ hγ) (hpoint γ hγ) j hj
      rw [hΦmap, Polynomial.eval_map_apply, h, map_add, map_mul]
      rfl
    obtain ⟨Q, hQ, hform, _⟩ := Koala6831Moving.exists_identity_shortened_tail
      κ I x u₀ u₁ hI w hshort (q 2) Φ
      (globalPolynomial_natDegree_le _ _ _ _ _ _) hident
    have hΦ : Φ = B₀.map (RingHom.id E) + Polynomial.C (q 2) * B₁.map (RingHom.id E) +
        H.map (RingHom.id E) * Q := by simpa only [Polynomial.map_id] using hform
    have heval := hcut (RingHom.id E) q hrel hreg Q hQ hΦ
    have hzero : Φ.eval (κ (x i)) - (κ (u₀ i) + q 2 * κ (u₁ i)) = 0 := by
      rw [hΦmap, Polynomial.eval_map_apply, hagree, map_add, map_mul]
      exact sub_self _
    change MvPolynomial.eval₂Hom (RingHom.id E) q A = 0
    change MvPolynomial.eval₂Hom (RingHom.id E) q A = _ *
      (Φ.eval (κ (x i)) - (κ (u₀ i) + q 2 * κ (u₁ i))) at heval
    rw [heval, hzero, mul_zero]

end

end ProximityPrize.SubmissionLower.Koala6831MovingShortenedCut
