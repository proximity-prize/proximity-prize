import ProximityPrize.SubmissionLower.StructuralListPrice
import ProximityPrize.SubmissionLower.ListProofA

set_option Elab.async false

-- merged module StructuralListIncidence
section Merged_StructuralListIncidence

set_option Elab.async false

namespace StructuralList

open CJ0 Finset Polynomial
open K1_14_6 (occupancy)

noncomputable section

/-- Positions at which every polynomial in the finite family agrees with the word. -/
def commonSites (w : Node → K) (T : Finset (Polynomial K)) : Finset Node :=
  univ.filter fun i => ∀ f ∈ T, f.eval (node i) = w i

theorem mem_commonSites {w : Node → K} {T : Finset (Polynomial K)} {i : Node} :
    i ∈ commonSites w T ↔ ∀ f ∈ T, f.eval (node i) = w i := by
  simp [commonSites]

theorem commonSites_card_le {A w} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ close A w) (hsize : 1 < T.card) :
    (commonSites w T).card ≤ N := by
  obtain ⟨f, hf, g, hg, hfg⟩ := one_lt_card.mp hsize
  have hdeg {P : (Polynomial K)} (hP : P ∈ T) : P.natDegree ≤ N := by
    by_cases hz : P = 0
    · simp [hz, N]
    · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hz).2 (hT hP).1)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node node.injective (f - g)
    (sub_ne_zero.mpr hfg) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (hdeg hf) (hdeg hg)))
  intro i hi
  change (f-g).eval (node i) = 0
  rw [eval_sub, mem_commonSites.mp hi f hf, mem_commonSites.mp hi g hg, sub_self]

theorem firstMoment {A w} {T : Finset (Polynomial K)}
    (hT : (T : Set (Polynomial K)) ⊆ close A w) (hS : (commonSites w T).card ≤ A)
    (cap : ℚ) (hcap : ∀ i ∉ commonSites w T,
      ((T.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ cap) :
    ((A - (commonSites w T).card : ℕ) : ℚ) * T.card ≤
      ((n - (commonSites w T).card : ℕ) : ℚ) * cap := by
  classical
  let S := commonSites w T
  let candidates := (univ : Finset Node) \ S
  let hits := fun f : (Polynomial K) => univ.filter fun i : Node => f.eval (node i) = w i
  let occ := fun i : Node => (T.filter fun f => f.eval (node i) = w i).card
  have hcard : candidates.card = n - S.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, ProximityPrize.Benchmark.IRSProfile.card_index]
  have hnew (f : (Polynomial K)) (hf : f ∈ T) : A - S.card ≤ (hits f \ S).card := by
    have hsub : S ⊆ hits f := fun i hi => mem_filter.mpr ⟨mem_univ _, mem_commonSites.mp hi f hf⟩
    exact (Nat.sub_le_sub_right (hT hf).2 _).trans_eq (card_sdiff_of_subset hsub).symm
  have hsum : ∑ i ∈ candidates, occ i = ∑ f ∈ T, (hits f \ S).card := by
    simp only [occ, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun f _ => ?_
    rw [sum_boole, Nat.cast_id]
    have eqSet : (candidates.filter fun i => f.eval (node i) = w i) = hits f \ S := by
      ext i
      simp [candidates, hits, and_comm]
    rw [eqSet]
  have lower : T.card * (A - S.card) ≤ ∑ i ∈ candidates, occ i := by
    rw [hsum]
    calc
      _ = ∑ f ∈ T, (A - S.card) := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum hnew
  have hlower : (T.card : ℚ) * (A - S.card : ℕ) ≤ ∑ i ∈ candidates, (occ i : ℚ) := by
    exact_mod_cast lower
  calc
    _ = (T.card : ℚ) * (A - S.card : ℕ) := mul_comm _ _
    _ ≤ _ := hlower
    _ ≤ ∑ i ∈ candidates, cap := sum_le_sum fun i hi => hcap i (mem_sdiff.mp hi).2
    _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]

end

end StructuralList

end Merged_StructuralListIncidence

-- merged module StructuralListMain
section Merged_StructuralListMain

-- merged module ScalarCutCapacity
section Merged_ScalarCutCapacity
set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace ScalarCutCapacity
noncomputable section
open CJ0 CJ0_4 MvPolynomial Finset
open scoped BigOperators Polynomial
open CJ0 (valueCut valueCut_eval valueCut_degree curve_capacity)
open CJ0_4 (openEval openEval_localize openEval_chartMap)
open K1_14_6 (curve_degree_nat)
private def pullback (T : Chart 2) (x a : K) : InitialRing 2 :=
  (∑ j : Fin k, C (embed x ^ j.val) * T.numerator j) - C (embed a) * T.denominator
private theorem pullback_degree (T : Chart 2) (x a : K) (b : ℕ)
    (hd : T.denominator.totalDegree ≤ b) (hn : ∀ j, (T.numerator j).totalDegree ≤ b) :
    (pullback T x a).totalDegree ≤ b := by
  apply (totalDegree_sub _ _).trans
  refine max_le (totalDegree_finsetSum_le ?_) ?_
  · intro j _
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hn j)
  · exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hd)
private theorem eval_pullback (T : Chart 2) (x a : K) (y : Fin 3 → Geo)
    (hd : eval y T.denominator ≠ 0) :
    eval y (pullback T x a) = eval (T.output y) (valueCut x a) * eval y T.denominator := by
  simp only [pullback, valueCut, map_sub, map_sum, map_mul, eval_C, eval_X, Chart.output]
  rw [sub_mul, sum_mul]
  refine congrArg₂ (· - ·) (sum_congr rfl ?_) rfl
  intro j _
  rw [mul_assoc, div_mul_cancel₀ _ hd]
private def componentImage (T : Chart 2) (Q : Ideal (InitialRing 2)) : Set (Fin k → Geo) :=
  T.output '' {y | y ∈ zeroLocus Geo Q ∧ eval y T.denominator ≠ 0}
private theorem belongs_chart (T : Chart 2) {Q : Ideal (InitialRing 2)}
    (hle : sourceIdeal T ≤ Q) {y : Fin 3 → Geo}
    (hy : y ∈ zeroLocus Geo Q) (hd : eval y T.denominator ≠ 0) : y ∈ T.locus :=
  ⟨hy _ (hle (Ideal.mem_span_singleton_self T.equation)), hd⟩
private theorem clear_at_chart (T : Chart 2) (P : CoeffRing) :
    ∃ R : InitialRing 2, ∃ m : ℕ, ∀ y ∈ T.locus,
      eval y R = eval (T.output y) P * eval y T.denominator ^ m := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (chartMap T P)
  obtain ⟨R, rfl⟩ := Ideal.Quotient.mk_surjective a
  change chartMap T P * localize T T.denominator ^ m = localize T R at ha
  refine ⟨R, m, fun y hy => ?_⟩
  have hh := congrArg (openEval hy) ha
  rw [map_mul, map_pow, openEval_chartMap hy, openEval_localize hy, openEval_localize hy] at hh
  exact hh.symm
private theorem component_image_prime (T : Chart 2) (Q : Ideal (InitialRing 2))
    (hQ : Q.IsPrime) (hle : sourceIdeal T ≤ Q) (hD : T.denominator ∉ Q) :
    (vanishingIdeal Geo (componentImage T Q)).IsPrime := by
  let _ := hQ
  have hrad := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := Geo) Q
  have hpoint : ∃ y ∈ zeroLocus Geo Q, eval y T.denominator ≠ 0 := by
    by_contra! h
    apply hD
    rw [← hrad]
    exact h
  apply Ideal.isPrime_iff.mpr
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨y,hy,hdy⟩ := hpoint
    have hone : (1 : CoeffRing) ∈ vanishingIdeal Geo (componentImage T Q) := by rw [h]; trivial
    have hh := hone _ ⟨y, ⟨hy,hdy⟩, rfl⟩
    exact one_ne_zero (by simpa only [map_one] using hh)
  · intro P₁ P₂ hmul
    obtain ⟨R₁,m₁,h₁⟩ := clear_at_chart T P₁
    obtain ⟨R₂,m₂,h₂⟩ := clear_at_chart T P₂
    have hRs : T.denominator * (R₁ * R₂) ∈ Q := by
      rw [← hrad]
      intro y hy
      change eval y (T.denominator * (R₁ * R₂)) = 0
      by_cases hdy : eval y T.denominator = 0
      · rw [map_mul, hdy, zero_mul]
      · have hchart := belongs_chart T hle hy hdy
        have hh : eval (T.output y) (P₁ * P₂) = 0 :=
          hmul _ ⟨y, ⟨hy,hdy⟩, rfl⟩
        rw [map_mul] at hh
        rw [map_mul, map_mul, h₁ y hchart, h₂ y hchart]
        calc
          _ = (eval (T.output y) P₁ * eval (T.output y) P₂) *
              (eval y T.denominator * eval y T.denominator ^ m₁ * eval y T.denominator ^ m₂) := by ring
          _ = 0 := by rw [hh, zero_mul]
    have hor := hQ.mem_or_mem ((hQ.mem_or_mem hRs).resolve_left hD)
    have conclude {P : CoeffRing} {R : InitialRing 2} {m : ℕ}
        (hr : R ∈ Q) (he : ∀ y ∈ T.locus,
          eval y R = eval (T.output y) P * eval y T.denominator ^ m) :
        P ∈ vanishingIdeal Geo (componentImage T Q) := by
      rintro _ ⟨y, ⟨hy,hdy⟩, rfl⟩
      have hval : eval y R = 0 := hy R hr
      exact (mul_eq_zero.mp ((he y (belongs_chart T hle hy hdy)).symm.trans hval)).resolve_right
        (pow_ne_zero _ hdy)
    exact hor.imp (fun hr => conclude hr h₁) (fun hr => conclude hr h₂)
private theorem component_target (T : Chart 2) (x a : K)
    {Q : Ideal (InitialRing 2)} (hQ : Q.IsPrime) (hle : sourceIdeal T ≤ Q)
    (hD : T.denominator ∉ Q) (hcut : pullback T x a ∈ Q) :
    ∃ P ∈ (T.ideal ⊔ Ideal.span {valueCut x a}).minimalPrimesFinset,
      componentImage T Q ⊆ zeroLocus Geo P := by
  let J := vanishingIdeal Geo (componentImage T Q)
  let _ : J.IsPrime := component_image_prime T Q hQ hle hD
  have hT : T.ideal ≤ J := by
    intro q hq
    rintro _ ⟨y,⟨hy,hdy⟩,rfl⟩
    exact hq _ ⟨y, belongs_chart T hle hy hdy, rfl⟩
  have hC : valueCut x a ∈ J := by
    rintro _ ⟨y,⟨hy,hdy⟩,rfl⟩
    have he : eval y (pullback T x a) = 0 := hy _ hcut
    exact (mul_eq_zero.mp ((eval_pullback T x a y hdy).symm.trans he)).resolve_right hdy
  obtain ⟨P,hP,hPJ⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hT ((Ideal.span_singleton_le_iff_mem J).mpr hC))
  exact ⟨P,Ideal.mem_minimalPrimesFinset.mpr hP,fun y hy q hq => hPJ hq _ hy⟩
theorem cutCap {A w} {V : Finset (Polynomial K)} (T : Chart 2) (hT : ChartOK T)
    (hA : AgreementOK A) (hV : (V : Set (Polynomial K)) ⊆ close A w)
    (hcover : ∀ f∈V, coeffPoint f ∈ T.imageSet)
    (i : Node) (hmiss : ∃ f∈V, f.eval (node i) ≠ w i)
    (a : ℕ) (hden : T.denominator.totalDegree ≤ a) (hnum : ∀ j, (T.numerator j).totalDegree ≤ a) :
    (gap A : ℚ) * (V.filter (fun f => f.eval (node i) = w i)).card ≤
      (errors A : ℚ) * affineDegree T.ideal + (gap A : ℚ) * (a * T.equation.totalDegree : ℕ) := by
  classical
  let x := node i
  let b := w i
  let c := valueCut x b
  let r := pullback T x b
  let J := sourceIdeal T ⊔ Ideal.span {r}
  let D := T.ideal ⊔ Ideal.span {c}
  let src := J.retainedMinimalPrimes T.denominator
  let Vhit := V.filter fun f => f.eval x = b
  have hp : (sourceIdeal T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  let _ := hp
  obtain ⟨hprime,hdim⟩ := image_geometry T hT
  let _ := hprime
  have hsrcDim : (affineHilbertPolynomial (sourceIdeal T)).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      hT.irreducible.ne_zero hp.ne_top
    rw [Nat.card_fin] at h
    exact Nat.add_right_cancel h
  obtain ⟨f,hf,hmiss⟩ := hmiss
  obtain ⟨y,hy,hyf⟩ := hcover f hf
  have hcNe : eval (T.output y) c ≠ 0 := by
    rw [hyf]
    exact fun h => hmiss ((valueCut_eval (hV hf).1 x b).mp h)
  have hc : c ∉ T.ideal := fun hm => hcNe (hm _ ⟨y,hy,rfl⟩)
  have hr : r ∉ sourceIdeal T := by
    intro hh
    have hpt : y ∈ zeroLocus Geo (sourceIdeal T) := by
      apply mem_zeroLocus_iff_le_ker_aeval.mpr
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact RingHom.mem_ker.mpr hy.1
    have he : eval y r = 0 := hpt _ hh
    rw [eval_pullback T x b y hy.2] at he
    exact mul_ne_zero hcNe hy.2 he
  have srcDegree : (src.card : ℚ) ≤ (a * T.equation.totalDegree : ℕ) := by
    have hs := principalCut_sum_affineDegree_minimalPrimes_le hr (pullback_degree T x b a hden hnum)
    rw [show affineDegree (sourceIdeal T) = (T.equation.totalDegree : ℚ) from
      affineDegree_span_singleton hT.irreducible.ne_zero] at hs
    rw [Nat.cast_mul]
    calc
      _ = ∑ Q ∈ src, (1 : ℚ) := by simp
      _ ≤ ∑ Q ∈ src, affineDegree Q := by
        apply sum_le_sum
        intro Q hQ
        have hmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
        have hq := principalCut_natDegree_affineHilbertPolynomial_add_one hr hmin
        obtain ⟨n,hn,he⟩ := curve_degree_nat Q hmin.isPrime (by omega)
        rw [he]
        exact_mod_cast hn
      _ ≤ ∑ Q ∈ J.minimalPrimesFinset, affineDegree Q :=
        sum_le_sum_of_subset_of_nonneg (Ideal.retainedMinimalPrimes_subset _ _)
          (fun Q _ _ => affineDegree_nonneg Q)
      _ ≤ _ := hs
  have hcomp (Q : Ideal (InitialRing 2)) (hQ : Q ∈ src) :
      ∃ P ∈ D.minimalPrimesFinset, componentImage T Q ⊆ zeroLocus Geo P := by
    obtain ⟨hmin,hdenQ⟩ := Ideal.mem_retainedMinimalPrimes.mp hQ
    exact component_target T x b hmin.isPrime (le_sup_left.trans hmin.le) hdenQ
      (hmin.le ((show Ideal.span {r} ≤ J from le_sup_right) (Ideal.mem_span_singleton_self r)))
  let pick (Q : Ideal (InitialRing 2)) : Ideal CoeffRing :=
    if hQ : Q ∈ src then (hcomp Q hQ).choose else ⊤
  have picked (Q : Ideal (InitialRing 2)) (hQ : Q ∈ src) :
      pick Q ∈ D.minimalPrimesFinset ∧ componentImage T Q ⊆ zeroLocus Geo (pick Q) := by
    dsimp only [pick]
    rw [dite_eq_left hQ]
    exact (hcomp Q hQ).choose_spec
  let Ps := src.image pick
  have hPs : Ps ⊆ D.minimalPrimesFinset := by
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := mem_image.mp hP
    exact (picked Q hQ).1
  let part (P : Ideal CoeffRing) := Vhit.filter fun f => coeffPoint f ∈ zeroLocus Geo P
  have hpart : Vhit ⊆ Ps.biUnion part := by
    intro f hf
    obtain ⟨hfV,hfb⟩ := mem_filter.mp hf
    obtain ⟨z,hz,hzf⟩ := hcover f hfV
    have hzEq : eval z r = 0 := by
      have hv : eval (coeffPoint f) (valueCut x b) = 0 := (valueCut_eval (hV hfV).1 x b).mpr hfb
      rw [eval_pullback T x b z hz.2, hzf, hv, zero_mul]
    have hzJ : z ∈ zeroLocus Geo J := by
      apply mem_zeroLocus_sup_span_singleton_iff.mpr
      refine ⟨?_, hzEq⟩
      apply mem_zeroLocus_iff_le_ker_aeval.mpr
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact RingHom.mem_ker.mpr hz.1
    obtain ⟨Q,hQ,hzQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J T.denominator z hzJ hz.2
    refine mem_biUnion.mpr ⟨pick Q, mem_image.mpr ⟨Q,hQ,rfl⟩, mem_filter.mpr ⟨hf, ?_⟩⟩
    apply (picked Q hQ).2
    exact ⟨z,⟨hzQ,hz.2⟩,hzf⟩
  have hone (P : Ideal CoeffRing) (hP : P ∈ Ps) :
      (gap A : ℚ) * (part P).card ≤ (errors A : ℚ) * affineDegree P + gap A := by
    have hmin := Ideal.mem_minimalPrimesFinset.mp (hPs hP)
    have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hc hmin
    exact (curve_capacity (fun _ hf => hV (mem_filter.mp (mem_filter.mp hf).1).1) hA
      hmin.isPrime (by omega) (fun _ hf => (mem_filter.mp hf).2)).1
  have hsum : (Vhit.card : ℚ) ≤ ∑ P ∈ Ps, ((part P).card : ℚ) := by
    exact_mod_cast ((card_le_card hpart).trans card_biUnion_le)
  have hpdeg : (∑ P ∈ Ps, affineDegree P) ≤ affineDegree T.ideal := by
    apply (sum_le_sum_of_subset_of_nonneg hPs (fun P _ _ => affineDegree_nonneg P)).trans
    simpa only [D, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hc (valueCut_degree x b)
  have hcard : (Ps.card : ℚ) ≤ (a * T.equation.totalDegree : ℕ) :=
    (Nat.cast_le.mpr card_image_le).trans srcDegree
  calc
    _ ≤ (gap A : ℚ) * ∑ P ∈ Ps, ((part P).card : ℚ) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = ∑ P ∈ Ps, (gap A : ℚ) * (part P).card := mul_sum ..
    _ ≤ _ := sum_le_sum hone
    _ = (errors A : ℚ) * (∑ P ∈ Ps, affineDegree P) + (gap A : ℚ) * Ps.card := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm (Ps.card : ℚ)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hpdeg (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _))
end
end ScalarCutCapacity

end Merged_ScalarCutCapacity

-- merged module StructuralListMain
section Merged_StructuralListMain

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

namespace StructuralList

open CJ0 Polynomial PolynomialDifferential Finset
open scoped BigOperators

noncomputable section

/-- A shortened order-two chart using a prescribed set of common evaluations. -/
def ShortenChartClaim : Prop :=
  ∀ (s : Source) (_ : ShapeOK s) (G : CJ0_3.Equation) (_ : OrderTwo s G)
      (E : InitialRing 2) (_ : Irreducible E) (_ : E ∣ CJ0_3.initial G)
      (_ : ¬ E ∣ CJ0_3.initialSep G) (S : Finset Node) (_ : S.card + 3 ≤ k) (w : Node → K),
    ∃ T : Chart 2, ChartOK T ∧ T.equation = E ∧ ShortBand s (k-S.card) T ∧
      ∀ f : (Polynomial K), f.degree < k → differentialSpecialization G f = 0 →
        MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 →
        MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0 →
        (∀ i∈S, f.eval (node i)=w i) → coeffPoint f ∈ T.imageSet

private theorem factorPrice (shorten : ShortenChartClaim)
    {A w s} (hA : AgreementOK A) (hA₅ : k + 5 ≤ A) (hs : ShapeOK s)
    (hJ : 2 * s.C + 1 ≤ s.J) {G : CJ0_3.Equation} (hG : OrderTwo s G)
    {E : InitialRing 2} (hE : Irreducible E) (hEdvd : E ∣ CJ0_3.initial G)
    (hreg : ¬ E ∣ CJ0_3.initialSep G) (V : Finset (Polynomial K))
    (hV : (V : Set (Polynomial K)) ⊆ close A w)
    (hroots : ∀ f∈V, differentialSpecialization G f = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0) :
    (V.card : ℚ) ≤ baseFactor A * slicePrice A s k E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) + 1 := by
  classical
  by_cases hv : 1 < V.card
  · let S := commonSites w V
    obtain ⟨S', hsubset, hcard⟩ := exists_subset_card_eq (min_le_left S.card (k-3))
    have hshort : S'.card + 3 ≤ k := by rw [hcard]; have := min_le_right S.card (k-3); unfold k at *; omega
    have hL : k - S'.card = shortLength S.card := by
      rw [hcard]; unfold shortLength k; omega
    obtain ⟨T, hT, heq, hband, hcovers⟩ := shorten s hs G hG E hE hEdvd hreg S' hshort w
    rw [hL] at hband
    have hcov (f : (Polynomial K)) (hf : f ∈ V) : coeffPoint f ∈ T.imageSet := by
      obtain ⟨h₁, h₂, h₃⟩ := hroots f hf
      exact hcovers f (hV hf).1 h₁ h₂ h₃ (fun i hi => mem_commonSites.mp (hsubset hi) f hf)
    have hc : S.card ≤ N := commonSites_card_le hV hv
    have hS : S.card < A := hc.trans_lt hA.gt_degree
    have hd : (0 : ℚ) < gap A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
    have hdegree := volumeDegree s hs (shortLength S.card) (le_max_left ..) T hT hband
    rw [heq] at hdegree
    let price := slicePrice A s (shortLength S.card) E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2))
    have hprice (i : Node) (hi : i ∉ S) : ((V.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ price := by
      have hmiss : ∃ f∈V, f.eval (node i) ≠ w i := by
        simpa only [S, mem_commonSites, not_forall, exists_prop] using hi
      have cut := ScalarCutCapacity.cutCap T hT hA hV hcov i hmiss
        (totalCap s (shortLength S.card)) hband.denominator.1 (fun i => (hband.numerator i).1)
      rw [heq, Nat.cast_mul] at cut
      have price_mul : (gap A : ℚ) * price =
          (errors A : ℚ) * bandVolume s (shortLength S.card) E.totalDegree
            (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) +
          (gap A : ℚ) * ((totalCap s (shortLength S.card) : ℚ) * E.totalDegree) := by
        dsimp only [price, slicePrice, curveFactor]
        rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
      apply le_of_mul_le_mul_left _ hd
      rw [price_mul]
      exact cut.trans (add_le_add (mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg (errors A))) le_rfl)
    have hh := firstMoment hV hS.le price hprice
    have hu : (0 : ℚ) < (A - S.card : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hS)
    have hpart : (V.card : ℚ) ≤ incidenceFactor A S.card * price := by
      rw [incidenceFactor, div_mul_eq_mul_div, le_div_iff₀ hu, mul_comm (V.card : ℚ)]
      exact hh
    exact hpart.trans ((weighted_price A S.card s hs hJ hA₅ hA.lt_length.le hc ..).trans
      (le_add_of_nonneg_right zero_le_one))
  · have hc : (V.card : ℚ) ≤ 1 := by exact_mod_cast (show V.card ≤ 1 by omega)
    have hp : 0 ≤ baseFactor A * slicePrice A s k E.totalDegree
        (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) := by
      obtain ⟨ht, hi, hz⟩ := volume_nonneg s hs k (by decide)
      have hbf : 0 ≤ baseFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hcf : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      unfold slicePrice bandVolume
      positivity
    exact hc.trans (le_add_of_nonneg_left hp)

private theorem regularPrice (shorten : ShortenChartClaim)
    {A w s Q} (hA : AgreementOK A) (hA₅ : k + 5 ≤ A) (hs : ShapeOK s)
    (hJ : 2 * s.C + 1 ≤ s.J) (hQ : OrderTwo s Q) (T : Finset (Polynomial K))
    (hT : (T : Set (Polynomial K)) ⊆ close A w) (hreg : ∀ f∈T, RegularRoot Q f) :
    (T.card : ℚ) ≤ surfacePrice A s + s.B := by
  classical
  obtain ⟨F⟩ := CJ0_3_1.proof Q hQ.1
  let root (i : Fin F.count) (f : (Polynomial K)) := differentialSpecialization (F.source i) f = 0 ∧
    MvPolynomial.eval (CJ0_3.nativeJet f) (F.equation i) = 0 ∧
    MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep (F.source i)) ≠ 0
  let part (i : Fin F.count) := T.filter (root i)
  have hc : T.card ≤ ∑ i, (part i).card := by
    apply (card_le_card (t := univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i, hi⟩ := F.covers f (hreg f hf)
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hf, hi⟩⟩
  let b (i : Fin F.count) := (F.equation i).totalDegree
  let j (i : Fin F.count) := (F.equation i).weightedTotalDegree Fin.val
  let c (i : Fin F.count) := (F.equation i).degreeOf (Fin.last 2)
  have hp (i : Fin F.count) : ((part i).card : ℚ) ≤
      baseFactor A * slicePrice A s k (b i) (j i) (c i) + 1 :=
    factorPrice shorten hA hA₅ hs hJ (CJ0_3.orderTwo_of_dvd hQ (F.source_dvd i))
      (F.irreducible i) (F.component i) (F.regular i) (part i)
      (fun _ hf => hT (mem_filter.mp hf).1) (fun _ hf => (mem_filter.mp hf).2)
  obtain ⟨hb, hj, ht⟩ := CJ0_3.factor_weights hQ F
  have hn : F.count ≤ s.B := (CJ0_3.factor_count F).trans hb
  have hbq : (∑ i, (b i : ℚ)) ≤ s.B := by exact_mod_cast hb
  have hjq : (∑ i, (j i : ℚ)) ≤ s.J := by exact_mod_cast hj
  have hcq : (∑ i, (c i : ℚ)) ≤ s.C := by exact_mod_cast ht
  obtain ⟨hu, hv, hw⟩ := volume_nonneg s hs k (by decide)
  have hsum : (∑ i, bandVolume s k (b i) (j i) (c i)) ≤ R₂ s := by
    rw [← volume_full s hs]
    simp only [bandVolume, sum_add_distrib, ← mul_sum]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbq hu)
      (mul_le_mul_of_nonneg_left hjq hv)) (mul_le_mul_of_nonneg_left hcq hw)
  have hprice : (∑ i, slicePrice A s k (b i) (j i) (c i)) ≤
      curveFactor A * R₂ s + (s.B : ℚ) * totalCap s k := by
    simp only [slicePrice, sum_add_distrib, ← mul_sum]
    rw [mul_comm (s.B : ℚ)]
    exact add_le_add (mul_le_mul_of_nonneg_left hsum (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (mul_le_mul_of_nonneg_left hbq (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ i, ((part i).card : ℚ) := by exact_mod_cast hc
    _ ≤ ∑ i, (baseFactor A * slicePrice A s k (b i) (j i) (c i) + 1) := sum_le_sum fun i _ => hp i
    _ = baseFactor A * (∑ i, slicePrice A s k (b i) (j i) (c i)) + F.count := by
      simp only [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprice (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Nat.cast_le.mpr hn)

/-- Use the original rank certificate with proper value sections and shortened charts. -/
theorem scalar_list_of_shortening (shorten : ShortenChartClaim)
    (A : ℕ) (s : Source) (R : ℕ) (hA : AgreementOK A) (hA₅ : k+5 ≤ A)
    (hs : ShapeOK s) (hJ : 2*s.C+1 ≤ s.J) (hw : s.m ≤ s.m*A - N*s.B)
    (hsur : Surplus A s R) (hcert : RankCertificate A s R) : ScalarList A (tariff A s) := by
  classical
  intro w
  have horig : originRank A s ≤ R := by
    rcases hcert with h | ⟨cut, hcut, htail, hp⟩
    · exact h
    · exact (CJ0_1.proof A s cut hs hw hcut htail).trans hp
  have hr := (CJ0_2.proof A s hs hw w).trans (Nat.mul_le_mul_left n horig)
  have hdim := source_dimension A s hs hw
  unfold Surplus at hsur
  have hsmall : stackRank A s w < Fintype.card (ColumnIndex A s) := by omega
  obtain ⟨Q, hQ, hwt, hloc⟩ := interpolant hs hw w hsmall
  have hroot := specializes hwt hloc
  obtain ⟨Q₁, hQ₁, hremain₁⟩ := CJ0_5.proof s hs Q hQ
  obtain ⟨F₁, hF₁, hcover₁⟩ := CJ0_6.proof s hs Q₁ hQ₁
  obtain ⟨G, hG, hGdeg, hordinary⟩ := CJ0_8.proof s hs Q₁ hQ₁
  have hfin : (close A w).Finite :=
    ReedSolomon.closePolynomialSet_finite node w (show k ≤ A from hA.gt_degree)
  let T := hfin.toFinset
  have hall (f : (Polynomial K)) (hf : f ∈ T) : f ∈ close A w := hfin.mem_toFinset.mp hf
  let T₂ := T.filter (RegularRoot Q)
  let rest := T.filter fun f => ¬ RegularRoot Q f
  let T₁ := rest.filter (RegularRoot Q₁)
  let T₀ := rest.filter fun f => ¬ RegularRoot Q₁ f
  have h₂ (f) (hf : f ∈ T₂) := hall f (mem_filter.mp hf).1
  have hrest (f) (hf : f ∈ rest) := hall f (mem_filter.mp hf).1
  have h₁ (f) (hf : f ∈ T₁) := hrest f (mem_filter.mp hf).1
  have p₂ := regularPrice shorten hA hA₅ hs hJ hQ T₂
    (fun f hf => h₂ f hf) (fun _ hf => (mem_filter.mp hf).2)
  have hprice₁ := family_capacity (fun f hf => h₁ f hf) hA (Or.inl rfl) F₁ (CJ0_7.proof s hs F₁ hF₁)
    (fun f hf => hcover₁ f (h₁ f hf).1 (mem_filter.mp hf).2)
  have hd : (0 : ℚ) < gap A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
  have p₁ : (T₁.card : ℚ) ≤ curveFactor A * R₁ s + H s := by
    apply le_of_mul_le_mul_left _ hd
    unfold curveFactor
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
    simp only [one_mul] at hprice₁
    have hcount : (F₁.count : ℚ) ≤ H s := by exact_mod_cast hF₁.count
    exact hprice₁.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hd.le))
  have p₀ : T₀.card ≤ H s*(H s-1) := by
    refine (Polynomial.card_le_degree_of_subset_roots (p := G) ?_).trans hGdeg
    intro f hf
    obtain ⟨hr', hsing₁⟩ := mem_filter.mp (show f ∈ T₀ from hf)
    have hf' := hrest f hr'
    exact (Polynomial.mem_roots hG).mpr (hordinary f hf'.1
      (hremain₁ f hf'.1 (hroot f hf') (mem_filter.mp hr').2) hsing₁)
  have htail : ∀ h : ℕ, h+h*(h-1) = h^2 := by
    intro h
    cases h with
    | zero => rfl
    | succ h => rw [Nat.succ_sub_one]; ring
  have hp₀ : (H s : ℚ) + T₀.card ≤ (H s : ℚ)^2 := by
    exact_mod_cast (Nat.add_le_add_left p₀ (H s)).trans_eq (htail (H s))
  have hpart₂ : T₂.card + rest.card = T.card := card_filter_add_card_filter_not ..
  have hpart₁ : T₁.card + T₀.card = rest.card := card_filter_add_card_filter_not ..
  have hp : (T.card : ℚ) ≤ totalPrice A s := by
    rw [show T.card = T₂.card+T₁.card+T₀.card by omega, Nat.cast_add, Nat.cast_add]
    unfold totalPrice
    linarith only [p₂, p₁, hp₀]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact Nat.cast_le.mp (hp.trans (Nat.le_ceil _))

end

end StructuralList


end Merged_StructuralListMain

end Merged_StructuralListMain
