import ProximityPrize.SubmissionLower.ListProofA

set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace ScalarCutCapacity
noncomputable section
open CJ0 CJ0_4 MvPolynomial Finset
open scoped BigOperators Polynomial
open private valueCut valueCut_eval valueCut_degree curve_capacity openEval
  openEval_localize openEval_chartMap from ProximityPrize.SubmissionLower.ListProofA
open private curve_degree_nat from ProximityPrize.SubmissionLower.Fast055

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

/-- Clearing the chart denominator makes evaluation of a coefficient polynomial
    on the whole chart equivalent to evaluation of a polynomial in the jet ring. -/
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

/-- A component's coefficient image on the open denominator has prime
    vanishing ideal, including when that image has dimension zero. -/
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

/-- Bound the agreeing subset of a proper evaluation section of a surface chart. -/
theorem cutCap {A w} {V : Finset K[X]} (T : Chart 2) (hT : ChartOK T)
    (hA : AgreementOK A) (hV : (V : Set K[X]) ⊆ close A w)
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

#print axioms cutCap
end
end ScalarCutCapacity
