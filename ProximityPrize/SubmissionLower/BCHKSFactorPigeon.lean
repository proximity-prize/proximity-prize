import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

/-- A finite pigeonhole principle for a relation which may relate one source
point to several possible pigeonholes. -/
theorem exists_large_rel_fiber
    {σ π : Type*} [DecidableEq σ] [DecidableEq π]
    (S : Finset σ) (P : Finset π) (R : σ → π → Prop) [DecidableRel R]
    (DY B : Nat)
    (hR : ∀ s ∈ S, ∃ p ∈ P, R s p)
    (hP : P.card ≤ DY) (hS : DY * B < S.card) :
    ∃ p ∈ P, B < (S.filter fun s => R s p).card := by
  by_contra h
  push Not at h
  have hsub : S ⊆ P.biUnion (fun p => S.filter fun s => R s p) := by
    intro s hs
    obtain ⟨p, hp, hsp⟩ := hR s hs
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    exact ⟨p, hp, hs, hsp⟩
  have hcard : S.card ≤ P.card * B :=
    (Finset.card_le_card hsub).trans
      (Finset.card_biUnion_le_card_mul P (fun p => S.filter fun s => R s p) B h)
  exact (not_lt_of_ge (hcard.trans (Nat.mul_le_mul_right B hP))) hS

/-- If the image under a specialization of the product of all normalized
factors vanishes in a domain, one of the normalized factors vanishes. -/
theorem exists_normalizedFactor_map_eq_zero_of_prod_map_eq_zero
    {A K : Type*} [CommSemiring A] [NormalizationMonoid A]
    [UniqueFactorizationMonoid A] [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
    (φ : A →+* K) (Q : A)
    (h : φ (UniqueFactorizationMonoid.normalizedFactors Q).prod = 0) :
    ∃ q ∈ UniqueFactorizationMonoid.normalizedFactors Q, φ q = 0 := by
  have hprod :
      (Multiset.map φ (UniqueFactorizationMonoid.normalizedFactors Q)).prod = 0 := by
    rw [← map_multiset_prod]
    exact h
  obtain ⟨q, hq, hq0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
  exact ⟨q, hq, hq0⟩

/-- A vanishing element has a normalized factor which vanishes under the same
specialization. -/
theorem exists_normalizedFactor_map_eq_zero
    {A K : Type*} [CommSemiring A] [NormalizationMonoid A]
    [UniqueFactorizationMonoid A] [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
    (φ : A →+* K) {Q : A} (hQ : Q ≠ 0) (h : φ Q = 0) :
    ∃ q ∈ UniqueFactorizationMonoid.normalizedFactors Q, φ q = 0 := by
  apply exists_normalizedFactor_map_eq_zero_of_prod_map_eq_zero φ Q
  exact ((UniqueFactorizationMonoid.prod_normalizedFactors hQ).map φ).eq_zero_iff.mpr h

/-- Polynomial-evaluation form of
`exists_normalizedFactor_map_eq_zero_of_prod_map_eq_zero`. -/
theorem exists_normalizedFactor_eval_eq_zero_of_prod_eval_eq_zero
    {K : Type*} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
    [NormalizationMonoid (Polynomial K)] [UniqueFactorizationMonoid (Polynomial K)]
    (Q : Polynomial K) (z : K)
    (h : Polynomial.eval z
      (UniqueFactorizationMonoid.normalizedFactors Q).prod = 0) :
    ∃ q ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      Polynomial.eval z q = 0 := by
  exact exists_normalizedFactor_map_eq_zero_of_prod_map_eq_zero
    (Polynomial.evalRingHom z) Q h

/-- If a nonzero polynomial specializes to zero at `z`, one of its normalized
factors specializes to zero there. -/
theorem exists_normalizedFactor_eval_eq_zero
    {K : Type*} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
    [NormalizationMonoid (Polynomial K)] [UniqueFactorizationMonoid (Polynomial K)]
    {Q : Polynomial K} (hQ : Q ≠ 0) (z : K) (h : Polynomial.eval z Q = 0) :
    ∃ q ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      Polynomial.eval z q = 0 := by
  exact exists_normalizedFactor_map_eq_zero (Polynomial.evalRingHom z) hQ h


/-! ### Concrete nested-polynomial factor selection -/

/-- Substitute `Z = z` and then `Y = P(X)` in a polynomial represented as
`F[Z][X][Y]`. -/
noncomputable def triEval {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F) :
    Polynomial F :=
  Polynomial.eval P
    (Polynomial.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) Q)

/-- Substitute `X = x₀` in a polynomial represented as `F[Z][X][Y]`, leaving
an element of `F[Z][Y]`. -/
noncomputable def triSpecializeX {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (x₀ : F) :
    Polynomial (Polynomial F) :=
  Polynomial.map (Polynomial.evalRingHom (Polynomial.C x₀)) Q

/-- Evaluate an `F[Z][Y]` polynomial at `(Y,Z) = (y,z)`. -/
noncomputable def biEval {F : Type*} [Field F]
    (H : Polynomial (Polynomial F)) (y z : F) : F :=
  Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom z) H)

lemma eval_map_eval_eq_eval_eval_C
    {F : Type*} [Field F]
    (A : Polynomial (Polynomial F)) (x z : F) :
    Polynomial.eval x (Polynomial.map (Polynomial.evalRingHom z) A) =
      Polynomial.eval z (Polynomial.eval (Polynomial.C x) A) := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp [hA, hB]
  | monomial n a => simp [Polynomial.map_monomial, Polynomial.eval_monomial]

lemma eval_triEval_eq_biEval_triSpecializeX
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (P : Polynomial F) (x₀ z : F) :
    Polynomial.eval x₀ (triEval Q z P) =
      biEval (triSpecializeX Q x₀) (Polynomial.eval x₀ P) z := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
      calc
        Polynomial.eval x₀ (triEval (Q + R) z P) =
            Polynomial.eval x₀ (triEval Q z P) +
              Polynomial.eval x₀ (triEval R z P) := by simp [triEval]
        _ = biEval (triSpecializeX Q x₀) (Polynomial.eval x₀ P) z +
              biEval (triSpecializeX R x₀) (Polynomial.eval x₀ P) z := by rw [hQ, hR]
        _ = biEval (triSpecializeX (Q + R) x₀) (Polynomial.eval x₀ P) z := by
              simp [triSpecializeX, biEval]
  | monomial n A =>
      simp [triEval, triSpecializeX, biEval, Polynomial.map_monomial,
        Polynomial.eval_monomial, eval_map_eval_eq_eval_eval_C]

/-- Candidate pairs consisting of a normalized trivariate factor `R` of `Q`
and a normalized bivariate factor `H` of `R(X₀,Y,Z)`. -/
noncomputable def normalizedFactorPairs
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (x₀ : F) :
    Finset (Polynomial (Polynomial (Polynomial F)) × Polynomial (Polynomial F)) :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.biUnion fun R =>
    (UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀)).toFinset.image
      fun H => (R, H)



/-- Two-stage factor selection for `F[Z][X][Y]`.  The finite set `T` lives
in the subtype `S`, so `T ⊆ S.attach` is the literal subtype version of
`T ⊆ S`.  The hypothesis `hx₀` is the promised goodness of `x₀`: no
normalized trivariate factor disappears identically after substituting `X=x₀`.
The caller may bound the finite candidate-pair set by any convenient `DY`. -/
theorem exists_normalizedFactorPair_large_fiber
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (S : Finset F) (Pz : ↥S → Polynomial F) (x₀ : F)
    (hvanish : ∀ z : ↥S, triEval Q z.1 (Pz z) = 0)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0)
    (DY B : Nat) (hpairs : (normalizedFactorPairs Q x₀).card ≤ DY)
    (hS : DY * B < S.card) :
    ∃ R : Polynomial (Polynomial (Polynomial F)),
      ∃ H : Polynomial (Polynomial F), ∃ T : Finset ↥S,
        R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) ∧
        T ⊆ S.attach ∧ B < T.card ∧
        ∀ z ∈ T,
          triEval R z.1 (Pz z) = 0 ∧
          biEval H (Polynomial.eval x₀ (Pz z)) z.1 = 0 := by
  let Rel : ↥S →
      (Polynomial (Polynomial (Polynomial F)) × Polynomial (Polynomial F)) → Prop :=
    fun z RH =>
      triEval RH.1 z.1 (Pz z) = 0 ∧
        biEval RH.2 (Polynomial.eval x₀ (Pz z)) z.1 = 0
  have htotal : ∀ z ∈ S.attach, ∃ RH ∈ normalizedFactorPairs Q x₀, Rel z RH := by
    intro z _hz
    let φ : Polynomial (Polynomial (Polynomial F)) →+* Polynomial F :=
      (Polynomial.evalRingHom (Pz z)).comp
        (Polynomial.mapRingHom
          (Polynomial.mapRingHom (Polynomial.evalRingHom z.1)))
    have hφ : φ Q = 0 := by
      simpa [φ, triEval] using hvanish z
    obtain ⟨R, hRQ, hRzero⟩ :=
      exists_normalizedFactor_map_eq_zero (Q := Q) φ hQ hφ
    have hRtri : triEval R z.1 (Pz z) = 0 := by
      simpa [φ, triEval] using hRzero
    have hpoint :
        biEval (triSpecializeX R x₀) (Polynomial.eval x₀ (Pz z)) z.1 = 0 := by
      rw [← eval_triEval_eq_biEval_triSpecializeX]
      rw [hRtri]
      simp
    let ψ : Polynomial (Polynomial F) →+* F :=
      (Polynomial.evalRingHom (Polynomial.eval x₀ (Pz z))).comp
        (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
    have hψ : ψ (triSpecializeX R x₀) = 0 := by
      simpa [ψ, biEval] using hpoint
    obtain ⟨H, hHR, hHzero⟩ :=
      exists_normalizedFactor_map_eq_zero (Q := triSpecializeX R x₀) ψ (hx₀ R hRQ) hψ
    refine ⟨(R, H), ?_, hRzero, ?_⟩
    · simp only [normalizedFactorPairs, Finset.mem_biUnion, Multiset.mem_toFinset,
        Finset.mem_image]
      exact ⟨R, hRQ, H, hHR, rfl⟩
    · simpa [ψ, biEval] using hHzero
  obtain ⟨RH, hRHmem, hlarge⟩ :=
    exists_large_rel_fiber S.attach (normalizedFactorPairs Q x₀) Rel DY B
      htotal hpairs (by simpa using hS)
  have hRmem : RH.1 ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
    simp only [normalizedFactorPairs, Finset.mem_biUnion, Multiset.mem_toFinset,
      Finset.mem_image] at hRHmem
    obtain ⟨R, hR, H, hH, heq⟩ := hRHmem
    exact heq ▸ hR
  have hHmem :
      RH.2 ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX RH.1 x₀) := by
    simp only [normalizedFactorPairs, Finset.mem_biUnion, Multiset.mem_toFinset,
      Finset.mem_image] at hRHmem
    obtain ⟨R, hR, H, hH, heq⟩ := hRHmem
    exact heq ▸ hH
  let T := S.attach.filter fun z => Rel z RH
  refine ⟨RH.1, RH.2, T, hRmem, hHmem, ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _
  · exact hlarge
  · intro z hz
    exact (Finset.mem_filter.mp hz).2


/-- The same selection statement with `T` returned as an actual `Finset F`
and an explicit proof `T ⊆ S`. -/
theorem exists_normalizedFactorPair_large_fiber_on_finset
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (S : Finset F) (Pz : ↥S → Polynomial F) (x₀ : F)
    (hvanish : ∀ z : ↥S, triEval Q z.1 (Pz z) = 0)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0)
    (DY B : Nat) (hpairs : (normalizedFactorPairs Q x₀).card ≤ DY)
    (hS : DY * B < S.card) :
    ∃ R : Polynomial (Polynomial (Polynomial F)),
      ∃ H : Polynomial (Polynomial F), ∃ T : Finset F, ∃ hTS : T ⊆ S,
        R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) ∧
        B < T.card ∧
        ∀ z, ∀ hz : z ∈ T,
          triEval R z (Pz ⟨z, hTS hz⟩) = 0 ∧
          biEval H (Polynomial.eval x₀ (Pz ⟨z, hTS hz⟩)) z = 0 := by
  obtain ⟨R, H, U, hR, hH, _hUS, hUcard, hU⟩ :=
    exists_normalizedFactorPair_large_fiber Q hQ S Pz x₀ hvanish hx₀ DY B hpairs hS
  let e : ↥S ↪ F := Function.Embedding.subtype fun z => z ∈ S
  let T : Finset F := U.map e
  have hTS : T ⊆ S := by
    intro z hz
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hz
    exact u.2
  refine ⟨R, H, T, hTS, hR, hH, ?_, ?_⟩
  · simpa [T] using hUcard
  · intro z hz
    obtain ⟨u, hu, huz⟩ := Finset.mem_map.mp hz
    have huv : u.1 = z := by
      simpa [e] using huz
    subst z
    have hgood := hU u hu
    simpa [e] using hgood


/-! ### Degree and candidate-cardinality accounting -/

/-- The outer degrees of the normalized factors, counted with multiplicity,
sum to the outer degree of a nonzero polynomial. -/
theorem normalizedFactors_sum_natDegree_eq
    {K : Type*} [CommSemiring K] [NoZeroDivisors K]
    [NormalizationMonoid (Polynomial K)] [UniqueFactorizationMonoid (Polynomial K)]
    (Q : Polynomial K) (hQ : Q ≠ 0) :
    (Multiset.map Polynomial.natDegree
      (UniqueFactorizationMonoid.normalizedFactors Q)).sum = Q.natDegree := by
  let M := UniqueFactorizationMonoid.normalizedFactors Q
  have ha := UniqueFactorizationMonoid.prod_normalizedFactors hQ
  have hM0 : M.prod ≠ 0 := by
    exact fun h => hQ (ha.eq_zero_iff.mp h)
  have hdeg : M.prod.natDegree = Q.natDegree := by
    apply Nat.le_antisymm
    · exact Polynomial.natDegree_le_of_dvd ha.dvd hQ
    · exact Polynomial.natDegree_le_of_dvd ha.symm.dvd hM0
  rw [← hdeg]
  exact (Polynomial.natDegree_multiset_prod M
    (UniqueFactorizationMonoid.zero_notMem_normalizedFactors Q)).symm

/-- Removing repeated normalized factors can only decrease the sum of their
outer degrees. -/
theorem normalizedFactors_toFinset_sum_natDegree_le
    {K : Type*} [CommSemiring K] [NoZeroDivisors K]
    [NormalizationMonoid (Polynomial K)] [UniqueFactorizationMonoid (Polynomial K)]
    [DecidableEq (Polynomial K)]
    (Q : Polynomial K) (hQ : Q ≠ 0) :
    ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
      R.natDegree ≤ Q.natDegree := by
  let M := UniqueFactorizationMonoid.normalizedFactors Q
  let s := M.toFinset
  have ha := UniqueFactorizationMonoid.prod_normalizedFactors hQ
  have hM0 : M.prod ≠ 0 := fun h => hQ (ha.eq_zero_iff.mp h)
  have hs0 : ∀ R ∈ s, R ≠ 0 := by
    intro R hR
    exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hR)
  have hdvd : s.prod id ∣ M.prod := by
    apply Multiset.prod_dvd_prod_of_le
    simpa [s, M, Multiset.toFinset_val] using (Multiset.dedup_le M)
  calc
    ∑ R ∈ s, R.natDegree = (s.prod id).natDegree := by
      simpa using (Polynomial.natDegree_prod s id hs0).symm
    _ ≤ M.prod.natDegree := Polynomial.natDegree_le_of_dvd hdvd hM0
    _ ≤ Q.natDegree := Polynomial.natDegree_le_of_dvd ha.dvd hQ

/-- If every normalized factor has positive outer degree, the number of
distinct normalized factors is bounded by the outer degree.  The positivity
hypothesis is necessary over coefficient rings which are not fields. -/
theorem normalizedFactors_toFinset_card_le_natDegree
    {K : Type*} [CommSemiring K] [NoZeroDivisors K]
    [NormalizationMonoid (Polynomial K)] [UniqueFactorizationMonoid (Polynomial K)]
    [DecidableEq (Polynomial K)]
    (Q : Polynomial K) (hQ : Q ≠ 0)
    (hpos : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q, 0 < R.natDegree) :
    (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card ≤ Q.natDegree := by
  let s := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  calc
    s.card = s.card • (1 : Nat) := by simp
    _ ≤ ∑ R ∈ s, R.natDegree :=
      Finset.card_nsmul_le_sum s Polynomial.natDegree 1 fun R hR =>
        hpos R (Multiset.mem_toFinset.mp hR)
    _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ

/-- A purely finite bound for the pair construction: at most `a` first-stage
factors and at most `b` second-stage factors per first-stage factor give at
most `a*b` candidate pairs. -/
theorem normalizedFactorPairs_card_le_mul
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (x₀ : F) (a b : Nat)
    (hfirst : (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card ≤ a)
    (hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀)).toFinset.card ≤ b) :
    (normalizedFactorPairs Q x₀).card ≤ a * b := by
  let s := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  let t := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀)).toFinset.image
      fun H => (R, H)
  calc
    (normalizedFactorPairs Q x₀).card = (s.biUnion t).card := by
      rfl
    _ ≤ s.card * b := by
      apply Finset.card_biUnion_le_card_mul
      intro R hR
      exact (Finset.card_image_le.trans
        (hsecond R (Multiset.mem_toFinset.mp hR)))
    _ ≤ a * b := Nat.mul_le_mul_right b hfirst

/-- Degree-cap version of the candidate-pair bound.  Positivity says that the
chosen outer variable actually occurs in every factor at each stage; without
it, constant nonunit coefficient factors make a degree-only cardinality bound
false. -/
theorem normalizedFactorPairs_card_le_sq_natDegree
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F) (DY : Nat)
    (hQdeg : Q.natDegree ≤ DY)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0)
    (hRpos : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q, 0 < R.natDegree)
    (hHpos : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      ∀ H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀),
        0 < H.natDegree)
    (hRXdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (triSpecializeX R x₀).natDegree ≤ DY) :
    (normalizedFactorPairs Q x₀).card ≤ DY ^ 2 := by
  have hfirst :
      (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card ≤ DY :=
    (normalizedFactors_toFinset_card_le_natDegree Q hQ hRpos).trans hQdeg
  have hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀)).toFinset.card ≤ DY := by
    intro R hR
    exact (normalizedFactors_toFinset_card_le_natDegree
      (triSpecializeX R x₀) (hx₀ R hR) (hHpos R hR)).trans (hRXdeg R hR)
  simpa [pow_two] using normalizedFactorPairs_card_le_mul Q x₀ DY DY hfirst hsecond


/-- A weighted version: under the same degree caps, the sum over distinct
candidate pairs of the product of their two outer degrees is at most `DY²`.
Unlike the cardinality corollary, this estimate needs no positivity assumption. -/
theorem normalizedFactorPairs_sum_mul_natDegree_le_sq
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F) (DY : Nat)
    (hQdeg : Q.natDegree ≤ DY)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0)
    (hRXdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (triSpecializeX R x₀).natDegree ≤ DY) :
    ∑ RH ∈ normalizedFactorPairs Q x₀,
      RH.1.natDegree * RH.2.natDegree ≤ DY ^ 2 := by
  let s := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  let u := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀)).toFinset
  let t := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (u R).image fun H => (R, H)
  have hdisj : (s : Set (Polynomial (Polynomial (Polynomial F)))).PairwiseDisjoint t := by
    intro R hR R' hR' hne
    change Disjoint (t R) (t R')
    rw [Finset.disjoint_left]
    intro RH hRH hRH'
    apply hne
    obtain ⟨H, _hH, hpair⟩ := Finset.mem_image.mp hRH
    obtain ⟨H', _hH', hpair'⟩ := Finset.mem_image.mp hRH'
    exact congrArg Prod.fst (hpair.trans hpair'.symm)
  have hinner : ∀ R ∈ s,
      ∑ RH ∈ t R, RH.1.natDegree * RH.2.natDegree ≤ R.natDegree * DY := by
    intro R hR
    have hinj : Set.InjOn (fun H : Polynomial (Polynomial F) => (R, H)) (u R) := by
      intro H hH H' hH' heq
      exact congrArg Prod.snd heq
    rw [Finset.sum_image hinj]
    change (∑ H ∈ u R, R.natDegree * H.natDegree) ≤ R.natDegree * DY
    rw [← Finset.mul_sum]
    apply Nat.mul_le_mul_left
    exact (normalizedFactors_toFinset_sum_natDegree_le
      (triSpecializeX R x₀)
      (hx₀ R (Multiset.mem_toFinset.mp hR))).trans
        (hRXdeg R (Multiset.mem_toFinset.mp hR))
  calc
    ∑ RH ∈ normalizedFactorPairs Q x₀, RH.1.natDegree * RH.2.natDegree =
        ∑ RH ∈ s.biUnion t, RH.1.natDegree * RH.2.natDegree := by rfl
    _ = ∑ R ∈ s, ∑ RH ∈ t R, RH.1.natDegree * RH.2.natDegree :=
      Finset.sum_biUnion hdisj
    _ ≤ ∑ R ∈ s, R.natDegree * DY := Finset.sum_le_sum hinner
    _ = (∑ R ∈ s, R.natDegree) * DY := by rw [Finset.sum_mul]
    _ ≤ Q.natDegree * DY := Nat.mul_le_mul_right DY
      (normalizedFactors_toFinset_sum_natDegree_le Q hQ)
    _ ≤ DY * DY := Nat.mul_le_mul_right DY hQdeg
    _ = DY ^ 2 := by simp [pow_two]


/-- Over a field, positivity of every normalized factor's degree is automatic,
so the familiar factor-count bound has no extra hypothesis. -/
theorem normalizedFactors_toFinset_card_le_natDegree_of_field
    {K : Type*} [Field K] [DecidableEq K] [NormalizationMonoid K]
    (Q : Polynomial K) (hQ : Q ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card ≤ Q.natDegree := by
  apply normalizedFactors_toFinset_card_le_natDegree Q hQ
  intro R hR
  apply Nat.pos_of_ne_zero
  intro hdeg
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
  have hR0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hR
  have hc0 : c ≠ 0 := by
    intro hczero
    apply hR0
    rw [← hc, hczero, map_zero]
  have hRirr := (UniqueFactorizationMonoid.prime_of_normalized_factor R hR).irreducible
  apply hRirr.not_isUnit
  rw [← hc, Polynomial.isUnit_C]
  exact isUnit_iff_ne_zero.mpr hc0


/-! ### Positive-`Y` factor selection -/

/-- Fix the innermost `Z` variable, leaving a polynomial in `Y` over `F[X]`. -/
noncomputable def triSpecializeZ {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) :
    Polynomial (Polynomial F) :=
  Polynomial.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) Q

lemma triEval_eq_eval_triSpecializeZ {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F) :
    triEval Q z P = Polynomial.eval P (triSpecializeZ Q z) := rfl

/-- The elementary factor theorem in the coefficient ring `F[X]`. -/
lemma Y_sub_C_dvd_triSpecializeZ
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F)
    (h : triEval Q z P = 0) :
    Polynomial.X - Polynomial.C P ∣ triSpecializeZ Q z := by
  rw [Polynomial.dvd_iff_isRoot]
  exact h

/-- If `Q|_{Z=z}` is nonzero but vanishes after `Y=P(X)`, then a normalized
factor of the original trivariate `Q` which vanishes after the same
specialization has positive `Y`-degree.  Thus coefficient/content factors are
excluded. -/
theorem exists_positive_normalizedFactor_triEval_eq_zero
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F)
    (hQz : triSpecializeZ Q z ≠ 0) (h : triEval Q z P = 0) :
    ∃ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree ∧ triEval R z P = 0 := by
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hQz
    simp [triSpecializeZ, hzero]
  let φ : Polynomial (Polynomial (Polynomial F)) →+* Polynomial F :=
    (Polynomial.evalRingHom P).comp
      (Polynomial.mapRingHom
        (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
  have hφ : φ Q = 0 := by
    simpa [φ, triEval, triSpecializeZ] using h
  obtain ⟨R, hRQ, hRφ⟩ :=
    exists_normalizedFactor_map_eq_zero (Q := Q) φ hQ hφ
  have hRtri : triEval R z P = 0 := by
    simpa [φ, triEval, triSpecializeZ] using hRφ
  have hRz : triSpecializeZ R z ≠ 0 := by
    have hdvd : triSpecializeZ R z ∣ triSpecializeZ Q z :=
      map_dvd (Polynomial.mapRingHom
        (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ)
    intro hzero
    apply hQz
    exact zero_dvd_iff.mp (hzero ▸ hdvd)
  refine ⟨R, hRQ, ?_, hRtri⟩
  apply Nat.pos_of_ne_zero
  intro hdeg
  obtain ⟨A, hA⟩ := Polynomial.natDegree_eq_zero.mp hdeg
  apply hRz
  have heval : Polynomial.eval P (triSpecializeZ R z) = 0 := hRtri
  rw [← hA] at heval ⊢
  simp [triSpecializeZ] at heval ⊢
  exact heval

/-- Candidate pairs with positive outer degree at both stages. -/
noncomputable def positiveNormalizedFactorPairs
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (x₀ : F) :
    Finset (Polynomial (Polynomial (Polynomial F)) × Polynomial (Polynomial F)) :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.biUnion fun R =>
    (((UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀)).toFinset.filter
      fun H => 0 < H.natDegree).image fun H => (R, H))


/-- Claim-5.7 accounting: positive second-stage factors for `R` cost at most
`deg_Y(R|_{X=x₀})`, hence at most `deg_Y R`; summing over `R` costs at most
`deg_Y Q`, not its square. -/
theorem positiveNormalizedFactorPairs_card_le_natDegree
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0)
    (hdegree : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (triSpecializeX R x₀).natDegree ≤ R.natDegree) :
    (positiveNormalizedFactorPairs Q x₀).card ≤ Q.natDegree := by
  let s := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  let u := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀)).toFinset
  let upos := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (u R).filter fun H => 0 < H.natDegree
  let pairs := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (upos R).image fun H => (R, H)
  have hinner : ∀ R ∈ s, (pairs R).card ≤ R.natDegree := by
    intro R hR
    have hRnf : R ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp hR
    calc
      (pairs R).card ≤ (upos R).card := Finset.card_image_le
      _ = (upos R).card • (1 : Nat) := by simp
      _ ≤ ∑ H ∈ upos R, H.natDegree := by
        apply Finset.card_nsmul_le_sum
        intro H hH
        exact (Finset.mem_filter.mp hH).2
      _ ≤ ∑ H ∈ u R, H.natDegree := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        simp
      _ ≤ (triSpecializeX R x₀).natDegree := by
        exact normalizedFactors_toFinset_sum_natDegree_le
          (triSpecializeX R x₀) (hx₀ R hRnf)
      _ ≤ R.natDegree := hdegree R hRnf
  calc
    (positiveNormalizedFactorPairs Q x₀).card = (s.biUnion pairs).card := by rfl
    _ ≤ ∑ R ∈ s, (pairs R).card := Finset.card_biUnion_le
    _ ≤ ∑ R ∈ s, R.natDegree := Finset.sum_le_sum hinner
    _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ

/-- Degree-cap corollary of the sharp pair count. -/
theorem positiveNormalizedFactorPairs_card_le
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F) (DY : Nat)
    (hQdeg : Q.natDegree ≤ DY)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0)
    (hdegree : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (triSpecializeX R x₀).natDegree ≤ R.natDegree) :
    (positiveNormalizedFactorPairs Q x₀).card ≤ DY :=
  (positiveNormalizedFactorPairs_card_le_natDegree Q hQ x₀ hx₀ hdegree).trans hQdeg


/-- Specialization points at which the whole trivariate polynomial disappears. -/
noncomputable def badZSpecializations
    {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial (Polynomial F))) (S : Finset F) : Finset F :=
  S.filter fun z => triSpecializeZ Q z = 0

/-- Any one nonzero coefficient polynomial controls all bad `Z`-specializations. -/
theorem badZSpecializations_card_le_natDegree_coeff
    {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial (Polynomial F))) (S : Finset F)
    (j a : Nat) (hc : (Q.coeff j).coeff a ≠ 0) :
    (badZSpecializations Q S).card ≤ ((Q.coeff j).coeff a).natDegree := by
  let c : Polynomial F := (Q.coeff j).coeff a
  have hsub : badZSpecializations Q S ⊆ c.roots.toFinset := by
    intro z hz
    have hbad := (Finset.mem_filter.mp hz).2
    have heq := congrArg (fun T : Polynomial (Polynomial F) => (T.coeff j).coeff a) hbad
    have heval : Polynomial.eval z c = 0 := by
      simpa [triSpecializeZ, c] using heq
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (by simpa [c] using hc)]
    exact heval
  calc
    (badZSpecializations Q S).card ≤ c.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ c.roots.card := Multiset.toFinset_card_le _
    _ ≤ c.natDegree := Polynomial.card_roots' c
    _ = ((Q.coeff j).coeff a).natDegree := rfl

/-- In particular, a nonzero coefficient of `Z`-degree `< DZ` leaves fewer
than `DZ` bad specialization points. -/
theorem badZSpecializations_card_lt
    {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial (Polynomial F))) (S : Finset F)
    (j a DZ : Nat) (hc : (Q.coeff j).coeff a ≠ 0)
    (hdeg : ((Q.coeff j).coeff a).natDegree < DZ) :
    (badZSpecializations Q S).card < DZ :=
  (badZSpecializations_card_le_natDegree_coeff Q S j a hc).trans_lt hdeg

/-- Concrete `DZ=519143` form: at most `519142` bad points. -/
theorem badZSpecializations_card_le_519142
    {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial (Polynomial F))) (S : Finset F)
    (j a : Nat) (hc : (Q.coeff j).coeff a ≠ 0)
    (hdeg : ((Q.coeff j).coeff a).natDegree < 519143) :
    (badZSpecializations Q S).card ≤ 519142 := by
  have := badZSpecializations_card_lt Q S j a 519143 hc hdeg
  omega


/-! ### Weighted relational pigeonhole -/

/-- Relational pigeonhole with a separate capacity for every pigeonhole. -/
theorem exists_rel_fiber_gt_capacity
    {σ π : Type*} [DecidableEq σ] [DecidableEq π]
    (S : Finset σ) (P : Finset π) (R : σ → π → Prop) [DecidableRel R]
    (capacity : π → Nat)
    (hcover : ∀ s ∈ S, ∃ p ∈ P, R s p)
    (hlarge : (∑ p ∈ P, capacity p) < S.card) :
    ∃ p ∈ P, capacity p < (S.filter fun s => R s p).card := by
  by_contra h
  push Not at h
  have hsub : S ⊆ P.biUnion (fun p => S.filter fun s => R s p) := by
    intro s hs
    obtain ⟨p, hp, hsp⟩ := hcover s hs
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    exact ⟨p, hp, hs, hsp⟩
  have hcard : S.card ≤ ∑ p ∈ P, (S.filter fun s => R s p).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcap : (∑ p ∈ P, (S.filter fun s => R s p).card) ≤
      ∑ p ∈ P, capacity p := Finset.sum_le_sum h
  exact (not_lt_of_ge (hcard.trans hcap)) hlarge

/-- Sum the optimized BCHKS pair capacities from a weighted degree-product
bound. -/
theorem sum_pair_capacity_le
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (P : Finset (A × B)) (degA : A → Nat) (degB : B → Nat)
    (DX DZ DY e : Nat)
    (hweighted : (∑ p ∈ P, degA p.1 * degB p.2) ≤ DY ^ 2) :
    (∑ p ∈ P,
      ((2 * DX * DZ) * (degA p.1 * degB p.2) + (e + 1))) ≤
      (2 * DX * DZ) * DY ^ 2 + (e + 1) * P.card := by
  rw [Finset.sum_add_distrib]
  calc
    (∑ p ∈ P, (2 * DX * DZ) * (degA p.1 * degB p.2)) +
          ∑ _p ∈ P, (e + 1) =
        (2 * DX * DZ) * (∑ p ∈ P, degA p.1 * degB p.2) +
          (e + 1) * P.card := by
            rw [Finset.mul_sum]
            simp [Nat.mul_comm]
    _ ≤ (2 * DX * DZ) * DY ^ 2 + (e + 1) * P.card := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hweighted) _

/-- Optimized weighted relational pigeonhole with the standard BCHKS
capacity `2*DX*DZ*degR*degH + (e+1)`. -/
theorem exists_pair_fiber_gt_BCHKS_capacity
    {σ A B : Type*} [DecidableEq σ] [DecidableEq A] [DecidableEq B]
    (S : Finset σ) (P : Finset (A × B)) (R : σ → (A × B) → Prop) [DecidableRel R]
    (degA : A → Nat) (degB : B → Nat) (DX DZ DY e : Nat)
    (hcover : ∀ s ∈ S, ∃ p ∈ P, R s p)
    (hweighted : (∑ p ∈ P, degA p.1 * degB p.2) ≤ DY ^ 2)
    (hlarge : (2 * DX * DZ) * DY ^ 2 + (e + 1) * P.card < S.card) :
    ∃ p ∈ P,
      (2 * DX * DZ) * (degA p.1 * degB p.2) + (e + 1) <
        (S.filter fun s => R s p).card := by
  apply exists_rel_fiber_gt_capacity S P R
    (fun p => (2 * DX * DZ) * (degA p.1 * degB p.2) + (e + 1)) hcover
  exact (sum_pair_capacity_le P degA degB DX DZ DY e hweighted).trans_lt hlarge


/-- The positive candidate subset inherits the `DY²` weighted degree-product
bound from all normalized factor pairs. -/
theorem positiveNormalizedFactorPairs_sum_mul_natDegree_le_sq
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F) (DY : Nat)
    (hQdeg : Q.natDegree ≤ DY)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0)
    (hRXdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (triSpecializeX R x₀).natDegree ≤ DY) :
    ∑ RH ∈ positiveNormalizedFactorPairs Q x₀,
      RH.1.natDegree * RH.2.natDegree ≤ DY ^ 2 := by
  have hsub : positiveNormalizedFactorPairs Q x₀ ⊆ normalizedFactorPairs Q x₀ := by
    intro RH hRH
    simp only [positiveNormalizedFactorPairs, normalizedFactorPairs,
      Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_image,
      Finset.mem_filter] at hRH ⊢
    obtain ⟨R, hR, H, ⟨hH, _hpos⟩, heq⟩ := hRH
    exact ⟨R, hR, H, hH, heq⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (by simp)).trans
    (normalizedFactorPairs_sum_mul_natDegree_le_sq Q hQ x₀ DY hQdeg hx₀ hRXdeg)


/-- Fix `Z` in an `F[Z][Y]` polynomial. -/
noncomputable def biSpecializeZ {F : Type*} [Field F]
    (B : Polynomial (Polynomial F)) (z : F) : Polynomial F :=
  Polynomial.map (Polynomial.evalRingHom z) B

lemma biEval_eq_eval_biSpecializeZ {F : Type*} [Field F]
    (B : Polynomial (Polynomial F)) (y z : F) :
    biEval B y z = Polynomial.eval y (biSpecializeZ B z) := rfl

/-- Positive-degree factor selection for `F[Z][Y]`. -/
theorem exists_positive_normalizedFactor_biEval_eq_zero
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (B : Polynomial (Polynomial F)) (z y : F)
    (hBz : biSpecializeZ B z ≠ 0) (h : biEval B y z = 0) :
    ∃ H ∈ UniqueFactorizationMonoid.normalizedFactors B,
      0 < H.natDegree ∧ biEval H y z = 0 := by
  have hB : B ≠ 0 := by
    intro hzero
    apply hBz
    simp [biSpecializeZ, hzero]
  let φ : Polynomial (Polynomial F) →+* F :=
    (Polynomial.evalRingHom y).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  have hφ : φ B = 0 := by simpa [φ, biEval, biSpecializeZ] using h
  obtain ⟨H, hHB, hHφ⟩ :=
    exists_normalizedFactor_map_eq_zero (Q := B) φ hB hφ
  have hHeval : biEval H y z = 0 := by simpa [φ, biEval, biSpecializeZ] using hHφ
  have hHz : biSpecializeZ H z ≠ 0 := by
    have hdvd : biSpecializeZ H z ∣ biSpecializeZ B z :=
      map_dvd (Polynomial.mapRingHom (Polynomial.evalRingHom z))
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHB)
    intro hzero
    apply hBz
    exact zero_dvd_iff.mp (hzero ▸ hdvd)
  refine ⟨H, hHB, ?_, hHeval⟩
  apply Nat.pos_of_ne_zero
  intro hdeg
  obtain ⟨A, hA⟩ := Polynomial.natDegree_eq_zero.mp hdeg
  apply hHz
  have heval : Polynomial.eval y (biSpecializeZ H z) = 0 := hHeval
  rw [← hA] at heval ⊢
  simp [biSpecializeZ] at heval ⊢
  exact heval

/-- Pointwise two-stage positive factor selection, ready to serve as the
coverage hypothesis of either relational pigeonhole theorem. -/
theorem exists_positive_normalizedFactorPair
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F) (x₀ : F)
    (hQz : triSpecializeZ Q z ≠ 0) (hQeval : triEval Q z P = 0)
    (hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → triEval R z P = 0 →
      biSpecializeZ (triSpecializeX R x₀) z ≠ 0) :
    ∃ RH ∈ positiveNormalizedFactorPairs Q x₀,
      triEval RH.1 z P = 0 ∧
      biEval RH.2 (Polynomial.eval x₀ P) z = 0 := by
  obtain ⟨R, hRQ, hRpos, hRzero⟩ :=
    exists_positive_normalizedFactor_triEval_eq_zero Q z P hQz hQeval
  have hpoint : biEval (triSpecializeX R x₀) (Polynomial.eval x₀ P) z = 0 := by
    rw [← eval_triEval_eq_biEval_triSpecializeX]
    rw [hRzero]
    simp
  obtain ⟨H, hHR, hHpos, hHzero⟩ :=
    exists_positive_normalizedFactor_biEval_eq_zero
      (triSpecializeX R x₀) z (Polynomial.eval x₀ P)
      (hsecond R hRQ hRpos hRzero) hpoint
  refine ⟨(R, H), ?_, hRzero, hHzero⟩
  simp only [positiveNormalizedFactorPairs, Finset.mem_biUnion,
    Multiset.mem_toFinset, Finset.mem_image, Finset.mem_filter]
  exact ⟨R, hRQ, H, ⟨hHR, hHpos⟩, rfl⟩


lemma triSpecializeX_natDegree_le {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (x₀ : F) :
    (triSpecializeX R x₀).natDegree ≤ R.natDegree := by
  exact Polynomial.natDegree_map_le

/-- Sharp positive-pair count with the specialization degree inequality
supplied automatically by `Polynomial.natDegree_map_le`. -/
theorem positiveNormalizedFactorPairs_card_le_natDegree'
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0) :
    (positiveNormalizedFactorPairs Q x₀).card ≤ Q.natDegree :=
  positiveNormalizedFactorPairs_card_le_natDegree Q hQ x₀ hx₀
    (fun R _ => triSpecializeX_natDegree_le R x₀)

theorem positiveNormalizedFactorPairs_card_le'
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F) (DY : Nat)
    (hQdeg : Q.natDegree ≤ DY)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0) :
    (positiveNormalizedFactorPairs Q x₀).card ≤ DY :=
  (positiveNormalizedFactorPairs_card_le_natDegree' Q hQ x₀ hx₀).trans hQdeg


/-- A nonzero `Q` with every nonzero coefficient polynomial of `Z`-degree
`< DZ` has fewer than `DZ` disappearing specializations. -/
theorem badZSpecializations_card_lt_of_forall_coeff
    {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (S : Finset F) (DZ : Nat)
    (hdeg : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      ((Q.coeff j).coeff a).natDegree < DZ) :
    (badZSpecializations Q S).card < DZ := by
  have hj : ∃ j, Q.coeff j ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ
    ext j a z
    simp [h]
  obtain ⟨j, hj⟩ := hj
  have ha : ∃ a, (Q.coeff j).coeff a ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    ext a z
    simp [h]
  obtain ⟨a, ha⟩ := ha
  exact badZSpecializations_card_lt Q S j a DZ ha (hdeg j a ha)

end ProximityPrize.SubmissionLower
