import ProximityPrize.SubmissionLower.PortHighFinish
import ProximityPrize.SubmissionLower.UpperBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_3
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4
open K1_14_2_4_1 hiding chartResultant_proper
open scoped Polynomial
open private chartEvaluation from ProximityPrize.SubmissionLower.Fast055
open private donor_1_1 donor_1_2 donor_1_3 donor_1_4 donor_1_5 from ProximityPrize.SubmissionLower.PortHighFinish
private theorem generic_separability {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g}
    (R : PrimitiveRoot C₀ J g) (hg : 0 < g) (hgp : g < p) :
    (R.equation.map (insertX C₀)).Separable := by
  let F := R.equation.map (insertX C₀)
  let : CharP (ConstantSeedX C₀) p :=
    charP_of_injective_ringHom ((extendX C₀).comp seedEmbedding).injective p
  have hdeg : F.natDegree = g :=
    (Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (ConstantSeedField C₀)[X] (ConstantSeedX C₀)) _).trans R.degree
  have hgc : (g : ConstantSeedX C₀) ≠ 0 := by
    intro hz
    have hp := (CharP.cast_eq_zero_iff (ConstantSeedX C₀) p g).mp hz
    exact (not_le_of_gt hgp) (Nat.le_of_dvd hg hp)
  refine (Polynomial.separable_iff_derivative_ne_zero R.irreducible).mpr ?_
  intro hd
  have hz := congrArg (fun Q : (ConstantSeedX C₀)[X] => Q.coeff (g - 1)) hd
  have hsucc : g - 1 + 1 = g := Nat.sub_add_cancel hg
  have hcast : (↑(g - 1) + 1 : ConstantSeedX C₀) = (g : ConstantSeedX C₀) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : ConstantSeedX C₀)) hsucc
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, hcast, hsucc] at hz
  change F.coeff g * (g : ConstantSeedX C₀) = 0 at hz
  rw [show F.coeff g = F.leadingCoeff by rw [← hdeg, Polynomial.coeff_natDegree]] at hz
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr R.irreducible.ne_zero) hgc) hz
theorem chartResultant_proper {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) (hg : 0 < g) (hgp : g < p) :
    parameterInclusion n (chartResultant A.equation g) ∉ chartBase A := by
  let ev := (chartBaseMap A).comp (parameterInclusion n)
  let F := R.equation.map (insertX C₀)
  let a := insertConstant C₀ (A.scale : ConstantSeedField C₀)
  have ha : IsUnit (Polynomial.C a) :=
    (show IsUnit (A.scale : ConstantSeedField C₀) from A.scale.isUnit).map
      (Polynomial.C.comp (insertConstant C₀))
  have hFdeg : F.natDegree = g :=
    (Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (ConstantSeedField C₀)[X] (ConstantSeedX C₀)) _).trans R.degree
  have hG : (equationAtX A.equation).map ev = Polynomial.C a * F := by
    rw [equationAtX, Polynomial.map_map, chartEvaluation A, ← Polynomial.map_map,
      A.generic_eq, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hGdeg : (Polynomial.C a * F).natDegree = g :=
    (Polynomial.natDegree_C_mul (isUnit_iff_ne_zero.mp (Polynomial.isUnit_C.mp ha))).trans hFdeg
  have hsep := (generic_separability R hg hgp).unit_mul ha
  have hres := Polynomial.resultant_derivative_ne_zero_of_separable _ hsep
  rw [hGdeg, ← hG, Polynomial.derivative_map, Polynomial.resultant_map_map] at hres
  exact fun h => hres (RingHom.mem_ker.mp h)
theorem regular_chart (T : Finset K) (z : K → K) (s : K → K[X])
    (J : Ideal RootAmbient) (g H : ℕ) (hg : 0 < g) (hgp : g < p)
    (hcurve : SmallRootCurve J g H) (hinj : Set.InjOn z (T : Set K))
    (hmark : ∀ γ ∈ T, OnRoot J (z γ) (s γ)) :
    ∃ U ⊆ T, (T \ U).card ≤ taylorPower g * H ∧
      ∃ n : ℕ, Nonempty (RegularChart U s g H n) := by
  classical
  obtain ⟨hJ, C₀, hC₀, hseed, hsf, hs, hyf, hy⟩ := hcurve
  let : Fact (Irreducible C₀) := ⟨hC₀⟩
  obtain ⟨R⟩ := donor_1_1 C₀ J g hJ hseed hsf hs hg
  obtain ⟨n, A, t, hbase, hpoints, hroots⟩ := donor_1_2 C₀ J g R T z s hmark
  have hheight := donor_1_3 C₀ J g H n R A hg hyf hy
  obtain ⟨hdim, hslices⟩ := donor_1_4 C₀ J g H n R A hheight hyf hy
  let q := chartResultant A.equation g
  let point (γ : K) := baseMark (z γ) (t γ)
  let U := T.filter fun γ => MvPolynomial.aeval (point γ) (parameterInclusion n q) ≠ 0
  have hU : U ⊆ T := Finset.filter_subset _ _
  have hpt : Set.InjOn point (T : Set K) := by
    intro γ hγ η hη heq
    apply hinj hγ hη
    apply seedEmbedding.injective
    exact congrFun heq (Sum.inl 0)
  have hbad_inj : Set.InjOn point ((T \ U : Finset K) : Set K) :=
    hpt.mono (by
      intro γ hγ
      exact (Finset.mem_sdiff.mp hγ).1)
  have hbudget := donor_1_5 n H (chartBase A) (RingHom.ker_isPrime (chartBaseMap A)) hheight q
    (chartResultant_proper A hg hgp) (T \ U) point hbad_inj (by
      intro γ hγ
      obtain ⟨hγT, hγU⟩ := Finset.mem_sdiff.mp hγ
      refine ⟨hbase γ hγT, ?_⟩
      by_contra hn
      exact hγU (Finset.mem_filter.mpr ⟨hγT, hn⟩))
  have hsrc : (chartSource A).IsPrime :=
    ((Ideal.span_singleton_prime R.irreducible.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp R.irreducible)).comap (chartRootMap A)
  refine ⟨U, hU, hbudget.trans (Nat.mul_le_mul_right H (chartResultant_degree A.degree hg)),
    n, ⟨{
      equation := A.equation
      equation_degree := A.degree
      parameter := t
      source := chartSource A
      source_prime := hsrc
      source_dim := hdim
      slices := hslices
      lies_on := fun γ hγ => hpoints γ (hU hγ)
      root := fun γ hγ => hroots γ (hU hγ)
      simple := ?_ }⟩⟩
  intro γ hγ
  exact simple_of_resultant A.degree hg (hroots γ (hU hγ)) (Finset.mem_filter.mp hγ).2
end
end P1_7_3
end
section
namespace P1_7_3
noncomputable section
open P1 (K I node agreement blockLength)
open K1_14 (FX L seedEmbedding)
open K1_14_2_4 hiding specialize
open Polynomial MvPolynomial Finset ProximityPrize.Benchmark
open scoped BigOperators
open private proper_section_card from ProximityPrize.SubmissionLower.Fast055
structure FixedWord (w : I → K) (U : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
def persistentNodes (w : I → K) (U : Finset K) (s : K → K[X]) : Finset I := by
  classical
  exact univ.filter fun i => ∀ γ ∈ U, (s γ).eval (node i) = w i
theorem hits_persistent {w U s} {γ : K} (hγ : γ ∈ U) {i : I}
    (hi : i ∈ persistentNodes w U s) : (s γ).eval (node i) = w i := by
  classical
  exact (mem_filter.mp hi).2 γ hγ
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
theorem section_bounds {n g H t : ℕ} {U : Finset K} {s : K → K[X]} {w : I → K}
    (A : RegularChart U s g H n) (ht : 0 < t) (hdistinct : Set.InjOn s (U : Set K))
    (C : TaylorForms n (ordinateBound t g) (taylorPower t))
    (hrec : ∀ γ ∈ U, C.Recovers (A.parameter γ) (s γ)) :
    ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤
        taylorPower t * (g * H) + ordinateBound t g * H := by
  classical
  let a := ordinateBound t g
  let b := taylorPower t
  let D := b * (g * H) + a * H
  have ha : 0 < a := by simp [a, ordinateBound]
  have hb : 0 < b := by dsimp [b, taylorPower]; omega
  let P := linearIdeal a b A.source
  let M := bidegreeMap (Fin n) FX a b
  let v (γ : K) := markedPoint (A.parameter γ) (s γ)
  let point (γ : K) := monomialPoint (bidegreeExponents (Fin n) a b) (v γ)
  have hP : P.IsPrime := A.source_prime.comap M
  let _ : P.IsPrime := hP
  have hdim_eq : (affineHilbertPolynomial P).natDegree =
      (affineHilbertPolynomial A.source).natDegree :=
    natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb _
  have hdim := hdim_eq.trans_le A.source_dim
  have hdeg (h : (affineHilbertPolynomial P).natDegree = 1) : affineDegree P ≤ (D : ℚ) :=
    P0_10R.Bridge.root_embedding n a b (g * H) H ha hb A.source A.source_prime (hdim_eq.symm.trans h) A.slices
  have eval_linear (γ : K) (F : LinearRing n a b) :
      MvPolynomial.aeval (point γ) F = MvPolynomial.aeval (v γ) (M F) := by
    rw [show M = monomialMap FX (bidegreeExponents (Fin n) a b) from
      bidegreeMap_eq_monomialMap a b]
    exact aeval_monomialPoint _ _
  have hpoints (γ : K) (hγ : γ ∈ U) : point γ ∈ zeroLocus FX P := by
    intro F hF
    rw [eval_linear]
    exact A.lies_on γ hγ _ hF
  have hinj : Set.InjOn point (U : Set K) := by
    intro γ hγ η hη heq
    have hv := (monomialPoint_injective (fun i =>
      single_mem_bidegreeExponents ha hb i) : Function.Injective
      (monomialPoint (E := FX) (bidegreeExponents (Fin n) a b))) heq
    exact hdistinct hγ hη (Polynomial.map_injective _ (algebraMap K L).injective
      (IsFractionRing.injective L[X] FX (congrFun hv none)))
  have hsection (i : I) (hmiss : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D := by
    let x := node i
    let y := w i
    let q := C.numerator x - MvPolynomial.C (seedEmbedding y) * C.denominator
    have hq : q ∈ restrictBidegree (Fin n) FX a b := by
      refine Submodule.sub_mem _ (C.numerator_bound x) ?_
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ C.denominator_bound
    let Q := bidegreeLift q hq
    have hcut (γ : K) (hγ : γ ∈ U) :
        MvPolynomial.aeval (point γ) Q = 0 ↔ (s γ).eval x = y := by
      have hr := hrec γ hγ
      change MvPolynomial.aeval (v γ) C.denominator ≠ 0 ∧
        (∀ x, MvPolynomial.aeval (v γ) (C.numerator x) =
          MvPolynomial.aeval (v γ) C.denominator * seedEmbedding ((s γ).eval x)) at hr
      rw [eval_linear, show M Q = q from bidegreeMap_bidegreeLift q hq]
      dsimp only [q]
      rw [map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, hr.2 x,
        sub_eq_zero, mul_comm (seedEmbedding y), mul_right_inj' hr.1]
      exact seedEmbedding.injective.eq_iff
    have hproper : Q ∉ P := by
      obtain ⟨γ, hγ, hγmiss⟩ := hmiss
      exact fun hQ => hγmiss ((hcut γ hγ).mp (hpoints γ hγ Q hQ))
    refine proper_section_card _ point (hinj.mono (filter_subset _ _)) hproper
      (totalDegree_bidegreeLift_le_one q hq) (fun γ hγ => ?_) hdim hdeg
    obtain ⟨hγU, hγhit⟩ := mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU, (hcut γ hγU).mpr hγhit⟩
  exact hsection
end
end P1_7_3
end
section
namespace P1_7_3
noncomputable section
open K1 (K I node)
open K1_14 (FX L seedEmbedding)
open K1_14_2_4_2 (center)
open Polynomial Finset ProximityPrize.Benchmark
open scoped BigOperators
private theorem mapped_node_ne_center (x : K) : seedEmbedding x ≠ center := by
  intro h
  exact (Polynomial.X_ne_C (algebraMap K L x))
    ((IsFractionRing.injective L[X] FX) h.symm)
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem linear_interpolation_weights {E : Type} [Field E]
    (nodes : I → E) (hnodesInj : Function.Injective nodes)
    (ξ : E) (hne : ∀ i, nodes i ≠ ξ)
    (sites : Finset I) (d t : ℕ) (hdt : d ≤ sites.card + t)
    (w : I → E) (x : E) :
    ∃ c : E, ∃ a : Fin (t+1) → E, ∀ P : E[X], P.natDegree ≤ d →
      (∀ i ∈ sites, P.eval (nodes i) = w i) →
      P.eval (x) = c + ∑ j, a j * (taylor ξ P).coeff j := by
  classical
  let V := degreeLE E (d : WithBot ℕ)
  let evalAtNodes : V →ₗ[E] (sites → E) := LinearMap.pi fun i =>
    (leval (nodes i)).comp V.subtype
  let jets : V →ₗ[E] (Fin (t+1) → E) := LinearMap.pi fun j =>
    ((lcoeff E (j : ℕ)).comp (taylor ξ)).comp V.subtype
  let data : V →ₗ[E] (sites → E) × (Fin (t+1) → E) := evalAtNodes.prod jets
  have hker : LinearMap.ker data = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro P hP
    have hn (i : sites) : P.1.eval (nodes i) = 0 := by
      exact congrFun (congrArg Prod.fst hP) i
    have hj (j : Fin (t+1)) : (taylor ξ P.1).coeff j = 0 := by
      exact congrFun (congrArg Prod.snd hP) j
    have hdvd : Polynomial.X^(t+1) ∣ taylor ξ P.1 :=
      X_pow_dvd_iff.mpr fun j hj' => hj ⟨j,hj'⟩
    obtain ⟨Q, hQ⟩ := hdvd
    by_cases hQ0 : Q = 0
    · apply Subtype.ext
      have hz : taylor ξ P.1 = 0 := by rw [hQ, hQ0, mul_zero]
      rw [← taylor_zero P.1, ← neg_add_cancel ξ, ← taylor_taylor, hz, map_zero]
      rfl
    · have hdeg : t+1 + Q.natDegree ≤ d := by
        have hd := natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp P.2)
        rwa [← natDegree_taylor P.1 ξ, hQ, natDegree_mul (pow_ne_zero _ X_ne_zero) hQ0,
          natDegree_X_pow] at hd
      let site (i : I) := nodes i - ξ
      have hinj : Function.Injective site := fun i j h =>
        hnodesInj (sub_left_inj.mp h)
      have hroots (i : I) (hi : i ∈ sites) : Q.eval (site i) = 0 := by
        have h := hn ⟨i, hi⟩
        rw [← sub_add_cancel (nodes i) ξ, ← taylor_eval, hQ,
          eval_mul, eval_pow, eval_X] at h
        exact (mul_eq_zero.mp h).resolve_left
          (pow_ne_zero _ (sub_ne_zero.mpr (hne i)))
      have hc := FrobeniusLocator.Strata.root_nodes_card_le site hinj Q hQ0 sites hroots
      omega
  have hleft : ∃ lift : ((sites → E) × (Fin (t+1) → E)) →ₗ[E] V,
      lift.comp data = LinearMap.id := by
    apply LinearMap.exists_leftInverse_of_injective
    exact hker
  obtain ⟨lift, hlift⟩ := hleft
  let value := ((leval (x)).comp V.subtype).comp lift
  let fixed : sites → E := fun i => w i
  let unit (j : Fin (t+1)) : Fin (t+1) → E := Pi.single j 1
  refine ⟨value (fixed, 0), (fun j => value (0, unit j)), ?_⟩
  intro P hP hnodes
  let P' : V := ⟨P, mem_degreeLE.mpr (natDegree_le_iff_degree_le.mp hP)⟩
  let v := jets P'
  have hdata : data P' = (fixed, 0) + ∑ j, v j • ((0 : sites → E), unit j) := by
    have hsum : (∑ j, v j • unit j) = v := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp [unit]
      · intro j _ hji
        simp [unit, Pi.single_eq_of_ne hji.symm]
      · simp
    have hpairs : (∑ j, v j • ((0 : sites → E), unit j)) = ((0 : sites → E), v) := by
      apply Prod.ext
      · change (LinearMap.fst E (sites → E) (Fin (t+1) → E))
            (∑ j, v j • ((0 : sites → E), unit j)) = 0
        rw [map_sum]
        simp
      · change (LinearMap.snd E (sites → E) (Fin (t+1) → E))
            (∑ j, v j • ((0 : sites → E), unit j)) = v
        rw [map_sum]
        exact hsum
    rw [hpairs]
    change (evalAtNodes P', v) = _
    rw [show evalAtNodes P' = fixed from funext fun i => hnodes i i.property]
    simp
  have hval : value (data P') = P.eval (x) := by
    change (lift (data P')).1.eval (x) = _
    rw [show lift (data P') = P' from DFunLike.congr_fun hlift P']
  rw [hdata, map_add, map_sum] at hval
  rw [← hval]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl
theorem interpolation_weights (sites : Finset I) (d t : ℕ) (hdt : d ≤ sites.card + t)
    (w : I → K) (x : K) :
    ∃ c : FX, ∃ a : Fin (t+1) → FX, ∀ P : FX[X], P.natDegree ≤ d →
      (∀ i ∈ sites, P.eval (seedEmbedding (node i)) = seedEmbedding (w i)) →
      P.eval (seedEmbedding x) = c + ∑ j, a j * (taylor center P).coeff j :=
  linear_interpolation_weights (seedEmbedding ∘ node)
    (seedEmbedding.injective.comp IRSProfile.domain.injective) center
    (fun i => mapped_node_ne_center (node i)) sites d t hdt (seedEmbedding ∘ w) (seedEmbedding x)
end
end P1_7_3
end
section
namespace P1_7_3
noncomputable section
open K1 (K I node p)
open K1_14 (L FX seedEmbedding liftPoly atX)
open K1_14_2_4 K1_14_2_4_2 MvPolynomial
open K1_14_6_1 (derivativeAt)
open scoped Polynomial BigOperators
open private eval_center factorial_ne_zero from ProximityPrize.SubmissionLower.Fast069
private def jetNumerator {n : ℕ} (f : SourceRing n) (t : ℕ) :
    Fin (t+1) → SourceRing n :=
  Fin.cases (separant f ^ taylorPower t * ordinate) fun i =>
    (((i.val+1).factorial : FX)⁻¹) •
      (separant f ^ (taylorPower t - (2*i.val+1)) * cleared f i.val)
private theorem jet_pad {t : ℕ} (i : Fin t) :
    taylorPower t - (2*i.val+1) + (2*i.val+1) = taylorPower t := by
  have hi := i.isLt
  unfold taylorPower
  omega
private theorem jet_bound {n g t : ℕ} {f : SourceRing n} (hg : 0 < g)
    (hf : f ∈ box n g 1) (j : Fin (t+1)) :
    jetNumerator f t j ∈ box n (ordinateBound t g) (taylorPower t) := by
  have hsep := separant_bound hf
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [jetNumerator, Fin.cases_zero, ordinateBound, Nat.add_comm, Nat.add_zero,
      Nat.mul_one] using
      mul_mem_restrictBidegree (box_pow hsep (taylorPower t)) (ordinate_mem (n := n))
  · simp only [jetNumerator, Fin.cases_succ]
    apply (box _ _ _).smul_mem
    have hpad := jet_pad i
    have h := mul_mem_restrictBidegree (box_pow hsep (taylorPower t - (2*i.val+1)))
      (cleared_bound hg hf i.val)
    have hy : (taylorPower t - (2*i.val+1))*(g-1) + (1+(2*i.val+1)*(g-1)) =
        ordinateBound t g := by
      calc
        _ = 1+(taylorPower t - (2*i.val+1)+(2*i.val+1))*(g-1) := by ring
        _ = _ := by rw [hpad, ordinateBound]
    rwa [hy, ← Nat.add_mul, hpad, Nat.mul_one] at h
private theorem jet_eval {n t : ℕ} (htp : t < p) (f : SourceRing n)
    (v : Fin n → L) (S : K[X]) (hroot : markEval v S f = 0) (j : Fin (t+1)) :
    markEval v S (jetNumerator f t j) =
      markEval v S (separant f ^ taylorPower t) *
        (Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [jetNumerator, Fin.cases_zero, map_mul, Fin.val_zero,
      Polynomial.taylor_coeff_zero, eval_center]
    rw [show markEval v S ordinate = atX S from eval_X _]
  · let a := markEval v S (separant f)
    let j' := i.val+1
    have hjp : j' < p := (Nat.succ_le_of_lt i.isLt).trans_lt htp
    have hfactor : derivativeAt S j' =
        (j'.factorial : FX) * (Polynomial.taylor center (S.map seedEmbedding)).coeff j' := by
      rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
      have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) j') S
      dsimp only [derivativeAt]
      rw [← h, LinearMap.smul_apply]
      simp only [nsmul_eq_mul, atX, liftPoly, Polynomial.map_mul,
        Polynomial.map_natCast, map_mul, map_natCast]
    simp only [jetNumerator, Fin.cases_succ, MvPolynomial.smul_eq_C_mul, map_mul, map_pow,
      MvPolynomial.eval_C, eval_cleared _ _ _ hroot, Fin.val_succ]
    change (j'.factorial : FX)⁻¹ *
      (a ^ (taylorPower t - (2*i.val+1)) * (a ^ (2*i.val+1) * derivativeAt S j')) =
        a ^ taylorPower t * _
    rw [hfactor]
    calc
      _ = ((j'.factorial : FX) * (j'.factorial : FX)⁻¹) *
          (a ^ (taylorPower t - (2*i.val+1)) * a ^ (2*i.val+1)) *
          (Polynomial.taylor center (S.map seedEmbedding)).coeff j' := by ring
      _ = _ := by rw [mul_inv_cancel₀ (factorial_ne_zero hjp), one_mul, ← pow_add, jet_pad i]
theorem persistent_taylor {n d t g : ℕ} (sites : Finset I) (w : I → K)
    (hdt : d ≤ sites.card + t) (htp : t < p) (hg : 0 < g)
    (f : FamilyEquation n) (hf : FamilyDegree f g) :
    ∃ C : TaylorForms n (ordinateBound t g) (taylorPower t),
      ∀ (v : Fin n → L) (S : K[X]), S.natDegree ≤ d →
        (∀ i ∈ sites, S.eval (node i) = w i) →
        (specialize f v).eval (liftPoly S) = 0 →
        (specialize f v).derivative.eval (liftPoly S) ≠ 0 → C.Recovers v S := by
  classical
  choose c a hweights using fun x => interpolation_weights sites d t hdt w x
  let F := flatten f
  let D := separant F ^ taylorPower t
  have hF := flatten_bound hf
  have hD : D ∈ box n (ordinateBound t g) (taylorPower t) := by
    have hb := box_pow (separant_bound hF) (taylorPower t)
    rw [Nat.mul_one] at hb
    exact mem_restrictBidegree_mono hb (Nat.le_add_left _ _) le_rfl
  let N (x : K) := c x • D + ∑ j, a x j • jetNumerator F t j
  have hN (x : K) : N x ∈ box n (ordinateBound t g) (taylorPower t) := by
    apply Submodule.add_mem _ (Submodule.smul_mem _ _ hD)
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (jet_bound hg hF j)
  refine ⟨⟨D, N, hD, hN⟩, ?_⟩
  intro v S hS hnodes hroot hsep
  have hroot' : markEval v S F = 0 := by rw [eval_flatten, hroot, map_zero]
  constructor
  · change markEval v S (separant F ^ taylorPower t) ≠ 0
    rw [map_pow, eval_separant]
    exact pow_ne_zero _ (by
      simpa only [map_zero] using (IsFractionRing.injective L[X] FX).ne hsep)
  · intro x
    change markEval v S (N x) = markEval v S D * seedEmbedding (S.eval x)
    have hv := hweights x (S.map seedEmbedding) (Polynomial.natDegree_map_le.trans hS)
      (fun i hi => by rw [Polynomial.eval_map_apply, hnodes i hi])
    rw [Polynomial.eval_map_apply] at hv
    rw [hv, mul_add, Finset.mul_sum]
    simp only [N, map_add, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
      MvPolynomial.eval_C, jet_eval htp F v S hroot']
    rw [mul_comm (c x)]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by dsimp only [D]; ring
end
end P1_7_3
end
section
namespace P1_7_3
noncomputable section
open P1 (K p agreement blockLength AnchorModel AnchoredFamily)
open P1_7 (InBand CurveTariff degreeAt gap curveUnit)
open K1_14_2_4 (taylorPower ordinateBound)
open Finset
open scoped Polynomial
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
private abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164398) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179944 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 164398 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
end
end P1_7_3
end
