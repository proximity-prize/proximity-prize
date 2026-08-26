import ProximityPrize.SubmissionLower.BCHKSFrobeniusPrimitiveDegreeDrop6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusConstantPairEndpoint6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusPrimitiveZeroExtraction6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSFrobeniusFailurePairRankOne6401
open BCHKSFrobeniusKernelPairSpace6401
open BCHKSFrobeniusPrimitiveDegreeDrop6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSFrobeniusConstantPairClosure6401
open BCHKSFrobeniusConstantPairEndpoint6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section FullMultiplierWindow
variable {F : Type*} [Field F] {n : Nat}
noncomputable def pairFirstDegreeLT
    (V : Submodule F
      (Polynomial.degreeLT F n × Polynomial.degreeLT F n)) :
    V →ₗ[F] Polynomial.degreeLT F n where
  toFun v := v.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def pairSecondDegreeLT
    (V : Submodule F
      (Polynomial.degreeLT F n × Polynomial.degreeLT F n)) :
    V →ₗ[F] Polynomial.degreeLT F n where
  toFun v := v.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem exists_primitive_pair_mem_of_full_multiplier_finrank
    (V : Submodule F
      (Polynomial.degreeLT F n × Polynomial.degreeLT F n))
    (A B : Polynomial F) (hVdim : Module.finrank F V = n)
    (hAmem : A ∈ Polynomial.degreeLT F n)
    (hBmem : B ∈ Polynomial.degreeLT F n)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hfactor : ∀ v : V, ∃ H : Polynomial F,
      v.1.1.1 = H * A ∧ v.1.2.1 = H * B) :
    ∃ v : V, v.1.1.1 = A ∧ v.1.2.1 = B := by
  classical
  have htarget : Module.finrank F (Polynomial.degreeLT F n) = n := by
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F n)]
    simp
  rcases hAB with hA | hB
  · have hinj : Function.Injective (pairFirstDegreeLT V) := by
      intro v w hvw
      obtain ⟨Hv, hvA, hvB⟩ := hfactor v
      obtain ⟨Hw, hwA, hwB⟩ := hfactor w
      have hfirst : v.1.1.1 = w.1.1.1 := congrArg Subtype.val hvw
      have hH : Hv = Hw := by
        apply mul_right_cancel₀ hA
        exact hvA.symm.trans (hfirst.trans hwA)
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact hfirst
      · apply Subtype.ext
        exact hvB.trans (hH ▸ hwB.symm)
    have hiff : Function.Injective (pairFirstDegreeLT V) ↔
        Function.Surjective (pairFirstDegreeLT V) :=
      LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (K := F) (V := V) (V₂ := Polynomial.degreeLT F n)
        (f := pairFirstDegreeLT V) (hVdim.trans htarget.symm)
    have hsurj : Function.Surjective (pairFirstDegreeLT V) := hiff.mp hinj
    obtain ⟨v, hv⟩ := hsurj ⟨A, hAmem⟩
    obtain ⟨H, hHA, hHB⟩ := hfactor v
    have hvA : v.1.1.1 = A := congrArg Subtype.val hv
    have hHAeq : H * A = A := hHA.symm.trans hvA
    have hH : H = 1 := by
      apply mul_right_cancel₀ hA
      simpa using hHAeq
    refine ⟨v, hvA, ?_⟩
    simpa [hH] using hHB
  · have hinj : Function.Injective (pairSecondDegreeLT V) := by
      intro v w hvw
      obtain ⟨Hv, hvA, hvB⟩ := hfactor v
      obtain ⟨Hw, hwA, hwB⟩ := hfactor w
      have hsecond : v.1.2.1 = w.1.2.1 := congrArg Subtype.val hvw
      have hH : Hv = Hw := by
        apply mul_right_cancel₀ hB
        exact hvB.symm.trans (hsecond.trans hwB)
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact hvA.trans (hH ▸ hwA.symm)
      · apply Subtype.ext
        exact hsecond
    have hiff : Function.Injective (pairSecondDegreeLT V) ↔
        Function.Surjective (pairSecondDegreeLT V) :=
      LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (K := F) (V := V) (V₂ := Polynomial.degreeLT F n)
        (f := pairSecondDegreeLT V) (hVdim.trans htarget.symm)
    have hsurj : Function.Surjective (pairSecondDegreeLT V) := hiff.mp hinj
    obtain ⟨v, hv⟩ := hsurj ⟨B, hBmem⟩
    obtain ⟨H, hHA, hHB⟩ := hfactor v
    have hvB : v.1.2.1 = B := congrArg Subtype.val hv
    have hHBeq : H * B = B := hHB.symm.trans hvB
    have hH : H = 1 := by
      apply mul_right_cancel₀ hB
      simpa using hHBeq
    refine ⟨v, ?_, hvB⟩
    simpa [hH] using hHA
end FullMultiplierWindow
section FullStackExtraction
theorem exists_constant_failurePair_of_fullTwoLane_rank_eq_rows
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t ↪ F) (beta E : Fin t → F)
    (hrows : rows < t)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hrank :
      (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).rank = rows)
    (hmass : (t - rows - 1) + (t - rows - 1) < t) :
    ∃ A B : Polynomial F,
      A ≠ 0 ∧ A.natDegree ≤ 0 ∧ B.natDegree ≤ 0 ∧
      TwoLaneFailureRelation sigma alpha E A B := by
  classical
  have hrowsle : rows ≤ t := hrows.le
  have hwindow : 0 < t - rows := Nat.sub_pos_of_lt hrows
  have hkerdim : Module.finrank F
      (LinearMap.ker
        (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin) =
      t - rows := by
    rw [fullTwoLane_kernel_finrank_eq_sub_rank, hrank]
  have hnull : 0 < Module.finrank F
      (LinearMap.ker
        (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin) := by
    rw [hkerdim]
    exact hwindow
  obtain ⟨A, B, hAB, _hcop, hdeg, hfactorKernel⟩ :=
    exists_ownerwise_primitive_pair_of_fullTwoLane_kernel
      sigma alpha beta E hrowsle hbeta hE hnull hwindow hmass
  have hdeg0 : max A.natDegree B.natDegree ≤ 0 := by
    simpa [hkerdim] using hdeg
  have hAdeg : A.natDegree ≤ 0 :=
    (Nat.le_max_left _ _).trans hdeg0
  have hBdeg : B.natDegree ≤ 0 :=
    (Nat.le_max_right _ _).trans hdeg0
  let Φ := fullKernelFailurePairLinear sigma alpha rows hrowsle beta E
  let V : Submodule F
      (Polynomial.degreeLT F (t - rows) ×
        Polynomial.degreeLT F (t - rows)) := LinearMap.range Φ
  have hVdim : Module.finrank F V = t - rows := by
    exact (fullKernelFailurePair_range_finrank
      sigma alpha hrowsle beta E hbeta hE).trans hkerdim
  have hAmem : A ∈ Polynomial.degreeLT F (t - rows) := by
    rw [Polynomial.mem_degreeLT]
    by_cases hA : A = 0
    · simp [hA]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hA).1
        (lt_of_le_of_lt hAdeg hwindow)
  have hBmem : B ∈ Polynomial.degreeLT F (t - rows) := by
    rw [Polynomial.mem_degreeLT]
    by_cases hB : B = 0
    · simp [hB]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hB).1
        (lt_of_le_of_lt hBdeg hwindow)
  have hfactorV : ∀ v : V, ∃ H : Polynomial F,
      v.1.1.1 = H * A ∧ v.1.2.1 = H * B := by
    intro v
    rcases v.2 with ⟨x, hx⟩
    obtain ⟨H, hHA, hHB⟩ := hfactorKernel x
    refine ⟨H, ?_, ?_⟩
    · exact (congrArg (fun p ↦ p.1.1) hx.symm).trans hHA
    · exact (congrArg (fun p ↦ p.2.1) hx.symm).trans hHB
  obtain ⟨v, hvA, hvB⟩ :=
    exists_primitive_pair_mem_of_full_multiplier_finrank
      V A B hVdim hAmem hBmem hAB hfactorV
  rcases v.2 with ⟨x, hx⟩
  have hxA : (Φ x).1.1 = A :=
    (congrArg (fun p ↦ p.1.1) hx).trans hvA
  have hxB : (Φ x).2.1 = B :=
    (congrArg (fun p ↦ p.2.1) hx).trans hvB
  have hrel : TwoLaneFailureRelation sigma alpha E A B := by
    have hraw := fullKernelFailurePairLinear_relation
      sigma alpha hrowsle beta E x
    change TwoLaneFailureRelation sigma alpha E
      (Φ x).1.1 (Φ x).2.1 at hraw
    rw [hxA, hxB] at hraw
    exact hraw
  have hA : A ≠ 0 := by
    intro hAzero
    have hB : B ≠ 0 := hAB.resolve_left (fun hAne ↦ hAne hAzero)
    let i : Fin t := ⟨0, Nat.zero_lt_of_lt hrows⟩
    have hprod : B.eval (alpha i) * E i = 0 := by
      have hi := hrel i
      simpa [hAzero] using hi.symm
    have hBeval : B.eval (alpha i) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right (hE i)
    have hBconst : B = Polynomial.C (B.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero hBdeg
    have hBcoeff : B.coeff 0 ≠ 0 := by
      intro hcoeff
      apply hB
      calc
        B = Polynomial.C (B.coeff 0) := hBconst
        _ = Polynomial.C 0 := by rw [hcoeff]
        _ = 0 := Polynomial.C_0
    apply hBcoeff
    rw [hBconst, Polynomial.eval_C] at hBeval
    exact hBeval
  exact ⟨A, B, hA, hAdeg, hBdeg, hrel⟩
theorem exists_constant_failurePair_of_exactSupport_rank_eq_rows
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {t rows : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (E : iota → F)
    (support : Fin t ↪ iota) (beta : Fin t → F)
    (hrows : rows < t) (hbeta : ∀ j, beta j ≠ 0)
    (hsupport : ∀ i, E i ≠ 0 ↔ i ∈ Set.range support)
    (hrank : (fullTwoLaneSupportKeyMatrix sigma rows
      (support.trans alpha) beta (fun j ↦ E (support j))).rank = rows)
    (hmass : (t - rows - 1) + (t - rows - 1) < t) :
    ∃ A B : Polynomial F,
      A ≠ 0 ∧ A.natDegree ≤ 0 ∧ B.natDegree ≤ 0 ∧
      TwoLaneFailureRelation sigma alpha E A B := by
  obtain ⟨A, B, hA, hAdeg, hBdeg, hrel⟩ :=
    exists_constant_failurePair_of_fullTwoLane_rank_eq_rows
      sigma (support.trans alpha) beta (fun j ↦ E (support j))
      hrows hbeta
      (fun j ↦ (hsupport (support j)).2 ⟨j, rfl⟩)
      hrank hmass
  refine ⟨A, B, hA, hAdeg, hBdeg, ?_⟩
  intro i
  by_cases hi : E i = 0
  · simp [hi]
  · obtain ⟨j, rfl⟩ := (hsupport i).1 hi
    simpa using hrel j
end FullStackExtraction
section BenchmarkEndpoint
theorem rankEqualFirstLaneRowsOwners_ownerCurve6401
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (Aagree : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (supportSize : F → Nat)
    (support : ∀ z, Fin (supportSize z) ↪ Fin n6401)
    (hsupport : ∀ z ∈ S, ∀ i,
      u0 i + z * u1 i - Polynomial.eval (alpha i) (P z) ≠ 0 ↔
        i ∈ Set.range (support z))
    (hsizeLower : ∀ z ∈ S,
      keyFirstLaneRows6401 < supportSize z)
    (hsizeUpper : ∀ z ∈ S,
      supportSize z ≤ bchksErrors6401)
    (hrank : ∀ z ∈ S,
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        ((support z).trans alpha)
        (fun j ↦ syndromeWeight ((support z).trans alpha) j)
        (fun j ↦ u0 (support z j) + z * u1 (support z j) -
          Polynomial.eval (alpha (support z j)) (P z))).rank =
        keyFirstLaneRows6401) :
    PolynomialAffineCurveWitness6401 S P := by
  apply constantPolynomialFailurePairsOnSupport_ownerCurve6401
    sigma alpha hfixed hfixedCard u0 u1 S Aagree P
    hSlarge hPdegree hrow howner
  intro z hz
  let Ez : Fin n6401 → F := fun i ↦
    u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)
  let beta : Fin (supportSize z) → F := fun j ↦
    syndromeWeight ((support z).trans alpha) j
  have hmass :
      (supportSize z - keyFirstLaneRows6401 - 1) +
          (supportSize z - keyFirstLaneRows6401 - 1) < supportSize z := by
    have hlo := hsizeLower z hz
    have hhi := hsizeUpper z hz
    norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
      bchksErrors6401, n6401, ownerDegreeCap6401] at hlo hhi ⊢
    omega
  obtain ⟨W0, W1, hW0, hW0deg, hW1deg, hrel⟩ :=
    exists_constant_failurePair_of_exactSupport_rank_eq_rows
      sigma alpha Ez (support z) beta (hsizeLower z hz)
      (fun j ↦ syndromeWeight_ne_zero ((support z).trans alpha) j)
      (hsupport z hz) (by simpa [Ez, beta] using hrank z hz) hmass
  refine ⟨W0, W1, hW0, hW0deg, hW1deg, ?_⟩
  intro i _hi
  exact hrel i
theorem rankEqualFirstLaneRowsOwners_card_le_cap6401_of_no_curve
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (Aagree : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (supportSize : F → Nat)
    (support : ∀ z, Fin (supportSize z) ↪ Fin n6401)
    (hsupport : ∀ z ∈ S, ∀ i,
      u0 i + z * u1 i - Polynomial.eval (alpha i) (P z) ≠ 0 ↔
        i ∈ Set.range (support z))
    (hsizeLower : ∀ z ∈ S,
      keyFirstLaneRows6401 < supportSize z)
    (hsizeUpper : ∀ z ∈ S,
      supportSize z ≤ bchksErrors6401)
    (hrank : ∀ z ∈ S,
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        ((support z).trans alpha)
        (fun j ↦ syndromeWeight ((support z).trans alpha) j)
        (fun j ↦ u0 (support z j) + z * u1 (support z j) -
          Polynomial.eval (alpha (support z j)) (P z))).rank =
        keyFirstLaneRows6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    S.card ≤ constantPrimitiveFamilyCap6401 := by
  apply constantPolynomialFailurePairsOnSupport_ownerFamily_card_le_cap6401
    sigma alpha hfixed hfixedCard u0 u1 S Aagree P hPdegree hrow howner
    (hfail := hfail)
  intro z hz
  let Ez : Fin n6401 → F := fun i ↦
    u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)
  let beta : Fin (supportSize z) → F := fun j ↦
    syndromeWeight ((support z).trans alpha) j
  have hmass :
      (supportSize z - keyFirstLaneRows6401 - 1) +
          (supportSize z - keyFirstLaneRows6401 - 1) < supportSize z := by
    have hlo := hsizeLower z hz
    have hhi := hsizeUpper z hz
    norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
      bchksErrors6401, n6401, ownerDegreeCap6401] at hlo hhi ⊢
    omega
  obtain ⟨W0, W1, hW0, hW0deg, hW1deg, hrel⟩ :=
    exists_constant_failurePair_of_exactSupport_rank_eq_rows
      sigma alpha Ez (support z) beta (hsizeLower z hz)
      (fun j ↦ syndromeWeight_ne_zero ((support z).trans alpha) j)
      (hsupport z hz) (by simpa [Ez, beta] using hrank z hz) hmass
  refine ⟨W0, W1, hW0, hW0deg, hW1deg, ?_⟩
  intro i _hi
  exact hrel i
end BenchmarkEndpoint
end BCHKSFrobeniusPrimitiveZeroExtraction6401
end ProximityPrize.SubmissionLower
