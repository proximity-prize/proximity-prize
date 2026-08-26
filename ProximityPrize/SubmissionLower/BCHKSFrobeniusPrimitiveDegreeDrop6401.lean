import ProximityPrize.SubmissionLower.BCHKSFrobeniusKernelPairSpace6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusPrimitiveDegreeDrop6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSGaoSpecializationCore6400
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSFrobeniusFailurePairRankOne6401
open BCHKSFrobeniusKernelPairSpace6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
theorem exists_primitive_factorization_of_cross
    {F : Type*} [Field F]
    (A₀ B₀ : Polynomial F) (hbase : A₀ ≠ 0 ∨ B₀ ≠ 0) :
    ∃ G A B : Polynomial F,
      G ≠ 0 ∧ (A ≠ 0 ∨ B ≠ 0) ∧ IsCoprime A B ∧
      A₀ = G * A ∧ B₀ = G * B ∧
      ∀ C D : Polynomial F, A₀ * D - C * B₀ = 0 →
        ∃ H : Polynomial F, C = H * A ∧ D = H * B := by
  classical
  by_cases hA₀ : A₀ = 0
  · have hB₀ : B₀ ≠ 0 := hbase.resolve_left (by simpa using hA₀)
    refine ⟨B₀, 0, 1, hB₀, Or.inr one_ne_zero,
      isCoprime_one_right, ?_, ?_, ?_⟩
    · simp [hA₀]
    · simp
    intro C D hcross
    have hCB : C * B₀ = 0 := by
      simpa [hA₀] using hcross
    have hC : C = 0 := (mul_eq_zero.mp hCB).resolve_right hB₀
    refine ⟨D, ?_, by simp⟩
    simp [hC]
  · by_cases hB₀ : B₀ = 0
    · refine ⟨A₀, 1, 0, hA₀, Or.inl one_ne_zero,
        isCoprime_one_left, ?_, ?_, ?_⟩
      · simp
      · simp [hB₀]
      intro C D hcross
      have hAD : A₀ * D = 0 := by
        simpa [hB₀] using hcross
      have hD : D = 0 := (mul_eq_zero.mp hAD).resolve_left hA₀
      refine ⟨C, by simp, ?_⟩
      simp [hD]
    · letI : GCDMonoid (Polynomial F) :=
        EuclideanDomain.gcdMonoid (Polynomial F)
      let G : Polynomial F := GCDMonoid.gcd A₀ B₀
      let A : Polynomial F := A₀ / G
      let B : Polynomial F := B₀ / G
      have hG : G ≠ 0 := by
        exact gcd_ne_zero_of_left hA₀
      have hA : A ≠ 0 := by
        exact left_div_gcd_ne_zero hA₀
      have hfactorA : G * A = A₀ := by
        exact EuclideanDomain.mul_div_cancel' hG (GCDMonoid.gcd_dvd_left A₀ B₀)
      have hfactorB : G * B = B₀ := by
        exact EuclideanDomain.mul_div_cancel' hG (GCDMonoid.gcd_dvd_right A₀ B₀)
      have hcoprime : IsCoprime A B := by
        exact isCoprime_div_gcd_div_gcd hB₀
      refine ⟨G, A, B, hG, Or.inl hA, hcoprime,
        hfactorA.symm, hfactorB.symm, ?_⟩
      intro C D hcross
      have hprimitiveCross : A * D = C * B := by
        apply mul_left_cancel₀ hG
        calc
          G * (A * D) = A₀ * D := by rw [← hfactorA]; ring
          _ = C * B₀ := sub_eq_zero.mp hcross
          _ = G * (C * B) := by rw [← hfactorB]; ring
      have hAdvd : A ∣ C * B := ⟨D, hprimitiveCross.symm⟩
      have hAC : A ∣ C := hcoprime.dvd_of_dvd_mul_right hAdvd
      rcases hAC with ⟨H, hCH⟩
      have hD : D = H * B := by
        apply mul_left_cancel₀ hA
        calc
          A * D = C * B := hprimitiveCross
          _ = A * (H * B) := by rw [hCH]; ring
      exact ⟨H, by rw [hCH, mul_comm], hD⟩
noncomputable def pairFirstPolynomial
    {F : Type*} [Field F] {n : Nat}
    (V : Submodule F
      (Polynomial.degreeLT F n × Polynomial.degreeLT F n)) :
    V →ₗ[F] Polynomial F where
  toFun v := v.1.1.1
  map_add' v w := rfl
  map_smul' a v := rfl
noncomputable def pairSecondPolynomial
    {F : Type*} [Field F] {n : Nat}
    (V : Submodule F
      (Polynomial.degreeLT F n × Polynomial.degreeLT F n)) :
    V →ₗ[F] Polynomial F where
  toFun v := v.1.2.1
  map_add' v w := rfl
  map_smul' a v := rfl
noncomputable def multiplyByPolynomial
    {F : Type*} [Field F] (P : Polynomial F) (r : Nat) :
    Polynomial.degreeLT F r →ₗ[F] Polynomial F where
  toFun H := H.1 * P
  map_add' H Q := by simp [add_mul]
  map_smul' a H := by simp [mul_assoc]
private theorem finrank_le_window_of_projection_factor
    {F : Type*} [Field F] {n r : Nat}
    (V : Submodule F
      (Polynomial.degreeLT F n × Polynomial.degreeLT F n))
    (proj : V →ₗ[F] Polynomial F) (P : Polynomial F)
    (hinj : Function.Injective proj)
    (hfactor : ∀ v : V, ∃ H : Polynomial.degreeLT F r,
      proj v = H.1 * P) :
    Module.finrank F V ≤ r := by
  have hrange : LinearMap.range proj ≤
      LinearMap.range (multiplyByPolynomial P r) := by
    intro C hC
    rcases hC with ⟨v, rfl⟩
    rcases hfactor v with ⟨H, hH⟩
    exact ⟨H, hH.symm⟩
  have hprojdim := LinearMap.finrank_range_of_inj hinj
  calc
    Module.finrank F V = Module.finrank F (LinearMap.range proj) := hprojdim.symm
    _ ≤ Module.finrank F
          (LinearMap.range (multiplyByPolynomial P r)) :=
      Submodule.finrank_mono hrange
    _ ≤ Module.finrank F (Polynomial.degreeLT F r) :=
      LinearMap.finrank_range_le (multiplyByPolynomial P r)
    _ = r := by
      rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F r)]
      simp
private theorem multiplier_degreeLT_of_maximal_component
    {F : Type*} [Field F] {n D : Nat}
    (P H C : Polynomial F) (hP : P ≠ 0)
    (hPdeg : P.natDegree = D) (hD : D < n)
    (hCdeg : C.degree < (n : WithBot Nat)) (hC : C = H * P) :
    H ∈ Polynomial.degreeLT F (n - D) := by
  rw [Polynomial.mem_degreeLT]
  by_cases hH : H = 0
  · simp [hH, hD]
  · have hCne : C ≠ 0 := by rw [hC]; exact mul_ne_zero hH hP
    have hnC : C.natDegree < n :=
      (Polynomial.natDegree_lt_iff_degree_lt hCne).2 hCdeg
    rw [hC, Polynomial.natDegree_mul hH hP, hPdeg] at hnC
    have hnH : H.natDegree < n - D := by omega
    exact (Polynomial.natDegree_lt_iff_degree_lt hH).1 hnH
theorem exists_primitive_pair_degree_le_sub_finrank
    {F : Type*} [Field F] {n : Nat}
    (V : Submodule F
      (Polynomial.degreeLT F n × Polynomial.degreeLT F n))
    (hpos : 0 < Module.finrank F V)
    (hcross : ∀ v w : V,
      v.1.1.1 * w.1.2.1 - w.1.1.1 * v.1.2.1 = 0) :
    ∃ A B : Polynomial F,
      (A ≠ 0 ∨ B ≠ 0) ∧ IsCoprime A B ∧
      max A.natDegree B.natDegree ≤ n - Module.finrank F V ∧
      ∀ v : V, ∃ H : Polynomial F,
        v.1.1.1 = H * A ∧ v.1.2.1 = H * B := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨base, hbase⟩ := exists_ne (0 : V)
  have hbasePair : base.1.1.1 ≠ 0 ∨ base.1.2.1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hbase
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact h.1
    · apply Subtype.ext
      exact h.2
  obtain ⟨G, A, B, hG, hAB, hcoprime, hbaseA, hbaseB, hfactor⟩ :=
    exists_primitive_factorization_of_cross
      base.1.1.1 base.1.2.1 hbasePair
  have hall : ∀ v : V, ∃ H : Polynomial F,
      v.1.1.1 = H * A ∧ v.1.2.1 = H * B := by
    intro v
    exact hfactor v.1.1.1 v.1.2.1 (hcross base v)
  let D := max A.natDegree B.natDegree
  have hdim : Module.finrank F V ≤ n - D := by
    by_cases hA : A = 0
    · have hB : B ≠ 0 := hAB.resolve_left (by simpa using hA)
      have hDdeg : B.natDegree = D := by simp [D, hA]
      have hbaseSecondNe : base.1.2.1 ≠ 0 := by
        rw [hbaseB]
        exact mul_ne_zero hG hB
      have hDlt : D < n := by
        have hnbase : base.1.2.1.natDegree < n :=
          (Polynomial.natDegree_lt_iff_degree_lt hbaseSecondNe).2
            (Polynomial.mem_degreeLT.mp base.1.2.2)
        rw [hbaseB, Polynomial.natDegree_mul hG hB, hDdeg] at hnbase
        omega
      apply finrank_le_window_of_projection_factor V
        (pairSecondPolynomial V) B
      · intro v w hvw
        rcases hall v with ⟨Hv, hvA, hvB⟩
        rcases hall w with ⟨Hw, hwA, hwB⟩
        have hH : Hv = Hw := by
          apply mul_right_cancel₀ hB
          exact hvB.symm.trans (hvw.trans hwB)
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          rw [hvA, hwA, hH]
        · apply Subtype.ext
          exact hvB.trans (hH ▸ hwB.symm)
      · intro v
        rcases hall v with ⟨H, _hA, hBfac⟩
        refine ⟨⟨H, ?_⟩, hBfac⟩
        exact multiplier_degreeLT_of_maximal_component B H v.1.2.1
          hB hDdeg hDlt (Polynomial.mem_degreeLT.mp v.1.2.2) hBfac
    · by_cases hB : B = 0
      · have hDdeg : A.natDegree = D := by simp [D, hB]
        have hbaseFirstNe : base.1.1.1 ≠ 0 := by
          rw [hbaseA]
          exact mul_ne_zero hG hA
        have hDlt : D < n := by
          have hnbase : base.1.1.1.natDegree < n :=
            (Polynomial.natDegree_lt_iff_degree_lt hbaseFirstNe).2
              (Polynomial.mem_degreeLT.mp base.1.1.2)
          rw [hbaseA, Polynomial.natDegree_mul hG hA, hDdeg] at hnbase
          omega
        apply finrank_le_window_of_projection_factor V
          (pairFirstPolynomial V) A
        · intro v w hvw
          rcases hall v with ⟨Hv, hvA, hvB⟩
          rcases hall w with ⟨Hw, hwA, hwB⟩
          have hH : Hv = Hw := by
            apply mul_right_cancel₀ hA
            exact hvA.symm.trans (hvw.trans hwA)
          apply Subtype.ext
          apply Prod.ext
          · apply Subtype.ext
            exact hvA.trans (hH ▸ hwA.symm)
          · apply Subtype.ext
            rw [hvB, hwB, hH]
        · intro v
          rcases hall v with ⟨H, hAfac, _hB⟩
          refine ⟨⟨H, ?_⟩, hAfac⟩
          exact multiplier_degreeLT_of_maximal_component A H v.1.1.1
            hA hDdeg hDlt (Polynomial.mem_degreeLT.mp v.1.1.2) hAfac
      · rcases le_total A.natDegree B.natDegree with hAleB | hBleA
        · have hDdeg : B.natDegree = D := by simp [D, hAleB]
          have hbaseSecondNe : base.1.2.1 ≠ 0 := by
            rw [hbaseB]
            exact mul_ne_zero hG hB
          have hDlt : D < n := by
            have hnbase : base.1.2.1.natDegree < n :=
              (Polynomial.natDegree_lt_iff_degree_lt hbaseSecondNe).2
                (Polynomial.mem_degreeLT.mp base.1.2.2)
            rw [hbaseB, Polynomial.natDegree_mul hG hB, hDdeg] at hnbase
            omega
          apply finrank_le_window_of_projection_factor V
            (pairSecondPolynomial V) B
          · intro v w hvw
            rcases hall v with ⟨Hv, hvA, hvB⟩
            rcases hall w with ⟨Hw, hwA, hwB⟩
            have hH : Hv = Hw := by
              apply mul_right_cancel₀ hB
              exact hvB.symm.trans (hvw.trans hwB)
            apply Subtype.ext
            apply Prod.ext
            · apply Subtype.ext
              rw [hvA, hwA, hH]
            · apply Subtype.ext
              exact hvB.trans (hH ▸ hwB.symm)
          · intro v
            rcases hall v with ⟨H, _hA, hBfac⟩
            refine ⟨⟨H, ?_⟩, hBfac⟩
            exact multiplier_degreeLT_of_maximal_component B H v.1.2.1
              hB hDdeg hDlt (Polynomial.mem_degreeLT.mp v.1.2.2) hBfac
        · have hDdeg : A.natDegree = D := by simp [D, hBleA]
          have hbaseFirstNe : base.1.1.1 ≠ 0 := by
            rw [hbaseA]
            exact mul_ne_zero hG hA
          have hDlt : D < n := by
            have hnbase : base.1.1.1.natDegree < n :=
              (Polynomial.natDegree_lt_iff_degree_lt hbaseFirstNe).2
                (Polynomial.mem_degreeLT.mp base.1.1.2)
            rw [hbaseA, Polynomial.natDegree_mul hG hA, hDdeg] at hnbase
            omega
          apply finrank_le_window_of_projection_factor V
            (pairFirstPolynomial V) A
          · intro v w hvw
            rcases hall v with ⟨Hv, hvA, hvB⟩
            rcases hall w with ⟨Hw, hwA, hwB⟩
            have hH : Hv = Hw := by
              apply mul_right_cancel₀ hA
              exact hvA.symm.trans (hvw.trans hwA)
            apply Subtype.ext
            apply Prod.ext
            · apply Subtype.ext
              exact hvA.trans (hH ▸ hwA.symm)
            · apply Subtype.ext
              rw [hvB, hwB, hH]
          · intro v
            rcases hall v with ⟨H, hAfac, _hB⟩
            refine ⟨⟨H, ?_⟩, hAfac⟩
            exact multiplier_degreeLT_of_maximal_component A H v.1.1.1
              hA hDdeg hDlt (Polynomial.mem_degreeLT.mp v.1.1.2) hAfac
  refine ⟨A, B, hAB, hcoprime, ?_, hall⟩
  dsimp [D] at hdim ⊢
  omega
private theorem natDegree_le_pred_of_degreeLT
    {F : Type*} [Field F] {n : Nat} (hn : 0 < n)
    (P : Polynomial.degreeLT F n) : P.1.natDegree ≤ n - 1 := by
  by_cases hP : P.1 = 0
  · simp [hP]
  · have hlt : P.1.natDegree < n :=
      (Polynomial.natDegree_lt_iff_degree_lt hP).2
        (Polynomial.mem_degreeLT.mp P.2)
    omega
theorem fullTwoLane_kernel_finrank_eq_sub_rank
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t → F) (beta E : Fin t → F) :
    Module.finrank F
        (LinearMap.ker
          (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin) =
      t - (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).rank := by
  have hnull := rank_add_finrank_ker_mulVecLin
    (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E)
  simp only [Fintype.card_fin] at hnull
  omega
theorem exists_ownerwise_primitive_pair_of_fullTwoLane_kernel
    {F : Type*} [Field F] {t rows : Nat}
    (sigma : F →+* F) (alpha : Fin t ↪ F) (beta E : Fin t → F)
    (hrows : rows ≤ t)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hnull : 0 < Module.finrank F
      (LinearMap.ker
        (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin))
    (hwindow : 0 < t - rows)
    (hmass : (t - rows - 1) + (t - rows - 1) < t) :
    ∃ A B : Polynomial F,
      (A ≠ 0 ∨ B ≠ 0) ∧ IsCoprime A B ∧
      max A.natDegree B.natDegree ≤
        (t - rows) - Module.finrank F
          (LinearMap.ker
            (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin) ∧
      ∀ v : LinearMap.ker
          (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin,
        ∃ H : Polynomial F,
          (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).1.1 =
              H * A ∧
            (fullKernelFailurePairLinear sigma alpha rows hrows beta E v).2.1 =
              H * B := by
  let Φ := fullKernelFailurePairLinear sigma alpha rows hrows beta E
  let V : Submodule F
      (Polynomial.degreeLT F (t - rows) ×
        Polynomial.degreeLT F (t - rows)) := LinearMap.range Φ
  have hVdim : Module.finrank F V =
      Module.finrank F
        (LinearMap.ker
          (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).mulVecLin) := by
    exact fullKernelFailurePair_range_finrank
      sigma alpha hrows beta E hbeta hE
  have hVpos : 0 < Module.finrank F V := hVdim.trans_gt hnull
  have hcross : ∀ v w : V,
      v.1.1.1 * w.1.2.1 - w.1.1.1 * v.1.2.1 = 0 := by
    intro v w
    rcases v.2 with ⟨x, hx⟩
    rcases w.2 with ⟨y, hy⟩
    have hx₀ : v.1.1.1 = (Φ x).1.1 := by
      exact congrArg (fun p => p.1.1) hx.symm
    have hx₁ : v.1.2.1 = (Φ x).2.1 := by
      exact congrArg (fun p => p.2.1) hx.symm
    have hy₀ : w.1.1.1 = (Φ y).1.1 := by
      exact congrArg (fun p => p.1.1) hy.symm
    have hy₁ : w.1.2.1 = (Φ y).2.1 := by
      exact congrArg (fun p => p.2.1) hy.symm
    rw [hx₀, hx₁, hy₀, hy₁]
    exact failurePairCross_eq_zero_of_two_mul_degree_lt_card
      sigma alpha E (Φ x).1.1 (Φ x).2.1 (Φ y).1.1 (Φ y).2.1
      (t - rows - 1) hE
      (natDegree_le_pred_of_degreeLT hwindow (Φ x).1)
      (natDegree_le_pred_of_degreeLT hwindow (Φ x).2)
      (natDegree_le_pred_of_degreeLT hwindow (Φ y).1)
      (natDegree_le_pred_of_degreeLT hwindow (Φ y).2)
      (fullKernelFailurePairLinear_relation sigma alpha hrows beta E x)
      (fullKernelFailurePairLinear_relation sigma alpha hrows beta E y)
      hmass
  obtain ⟨A, B, hAB, hcop, hdeg, hfactor⟩ :=
    exists_primitive_pair_degree_le_sub_finrank V hVpos hcross
  refine ⟨A, B, hAB, hcop, ?_, ?_⟩
  · simpa [hVdim] using hdeg
  · intro v
    have hmem : Φ v ∈ V := ⟨v, rfl⟩
    exact hfactor ⟨Φ v, hmem⟩
theorem ownerwise_primitive_degree_le_rank_sub_rows
    (t rows rho delta D : Nat)
    (hrows : rows ≤ rho) (hrho : rho ≤ t)
    (hdelta : delta = t - rho)
    (hD : D ≤ (t - rows) - delta) :
    D ≤ rho - rows := by
  omega
theorem primitive_degree_cap_from_nullity6401
    (delta D : Nat) (hdelta : delta ≤ keySecondLaneRows6401)
    (hD : D ≤ keySecondLaneRows6401 - delta) :
    D ≤ 22508 - delta := by
  simpa [keySecondLaneRows6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401,
    ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401.n6401,
    ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401.ownerDegreeCap6401,
    ProximityPrize.SubmissionLower.bchksErrors6401] using hD
theorem primitive_degree_delta_one_exact6401 :
    keySecondLaneRows6401 - 1 = 22507 := by
  norm_num [keySecondLaneRows6401, keyFirstLaneRows6401,
    keyRedundancy6401, keyErrors6401,
    ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401.n6401,
    ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusModuleAudit6401.ownerDegreeCap6401,
    ProximityPrize.SubmissionLower.bchksErrors6401]
end BCHKSFrobeniusPrimitiveDegreeDrop6401
end ProximityPrize.SubmissionLower
