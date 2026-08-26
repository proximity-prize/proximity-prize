import ProximityPrize.SubmissionLower.BCHKSMinimalYReplacement6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSSharpScaledLine6400
open BCHKSMinimalYReplacement6400
noncomputable def remainderCoeffMap {F : Type*} [Field F]
    (G U : Polynomial F) (q L : ℕ) :
    Polynomial.degreeLT F (L + 1) →ₗ[F] F :=
  (Polynomial.lcoeff F q).comp <|
    (Polynomial.modByMonicHom G).comp <|
      (LinearMap.mulRight F U).comp (Polynomial.degreeLT F (L + 1)).subtype
@[simp]
lemma remainderCoeffMap_apply {F : Type*} [Field F]
    (G U : Polynomial F) (q L : ℕ)
    (M : Polynomial.degreeLT F (L + 1)) :
    remainderCoeffMap G U q L M = ((M.1 * U) %ₘ G).coeff q := by
  rfl
noncomputable def twoRemainderTailMap {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) (D L r : ℕ) :
    Polynomial.degreeLT F (L + 1) →ₗ[F] (Fin 2 → Fin r → F) :=
  LinearMap.pi fun row => LinearMap.pi fun t =>
    remainderCoeffMap G (U row) (D + 1 + t.1) L
@[simp]
lemma twoRemainderTailMap_apply {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) (D L r : ℕ)
    (M : Polynomial.degreeLT F (L + 1)) (row : Fin 2) (t : Fin r) :
    twoRemainderTailMap G U D L r M row t =
      ((M.1 * U row) %ₘ G).coeff (D + 1 + t.1) := by
  rfl
theorem exists_nonzero_twoRemainderTailKernel
    {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) (D L r : ℕ)
    (hdim : 2 * r < L + 1) :
    ∃ M : Polynomial.degreeLT F (L + 1), M ≠ 0 ∧
      twoRemainderTailMap G U D L r M = 0 := by
  let T := twoRemainderTailMap G U D L r
  have hnotinj : ¬ Function.Injective T := by
    intro hinj
    have heq := LinearMap.finrank_range_of_inj hinj
    have hdom : Module.finrank F (Polynomial.degreeLT F (L + 1)) = L + 1 := by
      rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F (L + 1))]
      simp
    have hrange : Module.finrank F (LinearMap.range T) ≤ 2 * r := by
      calc
        Module.finrank F (LinearMap.range T) ≤
            Module.finrank F (Fin 2 → Fin r → F) :=
          (LinearMap.range T).finrank_le
        _ = 2 * r := by
          rw [Module.finrank_pi_fintype]
          simp [Module.finrank_fintype_fun_eq_card]
    rw [heq, hdom] at hrange
    omega
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    exact hnotinj (LinearMap.ker_eq_bot.mp hbot)
  obtain ⟨M, hMker, hMne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨M, hMne, LinearMap.mem_ker.mp hMker⟩
theorem exists_sharp_scaled_multiplier6400
    {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) :
    ∃ M : Polynomial F,
      M ≠ 0 ∧ M.natDegree ≤ 87382 ∧
      ∀ row : Fin 2, ∀ t : Fin 43690,
        ((M * U row) %ₘ G).coeff (218454 + t.1) = 0 := by
  obtain ⟨M, hMne, hMker⟩ :=
    exists_nonzero_twoRemainderTailKernel G U 218453 87382 43690 (by norm_num)
  refine ⟨M.1, ?_, ?_, ?_⟩
  · exact fun h => hMne (Subtype.ext h)
  · by_cases hzero : M.1 = 0
    · simp [hzero]
    · have hdeg := M.2
      rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree hzero] at hdeg
      have hdeg' : M.1.natDegree < 87383 := by exact_mod_cast hdeg
      omega
  · intro row t
    have ht := congrFun (congrFun hMker row) t
    simpa using ht
theorem exists_sharp_scaled_remainders6400
    {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F)
    (hGmonic : G.Monic) (hGdegree : G.natDegree = 262144) :
    ∃ (M : Polynomial F) (W : Fin 2 → Polynomial F),
      M ≠ 0 ∧ M.natDegree ≤ 87382 ∧
      (∀ row, W row = (M * U row) %ₘ G) ∧
      (∀ row, (W row).natDegree ≤ 218453) := by
  obtain ⟨M, hMne, hMdegree, htail⟩ :=
    exists_sharp_scaled_multiplier6400 G U
  let W : Fin 2 → Polynomial F := fun row => (M * U row) %ₘ G
  refine ⟨M, W, hMne, hMdegree, fun row => rfl, ?_⟩
  intro row
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro q hq
  by_cases hqn : q < 262144
  · have hlow : 218454 ≤ q := by omega
    let t : Fin 43690 := ⟨q - 218454, by omega⟩
    have ht := htail row t
    have hindex : 218454 + t.1 = q := by
      dsimp [t]
      omega
    simpa [W, hindex] using ht
  · have hlt : (W row).natDegree < 262144 := by
      rw [← hGdegree]
      exact Polynomial.natDegree_modByMonic_lt (M * U row) hGmonic
        (by intro h; rw [h, Polynomial.natDegree_one] at hGdegree; omega)
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hlt (by omega))
theorem scaledReceivedLine_weight_cap
    {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) (k L D : ℕ)
    (hM : M.natDegree ≤ L) (hW : ∀ row, (W row).natDegree ≤ D)
    (hbudget : L + k ≤ D) :
    ∀ j a, (((scaledReceivedLine M W).coeff j).coeff a) ≠ 0 →
      a + k * j ≤ D := by
  intro j a hcoeff
  by_cases hj0 : j = 0
  · subst j
    have ha := Polynomial.le_natDegree_of_ne_zero hcoeff
    have hd := scaledReceivedLine_coeff_zero_natDegree_le M W D hW
    simpa using ha.trans hd
  by_cases hj1 : j = 1
  · subst j
    rw [scaledReceivedLine_coeff_one, liftX_coeff] at hcoeff
    have ha : a ≤ M.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (Polynomial.C_ne_zero.mp hcoeff)
    simpa using (Nat.add_le_add_right (ha.trans hM) k).trans hbudget
  · have hj2 : 2 ≤ j := by omega
    rw [scaledReceivedLine_coeff_eq_zero_of_two_le M W j hj2] at hcoeff
    exact False.elim (hcoeff rfl)
theorem exists_sharp_scaled_received_line6400
    {F ι : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) (omega : ι → F)
    (hGmonic : G.Monic) (hGdegree : G.natDegree = 262144)
    (hroot : ∀ i, Polynomial.eval (omega i) G = 0) :
    ∃ (M : Polynomial F) (W : Fin 2 → Polynomial F)
      (S : Polynomial (Polynomial (Polynomial F))),
      M ≠ 0 ∧ M.natDegree ≤ 87382 ∧
      (∀ row, W row = (M * U row) %ₘ G) ∧
      (∀ row, (W row).natDegree ≤ 218453) ∧
      S = scaledReceivedLine M W ∧ S ≠ 0 ∧
      Polynomial.Bivariate.natDegreeY S = 1 ∧
      (∀ j a, ((S.coeff j).coeff a) ≠ 0 →
        a + 131071 * j ≤ 218453) ∧
      (∀ j a, ((S.coeff j).coeff a) ≠ 0 →
        ((S.coeff j).coeff a).natDegree + j ≤ 1) ∧
      (∀ i,
        (((Polynomial.Bivariate.shift S (Polynomial.C (omega i))
          (Polynomial.C (Polynomial.eval (omega i) (U 0)) +
            Polynomial.X * Polynomial.C
              (Polynomial.eval (omega i) (U 1)))).coeff 0).coeff 0) = 0) := by
  obtain ⟨M, W, hMne, hMdegree, hW, hWdegree⟩ :=
    exists_sharp_scaled_remainders6400 G U hGmonic hGdegree
  let S := scaledReceivedLine M W
  have hliftM : liftX M ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hMne
  have hScoeff : S.coeff 1 ≠ 0 := by simpa [S] using hliftM
  have hS : S ≠ 0 := fun hzero => hScoeff (by rw [hzero]; simp)
  have hSle : S.natDegree ≤ 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    exact scaledReceivedLine_coeff_eq_zero_of_two_le M W j (by omega)
  have hSdegree : Polynomial.Bivariate.natDegreeY S = 1 := by
    unfold Polynomial.Bivariate.natDegreeY
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hSle hScoeff
  refine ⟨M, W, S, hMne, hMdegree, hW, hWdegree, rfl, hS, hSdegree,
    ?_, ?_, ?_⟩
  · simpa [S] using scaledReceivedLine_weight_cap M W 131071 87382 218453
      hMdegree hWdegree (by norm_num)
  · simpa [S] using scaledReceivedLine_yz_cap6400 M W
  · intro i
    simpa [S] using scaledReceivedLine_local_order_one
      G M U W (omega i) hW (hroot i)
end BCHKSSharpScaledLine6400
end ProximityPrize.SubmissionLower
