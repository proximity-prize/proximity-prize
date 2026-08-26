import ProximityPrize.SubmissionLower.BCHKSStableInterpolation6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSMinimalYReplacement6400
open scoped BigOperators
noncomputable def topRemainderMap {F : Type*} [Field F]
    (G U : Polynomial F) (n k : ℕ) :
    Polynomial.degreeLT F (k + 1) →ₗ[F] F :=
  (Polynomial.lcoeff F (n - 1)).comp <|
    (Polynomial.modByMonicHom G).comp <|
      (LinearMap.mulRight F U).comp (Polynomial.degreeLT F (k + 1)).subtype
noncomputable def twoTopRemainderMap {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) (n k : ℕ) :
    Polynomial.degreeLT F (k + 1) →ₗ[F] (Fin 2 → F) :=
  LinearMap.pi fun r => topRemainderMap G (U r) n k
@[simp]
lemma topRemainderMap_apply {F : Type*} [Field F]
    (G U : Polynomial F) (n k : ℕ)
    (M : Polynomial.degreeLT F (k + 1)) :
    topRemainderMap G U n k M = ((M.1 * U) %ₘ G).coeff (n - 1) := by
  rfl
@[simp]
lemma twoTopRemainderMap_apply {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) (n k : ℕ)
    (M : Polynomial.degreeLT F (k + 1)) (r : Fin 2) :
    twoTopRemainderMap G U n k M r =
      ((M.1 * U r) %ₘ G).coeff (n - 1) := by
  rfl
theorem exists_nonzero_twoTopRemainderKernel
    {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) (n k : ℕ)
    (hk : 2 < k + 1) :
    ∃ M : Polynomial.degreeLT F (k + 1), M ≠ 0 ∧
      twoTopRemainderMap G U n k M = 0 := by
  let L := twoTopRemainderMap G U n k
  have hnotinj : ¬ Function.Injective L := by
    intro hinj
    have heq := LinearMap.finrank_range_of_inj hinj
    have hdom : Module.finrank F (Polynomial.degreeLT F (k + 1)) = k + 1 := by
      rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F (k + 1))]
      simp
    have hrange : Module.finrank F (LinearMap.range L) ≤ 2 := by
      calc
        Module.finrank F (LinearMap.range L) ≤ Module.finrank F (Fin 2 → F) :=
          (LinearMap.range L).finrank_le
        _ = 2 := by rw [Module.finrank_fintype_fun_eq_card]; simp
    rw [heq, hdom] at hrange
    omega
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    exact hnotinj (LinearMap.ker_eq_bot.mp hbot)
  obtain ⟨M, hMker, hMne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨M, hMne, LinearMap.mem_ker.mp hMker⟩
theorem exists_boundary_scaled_multiplier6400
    {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) :
    ∃ M : Polynomial F,
      M ≠ 0 ∧ M.natDegree ≤ 131071 ∧
      ∀ r : Fin 2, ((M * U r) %ₘ G).coeff 262143 = 0 := by
  obtain ⟨M, hMne, hMker⟩ :=
    exists_nonzero_twoTopRemainderKernel G U 262144 131071 (by norm_num)
  refine ⟨M.1, ?_, ?_, ?_⟩
  · exact fun h => hMne (Subtype.ext h)
  · by_cases hzero : M.1 = 0
    · simp [hzero]
    · have hdeg := M.2
      rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree hzero] at hdeg
      have hdeg' : M.1.natDegree < 131072 := by exact_mod_cast hdeg
      omega
  · intro r
    have hr := congrFun hMker r
    simpa using hr
theorem exists_boundary_scaled_remainders6400
    {F : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F)
    (hGmonic : G.Monic) (hGdegree : G.natDegree = 262144) :
    ∃ (M : Polynomial F) (W : Fin 2 → Polynomial F),
      M ≠ 0 ∧ M.natDegree ≤ 131071 ∧
      (∀ r, W r = (M * U r) %ₘ G) ∧
      (∀ r, (W r).natDegree ≤ 262142) := by
  obtain ⟨M, hMne, hMdegree, htop⟩ :=
    exists_boundary_scaled_multiplier6400 G U
  let W : Fin 2 → Polynomial F := fun r => (M * U r) %ₘ G
  refine ⟨M, W, hMne, hMdegree, fun r => rfl, ?_⟩
  intro r
  have hGone : G ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hGdegree
    norm_num at hGdegree
  have hlt : (W r).natDegree < G.natDegree := by
    exact Polynomial.natDegree_modByMonic_lt (M * U r) hGmonic hGone
  have hle : (W r).natDegree ≤ 262143 := by
    rw [hGdegree] at hlt
    omega
  have hcoeff : (W r).coeff 262143 = 0 := by
    exact htop r
  have := Polynomial.natDegree_le_pred hle hcoeff
  norm_num at this
  exact this
theorem boundary_scaled_remainder_eval
    {F : Type*} [Field F]
    (G M U W : Polynomial F) (x : F)
    (hW : W = (M * U) %ₘ G) (hx : Polynomial.eval x G = 0) :
    Polynomial.eval x W = Polynomial.eval x M * Polynomial.eval x U := by
  subst W
  have h := Polynomial.aeval_modByMonic_eq_self_of_root
    (p := M * U) (q := G) (x := x) (by simpa using hx)
  simpa using h
noncomputable def liftX {F : Type*} [Field F] (P : Polynomial F) :
    Polynomial (Polynomial F) := P.map Polynomial.C
@[simp]
lemma liftX_coeff {F : Type*} [Field F] (P : Polynomial F) (a : ℕ) :
    (liftX P).coeff a = Polynomial.C (P.coeff a) := by
  simp [liftX, Polynomial.coeff_map]
@[simp]
lemma liftX_natDegree {F : Type*} [Field F] (P : Polynomial F) :
    (liftX P).natDegree = P.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective P
noncomputable def scaledReceivedLine {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) :
    Polynomial (Polynomial (Polynomial F)) :=
  Polynomial.C (liftX M) * Polynomial.X -
    Polynomial.C
      (liftX (W 0) + Polynomial.C Polynomial.X * liftX (W 1))
@[simp]
lemma scaledReceivedLine_coeff_zero {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) :
    (scaledReceivedLine M W).coeff 0 =
      -(liftX (W 0) + Polynomial.C Polynomial.X * liftX (W 1)) := by
  simp [scaledReceivedLine]
@[simp]
lemma scaledReceivedLine_coeff_one {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) :
    (scaledReceivedLine M W).coeff 1 = liftX M := by
  simp [scaledReceivedLine]
lemma scaledReceivedLine_coeff_eq_zero_of_two_le {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) (j : ℕ) (hj : 2 ≤ j) :
    (scaledReceivedLine M W).coeff j = 0 := by
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  simp only [scaledReceivedLine, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X,
    if_neg hj1, Polynomial.coeff_C_of_ne_zero hj0]
  simp
lemma scaledReceivedLine_coeff_zero_natDegree_le {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) (D : ℕ)
    (hW : ∀ r, (W r).natDegree ≤ D) :
    ((scaledReceivedLine M W).coeff 0).natDegree ≤ D := by
  rw [scaledReceivedLine_coeff_zero, Polynomial.natDegree_neg]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simpa using hW 0
  · exact (Polynomial.natDegree_C_mul_le Polynomial.X (liftX (W 1))).trans (by
      simpa using hW 1)
lemma scaledReceivedLine_coeff_zero_coeff {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) (a : ℕ) :
    ((scaledReceivedLine M W).coeff 0).coeff a =
      -(Polynomial.C ((W 0).coeff a) +
        Polynomial.X * Polynomial.C ((W 1).coeff a)) := by
  simp [scaledReceivedLine, liftX, Polynomial.coeff_map,
    Polynomial.coeff_C_mul]
lemma scaledReceivedLine_coeff_zero_coeff_natDegree_le_one
    {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) (a : ℕ) :
    (((scaledReceivedLine M W).coeff 0).coeff a).natDegree ≤ 1 := by
  rw [scaledReceivedLine_coeff_zero_coeff, Polynomial.natDegree_neg]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · exact (Polynomial.natDegree_mul_le.trans (by simp))
theorem scaledReceivedLine_weight_cap6400 {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F)
    (hM : M.natDegree ≤ 131071)
    (hW : ∀ r, (W r).natDegree ≤ 262142) :
    ∀ j a, (((scaledReceivedLine M W).coeff j).coeff a) ≠ 0 →
      a + 131071 * j ≤ 262142 := by
  intro j a hcoeff
  by_cases hj0 : j = 0
  · subst j
    have ha := Polynomial.le_natDegree_of_ne_zero hcoeff
    have hd := scaledReceivedLine_coeff_zero_natDegree_le M W 262142 hW
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ha.trans hd
  by_cases hj1 : j = 1
  · subst j
    rw [scaledReceivedLine_coeff_one, liftX_coeff] at hcoeff
    have ha : a ≤ M.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (Polynomial.C_ne_zero.mp hcoeff)
    norm_num
    omega
  · have hj2 : 2 ≤ j := by omega
    rw [scaledReceivedLine_coeff_eq_zero_of_two_le M W j hj2] at hcoeff
    exact False.elim (hcoeff rfl)
theorem scaledReceivedLine_yz_cap6400 {F : Type*} [Field F]
    (M : Polynomial F) (W : Fin 2 → Polynomial F) :
    ∀ j a, (((scaledReceivedLine M W).coeff j).coeff a) ≠ 0 →
      (((scaledReceivedLine M W).coeff j).coeff a).natDegree + j ≤ 1 := by
  intro j a hcoeff
  by_cases hj0 : j = 0
  · subst j
    simpa using scaledReceivedLine_coeff_zero_coeff_natDegree_le_one M W a
  by_cases hj1 : j = 1
  · subst j
    rw [scaledReceivedLine_coeff_one, liftX_coeff]
    simp
  · have hj2 : 2 ≤ j := by omega
    rw [scaledReceivedLine_coeff_eq_zero_of_two_le M W j hj2] at hcoeff
    exact False.elim (hcoeff rfl)
theorem scaledReceivedLine_specializeX
    {F : Type*} [Field F]
    (G M : Polynomial F) (U W : Fin 2 → Polynomial F) (x : F)
    (hW : ∀ r, W r = (M * U r) %ₘ G)
    (hx : Polynomial.eval x G = 0) :
    (scaledReceivedLine M W).map
        (Polynomial.evalRingHom (Polynomial.C x)) =
      Polynomial.C (Polynomial.C (Polynomial.eval x M)) *
        (Polynomial.X - Polynomial.C
          (Polynomial.C (Polynomial.eval x (U 0)) +
            Polynomial.X * Polynomial.C (Polynomial.eval x (U 1)))) := by
  have hWr (r : Fin 2) :
      Polynomial.eval x (W r) =
        Polynomial.eval x M * Polynomial.eval x (U r) :=
    boundary_scaled_remainder_eval G M (U r) (W r) x (hW r) hx
  simp only [scaledReceivedLine, Polynomial.map_sub, Polynomial.map_C]
  simp [liftX, hWr]
  ring
lemma shift_coeff_zero_zero {R : Type*} [CommRing R]
    (Q : Polynomial (Polynomial R)) (x y : R) :
    ((Polynomial.Bivariate.shift Q x y).coeff 0).coeff 0 =
      Polynomial.eval y
        (Q.map (Polynomial.evalRingHom x)) := by
  simp only [Polynomial.Bivariate.shift, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coe_compRingHom_apply,
    Polynomial.eval₂_at_zero, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, zero_add, Polynomial.eval_map]
  simpa only [Polynomial.eval_map] using
    (Polynomial.map_evalRingHom_eval x y Q).symm
theorem scaledReceivedLine_local_order_one
    {F : Type*} [Field F]
    (G M : Polynomial F) (U W : Fin 2 → Polynomial F) (x : F)
    (hW : ∀ r, W r = (M * U r) %ₘ G)
    (hx : Polynomial.eval x G = 0) :
    (((Polynomial.Bivariate.shift (scaledReceivedLine M W)
        (Polynomial.C x)
        (Polynomial.C (Polynomial.eval x (U 0)) +
          Polynomial.X * Polynomial.C (Polynomial.eval x (U 1)))).coeff 0).coeff 0) = 0 := by
  rw [shift_coeff_zero_zero]
  rw [scaledReceivedLine_specializeX G M U W x hW hx]
  simp
theorem exists_boundary_scaled_received_line6400
    {F ι : Type*} [Field F]
    (G : Polynomial F) (U : Fin 2 → Polynomial F) (omega : ι → F)
    (hGmonic : G.Monic) (hGdegree : G.natDegree = 262144)
    (hroot : ∀ i, Polynomial.eval (omega i) G = 0) :
    ∃ (M : Polynomial F) (W : Fin 2 → Polynomial F)
      (S : Polynomial (Polynomial (Polynomial F))),
      M ≠ 0 ∧ M.natDegree ≤ 131071 ∧
      (∀ r, W r = (M * U r) %ₘ G) ∧
      (∀ r, (W r).natDegree ≤ 262142) ∧
      S = scaledReceivedLine M W ∧ S ≠ 0 ∧
      Polynomial.Bivariate.natDegreeY S = 1 ∧
      (∀ j a, ((S.coeff j).coeff a) ≠ 0 →
        a + 131071 * j ≤ 262142) ∧
      (∀ j a, ((S.coeff j).coeff a) ≠ 0 →
        ((S.coeff j).coeff a).natDegree + j ≤ 1) ∧
      (∀ i,
        (((Polynomial.Bivariate.shift S (Polynomial.C (omega i))
          (Polynomial.C (Polynomial.eval (omega i) (U 0)) +
            Polynomial.X * Polynomial.C
              (Polynomial.eval (omega i) (U 1)))).coeff 0).coeff 0) = 0) := by
  obtain ⟨M, W, hMne, hMdegree, hW, hWdegree⟩ :=
    exists_boundary_scaled_remainders6400 G U hGmonic hGdegree
  let S := scaledReceivedLine M W
  have hliftM : liftX M ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hMne
  have hScoeff : S.coeff 1 ≠ 0 := by
    simpa [S] using hliftM
  have hS : S ≠ 0 := by
    intro hzero
    apply hScoeff
    rw [hzero]
    simp
  have hSle : S.natDegree ≤ 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    exact scaledReceivedLine_coeff_eq_zero_of_two_le M W j (by omega)
  have hSdegree : Polynomial.Bivariate.natDegreeY S = 1 := by
    unfold Polynomial.Bivariate.natDegreeY
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hSle hScoeff
  refine ⟨M, W, S, hMne, hMdegree, hW, hWdegree, rfl, hS, hSdegree,
    ?_, ?_, ?_⟩
  · simpa [S] using scaledReceivedLine_weight_cap6400 M W hMdegree hWdegree
  · simpa [S] using scaledReceivedLine_yz_cap6400 M W
  · intro i
    simpa [S] using scaledReceivedLine_local_order_one
      G M U W (omega i) hW (hroot i)
end BCHKSMinimalYReplacement6400
end ProximityPrize.SubmissionLower
