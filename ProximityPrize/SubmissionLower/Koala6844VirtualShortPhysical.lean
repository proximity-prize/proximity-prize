import ProximityPrize.SubmissionLower.Koala6844VirtualShortNodeData
import ProximityPrize.SubmissionLower.Koala6844VirtualShortLeading


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetSpecialize SecondJetCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

variable {K : Type*} [Field K]

private def embedAt {n : ℕ} (i : Fin n) : Polynomial K →ₐ[K] MvPolynomial (Fin n) K :=
  Polynomial.aeval (MvPolynomial.X i)

private theorem comp_embedAt_of_X {n : ℕ} {R : Type*} [CommSemiring R] [Algebra K R]
    (φ : MvPolynomial (Fin n) K →ₐ[K] R) (i : Fin n)
    (ψ : Polynomial K →ₐ[K] R) (h : φ (MvPolynomial.X i) = ψ Polynomial.X)
    (p : Polynomial K) : φ (embedAt i p) = ψ p := by
  have he : φ.comp (embedAt (K := K) i) = ψ := Polynomial.algHom_ext (by simpa [embedAt] using h)
  exact DFunLike.congr_fun he p

private theorem specialize_embed (f p : Polynomial K) (g : K) :
    specialize f g (embedDisplacement p) = p := by
  exact comp_embedAt_of_X (specialize f g) 0 (AlgHom.id K (Polynomial K))
    (by simp [specialize]) p

@[simp] theorem specialize_normalizedDenominator (A₀ A₁ f : Polynomial K) (g : K) :
    specialize f g (normalizedDenominator A₀ A₁) = A₀+Polynomial.C g*A₁ := by
  simp only [normalizedDenominator, map_add, map_mul, specialize_embed]
  rw [show specialize f g (MvPolynomial.X 4) = Polynomial.C g by simp [specialize],mul_comm]

@[simp] theorem specialize_normalizedNumerator (d₀ C₁ f : Polynomial K) (g : K) :
    specialize f g (normalizedNumerator d₀ C₁) = d₀*f+Polynomial.C g*C₁ := by
  simp only [normalizedNumerator, map_add, map_mul, specialize_embed]
  rw [show specialize f g (MvPolynomial.X 2) = f by simp [specialize],
    show specialize f g (MvPolynomial.X 4) = Polynomial.C g by simp [specialize],mul_comm C₁]

private theorem map_X_asSeed_0 : asSeed (K := K) 4 (MvPolynomial.X 0) =
    Polynomial.C (MvPolynomial.X 3) := by
  change MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) (Fin.last 4)) (MvPolynomial.X 0)) = _
  rw [MvPolynomial.rename_X, Equiv.swap_apply_left]
  exact MvPolynomial.finSuccEquiv_X_succ (j := 3)

private theorem map_X_asSeed_2 : asSeed (K := K) 4 (MvPolynomial.X 2) =
    Polynomial.C (MvPolynomial.X 1) := by
  change MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) (Fin.last 4)) (MvPolynomial.X 2)) = _
  rw [MvPolynomial.rename_X, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  exact MvPolynomial.finSuccEquiv_X_succ (j := 1)

private theorem map_X_asSeed_4 : asSeed (K := K) 4 (MvPolynomial.X 4) = Polynomial.X := by
  change MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) (Fin.last 4)) (MvPolynomial.X (Fin.last 4))) = _
  rw [MvPolynomial.rename_X, Equiv.swap_apply_right, MvPolynomial.finSuccEquiv_X_zero]

private theorem asSeed_embed (p : Polynomial K) :
    asSeed 4 (embedDisplacement p) = Polynomial.C (embedAt 3 p : MvPolynomial (Fin 4) K) := by
  exact comp_embedAt_of_X (asSeed (K := K) 4).toAlgHom 0
    ((Polynomial.CAlgHom (R := K) (A := MvPolynomial (Fin 4) K)).comp (embedAt (K := K) 3))
    (by simpa [embedAt] using map_X_asSeed_0 (K := K)) p

private def evalSeedless (v : K) : MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![0,Polynomial.C v,0,Polynomial.X]

private theorem evalSeedless_embed (v : K) (p : Polynomial K) :
    evalSeedless v (embedAt (n := 4) 3 p) = p :=
  comp_embedAt_of_X (evalSeedless v) 3 (AlgHom.id K (Polynomial K)) (by simp [evalSeedless]) p

theorem normalized_affine_elimination (A₀ A₁ d₀ C₁ : Polynomial K) (ha : A₁ ≠ 0) (hd : d₀ ≠ 0) :
    ∃ a₀ a₁ b₀ b₁ : MvPolynomial (Fin 4) K,
      asSeed 4 (normalizedDenominator A₀ A₁) = Polynomial.C a₀+Polynomial.C a₁*Polynomial.X ∧
      asSeed 4 (normalizedNumerator d₀ C₁) = Polynomial.C b₀+Polynomial.C b₁*Polynomial.X ∧
      a₁ ≠ 0 ∧ a₁*b₀ ≠ a₀*b₁ := by
  refine ⟨embedAt 3 A₀,embedAt 3 A₁,embedAt 3 d₀*MvPolynomial.X 1,embedAt 3 C₁,?_,?_,?_,?_⟩
  · simp only [normalizedDenominator,map_add,map_mul,asSeed_embed,map_X_asSeed_4]
  · simp only [normalizedNumerator,map_add,map_mul,asSeed_embed,map_X_asSeed_2,map_X_asSeed_4]
  · intro hz
    exact ha (by simpa only [evalSeedless_embed,map_zero] using congrArg (evalSeedless (0 : K)) hz)
  · intro hz
    have h0 := congrArg (evalSeedless (0 : K)) hz
    have h1 := congrArg (evalSeedless (1 : K)) hz
    have ev (v : K) : evalSeedless v (MvPolynomial.X 1) = Polynomial.C v := by simp [evalSeedless]
    simp only [map_mul,evalSeedless_embed,ev,map_zero,mul_zero,map_one,mul_one] at h0 h1
    exact mul_ne_zero ha hd (h1.trans h0.symm)

private theorem map_X_asS_0 : asS (K := K) (MvPolynomial.X 0) =
    Polynomial.C (MvPolynomial.X 0) := by
  change MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) (MvPolynomial.X 0)) = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_left]
  exact MvPolynomial.finSuccEquiv_X_succ (j := 0)

private theorem map_X_asS_2 : asS (K := K) (MvPolynomial.X 2) =
    Polynomial.C (MvPolynomial.X 1) := by
  change MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) (MvPolynomial.X 2)) = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  exact MvPolynomial.finSuccEquiv_X_succ (j := 1)

private theorem map_X_asS_4 : asS (K := K) (MvPolynomial.X 4) =
    Polynomial.C (MvPolynomial.X 3) := by
  change MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) (MvPolynomial.X 4)) = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  exact MvPolynomial.finSuccEquiv_X_succ (j := 3)

private theorem asS_embed (p : Polynomial K) :
    asS (embedDisplacement p) = Polynomial.C (embedAt 0 p : MvPolynomial (Fin 4) K) := by
  exact comp_embedAt_of_X (asS (K := K)).toAlgHom 0
    ((Polynomial.CAlgHom (R := K) (A := MvPolynomial (Fin 4) K)).comp (embedAt (K := K) 0))
    (by simpa [embedAt] using map_X_asS_0 (K := K)) p

private theorem asS_den (a₀ a₁ : Polynomial K) : asS (normalizedDenominator a₀ a₁) =
    Polynomial.C (embedAt 0 a₀+embedAt 0 a₁*MvPolynomial.X 3) := by
  simp [normalizedDenominator,map_X_asS_4,asS_embed]

private theorem asS_num (d C₁ : Polynomial K) : asS (normalizedNumerator d C₁) =
    Polynomial.C (embedAt 0 d*MvPolynomial.X 1+embedAt 0 C₁*MvPolynomial.X 3) := by
  simp [normalizedNumerator,map_X_asS_2,map_X_asS_4,asS_embed]

@[simp] theorem pderiv_normalizedDenominator (a₀ a₁ : Polynomial K) :
    MvPolynomial.pderiv 1 (normalizedDenominator a₀ a₁) = 0 := by
  apply (asS (K := K)).injective
  rw [SecondJetCoefficientSpecialization.asS_pderiv,asS_den,Polynomial.derivative_C,map_zero]

@[simp] theorem pderiv_normalizedNumerator (d C₁ : Polynomial K) :
    MvPolynomial.pderiv 1 (normalizedNumerator d C₁) = 0 := by
  apply (asS (K := K)).injective
  rw [SecondJetCoefficientSpecialization.asS_pderiv,asS_num,Polynomial.derivative_C,map_zero]

private theorem fits_den (a₀ a₁ : Polynomial K) :
    FitsLocal ⟨0,0,0,0,1,1⟩ (normalizedDenominator a₀ a₁) := by
  unfold normalizedDenominator
  apply fits_add (from_pure_bound _ (by decide) _ (fits_embed _))
  simpa [LocalCaps.plus] using (fits_embed a₁).mul (fits_seed (K := K))

private theorem fits_num (d C₁ : Polynomial K) :
    FitsLocal ⟨1,0,0,1,1,1⟩ (normalizedNumerator d C₁) := by
  have hv := (fits_embed d).mul (fits_local_value (K := K))
  have hz := (fits_embed C₁).mul (fits_seed (K := K))
  unfold normalizedNumerator
  apply fits_add
  · intro e he
    obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hv e he
    dsimp [LocalCaps.plus] at h0 h1 h2 h3 h4 h5 ⊢
    exact ⟨h0,h1,h2,h3,h4,by omega⟩
  · intro e he
    obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hz e he
    dsimp [LocalCaps.plus] at h0 h1 h2 h3 h4 h5 ⊢
    exact ⟨by omega,h1,h2,by omega,h4,h5⟩

theorem clear_normalized_support (a₀ a₁ d C₁ : Polynomial K)
    (B s U L q : ℕ) (P : Polynomial (Poly (K := K)))
    (hP : ∀ j e, e ∈ (P.coeff j).support →
      2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3+j ≤ U ∧ e 1+e 2+e 3+e 4 ≤ L) :
    ∀ e ∈ (clearAux (normalizedDenominator a₀ a₁) (normalizedNumerator d C₁) q P).support,
      2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ L+q := by
  classical
  let A := normalizedDenominator a₀ a₁
  let N := normalizedNumerator d C₁
  suffices h : FitsLocal ⟨U,B,s,U,L+q,L+q⟩ (clearAux A N q P) from
    fun e he => ⟨(h e he).2.1,(h e he).2.2.1,(h e he).2.2.2.1,(h e he).2.2.2.2.1⟩
  have hsum (f : ℕ → Poly (K := K)) (v : Finset ℕ)
      (hf : ∀ i ∈ v, FitsLocal ⟨U,B,s,U,L+q,L+q⟩ (f i)) :
      FitsLocal ⟨U,B,s,U,L+q,L+q⟩ (∑ i ∈ v, f i) := by
    induction v using Finset.induction_on with
    | empty => simp [FitsLocal]
    | insert i v hiv ih =>
      rw [Finset.sum_insert hiv]
      exact fits_add (hf _ (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf _ (Finset.mem_insert_of_mem hj)))
  unfold clearAux
  apply hsum
  intro j hj
  have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hp : FitsLocal ⟨U-j,B,s,U-j,L,L⟩ (P.coeff j) := by
    intro e he
    obtain ⟨hB,hs,hU,hL⟩ := hP j e he
    dsimp only
    exact ⟨by omega,hB,hs,by omega,hL,by omega⟩
  intro e he
  have hh := ((fits_den a₀ a₁).pow (q-j)).mul (hp.mul ((fits_num d C₁).pow j)) e he
  dsimp [LocalCaps.plus,LocalCaps.times] at hh ⊢
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hh
  have hu : (j : ℤ) + (U : ℤ) - (j : ℤ) = (U : ℤ) := by ring
  by_cases hju : j ≤ U
  · exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
  · have hz : P.coeff j = 0 := by
      apply MvPolynomial.support_eq_empty.mp
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hh' := (hP j t ht).2.2.1
      omega
    simp [hz] at he

private theorem asSeed3_X0 : asSeed (K := K) 3 (MvPolynomial.X 0) =
    Polynomial.C (MvPolynomial.X 2) := by
  change MvPolynomial.finSuccEquiv K 3
    (MvPolynomial.rename (Equiv.swap (0 : Fin 4) (Fin.last 3)) (MvPolynomial.X 0)) = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_left]
  exact MvPolynomial.finSuccEquiv_X_succ (j := 2)

private theorem asSeed3_X1 : asSeed (K := K) 3 (MvPolynomial.X 1) =
    Polynomial.C (MvPolynomial.X 0) := by
  change MvPolynomial.finSuccEquiv K 3
    (MvPolynomial.rename (Equiv.swap (0 : Fin 4) (Fin.last 3)) (MvPolynomial.X 1)) = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  exact MvPolynomial.finSuccEquiv_X_succ (j := 0)

private theorem asSeed3_X3 : asSeed (K := K) 3 (MvPolynomial.X 3) = Polynomial.X := by
  change MvPolynomial.finSuccEquiv K 3
    (MvPolynomial.rename (Equiv.swap (0 : Fin 4) (Fin.last 3)) (MvPolynomial.X (Fin.last 3))) = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_right,MvPolynomial.finSuccEquiv_X_zero]

private theorem asSeed3_embed (p : Polynomial K) :
    asSeed 3 (embedAt 0 p) = Polynomial.C (embedAt 2 p : MvPolynomial (Fin 3) K) :=
  comp_embedAt_of_X (asSeed (K := K) 3).toAlgHom 0
    ((Polynomial.CAlgHom (R := K) (A := MvPolynomial (Fin 3) K)).comp (embedAt (K := K) 2))
    (by simpa [embedAt] using asSeed3_X0 (K := K)) p

private def evalJetSeedless (v : K) : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.C v,0,Polynomial.X]

private theorem evalJetSeedless_embed (v : K) (p : Polynomial K) :
    evalJetSeedless v (embedAt (n := 3) 2 p) = p :=
  comp_embedAt_of_X (evalJetSeedless v) 2 (AlgHom.id K (Polynomial K)) (by simp [evalJetSeedless]) p

theorem normalized_jet_index_le (a₀ a₁ d C₁ : Polynomial K) (ha : a₁ ≠ 0) (hd : d ≠ 0)
    (q : ℕ) (P : Polynomial (Poly (K := K))) (hdeg : P.natDegree ≤ q)
    (hseed : ∀ j e, e ∈ (P.coeff j).support → 0 < j → e 4 = 0)
    (j : ℕ) (e : Fin 5 →₀ ℕ) (he : e ∈ (P.coeff j).support) :
    e 1 ≤ (asS (clearAux (normalizedDenominator a₀ a₁) (normalizedNumerator d C₁) q P)).natDegree := by
  apply jet_index_le_cleared_degree P _ _ _ _ q (asS_den a₀ a₁) (asS_num d C₁) _ j e he
  intro h hz
  by_contra hp
  apply clearAux_ne_zero_mv _ _ (embedAt 2 a₀) (embedAt 2 a₁)
    (embedAt 2 d*MvPolynomial.X 0) (embedAt 2 C₁) q _ _ _ _ (jetSlice P h) hp _ _ hz
  · simp only [map_add,map_mul,asSeed3_embed,asSeed3_X3]
  · simp only [map_add,map_mul,asSeed3_embed,asSeed3_X1,asSeed3_X3]
  · intro ht
    exact ha (by simpa only [evalJetSeedless_embed,map_zero] using congrArg (evalJetSeedless (0 : K)) ht)
  · intro ht
    have h0 := congrArg (evalJetSeedless (0 : K)) ht
    have h1 := congrArg (evalJetSeedless (1 : K)) ht
    have ev (v : K) : evalJetSeedless v (MvPolynomial.X 0) = Polynomial.C v := by simp [evalJetSeedless]
    simp only [map_mul,evalJetSeedless_embed,ev,map_zero,mul_zero,map_one,mul_one] at h0 h1
    exact mul_ne_zero ha hd (h1.trans h0.symm)
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    change (jetSlice P h).coeff i = 0
    rw [jetSlice_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hi), map_zero, Polynomial.coeff_zero]
  · intro i hi v hv
    rw [jetSlice_coeff] at hv
    have hp := hseed i (liftExponent h v) (coefficient_support _ _ _ hv) hi
    exact (lift_coordinates h v).2.2.2.2.symm.trans hp

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
