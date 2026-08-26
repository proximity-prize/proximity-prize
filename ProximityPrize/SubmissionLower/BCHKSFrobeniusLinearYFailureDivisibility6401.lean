import ProximityPrize.SubmissionLower.BCHKSFrobeniusHighSupportMaxRank6401
import ProximityPrize.SubmissionLower.BCHKSLinearYInterpolation6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusLinearYFailureDivisibility6401
open Polynomial
open scoped BigOperators
open ProximityPrize.Benchmark
open BCHKSLinearYKernelAudit6401
open BCHKSLinearYInterpolation6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusKernelPairSpace6401
open BCHKSFrobeniusSupportStratification6401
open BCHKSFrobeniusPrimitiveZeroIRS6401
open BCHKSTwoFrobeniusModuleAudit6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
noncomputable def highCoefficientWindowOfMap
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (C : V →ₗ[F] F[X]) (h delta : Nat) :
    V →ₗ[F] (Fin (delta - 1) → F) where
  toFun v j := (C v).coeff (h + 1 + j.1)
  map_add' v w := by
    funext j
    simp
  map_smul' a v := by
    funext j
    simp
theorem exists_nonzero_highWindow_kernel
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (C : V →ₗ[F] F[X]) (h delta : Nat)
    (hdelta : 0 < delta) (hfin : Module.finrank F V = delta) :
    ∃ v : V, v ≠ 0 ∧
      ∀ j : Fin (delta - 1), (C v).coeff (h + 1 + j.1) = 0 := by
  let T := highCoefficientWindowOfMap C h delta
  have htarget : Module.finrank F (Fin (delta - 1) → F) = delta - 1 := by
    simp
  have hnotinj : ¬ Function.Injective T := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hfin, htarget] at hle
    omega
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective T := by
      intro x y hxy
      have hsub : x - y ∈ LinearMap.ker T := by
        rw [LinearMap.mem_ker]
        simpa [sub_eq_zero] using hxy
      have hsubBot : x - y ∈ (⊥ : Submodule F V) := by
        rw [← hbot]
        exact hsub
      have hzero : x - y = 0 := by simpa using hsubBot
      exact sub_eq_zero.mp hzero
    exact hnotinj hinj
  obtain ⟨v, hvker, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hv, ?_⟩
  intro j
  exact congrFun (LinearMap.mem_ker.mp hvker) j
theorem natDegree_le_of_degreeLT_highWindow
    {F : Type*} [Field F] {h delta : Nat} (P : F[X])
    (hdelta : 0 < delta)
    (hP : P ∈ Polynomial.degreeLT F (h + delta))
    (hwindow : ∀ j : Fin (delta - 1),
      P.coeff (h + 1 + j.1) = 0) :
    P.natDegree ≤ h := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hntop : n < h + delta
  · let j : Fin (delta - 1) := ⟨n - (h + 1), by omega⟩
    have hj : h + 1 + j.1 = n := by
      dsimp [j]
      omega
    simpa [hj] using hwindow j
  · by_cases hzero : P = 0
    · simp [hzero]
    · have hdeg : P.natDegree < h + delta :=
        (Polynomial.natDegree_lt_iff_degree_lt hzero).2
          (Polynomial.mem_degreeLT.mp hP)
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (hdeg.trans_le (Nat.le_of_not_gt hntop))
private theorem exists_low_pair_of_first_max
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    {h delta : Nat}
    (Phi : V →ₗ[F]
      (Polynomial.degreeLT F (h + delta) ×
        Polynomial.degreeLT F (h + delta)))
    (hinj : Function.Injective Phi)
    (hdelta : 0 < delta) (hfin : Module.finrank F V = delta)
    (A B : F[X]) (hA : A ≠ 0) (hBA : B.natDegree ≤ A.natDegree)
    (hfactor : ∀ v : V, ∃ H : F[X],
      (Phi v).1.1 = H * A ∧ (Phi v).2.1 = H * B) :
    ∃ v : V, v ≠ 0 ∧
      (Phi v).1.1.natDegree ≤ h ∧ (Phi v).2.1.natDegree ≤ h := by
  let C : V →ₗ[F] F[X] := {
    toFun := fun v ↦ (Phi v).1.1
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  obtain ⟨v, hv, hwindow⟩ :=
    exists_nonzero_highWindow_kernel C h delta hdelta hfin
  have hfirst : (Phi v).1.1.natDegree ≤ h :=
    natDegree_le_of_degreeLT_highWindow (Phi v).1.1 hdelta
      (Phi v).1.2 hwindow
  obtain ⟨H, hHA, hHB⟩ := hfactor v
  have hH : H ≠ 0 := by
    intro hHzero
    have hPhi : Phi v = 0 := by
      apply Prod.ext <;> apply Subtype.ext
      · simpa [hHzero] using hHA
      · simpa [hHzero] using hHB
    exact hv (hinj (hPhi.trans (map_zero Phi).symm))
  have hsecond : (Phi v).2.1.natDegree ≤ h := by
    by_cases hB : B = 0
    · simp [hHB, hB]
    · have hfirstDegree : (Phi v).1.1.natDegree =
          H.natDegree + A.natDegree := by
        rw [hHA, Polynomial.natDegree_mul hH hA]
      have hsecondDegree : (Phi v).2.1.natDegree =
          H.natDegree + B.natDegree := by
        rw [hHB, Polynomial.natDegree_mul hH hB]
      omega
  exact ⟨v, hv, hfirst, hsecond⟩
theorem exists_nonzero_pair_natDegree_le_excess
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    {h delta : Nat}
    (Phi : V →ₗ[F]
      (Polynomial.degreeLT F (h + delta) ×
        Polynomial.degreeLT F (h + delta)))
    (hinj : Function.Injective Phi)
    (hdelta : 0 < delta) (hfin : Module.finrank F V = delta)
    (A B : F[X]) (hAB : A ≠ 0 ∨ B ≠ 0)
    (hfactor : ∀ v : V, ∃ H : F[X],
      (Phi v).1.1 = H * A ∧ (Phi v).2.1 = H * B) :
    ∃ v : V, v ≠ 0 ∧
      (Phi v).1.1.natDegree ≤ h ∧ (Phi v).2.1.natDegree ≤ h := by
  let swap :
        (Polynomial.degreeLT F (h + delta) ×
          Polynomial.degreeLT F (h + delta)) →ₗ[F]
          (Polynomial.degreeLT F (h + delta) ×
            Polynomial.degreeLT F (h + delta)) :=
      (LinearEquiv.prodComm F _ _).toLinearMap
  have hswapInj : Function.Injective (swap.comp Phi) := by
    intro v w hvw
    apply hinj
    apply (LinearEquiv.prodComm F _ _).injective
    simpa [swap] using hvw
  have hfacSwap : ∀ v : V, ∃ H : F[X],
      ((swap.comp Phi) v).1.1 = H * B ∧
        ((swap.comp Phi) v).2.1 = H * A := by
    intro v
    obtain ⟨H, h0, h1⟩ := hfactor v
    exact ⟨H, by simpa [swap] using h1, by simpa [swap] using h0⟩
  by_cases hA : A = 0
  · have hB : B ≠ 0 := hAB.resolve_left (by simpa [hA])
    obtain ⟨v, hv, h1, h0⟩ :=
      exists_low_pair_of_first_max (swap.comp Phi) hswapInj hdelta hfin
        B A hB (by simp [hA]) hfacSwap
    exact ⟨v, hv, by simpa [swap] using h0, by simpa [swap] using h1⟩
  · by_cases hB : B = 0
    · exact exists_low_pair_of_first_max Phi hinj hdelta hfin A B hA
        (by simp [hB]) hfactor
    · rcases le_total B.natDegree A.natDegree with hBA | hABdeg
      · exact exists_low_pair_of_first_max Phi hinj hdelta hfin A B hA
          hBA hfactor
      · obtain ⟨v, hv, h1, h0⟩ :=
          exists_low_pair_of_first_max (swap.comp Phi) hswapInj hdelta hfin
            B A hB hABdeg hfacSwap
        exact ⟨v, hv, by simpa [swap] using h0,
          by simpa [swap] using h1⟩
abbrev BenchmarkField := IRSProfile.Field
abbrev Index := IRSProfile.Index
noncomputable def actualAgreementLocator6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField) :
    BenchmarkField[X] :=
  ∏ i ∈ actualAgreementSet6401 u0 u1 P z,
    (Polynomial.X - Polynomial.C (IRSProfile.domain i))
noncomputable def actualErrorLocator6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField) :
    BenchmarkField[X] :=
  ∏ i ∈ actualErrorSupport6401 u0 u1 P z,
    (Polynomial.X - Polynomial.C (IRSProfile.domain i))
noncomputable def specializedLinearYA6401
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (z : BenchmarkField) : BenchmarkField[X] :=
  (Q.coeff 0).map (Polynomial.evalRingHom z)
noncomputable def specializedLinearYB6401
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (z : BenchmarkField) : BenchmarkField[X] :=
  (Q.coeff 1).map (Polynomial.evalRingHom z)
theorem actualAgreementLocator_natDegree6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField) :
    (actualAgreementLocator6401 u0 u1 P z).natDegree =
      (actualAgreementSet6401 u0 u1 P z).card := by
  simpa [actualAgreementLocator6401] using
    (Polynomial.natDegree_finsetProd_X_sub_C_eq_card
      (actualAgreementSet6401 u0 u1 P z) IRSProfile.domain)
theorem actualErrorLocator_natDegree6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField) :
    (actualErrorLocator6401 u0 u1 P z).natDegree =
      (actualErrorSupport6401 u0 u1 P z).card := by
  simpa [actualErrorLocator6401] using
    (Polynomial.natDegree_finsetProd_X_sub_C_eq_card
      (actualErrorSupport6401 u0 u1 P z) IRSProfile.domain)
theorem exists_actualAgreementLocator_residual6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hvan : ∀ i s t, s + t < multiplicity6401 →
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i))).coeff t).coeff s = 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    ∃ H : BenchmarkField[X],
      BCHKSSubstitutionVanish.triEval Q z (P z) =
        actualAgreementLocator6401 u0 u1 P z * H ∧
      H.natDegree ≤
        (actualErrorSupport6401 u0 u1 P z).card - 65537 := by
  classical
  let A := actualAgreementSet6401 u0 u1 P z
  let s := (actualErrorSupport6401 u0 u1 P z).card
  let r := s - 65537
  let yZ : Index → BenchmarkField[X] := fun i ↦
    Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i)
  have hsum := actualAgreement_add_error_card6401 u0 u1 P z
  have hroom : xCap6401 ≤ multiplicity6401 * A.card + (r + 1) := by
    change 65537 ≤ s at hhigh
    dsimp [A, r, s]
    norm_num [xCap6401, multiplicity6401,
      BCHKSTwoFrobeniusModuleAudit6401.n6401] at hsum ⊢
    omega
  have hgap : 0 < r + 1 := Nat.zero_lt_succ r
  obtain ⟨H, hfac, hH⟩ :=
    BCHKSResidual6400.exists_triEval_locator_residual
    Q z (P z) IRSProfile.domain A yZ multiplicity6401 k6401
      xCap6401 (r + 1) (by norm_num [xCap6401]) hgap
      (by
        intro i hi a b c hab
        have hv := hvan i a b hab
        have hc := Polynomial.ext_iff.mp hv c
        simpa only [Polynomial.coeff_zero] using hc)
      (by
        intro i hi
        have himatch := (Finset.mem_filter.mp hi).2
        dsimp [yZ]
        rw [himatch]
        simp
        ring)
      (by simpa [k6401, ownerDegreeCap6401] using hP)
      (fun j x hx ↦ (hcaps j x hx).2.1)
      hroom
  refine ⟨H, ?_, ?_⟩
  · simpa [actualAgreementLocator6401, A, multiplicity6401] using hfac
  · dsimp [r, s] at hH ⊢
    omega
theorem actualAgreementLocator_eval_ne_zero_of_mem_error6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (i : Index) (hi : i ∈ actualErrorSupport6401 u0 u1 P z) :
    Polynomial.eval (IRSProfile.domain i)
      (actualAgreementLocator6401 u0 u1 P z) ≠ 0 := by
  classical
  have hiNot : i ∉ actualAgreementSet6401 u0 u1 P z :=
    (Finset.mem_sdiff.mp hi).2
  rw [actualAgreementLocator6401, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  apply sub_ne_zero.mpr
  apply IRSProfile.domain.injective.ne
  intro hij
  apply hiNot
  simpa [hij] using hj
theorem actualAgreementLocator_eval_frobenius_fixed6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (i : Index) :
    sigma (Polynomial.eval (IRSProfile.domain i)
      (actualAgreementLocator6401 u0 u1 P z)) =
        Polynomial.eval (IRSProfile.domain i)
          (actualAgreementLocator6401 u0 u1 P z) := by
  classical
  rw [actualAgreementLocator6401, Polynomial.eval_prod]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    map_sub, hfixed i, hfixed j]
theorem eval_specializedComponent_commute6401
    {F : Type*} [Field F] (R : Polynomial (Polynomial F)) (z x : F) :
    Polynomial.eval x (R.map (Polynomial.evalRingHom z)) =
      Polynomial.eval z (R.eval (Polynomial.C x)) := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp [Polynomial.eval_monomial]
theorem exists_actual_linearY_error_factorization6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (hQ : Q ≠ 0)
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hvan : ∀ i s t, s + t < multiplicity6401 →
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i))).coeff t).coeff s = 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    ∃ H : BenchmarkField[X],
      H.natDegree ≤
          (actualErrorSupport6401 u0 u1 P z).card - 65537 ∧
      BCHKSSubstitutionVanish.triEval Q z (P z) =
          actualAgreementLocator6401 u0 u1 P z * H ∧
      ∀ i : Index,
        Polynomial.eval (IRSProfile.domain i)
            (specializedLinearYB6401 Q z) *
              (u0 i + z * u1 i -
                Polynomial.eval (IRSProfile.domain i) (P z)) =
          - Polynomial.eval (IRSProfile.domain i)
              (actualAgreementLocator6401 u0 u1 P z) *
            Polynomial.eval (IRSProfile.domain i) H := by
  classical
  obtain ⟨H, hfac, hH⟩ := exists_actualAgreementLocator_residual6401
    u0 u1 P z Q hP hhigh hvan hcaps
  have hY : Q.natDegree ≤ 1 :=
    BCHKSJ0LinearYLowSupport6401.natDegreeY_le_one_of_support6401 Q hQ
      (fun j x hx ↦ (hcaps j x hx).1)
  refine ⟨H, hH, hfac, ?_⟩
  intro i
  let yZ : BenchmarkField[X] :=
    Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i)
  have hshift :
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i)) yZ).coeff 0).coeff 0 = 0 := by
    have hv := hvan i 0 0 (by norm_num [multiplicity6401])
    simpa [yZ] using hv
  have hcoordPoly :=
    BCHKSJ0LinearYLowSupport6401.linearY_coordinate_identity6401 Q
    (IRSProfile.domain i) yZ hY hshift
  have hcoord := congrArg (Polynomial.eval z) hcoordPoly
  have hcoord' :
      Polynomial.eval (IRSProfile.domain i) (specializedLinearYA6401 Q z) +
        Polynomial.eval (IRSProfile.domain i) (specializedLinearYB6401 Q z) *
          (u0 i + z * u1 i) = 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at hcoord
    rw [← eval_specializedComponent_commute6401 (Q.coeff 0) z
          (IRSProfile.domain i),
      ← eval_specializedComponent_commute6401 (Q.coeff 1) z
          (IRSProfile.domain i)] at hcoord
    simpa only [specializedLinearYA6401, specializedLinearYB6401, yZ,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_zero] using hcoord
  have hlinear :=
    BCHKSJ0LinearYLowSupport6401.triEval_eq_linearY6401 Q z (P z) hY
  have hpoly :
      specializedLinearYA6401 Q z +
          specializedLinearYB6401 Q z * P z =
        actualAgreementLocator6401 u0 u1 P z * H := by
    calc
      specializedLinearYA6401 Q z +
          specializedLinearYB6401 Q z * P z =
          ProximityPrize.SubmissionLower.triEval Q z (P z) := hlinear.symm
      _ = BCHKSSubstitutionVanish.triEval Q z (P z) := by rfl
      _ = actualAgreementLocator6401 u0 u1 P z * H := hfac
  have heval := congrArg (Polynomial.eval (IRSProfile.domain i)) hpoly
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at heval
  linear_combination hcoord' - heval
theorem eval_map_at_frobeniusFixed6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (R : F[X]) (x : F) (hx : sigma x = x) :
    (R.map sigma).eval x = sigma (R.eval x) := by
  calc
    (R.map sigma).eval x = (R.map sigma).eval (sigma x) := by rw [hx]
    _ = sigma (R.eval x) :=
      Polynomial.eval_map_apply (p := R) sigma x
theorem residualFrobeniusPair_failureRelation6401
    {F ι : Type*} [Field F]
    (sigma : F →+* F) (alpha : ι → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (E : ι → F) (B H L : F[X])
    (hLfixed : ∀ i, sigma (L.eval (alpha i)) = L.eval (alpha i))
    (hfactor : ∀ i,
      B.eval (alpha i) * E i = -L.eval (alpha i) * H.eval (alpha i)) :
    TwoLaneFailureRelation sigma alpha E
      (H * B.map sigma) (H.map sigma * B) := by
  intro i
  have hBmap := eval_map_at_frobeniusFixed6401
    sigma B (alpha i) (hfixed i)
  have hHmap := eval_map_at_frobeniusFixed6401
    sigma H (alpha i) (hfixed i)
  have hsigma := congrArg sigma (hfactor i)
  simp only [map_mul, map_neg] at hsigma
  rw [hLfixed i] at hsigma
  simp only [Polynomial.eval_mul]
  rw [hBmap, hHmap]
  calc
    (H.eval (alpha i) * sigma (B.eval (alpha i))) * sigma (E i) =
        H.eval (alpha i) *
          (sigma (B.eval (alpha i)) * sigma (E i)) := by ring
    _ = H.eval (alpha i) *
          (-L.eval (alpha i) * sigma (H.eval (alpha i))) := by rw [hsigma]
    _ = sigma (H.eval (alpha i)) *
          (-L.eval (alpha i) * H.eval (alpha i)) := by ring
    _ = sigma (H.eval (alpha i)) *
          (B.eval (alpha i) * E i) := by rw [hfactor i]
    _ = (sigma (H.eval (alpha i)) * B.eval (alpha i)) * E i := by ring
theorem exists_actual_residualFrobeniusPair6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i : Index,
      sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (hQ : Q ≠ 0)
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hvan : ∀ i s t, s + t < multiplicity6401 →
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i))).coeff t).coeff s = 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    ∃ H : BenchmarkField[X],
      H.natDegree ≤
          (actualErrorSupport6401 u0 u1 P z).card - 65537 ∧
      TwoLaneFailureRelation sigma IRSProfile.domain
        (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i))
        (H * (specializedLinearYB6401 Q z).map sigma)
        (H.map sigma * specializedLinearYB6401 Q z) := by
  obtain ⟨H, hH, hresidual, hfactor⟩ :=
    exists_actual_linearY_error_factorization6401
      u0 u1 P z Q hQ hP hhigh hvan hcaps
  refine ⟨H, hH, ?_⟩
  exact residualFrobeniusPair_failureRelation6401
    sigma IRSProfile.domain hfixed
    (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i))
    (specializedLinearYB6401 Q z) H
    (actualAgreementLocator6401 u0 u1 P z)
    (actualAgreementLocator_eval_frobenius_fixed6401
      sigma hfixed u0 u1 P z) hfactor
noncomputable def residualPrimitiveCross6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (W0 W1 B H : F[X]) : F[X] :=
  W0 * B * H.map sigma - W1 * B.map sigma * H
theorem residualPrimitiveCross_eq_neg_failurePairCross6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (W0 W1 B H : F[X]) :
    residualPrimitiveCross6401 sigma W0 W1 B H =
      -BCHKSFrobeniusFailurePairRankOne6401.failurePairCross
        (H * B.map sigma) (H.map sigma * B) W0 W1 := by
  simp only [residualPrimitiveCross6401,
    BCHKSFrobeniusFailurePairRankOne6401.failurePairCross]
  ring
theorem failurePairCross_eval_eq_zero_at6401
    {F ι : Type*} [Field F]
    (sigma : F →+* F) (alpha : ι → F) (E : ι → F)
    (U0 U1 W0 W1 : F[X]) (i : ι) (hEi : E i ≠ 0)
    (hU : TwoLaneFailureRelation sigma alpha E U0 U1)
    (hW : TwoLaneFailureRelation sigma alpha E W0 W1) :
    (BCHKSFrobeniusFailurePairRankOne6401.failurePairCross
      U0 U1 W0 W1).eval (alpha i) = 0 := by
  have hu := hU i
  have hw := hW i
  have hsigmaE : sigma (E i) ≠ 0 := by
    simpa using sigma.injective.ne hEi
  simp only [BCHKSFrobeniusFailurePairRankOne6401.failurePairCross,
    Polynomial.eval_sub, Polynomial.eval_mul]
  apply sub_eq_zero.mpr
  have hmul :
      (U0.eval (alpha i) * W1.eval (alpha i)) * E i * sigma (E i) =
        (W0.eval (alpha i) * U1.eval (alpha i)) * E i * sigma (E i) := by
    calc
      (U0.eval (alpha i) * W1.eval (alpha i)) * E i * sigma (E i) =
          (U0.eval (alpha i) * sigma (E i)) *
            (W1.eval (alpha i) * E i) := by ring
      _ = (U1.eval (alpha i) * E i) *
            (W0.eval (alpha i) * sigma (E i)) := by rw [hu, hw]
      _ = (W0.eval (alpha i) * U1.eval (alpha i)) *
            E i * sigma (E i) := by ring
  exact mul_right_cancel₀ hEi (mul_right_cancel₀ hsigmaE hmul)
theorem actualErrorLocator_dvd_failurePairCross6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (U0 U1 W0 W1 : BenchmarkField[X])
    (hU : TwoLaneFailureRelation sigma IRSProfile.domain
      (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) U0 U1)
    (hW : TwoLaneFailureRelation sigma IRSProfile.domain
      (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) W0 W1) :
    actualErrorLocator6401 u0 u1 P z ∣
      BCHKSFrobeniusFailurePairRankOne6401.failurePairCross
        U0 U1 W0 W1 := by
  classical
  unfold actualErrorLocator6401
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Polynomial.pairwise_coprime_X_sub_C
      IRSProfile.domain.injective hij
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    apply failurePairCross_eval_eq_zero_at6401
      sigma IRSProfile.domain
      (fun j ↦ u0 j + z * u1 j - (P z).eval (IRSProfile.domain j))
      U0 U1 W0 W1 i
    · exact (ownerError_ne_zero_iff_mem_actualErrorSupport6401
        u0 u1 P z i).2 hi
    · exact hU
    · exact hW
theorem failurePairCross_natDegree_le_add6401
    {F : Type*} [Field F] (U0 U1 W0 W1 : F[X]) (d e : Nat)
    (hU0 : U0.natDegree ≤ d) (hU1 : U1.natDegree ≤ d)
    (hW0 : W0.natDegree ≤ e) (hW1 : W1.natDegree ≤ e) :
    (BCHKSFrobeniusFailurePairRankOne6401.failurePairCross
      U0 U1 W0 W1).natDegree ≤ d + e := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hU0 hW1))
    (Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add hW0 hU1).trans_eq (Nat.add_comm e d)))
theorem residualPrimitiveCross_natDegree_le6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (W0 W1 B H : F[X]) (b r h : Nat)
    (hW0 : W0.natDegree ≤ h) (hW1 : W1.natDegree ≤ h)
    (hB : B.natDegree ≤ b) (hH : H.natDegree ≤ r) :
    (residualPrimitiveCross6401 sigma W0 W1 B H).natDegree ≤
      b + r + h := by
  have hBmap : (B.map sigma).natDegree ≤ b :=
    Polynomial.natDegree_map_le.trans hB
  have hHmap : (H.map sigma).natDegree ≤ r :=
    Polynomial.natDegree_map_le.trans hH
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · have h : (W0 * B * H.map sigma).natDegree ≤
        (W0 * B).natDegree + (H.map sigma).natDegree :=
      Polynomial.natDegree_mul_le
    have hWB : (W0 * B).natDegree ≤ W0.natDegree + B.natDegree :=
      Polynomial.natDegree_mul_le
    omega
  · have h : (W1 * B.map sigma * H).natDegree ≤
        (W1 * B.map sigma).natDegree + H.natDegree :=
      Polynomial.natDegree_mul_le
    have hWB : (W1 * B.map sigma).natDegree ≤
        W1.natDegree + (B.map sigma).natDegree :=
      Polynomial.natDegree_mul_le
    omega
theorem actualErrorLocator_dvd_residualPrimitiveCross6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i : Index,
      sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (B H W0 W1 : BenchmarkField[X])
    (hfactor : ∀ i : Index,
      B.eval (IRSProfile.domain i) *
          (u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) =
        -(actualAgreementLocator6401 u0 u1 P z).eval
            (IRSProfile.domain i) * H.eval (IRSProfile.domain i))
    (hW : TwoLaneFailureRelation sigma IRSProfile.domain
      (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) W0 W1) :
    actualErrorLocator6401 u0 u1 P z ∣
      residualPrimitiveCross6401 sigma W0 W1 B H := by
  have hU : TwoLaneFailureRelation sigma IRSProfile.domain
      (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i))
      (H * B.map sigma) (H.map sigma * B) :=
    residualFrobeniusPair_failureRelation6401
      sigma IRSProfile.domain hfixed
      (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i))
      B H (actualAgreementLocator6401 u0 u1 P z)
      (actualAgreementLocator_eval_frobenius_fixed6401
        sigma hfixed u0 u1 P z) hfactor
  obtain ⟨T, hT⟩ := actualErrorLocator_dvd_failurePairCross6401
    sigma u0 u1 P z (H * B.map sigma) (H.map sigma * B) W0 W1 hU hW
  refine ⟨-T, ?_⟩
  rw [residualPrimitiveCross_eq_neg_failurePairCross6401, hT]
  ring
theorem actualErrorLocator_crossQuotient_or_zero6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (D : BenchmarkField[X]) (h : Nat)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hdvd : actualErrorLocator6401 u0 u1 P z ∣ D)
    (hdegree : D.natDegree ≤
      (actualErrorSupport6401 u0 u1 P z).card + h - 1) :
    D = 0 ∨
      ∃ Omega : BenchmarkField[X], Omega ≠ 0 ∧
        D = actualErrorLocator6401 u0 u1 P z * Omega ∧
        Omega.natDegree ≤ h - 1 := by
  classical
  by_cases hD : D = 0
  · exact Or.inl hD
  right
  obtain ⟨Omega, hOmegaFac⟩ := hdvd
  have hOmega : Omega ≠ 0 := by
    intro hz
    apply hD
    simpa [hz] using hOmegaFac
  have hCmonic : (actualErrorLocator6401 u0 u1 P z).Monic := by
    simpa [actualErrorLocator6401] using
      (Polynomial.monic_prod_X_sub_C IRSProfile.domain
        (actualErrorSupport6401 u0 u1 P z))
  have hdegreeEq :
      (actualErrorSupport6401 u0 u1 P z).card + Omega.natDegree =
        D.natDegree := by
    rw [hOmegaFac, Polynomial.natDegree_mul hCmonic.ne_zero hOmega,
      actualErrorLocator_natDegree6401]
  refine ⟨Omega, hOmega, hOmegaFac, ?_⟩
  omega
theorem residualPrimitiveCross_quotient_or_zero6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i : Index,
      sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (B H W0 W1 : BenchmarkField[X]) (h : Nat)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hB : B.natDegree ≤ 65536)
    (hH : H.natDegree ≤
      (actualErrorSupport6401 u0 u1 P z).card - 65537)
    (hW0 : W0.natDegree ≤ h) (hW1 : W1.natDegree ≤ h)
    (hfactor : ∀ i : Index,
      B.eval (IRSProfile.domain i) *
          (u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) =
        -(actualAgreementLocator6401 u0 u1 P z).eval
            (IRSProfile.domain i) * H.eval (IRSProfile.domain i))
    (hW : TwoLaneFailureRelation sigma IRSProfile.domain
      (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) W0 W1) :
    residualPrimitiveCross6401 sigma W0 W1 B H = 0 ∨
      ∃ Omega : BenchmarkField[X], Omega ≠ 0 ∧
        residualPrimitiveCross6401 sigma W0 W1 B H =
          actualErrorLocator6401 u0 u1 P z * Omega ∧
        Omega.natDegree ≤ h - 1 := by
  apply actualErrorLocator_crossQuotient_or_zero6401
    u0 u1 P z (residualPrimitiveCross6401 sigma W0 W1 B H) h hhigh
  · exact actualErrorLocator_dvd_residualPrimitiveCross6401
      sigma hfixed u0 u1 P z B H W0 W1 hfactor hW
  · have hdeg := residualPrimitiveCross_natDegree_le6401
      sigma W0 W1 B H 65536
        ((actualErrorSupport6401 u0 u1 P z).card - 65537) h
        hW0 hW1 hB hH
    omega
theorem residualPrimitiveCross_eq_zero_of_small_degree6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i : Index,
      sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (B H W0 W1 : BenchmarkField[X]) (h : Nat)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hsmall : B.natDegree + h ≤ 65536)
    (hH : H.natDegree ≤
      (actualErrorSupport6401 u0 u1 P z).card - 65537)
    (hW0 : W0.natDegree ≤ h) (hW1 : W1.natDegree ≤ h)
    (hfactor : ∀ i : Index,
      B.eval (IRSProfile.domain i) *
          (u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) =
        -(actualAgreementLocator6401 u0 u1 P z).eval
            (IRSProfile.domain i) * H.eval (IRSProfile.domain i))
    (hW : TwoLaneFailureRelation sigma IRSProfile.domain
      (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) W0 W1) :
    residualPrimitiveCross6401 sigma W0 W1 B H = 0 := by
  let D := residualPrimitiveCross6401 sigma W0 W1 B H
  have hdvd : actualErrorLocator6401 u0 u1 P z ∣ D :=
    actualErrorLocator_dvd_residualPrimitiveCross6401
      sigma hfixed u0 u1 P z B H W0 W1 hfactor hW
  by_contra hD
  have hdegreeLower := Polynomial.natDegree_le_of_dvd hdvd hD
  rw [actualErrorLocator_natDegree6401] at hdegreeLower
  have hdegreeUpper : D.natDegree <
      (actualErrorSupport6401 u0 u1 P z).card := by
    have hdeg := residualPrimitiveCross_natDegree_le6401
      sigma W0 W1 B H B.natDegree
        ((actualErrorSupport6401 u0 u1 P z).card - 65537) h
        hW0 hW1 le_rfl hH
    dsimp [D]
    omega
  omega
theorem exists_multiplier_of_primitive_cross6401
    {F : Type*} [Field F] (U0 U1 W0 W1 : F[X])
    (hU0 : U0 ≠ 0) (hcop : IsCoprime W0 W1)
    (hcross : U0 * W1 - W0 * U1 = 0) :
    ∃ G : F[X], G ≠ 0 ∧ U0 = G * W0 ∧ U1 = G * W1 := by
  have hW0 : W0 ≠ 0 := by
    intro hzero
    have hW1 : W1 ≠ 0 :=
      hcop.ne_zero_or_ne_zero.resolve_left (by simpa [hzero])
    have hmul : U0 * W1 = 0 := by simpa [hzero] using hcross
    exact hU0 ((mul_eq_zero.mp hmul).resolve_right hW1)
  have heq : U0 * W1 = W0 * U1 := sub_eq_zero.mp hcross
  have hW0dvd : W0 ∣ U0 := by
    apply hcop.dvd_of_dvd_mul_right
    exact ⟨U1, heq⟩
  obtain ⟨G, hG⟩ := hW0dvd
  have hGne : G ≠ 0 := by
    intro hzero
    apply hU0
    simp [hG, hzero]
  refine ⟨G, hGne, ?_, ?_⟩
  · rw [hG, mul_comm]
  · apply mul_left_cancel₀ hW0
    calc
      W0 * U1 = U0 * W1 := heq.symm
      _ = (G * W0) * W1 := by rw [hG, mul_comm W0 G]
      _ = W0 * (G * W1) := by ring
noncomputable def canonicalPolynomialGcd6401
    {F : Type*} [Field F] (A B : F[X]) : F[X] := by
  classical
  letI : GCDMonoid (Polynomial F) :=
    EuclideanDomain.gcdMonoid (Polynomial F)
  exact GCDMonoid.gcd A B
theorem commonDivisor_degree_le_frobeniusGcd_add_twoResidual6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (B H G : F[X]) (hB : B ≠ 0) (hH : H ≠ 0) (hG : G ≠ 0)
    (hleft : G ∣ H * B.map sigma)
    (hright : G ∣ H.map sigma * B) :
    G.natDegree ≤
      (canonicalPolynomialGcd6401 B (B.map sigma)).natDegree +
        2 * H.natDegree := by
  classical
  letI : GCDMonoid (Polynomial F) :=
    EuclideanDomain.gcdMonoid (Polynomial F)
  have hBmap : B.map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 hB
  have hHmap : H.map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 hH
  let U0 := H * B.map sigma
  let U1 := H.map sigma * B
  let D := GCDMonoid.gcd U0 U1
  let D1 := GCDMonoid.gcd U0 (H.map sigma)
  let D2 := GCDMonoid.gcd U0 B
  have hU0 : U0 ≠ 0 := mul_ne_zero hH hBmap
  have hU1 : U1 ≠ 0 := mul_ne_zero hHmap hB
  have hD : D ≠ 0 := gcd_ne_zero_of_left hU0
  have hD1 : D1 ≠ 0 := gcd_ne_zero_of_left hU0
  have hD2 : D2 ≠ 0 := gcd_ne_zero_of_left hU0
  have hGD : G ∣ D := GCDMonoid.dvd_gcd hleft hright
  have hGdeg : G.natDegree ≤ D.natDegree :=
    Polynomial.natDegree_le_of_dvd hGD hD
  have hDdvd : D ∣ D1 * D2 := by
    simpa [D, D1, D2, U0, U1] using
      (gcd_mul_dvd_mul_gcd U0 (H.map sigma) B)
  have hDdeg : D.natDegree ≤ D1.natDegree + D2.natDegree := by
    exact (Polynomial.natDegree_le_of_dvd hDdvd (mul_ne_zero hD1 hD2)).trans
      Polynomial.natDegree_mul_le
  have hD1deg : D1.natDegree ≤ H.natDegree := by
    have hdvd : D1 ∣ H.map sigma := by
      exact GCDMonoid.gcd_dvd_right U0 (H.map sigma)
    have hle := Polynomial.natDegree_le_of_dvd hdvd hHmap
    rw [Polynomial.natDegree_map_eq_of_injective sigma.injective] at hle
    exact hle
  let GBH := GCDMonoid.gcd B H
  let GBB := GCDMonoid.gcd B (B.map sigma)
  have hGBH : GBH ≠ 0 := gcd_ne_zero_of_left hB
  have hGBB : GBB ≠ 0 := gcd_ne_zero_of_left hB
  have hD2dvd : D2 ∣ GBH * GBB := by
    exact (gcd_comm' U0 B).dvd.trans (by
      simpa only [U0, GBH, GBB] using
        (gcd_mul_dvd_mul_gcd B H (B.map sigma)))
  have hD2deg : D2.natDegree ≤ GBH.natDegree + GBB.natDegree := by
    exact (Polynomial.natDegree_le_of_dvd hD2dvd
      (mul_ne_zero hGBH hGBB)).trans Polynomial.natDegree_mul_le
  have hGBHdeg : GBH.natDegree ≤ H.natDegree := by
    exact Polynomial.natDegree_le_of_dvd
      (GCDMonoid.gcd_dvd_right B H) hH
  have hcanonical : canonicalPolynomialGcd6401 B (B.map sigma) = GBB := by
    rfl
  rw [hcanonical]
  omega
theorem frobeniusRecurrenceGcd_lower_of_primitive_cross6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (B H W0 W1 : F[X]) (h : Nat)
    (hB : B ≠ 0) (hH : H ≠ 0)
    (hcop : IsCoprime W0 W1)
    (hW0 : W0.natDegree ≤ h) (hW1 : W1.natDegree ≤ h)
    (hcross : residualPrimitiveCross6401 sigma W0 W1 B H = 0) :
    B.natDegree ≤
      (canonicalPolynomialGcd6401 B (B.map sigma)).natDegree +
        h + H.natDegree := by
  classical
  letI : GCDMonoid (Polynomial F) :=
    EuclideanDomain.gcdMonoid (Polynomial F)
  have hBmap : B.map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 hB
  have hU0 : H * B.map sigma ≠ 0 := mul_ne_zero hH hBmap
  have hcross' :
      (H * B.map sigma) * W1 - W0 * (H.map sigma * B) = 0 := by
    have hneg := congrArg Neg.neg hcross
    simpa [residualPrimitiveCross_eq_neg_failurePairCross6401,
      BCHKSFrobeniusFailurePairRankOne6401.failurePairCross] using hneg
  obtain ⟨G, hG, hU0fac, hU1fac⟩ :=
    exists_multiplier_of_primitive_cross6401
      (H * B.map sigma) (H.map sigma * B) W0 W1 hU0 hcop hcross'
  have hW0ne : W0 ≠ 0 := by
    intro hz
    apply hU0
    simp [hU0fac, hz]
  have hdegreeFac :
      H.natDegree + B.natDegree = G.natDegree + W0.natDegree := by
    calc
      H.natDegree + B.natDegree =
          (H * B.map sigma).natDegree := by
        rw [Polynomial.natDegree_mul hH hBmap,
          Polynomial.natDegree_map_eq_of_injective sigma.injective]
      _ = (G * W0).natDegree := by rw [hU0fac]
      _ = G.natDegree + W0.natDegree :=
        Polynomial.natDegree_mul hG hW0ne
  have hGleft : G ∣ H * B.map sigma := ⟨W0, hU0fac⟩
  have hGright : G ∣ H.map sigma * B := ⟨W1, hU1fac⟩
  have hGupper := commonDivisor_degree_le_frobeniusGcd_add_twoResidual6401
    sigma B H G hB hH hG hGleft hGright
  omega
theorem actualResidual_ne_zero_of_B_ne_zero6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (B H : BenchmarkField[X])
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hBdegree : B.natDegree ≤ 65536) (hB : B ≠ 0)
    (hfactor : ∀ i : Index,
      B.eval (IRSProfile.domain i) *
          (u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) =
        -(actualAgreementLocator6401 u0 u1 P z).eval
            (IRSProfile.domain i) * H.eval (IRSProfile.domain i)) :
    H ≠ 0 := by
  classical
  intro hHzero
  have hdvd : actualErrorLocator6401 u0 u1 P z ∣ B := by
    unfold actualErrorLocator6401
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact Polynomial.pairwise_coprime_X_sub_C
        IRSProfile.domain.injective hij
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
      have hfi := hfactor i
      rw [hHzero] at hfi
      simp only [Polynomial.eval_zero, mul_zero, neg_zero] at hfi
      exact (mul_eq_zero.mp hfi).resolve_right
        ((ownerError_ne_zero_iff_mem_actualErrorSupport6401
          u0 u1 P z i).2 hi)
  have hdegree := Polynomial.natDegree_le_of_dvd hdvd hB
  rw [actualErrorLocator_natDegree6401] at hdegree
  omega
theorem residualPrimitive_gcdOrSmallQuotient6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i : Index,
      sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (B H W0 W1 : BenchmarkField[X]) (h : Nat)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hBdegree : B.natDegree ≤ 65536) (hB : B ≠ 0)
    (hHdegree : H.natDegree ≤
      (actualErrorSupport6401 u0 u1 P z).card - 65537)
    (hcop : IsCoprime W0 W1)
    (hW0 : W0.natDegree ≤ h) (hW1 : W1.natDegree ≤ h)
    (hfactor : ∀ i : Index,
      B.eval (IRSProfile.domain i) *
          (u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) =
        -(actualAgreementLocator6401 u0 u1 P z).eval
            (IRSProfile.domain i) * H.eval (IRSProfile.domain i))
    (hW : TwoLaneFailureRelation sigma IRSProfile.domain
      (fun i ↦ u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) W0 W1) :
    B.natDegree ≤
        (canonicalPolynomialGcd6401 B (B.map sigma)).natDegree + h +
          ((actualErrorSupport6401 u0 u1 P z).card - 65537) ∨
      ∃ Omega : BenchmarkField[X], Omega ≠ 0 ∧
        residualPrimitiveCross6401 sigma W0 W1 B H =
          actualErrorLocator6401 u0 u1 P z * Omega ∧
        Omega.natDegree ≤ h - 1 := by
  have hH := actualResidual_ne_zero_of_B_ne_zero6401
    u0 u1 P z B H hhigh hBdegree hB hfactor
  rcases residualPrimitiveCross_quotient_or_zero6401
      sigma hfixed u0 u1 P z B H W0 W1 h hhigh hBdegree hHdegree
      hW0 hW1 hfactor hW with hzero | hquotient
  · left
    exact (frobeniusRecurrenceGcd_lower_of_primitive_cross6401
      sigma B H W0 W1 h hB hH hcop hW0 hW1 hzero).trans (by omega)
  · exact Or.inr hquotient
noncomputable def polynomialCoefficientVector6401
    {F : Type*} [Field F] (N : Nat) (B : F[X]) : Fin N → F :=
  fun c ↦ B.coeff c.1
noncomputable def weightedSyndromeHankel6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (rows cols : Nat) (alpha y : ι → F) : Matrix (Fin rows) (Fin cols) F :=
  fun i c ↦ weightedSyndrome alpha y (i.1 + c.1)
theorem weightedSyndrome_coeff_convolution6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha y : ι → F) (B : F[X]) (N j : Nat)
    (hB : B.natDegree < N) :
    ∑ c : Fin N, weightedSyndrome alpha y (j + c.1) * B.coeff c.1 =
      weightedSyndrome alpha (fun i ↦ B.eval (alpha i) * y i) j := by
  classical
  have hEval : ∀ x : F,
      ∑ c : Fin N, B.coeff c.1 * x ^ c.1 = B.eval x := by
    intro x
    calc
      (∑ c : Fin N, B.coeff c.1 * x ^ c.1) =
          ∑ c ∈ Finset.range N, B.coeff c * x ^ c :=
        Fin.sum_univ_eq_sum_range (fun c ↦ B.coeff c * x ^ c) N
      _ = B.eval x := (Polynomial.eval_eq_sum_range' hB x).symm
  simp only [weightedSyndrome]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ c : Fin N,
        (syndromeWeight alpha i * alpha i ^ (j + c.1) * y i) *
          B.coeff c.1) =
        syndromeWeight alpha i * alpha i ^ j *
          (∑ c : Fin N, B.coeff c.1 * alpha i ^ c.1) * y i := by
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro c hc
            simp only [pow_add]
            ring
    _ = syndromeWeight alpha i * alpha i ^ j *
          (B.eval (alpha i) * y i) := by rw [hEval]; ring
theorem weightedSyndromeHankel_mulVec_coeff6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (rows cols : Nat) (alpha y : ι → F) (B : F[X])
    (hB : B.natDegree < cols)
    (hzero : ∀ j < rows,
      weightedSyndrome alpha (fun i ↦ B.eval (alpha i) * y i) j = 0) :
    (weightedSyndromeHankel6401 rows cols alpha y).mulVec
      (polynomialCoefficientVector6401 cols B) = 0 := by
  funext i
  simp only [weightedSyndromeHankel6401, Matrix.mulVec, dotProduct,
    polynomialCoefficientVector6401]
  rw [weightedSyndrome_coeff_convolution6401 alpha y B cols i.1 hB]
  exact hzero i.1 i.2
theorem frobenius_transport_product_syndrome_zero6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (sigma : F →+* F) (alpha : ι ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (B : F[X]) (y : ι → F) (j : Nat)
    (hzero : weightedSyndrome alpha
      (fun i ↦ B.eval (alpha i) * y i) j = 0) :
    weightedSyndrome alpha
      (fun i ↦ (B.map sigma).eval (alpha i) * sigma (y i)) j = 0 := by
  have heval : ∀ i,
      (B.map sigma).eval (alpha i) = sigma (B.eval (alpha i)) := by
    intro i
    calc
      (B.map sigma).eval (alpha i) =
          (B.map sigma).eval (sigma (alpha i)) := by rw [hfixed i]
      _ = sigma (B.eval (alpha i)) :=
        Polynomial.eval_map_apply (p := B) sigma (alpha i)
  calc
    weightedSyndrome alpha
        (fun i ↦ (B.map sigma).eval (alpha i) * sigma (y i)) j =
        weightedSyndrome alpha
          (fun i ↦ sigma (B.eval (alpha i) * y i)) j := by
            congr 1
            funext i
            rw [heval i, map_mul]
    _ = sigma (weightedSyndrome alpha
          (fun i ↦ B.eval (alpha i) * y i) j) :=
      (BCHKSFrobeniusGenericMinor6401.sigma_weightedSyndrome_fixed6401
        sigma alpha hfixed _ j).symm
    _ = 0 := by rw [hzero, map_zero]
theorem weightedSyndrome_X_pow_mul6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (alpha : ι → F) (y : ι → F) (B : F[X]) (g j : Nat) :
    weightedSyndrome alpha
        (fun i ↦ (((Polynomial.X : F[X]) ^ g * B).eval (alpha i)) * y i) j =
      weightedSyndrome alpha (fun i ↦ B.eval (alpha i) * y i) (j + g) := by
  classical
  simp only [weightedSyndrome, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring
theorem shiftedPolynomial_hankelKernel6401
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (rows cols moments : Nat) (alpha y : ι → F) (B : F[X]) (g : Nat)
    (hdegree : (((Polynomial.X : F[X]) ^ g) * B).natDegree < cols)
    (hwindow : ∀ j < rows, j + g < moments)
    (hzero : ∀ j < moments,
      weightedSyndrome alpha (fun i ↦ B.eval (alpha i) * y i) j = 0) :
    (weightedSyndromeHankel6401 rows cols alpha y).mulVec
        (polynomialCoefficientVector6401 cols
          (((Polynomial.X : F[X]) ^ g) * B)) = 0 := by
  apply weightedSyndromeHankel_mulVec_coeff6401
    rows cols alpha y (((Polynomial.X : F[X]) ^ g) * B) hdegree
  intro j hj
  rw [weightedSyndrome_X_pow_mul6401]
  exact hzero (j + g) (hwindow j hj)
theorem linearY_B_received_syndromes_zero6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (B H : BenchmarkField[X])
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hB : B.natDegree ≤ 65536)
    (hsupport : 65537 ≤
      (actualErrorSupport6401 u0 u1 P z).card)
    (hH : H.natDegree ≤
      (actualErrorSupport6401 u0 u1 P z).card - 65537)
    (hfactor : ∀ i : Index,
      B.eval (IRSProfile.domain i) *
          (u0 i + z * u1 i - (P z).eval (IRSProfile.domain i)) =
        -(actualAgreementLocator6401 u0 u1 P z).eval
            (IRSProfile.domain i) * H.eval (IRSProfile.domain i)) :
    ∀ j < 65536,
      weightedSyndrome IRSProfile.domain
        (fun i ↦ B.eval (IRSProfile.domain i) * (u0 i + z * u1 i)) j = 0 := by
  classical
  intro j hj
  let R := B * P z - actualAgreementLocator6401 u0 u1 P z * H
  have hRdegree : R.natDegree ≤ 196607 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans (by
        norm_num [ownerDegreeCap6401] at hP ⊢
        omega)
    · have hsum := actualAgreement_add_error_card6401 u0 u1 P z
      exact Polynomial.natDegree_mul_le.trans (by
        rw [actualAgreementLocator_natDegree6401]
        norm_num [BCHKSTwoFrobeniusModuleAudit6401.n6401] at hsum ⊢
        omega)
  have hword : ∀ i : Index,
      B.eval (IRSProfile.domain i) * (u0 i + z * u1 i) =
        R.eval (IRSProfile.domain i) := by
    intro i
    dsimp [R]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    have hi := hfactor i
    linear_combination hi
  rw [show (fun i ↦ B.eval (IRSProfile.domain i) *
      (u0 i + z * u1 i)) = (fun i ↦ R.eval (IRSProfile.domain i)) by
        funext i
        exact hword i]
  apply weightedSyndrome_codeword_eq_zero IRSProfile.domain R j
  norm_num [IRSProfile.Index] at hj ⊢
  omega
theorem specializedLinearYB_ordinaryKernel6401
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (hQ : Q ≠ 0)
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hvan : ∀ i s t, s + t < multiplicity6401 →
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i))).coeff t).coeff s = 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
      IRSProfile.domain (fun i ↦ u0 i + z * u1 i)).mulVec
        (polynomialCoefficientVector6401 keyErrors6401
          (specializedLinearYB6401 Q z)) = 0 := by
  obtain ⟨H, hH, hresidual, hfactor⟩ :=
    exists_actual_linearY_error_factorization6401
      u0 u1 P z Q hQ hP hhigh hvan hcaps
  have hBX :=
    (BCHKSJ0LinearYLowSupport6401.component_X_caps6401 Q hcaps).2
  have hB : (specializedLinearYB6401 Q z).natDegree ≤ 65536 :=
    Polynomial.natDegree_map_le.trans hBX
  apply weightedSyndromeHankel_mulVec_coeff6401
  · norm_num [keyErrors6401, BCHKSTwoFrobeniusModuleAudit6401.n6401,
      ownerDegreeCap6401, bchksErrors6401] at hB ⊢
    omega
  · intro j hj
    exact linearY_B_received_syndromes_zero6401 u0 u1 P z
      (specializedLinearYB6401 Q z) H hP hB hhigh hH hfactor j
        (by
          norm_num [keyFirstLaneRows6401, keyErrors6401,
            keyRedundancy6401,
            BCHKSTwoFrobeniusModuleAudit6401.n6401,
            ownerDegreeCap6401, bchksErrors6401] at hj ⊢
          omega)
theorem specializedLinearYB_frobeniusKernel6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i : Index,
      sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (hQ : Q ≠ 0)
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hvan : ∀ i s t, s + t < multiplicity6401 →
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i))).coeff t).coeff s = 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
      IRSProfile.domain (fun i ↦ sigma (u0 i + z * u1 i))).mulVec
        (polynomialCoefficientVector6401 keyErrors6401
          ((specializedLinearYB6401 Q z).map sigma)) = 0 := by
  obtain ⟨H, hH, hresidual, hfactor⟩ :=
    exists_actual_linearY_error_factorization6401
      u0 u1 P z Q hQ hP hhigh hvan hcaps
  have hBX :=
    (BCHKSJ0LinearYLowSupport6401.component_X_caps6401 Q hcaps).2
  have hB : (specializedLinearYB6401 Q z).natDegree ≤ 65536 :=
    Polynomial.natDegree_map_le.trans hBX
  have hBmap : ((specializedLinearYB6401 Q z).map sigma).natDegree <
      keyErrors6401 := by
    apply lt_of_le_of_lt (Polynomial.natDegree_map_le.trans hB)
    norm_num [keyErrors6401, BCHKSTwoFrobeniusModuleAudit6401.n6401,
      ownerDegreeCap6401, bchksErrors6401]
  apply weightedSyndromeHankel_mulVec_coeff6401
    keyFirstLaneRows6401 keyErrors6401 IRSProfile.domain
      (fun i ↦ sigma (u0 i + z * u1 i))
      ((specializedLinearYB6401 Q z).map sigma) hBmap
  intro j hj
  apply frobenius_transport_product_syndrome_zero6401
    sigma IRSProfile.domain hfixed (specializedLinearYB6401 Q z)
      (fun i ↦ u0 i + z * u1 i) j
  exact linearY_B_received_syndromes_zero6401 u0 u1 P z
    (specializedLinearYB6401 Q z) H hP hB hhigh hH hfactor j (by
      norm_num [keyFirstLaneRows6401, keyErrors6401,
        keyRedundancy6401,
        BCHKSTwoFrobeniusModuleAudit6401.n6401,
        ownerDegreeCap6401, bchksErrors6401] at hj ⊢
      omega)
theorem specializedLinearYB_twoLaneKernels6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i : Index,
      sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (hQ : Q ≠ 0)
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hvan : ∀ i s t, s + t < multiplicity6401 →
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i))).coeff t).coeff s = 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
        IRSProfile.domain (fun i ↦ u0 i + z * u1 i)).mulVec
          (polynomialCoefficientVector6401 keyErrors6401
            (specializedLinearYB6401 Q z)) = 0 ∧
      (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
        IRSProfile.domain (fun i ↦ sigma (u0 i + z * u1 i))).mulVec
          (polynomialCoefficientVector6401 keyErrors6401
            ((specializedLinearYB6401 Q z).map sigma)) = 0 := by
  constructor
  · exact specializedLinearYB_ordinaryKernel6401
      u0 u1 P z Q hQ hP hhigh hvan hcaps
  · exact specializedLinearYB_frobeniusKernel6401
      sigma hfixed u0 u1 P z Q hQ hP hhigh hvan hcaps
theorem specializedLinearYB_shiftedLaneKernels6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (hfixed : ∀ i : Index,
      sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : Index → BenchmarkField)
    (P : BenchmarkField → BenchmarkField[X]) (z : BenchmarkField)
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (hQ : Q ≠ 0)
    (hP : (P z).natDegree ≤ ownerDegreeCap6401)
    (hhigh : 65537 ≤ (actualErrorSupport6401 u0 u1 P z).card)
    (hvan : ∀ i s t, s + t < multiplicity6401 →
      ((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (u0 i) + Polynomial.X * Polynomial.C (u1 i))).coeff t).coeff s = 0)
    (hcaps : ∀ j x, (Q.coeff j).coeff x ≠ 0 →
      j < 2 ∧ x + 131071 * j < 196608 ∧
        ((Q.coeff j).coeff x).natDegree + j < 65538) :
    ∀ g : Fin 11254,
      (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
        IRSProfile.domain (fun i ↦ u0 i + z * u1 i)).mulVec
          (polynomialCoefficientVector6401 keyErrors6401
            ((Polynomial.X : BenchmarkField[X]) ^ g.1 *
              specializedLinearYB6401 Q z)) = 0 ∧
      (weightedSyndromeHankel6401 keyFirstLaneRows6401 keyErrors6401
        IRSProfile.domain (fun i ↦ sigma (u0 i + z * u1 i))).mulVec
          (polynomialCoefficientVector6401 keyErrors6401
            ((Polynomial.X : BenchmarkField[X]) ^ g.1 *
              (specializedLinearYB6401 Q z).map sigma)) = 0 := by
  obtain ⟨H, hH, hresidual, hfactor⟩ :=
    exists_actual_linearY_error_factorization6401
      u0 u1 P z Q hQ hP hhigh hvan hcaps
  have hBX :=
    (BCHKSJ0LinearYLowSupport6401.component_X_caps6401 Q hcaps).2
  have hB : (specializedLinearYB6401 Q z).natDegree ≤ 65536 :=
    Polynomial.natDegree_map_le.trans hBX
  have hordinaryZero : ∀ j < 65536,
      weightedSyndrome IRSProfile.domain
        (fun i ↦ (specializedLinearYB6401 Q z).eval
          (IRSProfile.domain i) * (u0 i + z * u1 i)) j = 0 :=
    linearY_B_received_syndromes_zero6401 u0 u1 P z
      (specializedLinearYB6401 Q z) H hP hB hhigh hH hfactor
  have hfrobeniusZero : ∀ j < 65536,
      weightedSyndrome IRSProfile.domain
        (fun i ↦ ((specializedLinearYB6401 Q z).map sigma).eval
          (IRSProfile.domain i) * sigma (u0 i + z * u1 i)) j = 0 := by
    intro j hj
    exact frobenius_transport_product_syndrome_zero6401
      sigma IRSProfile.domain hfixed (specializedLinearYB6401 Q z)
        (fun i ↦ u0 i + z * u1 i) j (hordinaryZero j hj)
  intro g
  have hordinaryDegree :
      ((Polynomial.X : BenchmarkField[X]) ^ g.1 *
        specializedLinearYB6401 Q z).natDegree < keyErrors6401 := by
    apply lt_of_le_of_lt Polynomial.natDegree_mul_le
    have hg := g.2
    norm_num [keyErrors6401, keyRedundancy6401,
      BCHKSTwoFrobeniusModuleAudit6401.n6401,
      ownerDegreeCap6401, bchksErrors6401] at hg hB ⊢
    omega
  have hfrobeniusDegree :
      ((Polynomial.X : BenchmarkField[X]) ^ g.1 *
        (specializedLinearYB6401 Q z).map sigma).natDegree <
          keyErrors6401 := by
    apply lt_of_le_of_lt Polynomial.natDegree_mul_le
    have hBmap : ((specializedLinearYB6401 Q z).map sigma).natDegree ≤
        65536 := Polynomial.natDegree_map_le.trans hB
    have hg := g.2
    norm_num [keyErrors6401, keyRedundancy6401,
      BCHKSTwoFrobeniusModuleAudit6401.n6401,
      ownerDegreeCap6401, bchksErrors6401] at hg hBmap ⊢
    omega
  have hwindow : ∀ j < keyFirstLaneRows6401, j + g.1 < 65536 := by
    intro j hj
    have hg := g.2
    norm_num [keyFirstLaneRows6401, keyErrors6401,
      keyRedundancy6401,
      BCHKSTwoFrobeniusModuleAudit6401.n6401,
      ownerDegreeCap6401, bchksErrors6401] at hg hj ⊢
    omega
  constructor
  · exact shiftedPolynomial_hankelKernel6401
      keyFirstLaneRows6401 keyErrors6401 65536 IRSProfile.domain
      (fun i ↦ u0 i + z * u1 i) (specializedLinearYB6401 Q z) g.1
      hordinaryDegree hwindow hordinaryZero
  · exact shiftedPolynomial_hankelKernel6401
      keyFirstLaneRows6401 keyErrors6401 65536 IRSProfile.domain
      (fun i ↦ sigma (u0 i + z * u1 i))
      ((specializedLinearYB6401 Q z).map sigma) g.1
      hfrobeniusDegree hwindow hfrobeniusZero
theorem specializedLinearYB_shiftPolynomials_independent6401
    (sigma : BenchmarkField →+* BenchmarkField)
    (Q : Polynomial (Polynomial (Polynomial BenchmarkField)))
    (z : BenchmarkField) (hB : specializedLinearYB6401 Q z ≠ 0) :
    LinearIndependent BenchmarkField (fun g : Fin 11254 ↦
        (Polynomial.X : BenchmarkField[X]) ^ g.1 *
          specializedLinearYB6401 Q z) ∧
      LinearIndependent BenchmarkField (fun g : Fin 11254 ↦
        (Polynomial.X : BenchmarkField[X]) ^ g.1 *
          (specializedLinearYB6401 Q z).map sigma) := by
  constructor
  · exact BCHKSLinearYLowSupport6401.linearIndependent_X_pow_mul
      (specializedLinearYB6401 Q z) hB 11254
  · exact BCHKSLinearYLowSupport6401.linearIndependent_X_pow_mul
      ((specializedLinearYB6401 Q z).map sigma)
      ((Polynomial.map_ne_zero_iff sigma.injective).2 hB) 11254
end BCHKSFrobeniusLinearYFailureDivisibility6401
end ProximityPrize.SubmissionLower
