import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.IP
import ProximityPrize.SubmissionLower.C
import ProximityPrize.SubmissionLower.C2

/-!
Contact-order bridge for the regular-colon lower-bound candidate.

The order here is a MINIMUM weight; RCN081.weightedTotalDegree
is a MAXIMUM weight and cannot be substituted for it. Natural-number
`order` assigns zero polynomial the dummy value 0, and every theorem using
that value as an exact order explicitly requires nonzeroness. `AtLeast`
handles zero correctly at every level and is the preferred interface.

The core below proves the lowest-component product formula, exact
multiplication/colon laws, the contact-coordinate derivative identity,
and the local root-divisibility bridge. All are proof bodies, not extra
assumptions. The final comments describe the interfaces and their scope.
-/
namespace ProximityPrize.SubmissionLower.ContactOrderBridge

open scoped BigOperators Pointwise
open RCN081
open RCN119
open RCN100
open RCN122

noncomputable section

section MinimumWeight
variable {K σ : Type*} [Field K]

def AtLeast (w : σ → ℕ) (n : ℕ) (P : MvPolynomial σ K) : Prop :=
  ∀ d ∈ P.support, n ≤ Finsupp.weight w d

theorem atLeast_zero (w : σ → ℕ) (P : MvPolynomial σ K) : AtLeast w 0 P := by
  intro d hd
  exact Nat.zero_le _

theorem zero_atLeast (w : σ → ℕ) (n : ℕ) : AtLeast w n (0 : MvPolynomial σ K) := by
  intro d hd
  simp at hd

theorem atLeast_mono (w : σ → ℕ) {m n : ℕ} {P : MvPolynomial σ K}
    (hmn : m ≤ n) (hP : AtLeast w n P) : AtLeast w m P := by
  intro d hd
  exact hmn.trans (hP d hd)

theorem atLeast_add (w : σ → ℕ) {n : ℕ} {P Q : MvPolynomial σ K}
    (hP : AtLeast w n P) (hQ : AtLeast w n Q) : AtLeast w n (P + Q) := by
  change P ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hP
  change Q ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hQ
  exact (MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d}).add_mem hP hQ

theorem atLeast_sub (w : σ → ℕ) {n : ℕ} {P Q : MvPolynomial σ K}
    (hP : AtLeast w n P) (hQ : AtLeast w n Q) : AtLeast w n (P - Q) := by
  change P ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hP
  change Q ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hQ
  exact (MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d}).sub_mem hP hQ

theorem atLeast_mul (w : σ → ℕ) {m n : ℕ} {P Q : MvPolynomial σ K}
    (hP : AtLeast w m P) (hQ : AtLeast w n Q) : AtLeast w (m + n) (P * Q) := by
  have hset : {d : σ →₀ ℕ | m ≤ Finsupp.weight w d} +
      {d : σ →₀ ℕ | n ≤ Finsupp.weight w d} ⊆
      {d : σ →₀ ℕ | m + n ≤ Finsupp.weight w d} := by
    rintro _ ⟨d, hd, e, he, rfl⟩
    simpa only [Set.mem_setOf_eq, map_add] using Nat.add_le_add hd he
  change P ∈ MvPolynomial.restrictSupport K {d | m ≤ Finsupp.weight w d} at hP
  change Q ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hQ
  apply MvPolynomial.restrictSupport_mono (R := K) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hP hQ

theorem atLeast_X (w : σ → ℕ) (i : σ) :
    AtLeast w (w i) (MvPolynomial.X i : MvPolynomial σ K) := by
  classical
  intro d hd
  have he : d = Finsupp.single i 1 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp only [Finsupp.weight_single, one_nsmul, le_refl]

theorem atLeast_pderiv (w : σ → ℕ) (i : σ) {n : ℕ} {P : MvPolynomial σ K}
    (hP : AtLeast w n P) : AtLeast w (n - w i) (MvPolynomial.pderiv i P) := by
  classical
  intro d hd
  have hbefore : d + Finsupp.single i 1 ∈ P.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hne := MvPolynomial.mem_support_iff.mp hd
    apply hne
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have h := hP _ hbefore
  simp only [map_add, Finsupp.weight_single, one_nsmul] at h
  omega

theorem component_ne_zero_iff (w : σ → ℕ) (n : ℕ) (P : MvPolynomial σ K) :
    MvPolynomial.weightedHomogeneousComponent w n P ≠ 0 ↔
      ∃ d ∈ P.support, Finsupp.weight w d = n := by
  classical
  constructor
  · intro h
    obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero h
    rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with hw
    · exact ⟨d, MvPolynomial.mem_support_iff.mpr hd, hw⟩
    · exact False.elim (hd rfl)
  · rintro ⟨d, hd, hw⟩ hz
    have hc := congrArg (MvPolynomial.coeff d) hz
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hw,
      MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc

/-- The key cancellation argument: higher-weight terms cannot contribute
    to weight m+n. Zero weights on coefficient variables are allowed. -/
theorem initial_mul (w : σ → ℕ) {m n : ℕ} {P Q : MvPolynomial σ K}
    (hP : AtLeast w m P) (hQ : AtLeast w n Q) :
    MvPolynomial.weightedHomogeneousComponent w (m + n) (P * Q) =
      MvPolynomial.weightedHomogeneousComponent w m P *
        MvPolynomial.weightedHomogeneousComponent w n Q := by
  classical
  letI : DecidableEq σ := Classical.decEq σ
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq (σ →₀ ℕ) := Classical.decEq (σ →₀ ℕ)
  ext d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  split_ifs with hd
  · apply Finset.sum_congr rfl
    rintro ⟨e, f⟩ hef
    simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases he : MvPolynomial.coeff e P = 0
    · simp [he]
    by_cases hf : MvPolynomial.coeff f Q = 0
    · simp [hf]
    have hew := hP e (MvPolynomial.mem_support_iff.mpr he)
    have hfw := hQ f (MvPolynomial.mem_support_iff.mpr hf)
    have hef' : e + f = d := Finset.mem_antidiagonal.mp hef
    have hsum : Finsupp.weight w e + Finsupp.weight w f = m + n := by
      rw [← map_add, hef', hd]
    have hem : Finsupp.weight w e = m := by omega
    have hfn : Finsupp.weight w f = n := by omega
    simp [hem, hfn]
  · symm
    apply Finset.sum_eq_zero
    rintro ⟨e, f⟩ hef
    simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases he : Finsupp.weight w e = m
    · by_cases hf : Finsupp.weight w f = n
      · exfalso
        apply hd
        have hef' : e + f = d := Finset.mem_antidiagonal.mp hef
        rw [← hef', map_add, he, hf]
      · simp [he, hf]
    · simp [he]

def ExactOrder (w : σ → ℕ) (n : ℕ) (P : MvPolynomial σ K) : Prop :=
  AtLeast w n P ∧ MvPolynomial.weightedHomogeneousComponent w n P ≠ 0

theorem exists_exactOrder (w : σ → ℕ) (P : MvPolynomial σ K) (hP : P ≠ 0) :
    ∃ n, ExactOrder w n P := by
  classical
  have hex : ∃ n, ∃ d ∈ P.support, Finsupp.weight w d = n := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hP
    exact ⟨_, d, hd, rfl⟩
  refine ⟨Nat.find hex, ?_, (component_ne_zero_iff w _ P).mpr (Nat.find_spec hex)⟩
  intro d hd
  exact Nat.find_min' hex ⟨d, hd, rfl⟩

theorem exactOrder_unique (w : σ → ℕ) {m n : ℕ} {P : MvPolynomial σ K}
    (hm : ExactOrder w m P) (hn : ExactOrder w n P) : m = n := by
  obtain ⟨d, hd, hdm⟩ := (component_ne_zero_iff w m P).mp hm.2
  obtain ⟨e, he, hen⟩ := (component_ne_zero_iff w n P).mp hn.2
  have hnm := hn.1 d hd
  have hmn := hm.1 e he
  omega

def order (w : σ → ℕ) (P : MvPolynomial σ K) : ℕ := by
  classical
  exact if hP : P = 0 then 0 else Classical.choose (exists_exactOrder w P hP)

theorem exactOrder_order (w : σ → ℕ) (P : MvPolynomial σ K) (hP : P ≠ 0) :
    ExactOrder w (order w P) P := by
  simp only [order, dif_neg hP]
  exact Classical.choose_spec (exists_exactOrder w P hP)

theorem atLeast_iff_le_order (w : σ → ℕ) (n : ℕ) (P : MvPolynomial σ K)
    (hP : P ≠ 0) : AtLeast w n P ↔ n ≤ order w P := by
  have ho := exactOrder_order w P hP
  constructor
  · intro hn
    obtain ⟨d, hd, hw⟩ := (component_ne_zero_iff w _ P).mp ho.2
    simpa only [hw] using hn d hd
  · intro hn
    exact atLeast_mono w hn ho.1

theorem exactOrder_mul (w : σ → ℕ) {m n : ℕ} {P Q : MvPolynomial σ K}
    (hP : ExactOrder w m P) (hQ : ExactOrder w n Q) :
    ExactOrder w (m + n) (P * Q) := by
  refine ⟨atLeast_mul w hP.1 hQ.1, ?_⟩
  rw [initial_mul w hP.1 hQ.1]
  exact mul_ne_zero hP.2 hQ.2

theorem order_mul (w : σ → ℕ) (P Q : MvPolynomial σ K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    order w (P * Q) = order w P + order w Q := by
  exact exactOrder_unique w (exactOrder_order w (P * Q) (mul_ne_zero hP hQ))
    (exactOrder_mul w (exactOrder_order w P hP) (exactOrder_order w Q hQ))

theorem colon_iff (w : σ → ℕ) (m : ℕ) (F P : MvPolynomial σ K) (hF : F ≠ 0) :
    AtLeast w m (F * P) ↔ AtLeast w (m - order w F) P := by
  by_cases hP : P = 0
  · subst P
    simp only [mul_zero]
    exact iff_of_true (zero_atLeast w m) (zero_atLeast w _)
  · rw [atLeast_iff_le_order w m (F * P) (mul_ne_zero hF hP),
      atLeast_iff_le_order w _ P hP, order_mul w F P hF hP]
    omega
end MinimumWeight

section LocalCoordinates
variable (K : Type*) [Field K]
abbrev Poly4 := MvPolynomial (Fin 4) K

def localWeights : Fin 4 → ℕ := ![1, 2, 0, 0]

def localVariables (x u₀ u₁ : K) : Fin 4 → Poly4 K :=
  ![MvPolynomial.X 0 + MvPolynomial.C x,
    MvPolynomial.C u₀ + MvPolynomial.X 3 * MvPolynomial.C u₁ +
      MvPolynomial.X 2 * MvPolynomial.X 0 + MvPolynomial.X 1,
    MvPolynomial.X 2, MvPolynomial.X 3]

def inverseVariables (x u₀ u₁ : K) : Fin 4 → Poly4 K :=
  ![MvPolynomial.X 0 - MvPolynomial.C x,
    MvPolynomial.X 1 - (MvPolynomial.C u₀ + MvPolynomial.X 3 * MvPolynomial.C u₁) -
      MvPolynomial.X 2 * (MvPolynomial.X 0 - MvPolynomial.C x),
    MvPolynomial.X 2, MvPolynomial.X 3]

def localize (x u₀ u₁ : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval (localVariables K x u₀ u₁)

def unlocalize (x u₀ u₁ : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval (inverseVariables K x u₀ u₁)

theorem unlocalize_comp_localize (x u₀ u₁ : K) :
    (unlocalize K x u₀ u₁).comp (localize K x u₀ u₁) = AlgHom.id K (Poly4 K) := by
  ext i
  fin_cases i <;> simp [localize, unlocalize, localVariables, inverseVariables] <;> ring

theorem localize_injective (x u₀ u₁ : K) : Function.Injective (localize K x u₀ u₁) := by
  intro P Q h
  have hinv (P : Poly4 K) : unlocalize K x u₀ u₁ (localize K x u₀ u₁ P) = P :=
    DFunLike.congr_fun (unlocalize_comp_localize K x u₀ u₁) P
  simpa only [hinv] using congrArg (unlocalize K x u₀ u₁) h

theorem localize_ne_zero (x u₀ u₁ : K) (P : Poly4 K) (hP : P ≠ 0) :
    localize K x u₀ u₁ P ≠ 0 := by
  intro h
  apply hP
  apply localize_injective K x u₀ u₁
  simpa only [map_zero] using h

def ContactAtLeast (x u₀ u₁ : K) (m : ℕ) (P : Poly4 K) : Prop :=
  AtLeast localWeights m (localize K x u₀ u₁ P)

def contactOrder (x u₀ u₁ : K) (P : Poly4 K) : ℕ :=
  order localWeights (localize K x u₀ u₁ P)

theorem contactOrder_mul (x u₀ u₁ : K) (F P : Poly4 K) (hF : F ≠ 0) (hP : P ≠ 0) :
    contactOrder K x u₀ u₁ (F * P) =
      contactOrder K x u₀ u₁ F + contactOrder K x u₀ u₁ P := by
  unfold contactOrder
  rw [map_mul]
  exact order_mul localWeights _ _ (localize_ne_zero K x u₀ u₁ F hF)
    (localize_ne_zero K x u₀ u₁ P hP)

theorem contact_colon_iff (x u₀ u₁ : K) (m : ℕ) (F P : Poly4 K) (hF : F ≠ 0) :
    ContactAtLeast K x u₀ u₁ m (F * P) ↔
      ContactAtLeast K x u₀ u₁ (m - contactOrder K x u₀ u₁ F) P := by
  unfold ContactAtLeast contactOrder
  rw [map_mul]
  exact colon_iff localWeights m _ _ (localize_ne_zero K x u₀ u₁ F hF)

/-- Original R differentiation becomes partial_R - t*partial_v. -/
theorem localize_pderiv_R (x u₀ u₁ : K) (P : Poly4 K) :
    localize K x u₀ u₁ (MvPolynomial.pderiv (2 : Fin 4) P) =
      MvPolynomial.pderiv (2 : Fin 4) (localize K x u₀ u₁ P) -
        MvPolynomial.X 0 * MvPolynomial.pderiv (1 : Fin 4) (localize K x u₀ u₁ P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [localize]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      ring
  | mul_X P i hP =>
      simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hP]
      fin_cases i <;> simp [localize, localVariables, MvPolynomial.pderiv_mul] <;> ring

theorem contactAtLeast_pderiv_R (x u₀ u₁ : K) (m : ℕ) (P : Poly4 K)
    (hP : ContactAtLeast K x u₀ u₁ m P) :
    ContactAtLeast K x u₀ u₁ (m - 1) (MvPolynomial.pderiv (2 : Fin 4) P) := by
  change AtLeast localWeights (m - 1) (localize K x u₀ u₁ (MvPolynomial.pderiv 2 P))
  rw [localize_pderiv_R]
  have hR := atLeast_pderiv localWeights (2 : Fin 4) hP
  have hv := atLeast_pderiv localWeights (1 : Fin 4) hP
  have ht := atLeast_X (K := K) localWeights (0 : Fin 4)
  have htv := atLeast_mul localWeights ht hv
  apply atLeast_sub localWeights
  · apply atLeast_mono localWeights (show m - 1 ≤ m - localWeights 2 by
      change m - 1 ≤ m - 0
      omega) hR
  · apply atLeast_mono localWeights (show m - 1 ≤ localWeights 0 + (m - localWeights 1) by
      change m - 1 ≤ 1 + (m - 2)
      omega) htv

def localEvaluation (P : Polynomial K) (x γ : K) : Poly4 K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, RCN185.contactResidual P x,
    Polynomial.taylor x P.derivative, Polynomial.C γ]

theorem localEvaluation_localize (Q : Poly4 K) (P : Polynomial K)
    (x u₀ u₁ γ : K) (hvalue : P.eval x = u₀ + γ * u₁) :
    localEvaluation K P x γ (localize K x u₀ u₁ Q) =
      Polynomial.taylor x (specialization K P γ Q) := by
  have hhom : (localEvaluation K P x γ).comp (localize K x u₀ u₁) =
      (Polynomial.taylorAlgHom x).comp (specialization K P γ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [localEvaluation, localize, localVariables, specialization,
        RCN185.contactResidual, hvalue,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] <;> ring
  exact DFunLike.congr_fun hhom Q

theorem localEvaluation_dvd (Q : Poly4 K) (P : Polynomial K) (x γ : K) (m : ℕ)
    (hQ : AtLeast localWeights m Q) :
    (Polynomial.X : Polynomial K) ^ m ∣ localEvaluation K P x γ Q := by
  classical
  rw [MvPolynomial.as_sum Q, map_sum]
  apply Finset.dvd_sum
  intro d hd
  have hweight : m ≤ d 0 + 2 * d 1 := by
    have h := hQ d hd
    rw [weight_fin4] at h
    simpa [localWeights, Nat.mul_comm] using h
  have hterm := RCN185.contact_monomial_dvd
    (Polynomial.C (MvPolynomial.coeff d Q))
    (RCN185.contactResidual P x)
    (Polynomial.taylor x P.derivative) m (d 0) (d 1) (d 2)
    (RCN185.X_sq_dvd_contactResidual P x) hweight
  have hlast := dvd_mul_of_dvd_left hterm ((Polynomial.C γ) ^ d 3)
  simpa [RCN122.monomial_eq, localEvaluation,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] using hlast

theorem contactAtLeast_specialization_dvd (Q : Poly4 K) (P : Polynomial K)
    (x u₀ u₁ γ : K) (m : ℕ) (hvalue : P.eval x = u₀ + γ * u₁)
    (hQ : ContactAtLeast K x u₀ u₁ m Q) :
    (Polynomial.X - Polynomial.C x) ^ m ∣ specialization K P γ Q := by
  have hlocal := localEvaluation_dvd K (localize K x u₀ u₁ Q) P x γ m hQ
  rw [localEvaluation_localize K Q P x u₀ u₁ γ hvalue] at hlocal
  exact (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
    (specialization K P γ Q) x m).mpr (Polynomial.X_pow_dvd_iff.mp hlocal)

/-- This is the local hroot input required by ResidualOrderMoments.
    Nonzeroness of the specialized derivative is needed by the subsequent
    rootMultiplicity/mass argument, not by this divisibility theorem. -/
theorem specialized_R_derivative_dvd (F : Poly4 K) (hF : F ≠ 0)
    (P : Polynomial K) (x u₀ u₁ γ : K) (hvalue : P.eval x = u₀ + γ * u₁) :
    (Polynomial.X - Polynomial.C x) ^ (contactOrder K x u₀ u₁ F - 1) ∣
      specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) := by
  apply contactAtLeast_specialization_dvd K _ P x u₀ u₁ γ _ hvalue
  apply contactAtLeast_pderiv_R K x u₀ u₁ (contactOrder K x u₀ u₁ F) F
  exact (exactOrder_order localWeights (localize K x u₀ u₁ F)
    (localize_ne_zero K x u₀ u₁ F hF)).1

theorem specialized_R_rootMultiplicity [DecidableEq K] (F : Poly4 K) (hF : F ≠ 0)
    (P : Polynomial K) (x u₀ u₁ γ : K) (hvalue : P.eval x = u₀ + γ * u₁)
    (hregular : specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    contactOrder K x u₀ u₁ F - 1 ≤
      (specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F)).rootMultiplicity x := by
  exact (Polynomial.le_rootMultiplicity_iff hregular).mpr
    (specialized_R_derivative_dvd K F hF P x u₀ u₁ γ hvalue)

/-- The other polynomial input to ResidualOrderMoments: the MAXIMUM global
    contact degree of F drops by w-1 before specializing its R derivative.
    Regularity is needed to rule out the truncated-subtraction zero case. -/
theorem specialized_R_derivative_degree (F : Poly4 K) (P : Polynomial K) (γ : K)
    (w d : ℕ) (hP : P.natDegree ≤ w)
    (hF : MvPolynomial.weightedTotalDegree (contactWeights w) F ≤ d)
    (hregular : specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    (specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F)).natDegree + w ≤ d + 1 := by
  classical
  let H : Poly4 K := MvPolynomial.pderiv (2 : Fin 4) F
  have hsupport (e : Fin 4 →₀ ℕ) (he : e ∈ H.support) :
      Finsupp.weight (contactWeights w) e + (w - 1) ≤ d := by
    have hbefore : e + Finsupp.single (2 : Fin 4) 1 ∈ F.support := by
      apply MvPolynomial.mem_support_iff.mpr
      intro hz
      have hne := MvPolynomial.mem_support_iff.mp he
      apply hne
      change MvPolynomial.coeff e (MvPolynomial.pderiv (2 : Fin 4) F) = 0
      rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
    have hh := (MvPolynomial.le_weightedTotalDegree (contactWeights w) hbefore).trans hF
    simpa [map_add, Finsupp.weight_single, contactWeights] using hh
  have hH : H ≠ 0 := by
    intro hz
    apply hregular
    change specialization K P γ H = 0
    rw [hz, map_zero]
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hH
  have hdrop : w - 1 ≤ d := by
    have hh := hsupport e he
    omega
  have hterms : ∀ e ∈ H.support,
      (specialization K P γ (MvPolynomial.monomial e (MvPolynomial.coeff e H))).natDegree ≤
        d - (w - 1) := by
    intro e he
    have hw := hsupport e he
    rw [contact_weight] at hw
    have ht := specialization_monomial_natDegree_le K P γ w hP e (MvPolynomial.coeff e H)
    omega
  have hdegree : (specialization K P γ H).natDegree ≤ d - (w - 1) := by
    rw [MvPolynomial.as_sum H, map_sum]
    exact Polynomial.natDegree_sum_le_of_forall_le H.support
      (fun e => specialization K P γ (MvPolynomial.monomial e (MvPolynomial.coeff e H))) hterms
  change (specialization K P γ H).natDegree + w ≤ d + 1
  omega

end LocalCoordinates

section KernelBridge
variable (K : Type*) [Field K]

def diagonalWeights : Fin 4 → ℕ := ![1, 1, 0, 0]

def blowupExponent : (Fin 4 →₀ ℕ) →+ (Fin 4 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 0 + d 1) + Finsupp.single 1 (d 1) +
    Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3)
  map_zero' := by simp
  map_add' d e := by
    ext i
    fin_cases i <;> simp [Finsupp.add_apply] <;> omega

theorem blowupExponent_injective : Function.Injective blowupExponent := by
  intro d e h
  have hsum : d 0 + d 1 = e 0 + e 1 := by
    simpa [blowupExponent] using congrArg (fun q : Fin 4 →₀ ℕ => q 0) h
  have h1 : d 1 = e 1 := by
    simpa [blowupExponent] using congrArg (fun q : Fin 4 →₀ ℕ => q 1) h
  have h2 : d 2 = e 2 := by
    simpa [blowupExponent] using congrArg (fun q : Fin 4 →₀ ℕ => q 2) h
  have h3 : d 3 = e 3 := by
    simpa [blowupExponent] using congrArg (fun q : Fin 4 →₀ ℕ => q 3) h
  have h0 : d 0 = e 0 := by omega
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

def contactBlowup : Poly4 K →+* Poly4 K :=
  AddMonoidAlgebra.mapDomainRingHom K blowupExponent

theorem contactBlowup_monomial (d : Fin 4 →₀ ℕ) (a : K) :
    contactBlowup K (MvPolynomial.monomial d a) = MvPolynomial.monomial (blowupExponent d) a := by
  change AddMonoidAlgebra.mapDomain blowupExponent (AddMonoidAlgebra.single d a) =
    AddMonoidAlgebra.single (blowupExponent d) a
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem contactBlowup_C (a : K) :
    contactBlowup K (MvPolynomial.C a) = MvPolynomial.C a := by
  change contactBlowup K (MvPolynomial.monomial 0 a) = MvPolynomial.monomial 0 a
  rw [contactBlowup_monomial, map_zero]

@[simp] theorem contactBlowup_X (i : Fin 4) :
    contactBlowup K (MvPolynomial.X i) =
      ![MvPolynomial.X 0, MvPolynomial.X 0 * MvPolynomial.X 1,
        MvPolynomial.X 2, MvPolynomial.X 3] i := by
  change contactBlowup K (MvPolynomial.monomial (Finsupp.single i 1) 1) = _
  rw [contactBlowup_monomial]
  fin_cases i <;> simp [blowupExponent, MvPolynomial.monomial_add_single,
    ← MvPolynomial.X_pow_eq_monomial]

theorem support_contactBlowup (P : Poly4 K) :
    (contactBlowup K P).support = P.support.image blowupExponent := by
  change (Finsupp.mapDomain blowupExponent (AddMonoidAlgebra.coeff P)).support =
    Finset.image blowupExponent (AddMonoidAlgebra.coeff P).support
  exact Finsupp.mapDomain_support_of_injective blowupExponent_injective _

theorem weight_blowupExponent (d : Fin 4 →₀ ℕ) :
    Finsupp.weight diagonalWeights (blowupExponent d) = Finsupp.weight localWeights d := by
  rw [weight_fin4, weight_fin4]
  simp [diagonalWeights, localWeights, blowupExponent] <;> omega

theorem atLeast_contactBlowup_iff (m : ℕ) (P : Poly4 K) :
    AtLeast diagonalWeights m (contactBlowup K P) ↔ AtLeast localWeights m P := by
  classical
  constructor
  · intro h d hd
    have hmem : blowupExponent d ∈ (contactBlowup K P).support := by
      rw [support_contactBlowup]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    simpa only [weight_blowupExponent] using h _ hmem
  · intro h d hd
    rw [support_contactBlowup] at hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    simpa only [weight_blowupExponent] using h e he

@[simp] theorem shiftPlus_C_bridge (a : K) :
    shiftPlus K (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [shiftPlus]

@[simp] theorem shiftPlus_X_bridge (i : Fin 3) :
    shiftPlus K (MvPolynomial.X i) =
      ![MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 1, MvPolynomial.X 2] i := by
  fin_cases i <;> simp [shiftPlus] <;> rfl

@[simp] theorem shiftPlus_seedAffine_bridge (u₀ u₁ : K) :
    shiftPlus K (seedAffine K u₀ u₁) = seedAffine K u₀ u₁ := by
  simp [seedAffine, ← MvPolynomial.C_mul_X_eq_monomial]

/-- This identifies the existing t/A translation followed by A=R+C with
    the injective monomial blow-up v=t*C of our invertible local coordinates. -/
theorem collected_contactBlowup_localize (x u₀ u₁ : K) (Q : Poly4 K) :
    MvPolynomial.finSuccEquiv K 3 (contactBlowup K (localize K x u₀ u₁ Q)) =
      Polynomial.map (shiftPlus K).toRingHom (homogenizedTranslation K x u₀ u₁ Q) := by
  classical
  have hC (a : K) : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
    simp [MvPolynomial.finSuccEquiv_apply]
  have hX0 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (0 : Fin 4)) =
      Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
  have hX1 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (1 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j := (0 : Fin 3))
  have hX2 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (2 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j := (1 : Fin 3))
  have hX3 : MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (3 : Fin 4)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j := (2 : Fin 3))
  have hgen (i : Fin 4) :
      MvPolynomial.finSuccEquiv K 3
          (contactBlowup K (localize K x u₀ u₁ (MvPolynomial.X i))) =
        Polynomial.map (shiftPlus K).toRingHom
          (homogenizedTranslation K x u₀ u₁ (MvPolynomial.X i)) := by
    fin_cases i <;>
      simp [localize, localVariables, homogenizedTranslation, translationVariables,
        hC, hX0, hX1, hX2, hX3, seedAffine,
        ← MvPolynomial.C_mul_X_eq_monomial, Polynomial.algebraMap_apply,
        MvPolynomial.algebraMap_eq] <;> ring
  induction Q using MvPolynomial.induction_on with
  | C a =>
      simp [localize, homogenizedTranslation, MvPolynomial.finSuccEquiv_apply,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add P Q hP hQ =>
      simp only [map_add, Polynomial.map_add, hP, hQ]
  | mul_X P i hP =>
      simpa only [map_mul, Polynomial.map_mul] using congrArg₂ (· * ·) hP (hgen i)

theorem diagonalAtLeast_iff_coeff (m : ℕ) (Q : Poly4 K) :
    AtLeast diagonalWeights m Q ↔
      ∀ (r : ℕ) (d : Fin 3 →₀ ℕ), r + d 0 < m →
        MvPolynomial.coeff d ((MvPolynomial.finSuccEquiv K 3 Q).coeff r) = 0 := by
  classical
  constructor
  · intro h r d hsmall
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_contra hc
    have hw := h (Finsupp.cons r d) (MvPolynomial.mem_support_iff.mpr hc)
    have hcons : (Finsupp.cons r d) (1 : Fin 4) = d 0 := rfl
    rw [weight_fin4] at hw
    simp [diagonalWeights, hcons] at hw
    omega
  · intro h d hd
    have hweight : Finsupp.weight diagonalWeights d = d 0 + d 1 := by
      rw [weight_fin4]
      simp [diagonalWeights]
    by_contra hsmall
    have hlt : d 0 + d.tail 0 < m := by
      simp only [Finsupp.tail_apply]
      change d 0 + d 1 < m
      omega
    have hz := h (d 0) d.tail hlt
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hz
    have he : Finsupp.cons (d 0) d.tail = d := by
      ext i
      fin_cases i <;> simp [Finsupp.tail_apply]
    rw [he] at hz
    exact MvPolynomial.mem_support_iff.mp hd hz

theorem contactAtLeast_iff_block_divisibility (x u₀ u₁ : K) (m : ℕ) (Q : Poly4 K) :
    ContactAtLeast K x u₀ u₁ m Q ↔
      ∀ r : ℕ, slopeDifference K ^ (m - r) ∣
        (homogenizedTranslation K x u₀ u₁ Q).coeff r := by
  change AtLeast localWeights m (localize K x u₀ u₁ Q) ↔ _
  rw [← atLeast_contactBlowup_iff K m (localize K x u₀ u₁ Q), diagonalAtLeast_iff_coeff]
  simp only [collected_contactBlowup_localize, Polynomial.coeff_map]
  constructor
  · intro h r
    apply (contactJet_eq_zero_iff K (m - r) _).mp
    apply (contactJet_eq_zero_iff_coeff K (m - r) _).mpr
    intro d hd
    exact h r d (by omega)
  · intro h r d hd
    have hjet := (contactJet_eq_zero_iff K (m - r) _).mpr (h r)
    exact (contactJet_eq_zero_iff_coeff K (m - r) _).mp hjet d (by omega)

theorem contactAtLeast_of_mem_kernel {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u₀ u₁ : I → K)
    (a : CoefficientIndex D w L s → K)
    (ha : a ∈ LinearMap.ker (constraintMap K D w L s m nodes u₀ u₁)) (i : I) :
    ContactAtLeast K (nodes i) (u₀ i) (u₁ i) m (reconstruct K D w L s a) := by
  apply (contactAtLeast_iff_block_divisibility K (nodes i) (u₀ i) (u₁ i) m _).mpr
  exact RCN101.translated_contact_of_mem_ker
    K D w L s m nodes u₀ u₁ a ha i

def slopeDiagonal : Poly K →ₐ[K] Poly K :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 0, MvPolynomial.X 2]

theorem monomial_fin3 (d : Fin 3 →₀ ℕ) (a : K) :
    MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 *
        MvPolynomial.X 2 ^ d 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hd]
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem slopeDiagonal_fixed (P : Poly K) (hP : ∀ d ∈ P.support, d 1 = 0) :
    slopeDiagonal K P = P := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P, map_sum]
  conv_rhs => rw [MvPolynomial.as_sum P]
  apply Finset.sum_congr rfl
  intro d hd
  rw [monomial_fin3]
  simp [slopeDiagonal, hP d hd]

@[simp] theorem slopeDiagonal_slopeDifference :
    slopeDiagonal K (slopeDifference K) = 0 := by
  simp [slopeDiagonal, slopeDifference]

/-- A slope-free polynomial cannot have a nonzero low Taylor block divisible
    by a positive power of A-R. Setting R=A kills the divisor and fixes the
    block. This supplies the low-block hypothesis of the top-Y projection
    proof without proving a general ordinary-multiplicity equivalence. -/
theorem slopeFree_blocks_zero_of_contactAtLeast
    (D w L m : ℕ) (x u₀ u₁ : K) (a : CoefficientIndex D w L 0 → K)
    (ha : ContactAtLeast K x u₀ u₁ m (reconstruct K D w L 0 a)) :
    ∀ r : ℕ, r < m → ((extractBlock K D w L 0 x u₀ u₁ r a) : Poly K) = 0 := by
  intro r hr
  have hdiv := (contactAtLeast_iff_block_divisibility K x u₀ u₁ m _).mp ha r
  rw [translation_reconstruct_coeff] at hdiv
  let B : Poly K := extractBlock K D w L 0 x u₀ u₁ r a
  have hfree : ∀ d ∈ B.support, d 1 = 0 := by
    intro d hd
    have hbox := (extractBlock K D w L 0 x u₀ u₁ r a).property
    have hs := (mem_coefficientBox_iff K (min r L) L 0 B).mp hbox d hd
    omega
  obtain ⟨q, hq⟩ := hdiv
  have hdiag := congrArg (slopeDiagonal K) hq
  change slopeDiagonal K B = slopeDiagonal K (slopeDifference K ^ (m - r) * q) at hdiag
  rw [slopeDiagonal_fixed K B hfree, map_mul, map_pow, slopeDiagonal_slopeDifference] at hdiag
  have hpos : m - r ≠ 0 := by omega
  simpa only [zero_pow hpos, zero_mul] using hdiag

end KernelBridge

/- Interfaces and scope:

1. The C1 kernel is an exact weighted-contact condition. Its constraintMap
   really uses contactJet (m-r), not the min expression used only in the rank
   estimate. By BC.contactJet_eq_zero_iff_coeff and BD's coefficient identity,
   its local condition is: in H(t,C,R,Z) obtained by setting A=R+C in the
   homogenizedTranslation, coeff(t^r C^b R^c Z^z)=0 whenever r+b<m.
   H is the blow-up v=t*C of localize(F). The exponent map
       (a,b,c,z) |-> (a+b,b,c,z)
   is injective and changes weight a+2b into r+b. The KernelBridge section
   implements this using mapDomain and finSuccEquiv_coeff_coeff.
   slopeFree_blocks_zero_of_contactAtLeast is the narrow interface used by
   the separate Y=0/1 quotient projection proof.

2. For slope-free P, translate first by X=x+t,Y=u(Z)+q, WITHOUT R*t.
   Let n=min(a+b). Under q=R*t+v, the weight-n component is
       t^n * sum_{a+b=n} p_ab(Z)*R^b,
   which is nonzero because R is an indeterminate and different b cannot
   cancel. Thus contactOrder equals ordinary (t,q) multiplicity. One can
   implement it without a new initial-form theorem: shear q->R*t+v is
   filtration-preserving; setting v=0 can only increase order; on R-free
   support the remaining monomial map (a,b,0,z)->(a+b,0,b,z) is injective.
   Preserve the separate hypothesis degreeOf R=0 throughout. It is NOT
   enough to know partial_R P=0 in positive characteristic.

3. specialized_R_derivative_degree gives the global MAXIMUM-degree bound
   in precisely the natDegree+w<=d+1 form used by the mass proof. Combine
   it with specialized_R_derivative_dvd, a nonzero specialization, and the
   mass_of_regular_polynomial. This file does not establish
   full-kernel factor divisibility, the quotient dimension bound, or a
   ProtocolClaim.
-/
end
end ProximityPrize.SubmissionLower.ContactOrderBridge
