import ProximityPrize.SubmissionLower.BCHKSFrobeniusGenericRankFork6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusRectangularHankelAudit6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusGenericMinor6401
open Polynomial
open scoped BigOperators
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusGenericRankFork6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSGaoSpecializationCore6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
theorem sigma_syndromeWeight_fixed6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i) (i : iota) :
    sigma (syndromeWeight alpha i) = syndromeWeight alpha i := by
  classical
  simp [syndromeWeight, Lagrange.nodalWeight, hfixed]
theorem sigma_weightedSyndrome_fixed6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (y : iota → F) (j : Nat) :
    sigma (weightedSyndrome alpha y j) =
      weightedSyndrome alpha (fun i => sigma (y i)) j := by
  classical
  simp only [weightedSyndrome, map_sum, map_mul, map_pow,
    sigma_syndromeWeight_fixed6401 sigma alpha hfixed]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfixed i]
theorem weightedSyndrome_eq_supportSyndrome
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat} (alpha y : iota → F) (support : Fin s ↪ iota)
    (hy : ∀ i, i ∉ Set.range support → y i = 0) (j : Nat) :
    weightedSyndrome alpha y j =
      supportSyndrome (fun a => alpha (support a))
        (fun a => syndromeWeight alpha (support a) * y (support a)) j := by
  classical
  let f : iota → F := fun i =>
    syndromeWeight alpha i * alpha i ^ j * y i
  have hsum : ∑ i ∈ Finset.univ.image support, f i = ∑ i, f i := by
    apply Finset.sum_subset (by simp)
    intro i hiu hiimage
    have hirange : i ∉ Set.range support := by
      intro hir
      obtain ⟨a, rfl⟩ := hir
      apply hiimage
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    simp [f, hy i hirange]
  change (∑ i, f i) = ∑ a,
    (syndromeWeight alpha (support a) * y (support a)) *
      alpha (support a) ^ j
  rw [← hsum]
  rw [Finset.sum_image (fun a _ b _ hab => support.injective hab)]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp [f]
  ring
noncomputable def exactSupportLocator
    {F : Type*} [Field F] {s : Nat} (a : Fin s → F) : F[X] :=
  ∏ i, (Polynomial.X - Polynomial.C (a i))
noncomputable def exactSupportLocatorCoefficients
    {F : Type*} [Field F] {s : Nat} (a : Fin s → F) : Fin s → F :=
  fun j => (exactSupportLocator a).coeff j.1
theorem exactSupportLocator_monic
    {F : Type*} [Field F] {s : Nat} (a : Fin s → F) :
    (exactSupportLocator a).Monic := by
  exact Polynomial.monic_prod_of_monic _ _
    (fun i hi => Polynomial.monic_X_sub_C _)
theorem exactSupportLocator_natDegree
    {F : Type*} [Field F] {s : Nat} (a : Fin s → F) :
    (exactSupportLocator a).natDegree = s := by
  rw [exactSupportLocator, Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i hi
    exact Polynomial.monic_X_sub_C _
theorem locatorPolynomial_exactSupportCoefficients
    {F : Type*} [Field F] {s : Nat} (a : Fin s → F) :
    locatorPolynomial (exactSupportLocatorCoefficients a) =
      exactSupportLocator a := by
  let P := exactSupportLocator a
  have hdeg : P.natDegree = s := exactSupportLocator_natDegree a
  have hmonic : P.Monic := exactSupportLocator_monic a
  have hsum := P.as_sum_range
  rw [hdeg, Finset.sum_range_succ] at hsum
  have htop : P.coeff s = 1 := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact hmonic.leadingCoeff
  rw [htop, Polynomial.monomial_one_right_eq_X_pow, add_comm] at hsum
  rw [locatorPolynomial]
  rw [show (∑ j : Fin s,
      Polynomial.monomial j.1 (exactSupportLocatorCoefficients a j)) =
      ∑ j ∈ Finset.range s, Polynomial.monomial j (P.coeff j) by
    change (∑ j : Fin s, Polynomial.monomial j.1 (P.coeff j.1)) = _
    exact Fin.sum_univ_eq_sum_range
      (fun j => Polynomial.monomial j (P.coeff j)) s]
  exact hsum.symm
theorem exactSupportLocator_root
    {F : Type*} [Field F] {s : Nat} (a : Fin s → F) (i : Fin s) :
    (exactSupportLocator a).eval (a i) = 0 := by
  classical
  rw [exactSupportLocator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (s := Finset.univ) (i := i)
  · simp
  · simp
theorem exactSupportLocator_eval_eq_zero_iff
    {F : Type*} [Field F] {s : Nat} (a : Fin s → F) (x : F) :
    (exactSupportLocator a).eval x = 0 ↔ x ∈ Set.range a := by
  classical
  rw [exactSupportLocator, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, sub_eq_zero.mpr hi.symm⟩
theorem locatorPolynomial_exactSupport_root
    {F : Type*} [Field F] {s : Nat} (a : Fin s → F) (i : Fin s) :
    (locatorPolynomial (exactSupportLocatorCoefficients a)).eval (a i) = 0 := by
  rw [locatorPolynomial_exactSupportCoefficients]
  exact exactSupportLocator_root a i
abbrev GenericRankMinorRow6401 (rho : Nat) :=
  Fin (min keyFirstLaneRows6401 rho) ⊕
    Fin (rho - keyFirstLaneRows6401)
theorem genericRankMinorRows_add6401 (rho : Nat) :
    min keyFirstLaneRows6401 rho +
      (rho - keyFirstLaneRows6401) = rho := by
  omega
noncomputable def genericRankMinorColumnEquiv6401 (rho : Nat) :
    GenericRankMinorRow6401 rho ≃ Fin rho :=
  finSumFinEquiv.trans (finCongr (genericRankMinorRows_add6401 rho))
def genericRankMinorRowCap6401 (rho : Nat) :
    GenericRankMinorRow6401 rho → Nat
  | Sum.inl _ => 1
  | Sum.inr _ => q6401
theorem genericRankMinorRowCap_sum6401 (rho : Nat) :
    ∑ row : GenericRankMinorRow6401 rho,
      genericRankMinorRowCap6401 rho row =
        genericRankMinorDegreeCap6401 rho := by
  rw [Fintype.sum_sum_type]
  simp [genericRankMinorRowCap6401, genericRankMinorDegreeCap6401]
def genericRankSelectedRow6401 (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) :
    GenericRankMinorRow6401 rho → FullTwoLaneKeyRow6401
  | Sum.inl i => Sum.inl (Fin.castLE (Nat.min_le_left _ _) i)
  | Sum.inr i => Sum.inr (frobeniusRow i)
noncomputable def genericRankKeyMinorZ6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) :
    Matrix (GenericRankMinorRow6401 rho)
      (GenericRankMinorRow6401 rho) F[X] :=
  fun row col =>
    match row with
    | Sum.inl a =>
        affineSyndromeZ alpha u₀ u₁
          (a.1 + (genericRankMinorColumnEquiv6401 rho col).1)
    | Sum.inr b =>
        frobeniusSyndromeZ sigma q6401 alpha u₀ u₁
          ((frobeniusRow b).1 +
            (genericRankMinorColumnEquiv6401 rho col).1)
noncomputable def genericRankKeyRhsZ6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) :
    GenericRankMinorRow6401 rho → F[X]
  | Sum.inl a =>
      -affineSyndromeZ alpha u₀ u₁ (a.1 + rho)
  | Sum.inr b =>
      -frobeniusSyndromeZ sigma q6401 alpha u₀ u₁
        ((frobeniusRow b).1 + rho)
theorem genericRankKeyMinorZ_entry_degree6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) :
    ∀ row col,
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow row col).natDegree ≤
          genericRankMinorRowCap6401 rho row := by
  intro row col
  cases row with
  | inl a => exact affineSyndromeZ_natDegree_le_one alpha u₀ u₁ _
  | inr b =>
      exact frobeniusSyndromeZ_natDegree_le
        sigma q6401 alpha u₀ u₁ _
theorem genericRankKeyRhsZ_degree6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) :
    ∀ row,
      (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow row).natDegree ≤
          genericRankMinorRowCap6401 rho row := by
  intro row
  cases row with
  | inl a =>
      simpa [genericRankKeyRhsZ6401, genericRankMinorRowCap6401] using
        (affineSyndromeZ_natDegree_le_one alpha u₀ u₁ (a.1 + rho))
  | inr b =>
      simpa [genericRankKeyRhsZ6401, genericRankMinorRowCap6401] using
        (frobeniusSyndromeZ_natDegree_le (F := F) (ι := iota)
          sigma q6401 alpha u₀ u₁ ((frobeniusRow b).1 + rho))
theorem genericRankKeyMinorZ_eval_entry6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401) :
    ∀ row col,
      Polynomial.eval z
        (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow row col) =
        match row with
        | Sum.inl a =>
            weightedSyndrome alpha (fun i => u₀ i + z * u₁ i)
              (a.1 + (genericRankMinorColumnEquiv6401 rho col).1)
        | Sum.inr b =>
            weightedSyndrome alpha
              (fun i => sigma (u₀ i + z * u₁ i))
              ((frobeniusRow b).1 +
                (genericRankMinorColumnEquiv6401 rho col).1) := by
  intro row col
  cases row with
  | inl a => exact affineSyndromeZ_eval alpha u₀ u₁ _ z
  | inr b =>
      exact frobeniusSyndromeZ_eval (F := F) (ι := iota)
        sigma q6401 alpha u₀ u₁ _ z hz
theorem genericRankKeyRhsZ_eval6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401) :
    ∀ row,
      Polynomial.eval z
        (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow row) =
        match row with
        | Sum.inl a =>
            -weightedSyndrome alpha (fun i => u₀ i + z * u₁ i)
              (a.1 + rho)
        | Sum.inr b =>
            -weightedSyndrome alpha
              (fun i => sigma (u₀ i + z * u₁ i))
              ((frobeniusRow b).1 + rho) := by
  intro row
  cases row with
  | inl a =>
      simpa [genericRankKeyRhsZ6401] using congrArg Neg.neg
        (affineSyndromeZ_eval alpha u₀ u₁ (a.1 + rho) z)
  | inr b =>
      simpa [genericRankKeyRhsZ6401] using congrArg Neg.neg
        (frobeniusSyndromeZ_eval (F := F) (ι := iota)
          sigma q6401 alpha u₀ u₁ ((frobeniusRow b).1 + rho) z hz)
theorem genericRankKeyMinorZ_eval_eq_supportSubmatrix6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support → u₀ i + z * u₁ i = 0) :
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow).map
        (Polynomial.evalRingHom z) =
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a => alpha (support a))
        (fun a => syndromeWeight alpha (support a))
        (fun a => u₀ (support a) + z * u₁ (support a))).submatrix
          (genericRankSelectedRow6401 rho frobeniusRow)
          (genericRankMinorColumnEquiv6401 rho) := by
  apply Matrix.ext
  intro row col
  cases row with
  | inl a =>
      rw [show ((genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow).map (Polynomial.evalRingHom z)) (Sum.inl a) col =
          Polynomial.eval z (genericRankKeyMinorZ6401 sigma alpha u₀ u₁
            rho frobeniusRow (Sum.inl a) col) by rfl,
        genericRankKeyMinorZ_eval_entry6401 sigma alpha u₀ u₁ rho
          frobeniusRow z hz]
      simpa [fullTwoLaneSupportKeyMatrix, genericRankSelectedRow6401,
        mul_assoc] using
        (weightedSyndrome_eq_supportSyndrome alpha
          (fun i => u₀ i + z * u₁ i) support hout
          (a.1 + (genericRankMinorColumnEquiv6401 rho col).1))
  | inr b =>
      rw [show ((genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow).map (Polynomial.evalRingHom z)) (Sum.inr b) col =
          Polynomial.eval z (genericRankKeyMinorZ6401 sigma alpha u₀ u₁
            rho frobeniusRow (Sum.inr b) col) by rfl,
        genericRankKeyMinorZ_eval_entry6401 sigma alpha u₀ u₁ rho
          frobeniusRow z hz]
      have hsigmaOut : ∀ i, i ∉ Set.range support →
          sigma (u₀ i + z * u₁ i) = 0 := by
        intro i hi
        rw [hout i hi, map_zero]
      simpa [fullTwoLaneSupportKeyMatrix, genericRankSelectedRow6401,
        mul_assoc] using
        (weightedSyndrome_eq_supportSyndrome alpha
          (fun i => sigma (u₀ i + z * u₁ i)) support hsigmaOut
          ((frobeniusRow b).1 +
            (genericRankMinorColumnEquiv6401 rho col).1))
theorem genericRankKeyMinorZ_eval_eq_ownerErrorSubmatrix6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401)
    (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0) :
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).map (Polynomial.evalRingHom z) =
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a => alpha (support a))
        (fun a => syndromeWeight alpha (support a))
        (fun a => u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a)))).submatrix
            (genericRankSelectedRow6401 rho frobeniusRow)
            (genericRankMinorColumnEquiv6401 rho) := by
  classical
  let E : iota → F := fun i =>
    u₀ i + z * u₁ i - P.eval (alpha i)
  have hu : ∀ i, u₀ i + z * u₁ i = P.eval (alpha i) + E i := by
    intro i
    dsimp [E]
    ring
  have hred : keyFirstLaneRows6401 + keyErrors6401 =
      keyRedundancy6401 := by native_decide
  apply Matrix.ext
  intro row col
  cases row with
  | inl a =>
      let j := a.1 + (genericRankMinorColumnEquiv6401 rho col).1
      have hj : j < keyRedundancy6401 := by
        have ha := a.isLt
        have hc := (genericRankMinorColumnEquiv6401 rho col).isLt
        have hm := Nat.min_le_left keyFirstLaneRows6401 rho
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P E
        (fun i => u₀ i + z * u₁ i) j hu (hPcheck j hj)
      change Polynomial.eval z (affineSyndromeZ alpha u₀ u₁ j) =
        supportSyndrome (fun x => alpha (support x))
          (fun x => syndromeWeight alpha (support x) * E (support x)) j
      rw [affineSyndromeZ_eval, hrecv]
      exact weightedSyndrome_eq_supportSyndrome alpha E support hout j
  | inr b =>
      let j := (frobeniusRow b).1 +
        (genericRankMinorColumnEquiv6401 rho col).1
      have hj : j < keyRedundancy6401 := by
        have hb := (frobeniusRow b).isLt
        have hc := (genericRankMinorColumnEquiv6401 rho col).isLt
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P E
        (fun i => u₀ i + z * u₁ i) j hu (hPcheck j hj)
      have hsigma :
          weightedSyndrome alpha
              (fun i => sigma (u₀ i + z * u₁ i)) j =
            weightedSyndrome alpha (fun i => sigma (E i)) j := by
        calc
          _ = sigma (weightedSyndrome alpha
                (fun i => u₀ i + z * u₁ i) j) :=
            (sigma_weightedSyndrome_fixed6401 sigma alpha hfixed _ j).symm
          _ = sigma (weightedSyndrome alpha E j) := congrArg sigma hrecv
          _ = _ := sigma_weightedSyndrome_fixed6401 sigma alpha hfixed E j
      have hsigmaOut : ∀ i, i ∉ Set.range support → sigma (E i) = 0 := by
        intro i hi
        rw [show E i = 0 by simpa [E] using hout i hi, map_zero]
      change Polynomial.eval z
          (frobeniusSyndromeZ sigma q6401 alpha u₀ u₁ j) =
        supportSyndrome (fun x => alpha (support x))
          (fun x => syndromeWeight alpha (support x) *
            sigma (E (support x))) j
      rw [frobeniusSyndromeZ_eval sigma q6401 alpha u₀ u₁ j z hz,
        hsigma]
      exact weightedSyndrome_eq_supportSyndrome alpha
        (fun i => sigma (E i)) support hsigmaOut j
theorem genericRankKeyMinorZ_eval_eq_ownerErrorPrefixSubmatrix6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401) (hrhoS : rho ≤ s)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401)
    (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0) :
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).map (Polynomial.evalRingHom z) =
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a => alpha (support a))
        (fun a => syndromeWeight alpha (support a))
        (fun a => u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a)))).submatrix
            (genericRankSelectedRow6401 rho frobeniusRow)
            (fun col => Fin.castLE hrhoS
              (genericRankMinorColumnEquiv6401 rho col)) := by
  classical
  let E : iota → F := fun i =>
    u₀ i + z * u₁ i - P.eval (alpha i)
  have hu : ∀ i, u₀ i + z * u₁ i = P.eval (alpha i) + E i := by
    intro i
    dsimp [E]
    ring
  have hred : keyFirstLaneRows6401 + keyErrors6401 =
      keyRedundancy6401 := by native_decide
  apply Matrix.ext
  intro row col
  cases row with
  | inl a =>
      let j := a.1 + (genericRankMinorColumnEquiv6401 rho col).1
      have hj : j < keyRedundancy6401 := by
        have ha := a.isLt
        have hc := (genericRankMinorColumnEquiv6401 rho col).isLt
        have hm := Nat.min_le_left keyFirstLaneRows6401 rho
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P E
        (fun i => u₀ i + z * u₁ i) j hu (hPcheck j hj)
      change Polynomial.eval z (affineSyndromeZ alpha u₀ u₁ j) =
        supportSyndrome (fun x => alpha (support x))
          (fun x => syndromeWeight alpha (support x) * E (support x)) j
      rw [affineSyndromeZ_eval, hrecv]
      exact weightedSyndrome_eq_supportSyndrome alpha E support hout j
  | inr b =>
      let j := (frobeniusRow b).1 +
        (genericRankMinorColumnEquiv6401 rho col).1
      have hj : j < keyRedundancy6401 := by
        have hb := (frobeniusRow b).isLt
        have hc := (genericRankMinorColumnEquiv6401 rho col).isLt
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P E
        (fun i => u₀ i + z * u₁ i) j hu (hPcheck j hj)
      have hsigma :
          weightedSyndrome alpha
              (fun i => sigma (u₀ i + z * u₁ i)) j =
            weightedSyndrome alpha (fun i => sigma (E i)) j := by
        calc
          _ = sigma (weightedSyndrome alpha
                (fun i => u₀ i + z * u₁ i) j) :=
            (sigma_weightedSyndrome_fixed6401 sigma alpha hfixed _ j).symm
          _ = sigma (weightedSyndrome alpha E j) := congrArg sigma hrecv
          _ = _ := sigma_weightedSyndrome_fixed6401 sigma alpha hfixed E j
      have hsigmaOut : ∀ i, i ∉ Set.range support → sigma (E i) = 0 := by
        intro i hi
        rw [show E i = 0 by simpa [E] using hout i hi, map_zero]
      change Polynomial.eval z
          (frobeniusSyndromeZ sigma q6401 alpha u₀ u₁ j) =
        supportSyndrome (fun x => alpha (support x))
          (fun x => syndromeWeight alpha (support x) *
            sigma (E (support x))) j
      rw [frobeniusSyndromeZ_eval sigma q6401 alpha u₀ u₁ j z hz,
        hsigma]
      exact weightedSyndrome_eq_supportSyndrome alpha
        (fun i => sigma (E i)) support hsigmaOut j
theorem fullTwoLaneKeyMatrixZ_eval_eq_ownerErrorPrefix6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hs : s ≤ keyErrors6401) (z : F) (hz : sigma z = z ^ q6401)
    (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0) :
    ((fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).map
      (Polynomial.evalRingHom z)).submatrix id (Fin.castLE hs) =
      fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a ↦ alpha (support a))
        (fun a ↦ syndromeWeight alpha (support a))
        (fun a ↦ u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a))) := by
  classical
  let Err : iota → F := fun i ↦
    u₀ i + z * u₁ i - P.eval (alpha i)
  have hu : ∀ i, u₀ i + z * u₁ i = P.eval (alpha i) + Err i := by
    intro i
    dsimp [Err]
    ring
  have hred : keyFirstLaneRows6401 + keyErrors6401 =
      keyRedundancy6401 := by native_decide
  apply Matrix.ext
  intro row col
  cases row with
  | inl a =>
      let j := a.1 + col.1
      have hj : j < keyRedundancy6401 := by
        have ha := a.isLt
        have hc := col.isLt
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P Err
        (fun i ↦ u₀ i + z * u₁ i) j hu (hPcheck j hj)
      change Polynomial.eval z (affineSyndromeZ alpha u₀ u₁ j) =
        supportSyndrome (fun x ↦ alpha (support x))
          (fun x ↦ syndromeWeight alpha (support x) * Err (support x)) j
      rw [affineSyndromeZ_eval, hrecv]
      exact weightedSyndrome_eq_supportSyndrome alpha Err support hout j
  | inr a =>
      let j := a.1 + col.1
      have hj : j < keyRedundancy6401 := by
        have ha := a.isLt
        have hc := col.isLt
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P Err
        (fun i ↦ u₀ i + z * u₁ i) j hu (hPcheck j hj)
      have hsigma :
          weightedSyndrome alpha
              (fun i ↦ sigma (u₀ i + z * u₁ i)) j =
            weightedSyndrome alpha (fun i ↦ sigma (Err i)) j := by
        calc
          _ = sigma (weightedSyndrome alpha
                (fun i ↦ u₀ i + z * u₁ i) j) :=
            (sigma_weightedSyndrome_fixed6401 sigma alpha hfixed _ j).symm
          _ = sigma (weightedSyndrome alpha Err j) := congrArg sigma hrecv
          _ = _ := sigma_weightedSyndrome_fixed6401 sigma alpha hfixed Err j
      have hsigmaOut : ∀ i, i ∉ Set.range support → sigma (Err i) = 0 := by
        intro i hi
        rw [show Err i = 0 by simpa [Err] using hout i hi, map_zero]
      change Polynomial.eval z
          (frobeniusSyndromeZ sigma q6401 alpha u₀ u₁ j) =
        supportSyndrome (fun x ↦ alpha (support x))
          (fun x ↦ syndromeWeight alpha (support x) *
            sigma (Err (support x))) j
      rw [frobeniusSyndromeZ_eval sigma q6401 alpha u₀ u₁ j z hz,
        hsigma]
      exact weightedSyndrome_eq_supportSyndrome alpha
        (fun i ↦ sigma (Err i)) support hsigmaOut j
theorem fullTwoLaneKeyMatrixZ_eval_eq_ownerErrorRectangular6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0) :
    (fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).map
      (Polynomial.evalRingHom z) =
      BCHKSFrobeniusRectangularHankelAudit6401.twoLaneSupportSyndromeMatrix
        keyFirstLaneRows6401
        keyFirstLaneRows6401 keyErrors6401
        (fun a ↦ alpha (support a))
        (fun a ↦ syndromeWeight alpha (support a) *
          (u₀ (support a) + z * u₁ (support a) -
            P.eval (alpha (support a))))
        (fun a ↦ syndromeWeight alpha (support a) *
          sigma (u₀ (support a) + z * u₁ (support a) -
            P.eval (alpha (support a)))) := by
  classical
  let Err : iota → F := fun i ↦
    u₀ i + z * u₁ i - P.eval (alpha i)
  have hu : ∀ i, u₀ i + z * u₁ i = P.eval (alpha i) + Err i := by
    intro i
    dsimp [Err]
    ring
  have hred : keyFirstLaneRows6401 + keyErrors6401 =
      keyRedundancy6401 := by native_decide
  apply Matrix.ext
  intro row col
  cases row with
  | inl a =>
      let j := a.1 + col.1
      have hj : j < keyRedundancy6401 := by
        have ha := a.isLt
        have hc := col.isLt
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P Err
        (fun i ↦ u₀ i + z * u₁ i) j hu (hPcheck j hj)
      change Polynomial.eval z (affineSyndromeZ alpha u₀ u₁ j) =
        supportSyndrome (fun x ↦ alpha (support x))
          (fun x ↦ syndromeWeight alpha (support x) * Err (support x)) j
      rw [affineSyndromeZ_eval, hrecv]
      exact weightedSyndrome_eq_supportSyndrome alpha Err support hout j
  | inr a =>
      let j := a.1 + col.1
      have hj : j < keyRedundancy6401 := by
        have ha := a.isLt
        have hc := col.isLt
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P Err
        (fun i ↦ u₀ i + z * u₁ i) j hu (hPcheck j hj)
      have hsigma :
          weightedSyndrome alpha
              (fun i ↦ sigma (u₀ i + z * u₁ i)) j =
            weightedSyndrome alpha (fun i ↦ sigma (Err i)) j := by
        calc
          _ = sigma (weightedSyndrome alpha
                (fun i ↦ u₀ i + z * u₁ i) j) :=
            (sigma_weightedSyndrome_fixed6401 sigma alpha hfixed _ j).symm
          _ = sigma (weightedSyndrome alpha Err j) := congrArg sigma hrecv
          _ = _ := sigma_weightedSyndrome_fixed6401 sigma alpha hfixed Err j
      have hsigmaOut : ∀ i, i ∉ Set.range support → sigma (Err i) = 0 := by
        intro i hi
        rw [show Err i = 0 by simpa [Err] using hout i hi, map_zero]
      change Polynomial.eval z
          (frobeniusSyndromeZ sigma q6401 alpha u₀ u₁ j) =
        supportSyndrome (fun x ↦ alpha (support x))
          (fun x ↦ syndromeWeight alpha (support x) *
            sigma (Err (support x))) j
      rw [frobeniusSyndromeZ_eval sigma q6401 alpha u₀ u₁ j z hz,
        hsigma]
      exact weightedSyndrome_eq_supportSyndrome alpha
        (fun i ↦ sigma (Err i)) support hsigmaOut j
theorem fullTwoLaneKeyMatrixZ_eval_rank_eq_ownerErrorStack6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hs : s ≤ keyErrors6401)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0) :
    ((fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).map
      (Polynomial.evalRingHom z)).rank =
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a ↦ alpha (support a))
        (fun a ↦ syndromeWeight alpha (support a))
        (fun a ↦ u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a)))).rank := by
  let alphaS : Fin s → F := fun a ↦ alpha (support a)
  let d₀ : Fin s → F := fun a ↦ syndromeWeight alpha (support a) *
    (u₀ (support a) + z * u₁ (support a) -
      P.eval (alpha (support a)))
  let d₁ : Fin s → F := fun a ↦ syndromeWeight alpha (support a) *
    sigma (u₀ (support a) + z * u₁ (support a) -
      P.eval (alpha (support a)))
  rw [fullTwoLaneKeyMatrixZ_eval_eq_ownerErrorRectangular6401 sigma alpha
    u₀ u₁ hfixed z hz P hPcheck support hout]
  have hrect :=
    BCHKSFrobeniusRectangularHankelAudit6401.twoLaneSupportSyndromeMatrix_rank_eq_leftFactor
    keyFirstLaneRows6401 keyFirstLaneRows6401 alphaS d₀ d₁
    (support.trans alpha).injective hs
  have hsquare :=
    BCHKSFrobeniusRectangularHankelAudit6401.twoLaneSupportSyndromeMatrix_rank_eq_leftFactor
    keyFirstLaneRows6401 keyFirstLaneRows6401 alphaS d₀ d₁
    (support.trans alpha).injective (le_refl s)
  have hactual :
      fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
          (fun a ↦ alpha (support a))
          (fun a ↦ syndromeWeight alpha (support a))
          (fun a ↦ u₀ (support a) + z * u₁ (support a) -
            P.eval (alpha (support a))) =
        BCHKSFrobeniusRectangularHankelAudit6401.twoLaneSupportSyndromeMatrix
          keyFirstLaneRows6401 keyFirstLaneRows6401 s alphaS d₀ d₁ := by
    ext row col
    cases row <;> rfl
  rw [hactual, hrect, hsquare]
theorem ownerErrorStack_rank_eq_of_goodFixedMinor6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat)
    (rows : GenericRankMinorRow6401 rho → FullTwoLaneKeyRow6401)
    (cols : GenericRankMinorRow6401 rho → Fin keyErrors6401)
    (hs : s ≤ keyErrors6401)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0)
    (hdet : Polynomial.eval z
      ((fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).submatrix
        rows cols).det ≠ 0)
    (hrankUpper :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a ↦ alpha (support a))
        (fun a ↦ syndromeWeight alpha (support a))
        (fun a ↦ u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a)))).rank ≤ rho) :
    (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
      (fun a ↦ alpha (support a))
      (fun a ↦ syndromeWeight alpha (support a))
      (fun a ↦ u₀ (support a) + z * u₁ (support a) -
        P.eval (alpha (support a)))).rank = rho := by
  classical
  let Sym := (fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).map
    (Polynomial.evalRingHom z)
  have hminor : (Sym.submatrix rows cols).det ≠ 0 := by
    change (((fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).map
      (Polynomial.evalRingHom z)).submatrix rows cols).det ≠ 0
    rw [← eval_submatrix_det]
    exact hdet
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hminor
  have hminorRank : (Sym.submatrix rows cols).rank = rho := by
    calc
      _ = Fintype.card (GenericRankMinorRow6401 rho) :=
        LinearIndependent.rank_matrix hli
      _ = rho := by
        simp only [GenericRankMinorRow6401, Fintype.card_sum,
          Fintype.card_fin]
        exact genericRankMinorRows_add6401 rho
  have hsymLower : rho ≤ Sym.rank := by
    have hsub := Matrix.rank_submatrix_le Sym rows cols
    rwa [hminorRank] at hsub
  have hrankEq := fullTwoLaneKeyMatrixZ_eval_rank_eq_ownerErrorStack6401
    sigma alpha u₀ u₁ hfixed hs z hz P hPcheck support hout
  apply Nat.le_antisymm hrankUpper
  rw [← hrankEq]
  exact hsymLower
theorem ownerErrorStack_rank_eq_of_goodPrefixMinor6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401) (hrhoS : rho ≤ s)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401)
    (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0)
    (hrankUpper :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a ↦ alpha (support a))
        (fun a ↦ syndromeWeight alpha (support a))
        (fun a ↦ u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a)))).rank ≤ rho) :
    (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
      (fun a ↦ alpha (support a))
      (fun a ↦ syndromeWeight alpha (support a))
      (fun a ↦ u₀ (support a) + z * u₁ (support a) -
        P.eval (alpha (support a)))).rank = rho := by
  classical
  let Full := fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
    (fun a ↦ alpha (support a))
    (fun a ↦ syndromeWeight alpha (support a))
    (fun a ↦ u₀ (support a) + z * u₁ (support a) -
      P.eval (alpha (support a)))
  have hmatrix :=
    genericRankKeyMinorZ_eval_eq_ownerErrorPrefixSubmatrix6401
      sigma alpha u₀ u₁ hfixed rho hrho hrhoS frobeniusRow z hz P
      hPcheck support hout
  have hminor :
      (Full.submatrix (genericRankSelectedRow6401 rho frobeniusRow)
        (fun col ↦ Fin.castLE hrhoS
          (genericRankMinorColumnEquiv6401 rho col))).det ≠ 0 := by
    rw [← hmatrix]
    rw [← eval_polynomialMatrix_det]
    exact hdet
  apply Nat.le_antisymm hrankUpper
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hminor
  have hminorRank :
      (Full.submatrix (genericRankSelectedRow6401 rho frobeniusRow)
        (fun col ↦ Fin.castLE hrhoS
          (genericRankMinorColumnEquiv6401 rho col))).rank = rho := by
    calc
      _ = Fintype.card (GenericRankMinorRow6401 rho) :=
        LinearIndependent.rank_matrix hli
      _ = rho := by
        simp only [GenericRankMinorRow6401, Fintype.card_sum,
          Fintype.card_fin]
        exact genericRankMinorRows_add6401 rho
  have hsub := Matrix.rank_submatrix_le Full
    (genericRankSelectedRow6401 rho frobeniusRow)
    (fun col ↦ Fin.castLE hrhoS
      (genericRankMinorColumnEquiv6401 rho col))
  rwa [hminorRank] at hsub
theorem genericRank_exactSupport_keySystem6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support → u₀ i + z * u₁ i = 0)
    (c : Fin rho → F)
    (hroots : ∀ a,
      (locatorPolynomial c).eval (alpha (support a)) = 0) :
    ((genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow).map (Polynomial.evalRingHom z)).mulVec
        (fun j => c (genericRankMinorColumnEquiv6401 rho j)) =
      fun row => Polynomial.eval z
        (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow row) := by
  classical
  let alphaS : Fin rho → F := fun a => alpha (support a)
  let E : Fin rho → F := fun a => u₀ (support a) + z * u₁ (support a)
  let beta : Fin rho → F := fun a => syndromeWeight alpha (support a)
  let d₀ : Fin rho → F := fun a => beta a * E a
  let d₁ : Fin rho → F := fun a => beta a * sigma (E a)
  let Full := fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
    alphaS beta E
  have hkey₀ :
      (supportSyndromeMatrix keyFirstLaneRows6401 rho alphaS d₀).mulVec c =
        supportKeyRhs alphaS d₀ :=
    locator_keyEquation alphaS d₀ c hroots
  have hkey₁ :
      (supportSyndromeMatrix keyFirstLaneRows6401 rho alphaS d₁).mulVec c =
        supportKeyRhs alphaS d₁ :=
    locator_keyEquation alphaS d₁ c hroots
  have hFull : Full.mulVec c = fun row =>
      match row with
      | Sum.inl a => supportKeyRhs alphaS d₀ a
      | Sum.inr b => supportKeyRhs alphaS d₁ b := by
    funext row
    cases row with
    | inl a =>
        exact congrFun hkey₀ a
    | inr b =>
        exact congrFun hkey₁ b
  rw [genericRankKeyMinorZ_eval_eq_supportSubmatrix6401
    sigma alpha u₀ u₁ rho frobeniusRow z hz support hout]
  rw [Matrix.submatrix_mulVec_equiv]
  have hccomp :
      (fun j => c (genericRankMinorColumnEquiv6401 rho j)) ∘
          (genericRankMinorColumnEquiv6401 rho).symm = c := by
    funext j
    simp
  rw [hccomp]
  funext row
  change (Full.mulVec c) (genericRankSelectedRow6401 rho frobeniusRow row) = _
  rw [hFull]
  cases row with
  | inl a =>
      rw [genericRankKeyRhsZ_eval6401 sigma alpha u₀ u₁ rho
        frobeniusRow z hz]
      have hmom := weightedSyndrome_eq_supportSyndrome alpha
        (fun i => u₀ i + z * u₁ i) support hout (a.1 + rho)
      simpa [Full, alphaS, beta, E, d₀, supportKeyRhs,
        genericRankSelectedRow6401, mul_assoc] using (congrArg Neg.neg hmom).symm
  | inr b =>
      rw [genericRankKeyRhsZ_eval6401 sigma alpha u₀ u₁ rho
        frobeniusRow z hz]
      have hsigmaOut : ∀ i, i ∉ Set.range support →
          sigma (u₀ i + z * u₁ i) = 0 := by
        intro i hi
        rw [hout i hi, map_zero]
      have hmom := weightedSyndrome_eq_supportSyndrome alpha
        (fun i => sigma (u₀ i + z * u₁ i)) support hsigmaOut
        ((frobeniusRow b).1 + rho)
      simpa [Full, alphaS, beta, E, d₁, supportKeyRhs,
        genericRankSelectedRow6401, mul_assoc] using (congrArg Neg.neg hmom).symm
theorem genericRank_exactSupport_productLocator_keySystem6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support → u₀ i + z * u₁ i = 0) :
    ((genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow).map (Polynomial.evalRingHom z)).mulVec
        (fun j => exactSupportLocatorCoefficients
          (fun a => alpha (support a))
          (genericRankMinorColumnEquiv6401 rho j)) =
      fun row => Polynomial.eval z
        (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow row) := by
  apply genericRank_exactSupport_keySystem6401
    sigma alpha u₀ u₁ rho frobeniusRow z hz support hout
  intro a
  exact locatorPolynomial_exactSupport_root
    (fun x => alpha (support x)) a
theorem genericRank_ownerError_productLocator_keySystem6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z : F) (hz : sigma z = z ^ q6401)
    (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0) :
    ((genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow).map (Polynomial.evalRingHom z)).mulVec
        (fun j => exactSupportLocatorCoefficients
          (fun a => alpha (support a))
          (genericRankMinorColumnEquiv6401 rho j)) =
      fun row => Polynomial.eval z
        (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow row) := by
  classical
  let alphaS : Fin rho → F := fun a => alpha (support a)
  let E : iota → F := fun i =>
    u₀ i + z * u₁ i - P.eval (alpha i)
  let ES : Fin rho → F := fun a => E (support a)
  let beta : Fin rho → F := fun a => syndromeWeight alpha (support a)
  let d₀ : Fin rho → F := fun a => beta a * ES a
  let d₁ : Fin rho → F := fun a => beta a * sigma (ES a)
  let c : Fin rho → F := exactSupportLocatorCoefficients alphaS
  let Full := fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
    alphaS beta ES
  have hroots : ∀ a, (locatorPolynomial c).eval (alphaS a) = 0 := by
    intro a
    exact locatorPolynomial_exactSupport_root alphaS a
  have hkey₀ :
      (supportSyndromeMatrix keyFirstLaneRows6401 rho alphaS d₀).mulVec c =
        supportKeyRhs alphaS d₀ :=
    locator_keyEquation alphaS d₀ c hroots
  have hkey₁ :
      (supportSyndromeMatrix keyFirstLaneRows6401 rho alphaS d₁).mulVec c =
        supportKeyRhs alphaS d₁ :=
    locator_keyEquation alphaS d₁ c hroots
  have hFull : Full.mulVec c = fun row =>
      match row with
      | Sum.inl a => supportKeyRhs alphaS d₀ a
      | Sum.inr b => supportKeyRhs alphaS d₁ b := by
    funext row
    cases row with
    | inl a => exact congrFun hkey₀ a
    | inr b => exact congrFun hkey₁ b
  have hu : ∀ i, u₀ i + z * u₁ i = P.eval (alpha i) + E i := by
    intro i
    dsimp [E]
    ring
  have hred : keyFirstLaneRows6401 + keyErrors6401 =
      keyRedundancy6401 := by native_decide
  rw [genericRankKeyMinorZ_eval_eq_ownerErrorSubmatrix6401
    sigma alpha u₀ u₁ hfixed rho hrho frobeniusRow z hz P hPcheck
    support hout]
  rw [Matrix.submatrix_mulVec_equiv]
  have hccomp :
      (fun j => c (genericRankMinorColumnEquiv6401 rho j)) ∘
          (genericRankMinorColumnEquiv6401 rho).symm = c := by
    funext j
    simp
  rw [hccomp]
  funext row
  change (Full.mulVec c) (genericRankSelectedRow6401 rho frobeniusRow row) = _
  rw [hFull]
  cases row with
  | inl a =>
      let j := a.1 + rho
      have hj : j < keyRedundancy6401 := by
        have ha := a.isLt
        have hm := Nat.min_le_left keyFirstLaneRows6401 rho
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P E
        (fun i => u₀ i + z * u₁ i) j hu (hPcheck j hj)
      have hmom := weightedSyndrome_eq_supportSyndrome alpha E support hout j
      rw [genericRankKeyRhsZ_eval6401 sigma alpha u₀ u₁ rho
        frobeniusRow z hz]
      simpa [Full, alphaS, beta, ES, d₀, supportKeyRhs,
        genericRankSelectedRow6401, E, j, mul_assoc] using
        (congrArg Neg.neg (hrecv.trans hmom)).symm
  | inr b =>
      let j := (frobeniusRow b).1 + rho
      have hj : j < keyRedundancy6401 := by
        have hb := (frobeniusRow b).isLt
        dsimp [j]
        omega
      have hrecv := weightedSyndrome_received_eq_error alpha P E
        (fun i => u₀ i + z * u₁ i) j hu (hPcheck j hj)
      have hsigma :
          weightedSyndrome alpha
              (fun i => sigma (u₀ i + z * u₁ i)) j =
            weightedSyndrome alpha (fun i => sigma (E i)) j := by
        calc
          _ = sigma (weightedSyndrome alpha
                (fun i => u₀ i + z * u₁ i) j) :=
            (sigma_weightedSyndrome_fixed6401 sigma alpha hfixed _ j).symm
          _ = sigma (weightedSyndrome alpha E j) := congrArg sigma hrecv
          _ = _ := sigma_weightedSyndrome_fixed6401 sigma alpha hfixed E j
      have hsigmaOut : ∀ i, i ∉ Set.range support → sigma (E i) = 0 := by
        intro i hi
        rw [show E i = 0 by simpa [E] using hout i hi, map_zero]
      have hmom := weightedSyndrome_eq_supportSyndrome alpha
        (fun i => sigma (E i)) support hsigmaOut j
      rw [genericRankKeyRhsZ_eval6401 sigma alpha u₀ u₁ rho
        frobeniusRow z hz]
      simpa [Full, alphaS, beta, ES, d₁, supportKeyRhs,
        genericRankSelectedRow6401, E, j, mul_assoc] using
        (congrArg Neg.neg (hsigma.trans hmom)).symm
theorem genericRankKeyMinorZ_det_degree6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) :
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow).det.natDegree ≤
        genericRankMinorDegreeCap6401 rho := by
  calc
    _ ≤ ∑ row : GenericRankMinorRow6401 rho,
          genericRankMinorRowCap6401 rho row :=
      natDegree_det_le_sum_rowCaps _ (genericRankMinorRowCap6401 rho)
        (genericRankKeyMinorZ_entry_degree6401
          sigma alpha u₀ u₁ rho frobeniusRow)
    _ = _ := genericRankMinorRowCap_sum6401 rho
theorem genericRank_fixedMinor_nonzero_of_anchor6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (z₀ : F)
    (hanchor : Polynomial.eval z₀
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0) :
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow).det ≠ 0 := by
  intro hzero
  rw [hzero, Polynomial.eval_zero] at hanchor
  exact hanchor rfl
theorem genericRankKeyCramerNumerator_degree6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (j : GenericRankMinorRow6401 rho) :
    ((genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow).cramer
      (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
      j).natDegree ≤ genericRankMinorDegreeCap6401 rho := by
  rw [Matrix.cramer_apply]
  calc
    _ ≤ ∑ row : GenericRankMinorRow6401 rho,
          genericRankMinorRowCap6401 rho row := by
      apply natDegree_det_le_sum_rowCaps
      intro row col
      by_cases hcol : col = j
      · subst col
        simpa [Matrix.updateCol] using
          genericRankKeyRhsZ_degree6401
            sigma alpha u₀ u₁ rho frobeniusRow row
      · simpa [Matrix.updateCol, hcol] using
          genericRankKeyMinorZ_entry_degree6401
            sigma alpha u₀ u₁ rho frobeniusRow row col
    _ = _ := genericRankMinorRowCap_sum6401 rho
noncomputable def genericRankClearedLocatorCoordinate6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (x : F) : F[X] :=
  clearedLocatorCoordinate
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (fun j => (genericRankMinorColumnEquiv6401 rho j).1) rho x
theorem genericRankClearedLocatorCoordinate_degree6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401) (x : F) :
    (genericRankClearedLocatorCoordinate6401 sigma alpha u₀ u₁ rho
      frobeniusRow x).natDegree ≤ genericRankMinorDegreeCap6401 rho := by
  apply clearedLocatorCoordinate_natDegree_le
  · exact genericRankKeyMinorZ_det_degree6401
      sigma alpha u₀ u₁ rho frobeniusRow
  · exact genericRankKeyCramerNumerator_degree6401
      sigma alpha u₀ u₁ rho frobeniusRow
theorem clearedLocatorCoordinate_eval_eq_det_mul
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (b : I → F[X]) (pow : I → Nat)
    (t : Nat) (x z : F) (c : I → F)
    (hdet : Polynomial.eval z M.det ≠ 0)
    (hsys : (M.map (Polynomial.evalRingHom z)).mulVec c =
      fun i => Polynomial.eval z (b i)) :
    Polynomial.eval z (clearedLocatorCoordinate M b pow t x) =
      Polynomial.eval z M.det *
        (x ^ t + ∑ j, c j * x ^ pow j) := by
  classical
  let Az := M.map (Polynomial.evalRingHom z)
  let bz : I → F := fun i => Polynomial.eval z (b i)
  have hdet' : Az.det ≠ 0 := by
    change (M.map (Polynomial.evalRingHom z)).det ≠ 0
    rw [← eval_polynomialMatrix_det M z]
    exact hdet
  have hcr := cramer_eq_det_smul_of_mulVec_eq Az bz c hdet' hsys
  simp only [clearedLocatorCoordinate, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_finsetSum]
  rw [show Polynomial.eval z M.det = Az.det by
      exact eval_polynomialMatrix_det M z]
  simp_rw [eval_polynomialMatrix_cramer M b z]
  rw [hcr]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ j : I, Az.det * c j * x ^ pow j) =
      Az.det * (∑ j : I, c j * x ^ pow j) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring]
  rw [← mul_add]
theorem genericRank_exactSupport_locatorSum6401
    {F : Type*} [Field F] (rho : Nat) (a : Fin rho → F) (x : F) :
    x ^ rho + ∑ j : GenericRankMinorRow6401 rho,
      exactSupportLocatorCoefficients a
          (genericRankMinorColumnEquiv6401 rho j) *
        x ^ (genericRankMinorColumnEquiv6401 rho j).1 =
      (exactSupportLocator a).eval x := by
  rw [← locatorPolynomial_exactSupportCoefficients a,
    eval_locatorPolynomial]
  congr 1
  simpa using Equiv.sum_comp (genericRankMinorColumnEquiv6401 rho)
    (fun j : Fin rho => exactSupportLocatorCoefficients a j * x ^ j.1)
theorem genericRankClearedLocatorCoordinate_eval_exactSupport6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (z : F) (hz : sigma z = z ^ q6401)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support → u₀ i + z * u₁ i = 0)
    (x : F)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0) :
    Polynomial.eval z
        (genericRankClearedLocatorCoordinate6401 sigma alpha u₀ u₁ rho
          frobeniusRow x) =
      Polynomial.eval z
          (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
            frobeniusRow).det *
        (exactSupportLocator (fun a => alpha (support a))).eval x := by
  unfold genericRankClearedLocatorCoordinate6401
  rw [clearedLocatorCoordinate_eval_eq_det_mul
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (fun j => (genericRankMinorColumnEquiv6401 rho j).1)
    rho x z
    (fun j => exactSupportLocatorCoefficients
      (fun a => alpha (support a))
      (genericRankMinorColumnEquiv6401 rho j)) hdet
    (genericRank_exactSupport_productLocator_keySystem6401
      sigma alpha u₀ u₁ rho frobeniusRow z hz support hout)]
  rw [genericRank_exactSupport_locatorSum6401]
theorem genericRankClearedLocatorCoordinate_eval_ownerError6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0)
    (x : F)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0) :
    Polynomial.eval z
        (genericRankClearedLocatorCoordinate6401 sigma alpha u₀ u₁ rho
          frobeniusRow x) =
      Polynomial.eval z
          (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
            frobeniusRow).det *
        (exactSupportLocator (fun a => alpha (support a))).eval x := by
  unfold genericRankClearedLocatorCoordinate6401
  rw [clearedLocatorCoordinate_eval_eq_det_mul
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (fun j => (genericRankMinorColumnEquiv6401 rho j).1)
    rho x z
    (fun j => exactSupportLocatorCoefficients
      (fun a => alpha (support a))
      (genericRankMinorColumnEquiv6401 rho j)) hdet
    (genericRank_ownerError_productLocator_keySystem6401
      sigma alpha u₀ u₁ hfixed rho hrho frobeniusRow z hz P hPcheck
      support hout)]
  rw [genericRank_exactSupport_locatorSum6401]
theorem genericRankClearedLocatorCoordinate_ownerError_iff6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0)
    (i : iota)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0) :
    Polynomial.eval z
        (genericRankClearedLocatorCoordinate6401 sigma alpha u₀ u₁ rho
          frobeniusRow (alpha i)) = 0 ↔
      i ∈ Set.range support := by
  rw [genericRankClearedLocatorCoordinate_eval_ownerError6401
    sigma alpha u₀ u₁ hfixed rho hrho frobeniusRow z hz P hPcheck
    support hout (alpha i) hdet,
    mul_eq_zero, exactSupportLocator_eval_eq_zero_iff]
  have hrange :
      alpha i ∈ Set.range (fun a => alpha (support a)) ↔
        i ∈ Set.range support := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, alpha.injective ha⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  rw [hrange]
  simp [hdet]
theorem genericRankClearedLocatorCoordinate_eq_zero_iff_mem_support6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F)
    (halpha : Function.Injective alpha) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (z : F) (hz : sigma z = z ^ q6401)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support → u₀ i + z * u₁ i = 0)
    (i : iota)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0) :
    Polynomial.eval z
        (genericRankClearedLocatorCoordinate6401 sigma alpha u₀ u₁ rho
          frobeniusRow (alpha i)) = 0 ↔
      i ∈ Set.range support := by
  rw [genericRankClearedLocatorCoordinate_eval_exactSupport6401
    sigma alpha u₀ u₁ rho frobeniusRow z hz support hout (alpha i) hdet,
    mul_eq_zero, exactSupportLocator_eval_eq_zero_iff]
  have hrange :
      alpha i ∈ Set.range (fun a => alpha (support a)) ↔
        i ∈ Set.range support := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, halpha ha⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  rw [hrange]
  simp [hdet]
noncomputable def exactSupportFinset
    {iota : Type*} [Fintype iota] [DecidableEq iota] {rho : Nat}
    (support : Fin rho ↪ iota) : Finset iota :=
  Finset.univ.map support
theorem mem_exactSupportFinset_iff
    {iota : Type*} [Fintype iota] [DecidableEq iota] {rho : Nat}
    (support : Fin rho ↪ iota) (i : iota) :
    i ∈ exactSupportFinset support ↔ i ∈ Set.range support := by
  simp [exactSupportFinset]
theorem exactSupportFinset_card
    {iota : Type*} [Fintype iota] [DecidableEq iota] {rho : Nat}
    (support : Fin rho ↪ iota) :
    (exactSupportFinset support).card = rho := by
  simp [exactSupportFinset]
theorem ownerPolynomial_checkWindow6401
    {F iota : Type*} [Field F] [Fintype iota]
    (hambient : Fintype.card iota = n6401) (P : F[X])
    (hPdegree : P.natDegree ≤ ownerDegreeCap6401) :
    ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1 := by
  intro j hj
  rw [hambient]
  norm_num [n6401, ownerDegreeCap6401, keyRedundancy6401] at hPdegree hj ⊢
  omega
theorem genericRankFixedMinor_exactSupport_rootIncidence6401
    {F iota : Type} [Field F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (challenges : Finset F) (P : F → F[X])
    (support : F → Fin rho ↪ iota)
    (hz : ∀ z ∈ challenges, sigma z = z ^ q6401)
    (hPdegree : ∀ z ∈ challenges,
      (P z).natDegree ≤ ownerDegreeCap6401)
    (hout : ∀ z ∈ challenges, ∀ i,
      i ∉ Set.range (support z) →
        u₀ i + z * u₁ i - (P z).eval (alpha i) = 0)
    (hambient : Fintype.card iota = n6401)
    (hZ : BCHKSTwoFrobeniusWeakCurveSeed6401.weakCurveSeedInput6401 ≤
      challenges.card)
    (hDelta :
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0) :
    let Delta := (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow).det
    let A : F → Finset iota := fun z => exactSupportFinset (support z)
    let L : iota → F[X] := fun i =>
      genericRankClearedLocatorCoordinate6401 sigma alpha u₀ u₁ rho
        frobeniusRow (alpha i)
    let S := challenges.filter fun z => Polynomial.eval z Delta ≠ 0
    let c := rho - (fixedLocatorCoordinates L).card
    c ≤ keyVariableErrorCap6401 ∧
      (S.biUnion A).card ≤ rho + (S.card - 1) * c := by
  dsimp only
  apply fixedMinor_exactSupport_rootIncidence6401 rho hrho challenges
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow).det
    (fun z => exactSupportFinset (support z))
    (fun i => genericRankClearedLocatorCoordinate6401
      sigma alpha u₀ u₁ rho frobeniusRow (alpha i))
    hambient hZ hDelta
    (genericRankKeyMinorZ_det_degree6401
      sigma alpha u₀ u₁ rho frobeniusRow)
  · intro z hzgood
    exact exactSupportFinset_card (support z)
  · intro z hzgood i hi
    have hzmem : z ∈ challenges := (Finset.mem_filter.mp hzgood).1
    apply (genericRankClearedLocatorCoordinate_ownerError_iff6401
      sigma alpha u₀ u₁ hfixed rho hrho frobeniusRow z
      (hz z hzmem) (P z)
      (ownerPolynomial_checkWindow6401 hambient (P z) (hPdegree z hzmem))
      (support z) (hout z hzmem) i
      (Finset.mem_filter.mp hzgood).2).2
    exact (mem_exactSupportFinset_iff (support z) i).1 hi
  · intro i
    exact genericRankClearedLocatorCoordinate_degree6401
      sigma alpha u₀ u₁ rho frobeniusRow (alpha i)
  · intro z hzgood i hi
    have hzmem : z ∈ challenges := (Finset.mem_filter.mp hzgood).1
    have hLi : genericRankClearedLocatorCoordinate6401
        sigma alpha u₀ u₁ rho frobeniusRow (alpha i) = 0 := by
      simpa [fixedLocatorCoordinates] using hi
    apply (mem_exactSupportFinset_iff (support z) i).2
    apply (genericRankClearedLocatorCoordinate_ownerError_iff6401
      sigma alpha u₀ u₁ hfixed rho hrho frobeniusRow z
      (hz z hzmem) (P z)
      (ownerPolynomial_checkWindow6401 hambient (P z) (hPdegree z hzmem))
      (support z) (hout z hzmem) i
      (Finset.mem_filter.mp hzgood).2).1
    rw [hLi, Polynomial.eval_zero]
theorem genericRankFixedMinor_exactSupport_commonCore6401
    {F iota : Type} [Field F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (challenges owners : Finset F) (P : F → F[X])
    (support : F → Fin rho ↪ iota)
    (hz : ∀ z ∈ challenges, sigma z = z ^ q6401)
    (hPdegree : ∀ z ∈ challenges,
      (P z).natDegree ≤ ownerDegreeCap6401)
    (hout : ∀ z ∈ challenges, ∀ i,
      i ∉ Set.range (support z) →
        u₀ i + z * u₁ i - (P z).eval (alpha i) = 0)
    (hambient : Fintype.card iota = n6401)
    (hZ : BCHKSTwoFrobeniusWeakCurveSeed6401.weakCurveSeedInput6401 ≤
      challenges.card)
    (hDelta :
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0)
    (hownersSubset : owners ⊆
      challenges.filter fun z => Polynomial.eval z
        (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow).det ≠ 0)
    (hownersCard : owners.card =
      BCHKSTwoFrobeniusWeakCurveSeed6401.weakCurveOutput6401) :
    let A : F → Finset iota := fun z => exactSupportFinset (support z)
    147530 ≤ (Finset.univ \ owners.biUnion A).card ∧
      ownerDegreeCap6401 + 1 ≤
        (Finset.univ \ owners.biUnion A).card := by
  dsimp only
  apply fixedMinor_exactSupport_commonCore6401 rho hrho challenges owners
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow).det
    (fun z => exactSupportFinset (support z))
    (fun i => genericRankClearedLocatorCoordinate6401
      sigma alpha u₀ u₁ rho frobeniusRow (alpha i))
    hambient hZ hDelta
    (genericRankKeyMinorZ_det_degree6401
      sigma alpha u₀ u₁ rho frobeniusRow)
  · intro z hzgood
    exact exactSupportFinset_card (support z)
  · intro z hzgood i hi
    have hzmem : z ∈ challenges := (Finset.mem_filter.mp hzgood).1
    apply (genericRankClearedLocatorCoordinate_ownerError_iff6401
      sigma alpha u₀ u₁ hfixed rho hrho frobeniusRow z
      (hz z hzmem) (P z)
      (ownerPolynomial_checkWindow6401 hambient (P z) (hPdegree z hzmem))
      (support z) (hout z hzmem) i
      (Finset.mem_filter.mp hzgood).2).2
    exact (mem_exactSupportFinset_iff (support z) i).1 hi
  · intro i
    exact genericRankClearedLocatorCoordinate_degree6401
      sigma alpha u₀ u₁ rho frobeniusRow (alpha i)
  · intro z hzgood i hi
    have hzmem : z ∈ challenges := (Finset.mem_filter.mp hzgood).1
    have hLi : genericRankClearedLocatorCoordinate6401
        sigma alpha u₀ u₁ rho frobeniusRow (alpha i) = 0 := by
      simpa [fixedLocatorCoordinates] using hi
    apply (mem_exactSupportFinset_iff (support z) i).2
    apply (genericRankClearedLocatorCoordinate_ownerError_iff6401
      sigma alpha u₀ u₁ hfixed rho hrho frobeniusRow z
      (hz z hzmem) (P z)
      (ownerPolynomial_checkWindow6401 hambient (P z) (hPdegree z hzmem))
      (support z) (hout z hzmem) i
      (Finset.mem_filter.mp hzgood).2).1
    rw [hLi, Polynomial.eval_zero]
  · exact hownersSubset
  · exact hownersCard
theorem genericRankClearedLocatorCoordinate_root6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (x z : F) (c : GenericRankMinorRow6401 rho → F)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det ≠ 0)
    (hsys :
      ((genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).map (Polynomial.evalRingHom z)).mulVec c =
          fun i => Polynomial.eval z
            (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho
              frobeniusRow i))
    (hroot : x ^ rho + ∑ j : GenericRankMinorRow6401 rho,
      c j * x ^ (genericRankMinorColumnEquiv6401 rho j).1 = 0) :
    Polynomial.eval z
      (genericRankClearedLocatorCoordinate6401 sigma alpha u₀ u₁ rho
        frobeniusRow x) = 0 := by
  exact clearedLocatorCoordinate_root
    (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (genericRankKeyRhsZ6401 sigma alpha u₀ u₁ rho frobeniusRow)
    (fun j => (genericRankMinorColumnEquiv6401 rho j).1)
    rho x z c hdet hsys hroot
end BCHKSFrobeniusGenericMinor6401
end ProximityPrize.SubmissionLower
