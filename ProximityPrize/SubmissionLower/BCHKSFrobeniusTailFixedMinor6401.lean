import ProximityPrize.SubmissionLower.BCHKSFrobeniusTailGlobalKernel6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusPhiCofactorSection6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusTailFixedMinor6401
open Polynomial
open BCHKSFrobeniusPhiCofactorSection6401
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusTailCofactorSemantics6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSMixedHermiteRowSpan6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section Abstract
variable {F Row C : Type*} [Field F] [Fintype Row] [DecidableEq Row]
  [Fintype C]
noncomputable def fixedMinorKernelVector6401
    (M : Matrix Row C F[X]) (h : Nat) (col : Fin h ⊕ Unit ≃ C)
    (row : Fin h → Row) : C → F[X] :=
  fun c ↦ globalCramerVector6401 h (M.submatrix id col) row (col.symm c)
theorem fixedMinorKernelVector_ne_zero6401
    (M : Matrix Row C F[X]) (h : Nat) (col : Fin h ⊕ Unit ≃ C)
    (row : Fin h → Row)
    (hdet : (pivotMinor6401 h (M.submatrix id col) row).det ≠ 0) :
    fixedMinorKernelVector6401 M h col row ≠ 0 := by
  intro hz
  apply globalCramerVector_ne_zero6401 h (M.submatrix id col) row hdet
  funext c
  have hc := congrFun hz (col c)
  simpa [fixedMinorKernelVector6401] using hc
theorem fixedMinorKernelVector_mulVec_eq_zero6401
    (M : Matrix Row C F[X]) (h : Nat) (col : Fin h ⊕ Unit ≃ C)
    (row : Fin h → Row) (hrow : Function.Injective row)
    (hrank : ((M.submatrix id col).map
      (algebraMap F[X] (FractionRing F[X]))).rank ≤ h)
    (hdet : (pivotMinor6401 h (M.submatrix id col) row).det ≠ 0) :
    M.mulVec (fixedMinorKernelVector6401 M h col row) = 0 := by
  have hk := mulVec_globalCramerVector_eq_zero_of_fractionRank_le6401
    h (M.submatrix id col) row hrow hrank hdet
  rw [Matrix.submatrix_mulVec_equiv] at hk
  exact hk
theorem fixedMinorKernelVector_natDegree_le6401
    (M : Matrix Row C F[X]) (h D : Nat) (col : Fin h ⊕ Unit ≃ C)
    (row : Fin h → Row)
    (hentry : ∀ i c, (M (row i) c).natDegree ≤ D) (c : C) :
    (fixedMinorKernelVector6401 M h col row c).natDegree ≤ h * D := by
  unfold fixedMinorKernelVector6401
  apply globalCramerVector_natDegree_le6401
    h D (M.submatrix id col) row
  intro i j
  exact hentry i (col j)
theorem zeroSpecializations_fixedMinorKernel_card_le6401
    [DecidableEq F]
    (S : Finset F) (V : C → F[X]) (D : Nat) (hV : V ≠ 0)
    (hdegree : ∀ c, (V c).natDegree ≤ D) :
    (S.filter fun z ↦ (fun c ↦ Polynomial.eval z (V c)) = 0).card
      ≤ D := by
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hV
  have hsub :
      (S.filter fun z ↦ (fun j ↦ Polynomial.eval z (V j)) = 0) ⊆
        S.filter fun z ↦ Polynomial.eval z (V c) = 0 := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, congrFun hz.2 c⟩
  exact (Finset.card_le_card hsub).trans
    ((card_filter_eval_eq_zero_le_natDegree S (V c) hc).trans
      (hdegree c))
theorem fractionRank_le_of_all_maximalMinors_zero6401
    [DecidableEq C]
    (M : Matrix Row C F[X]) (h : Nat)
    (hcard : Fintype.card C = h + 1)
    (hminor : ∀ rows : C → Row, (M.submatrix rows id).det = 0) :
    (M.map (algebraMap F[X] (FractionRing F[X]))).rank ≤ h := by
  let f := algebraMap F[X] (FractionRing F[X])
  let MR := M.map f
  have hdep : ¬ LinearIndependent (FractionRing F[X]) MR.col := by
    intro hli
    have hrow : LinearIndependent (FractionRing F[X]) MR.transpose.row := by
      simpa [Matrix.transpose_apply] using hli
    obtain ⟨rows, hdet⟩ :=
      exists_columns_det_ne_zero_of_rows_linearIndependent MR.transpose hrow
    apply hdet
    have hz := hminor rows
    have hmap : f ((M.submatrix rows id).det) =
        ((MR.transpose.submatrix id rows).det) := by
      rw [RingHom.map_det]
      rw [← Matrix.det_transpose]
      congr 1
    rw [hz, map_zero] at hmap
    exact hmap.symm
  rw [Matrix.rank_eq_finrank_span_cols]
  change Set.finrank (FractionRing F[X]) (Set.range MR.col) ≤ h
  have hne : Fintype.card C ≠
      Set.finrank (FractionRing F[X]) (Set.range MR.col) := by
    intro heq
    exact hdep (linearIndependent_iff_card_eq_finrank_span.mpr heq)
  have hle : Set.finrank (FractionRing F[X]) (Set.range MR.col) ≤
      Fintype.card C :=
    finrank_range_le_card (R := FractionRing F[X]) MR.col
  rw [hcard] at hne hle
  omega
end Abstract
section ReceivedTail
variable {F I : Type*} [Field F] [Fintype I] [Nonempty I]
  [DecidableEq I]
theorem receivedTailColumn_card_eq_corankOne6401 (d : Nat) :
    Fintype.card (Fin (d + 1) ⊕ Fin (d + 1)) = (2 * d + 1) + 1 := by
  simp
  omega
noncomputable def receivedTailFixedMinorVector6401
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d h : Nat)
    (col : Fin h ⊕ Unit ≃ (Fin (d + 1) ⊕ Fin (d + 1)))
    (row : Fin h → Fin (Fintype.card I - (k + d + 1))) :
    Fin (d + 1) ⊕ Fin (d + 1) → F[X] :=
  fixedMinorKernelVector6401
    (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d) h col row
theorem receivedTail_fractionRank_le_of_manyOwnerKernels6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d h : Nat)
    (hcard : Fintype.card (Fin (d + 1) ⊕ Fin (d + 1)) = h + 1)
    (S : Finset F) (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (kernel : F → (Fin (d + 1) ⊕ Fin (d + 1) → F))
    (hkernel : ∀ z ∈ S,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d).mulVec (kernel z) = 0)
    (hnonzero : ∀ z ∈ S, kernel z ≠ 0)
    (hmass : (d + 1) * (q + 1) < S.card) :
    ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).map
      (algebraMap F[X] (FractionRing F[X]))).rank ≤ h := by
  classical
  apply fractionRank_le_of_all_maximalMinors_zero6401
    (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d) h hcard
  intro rows
  exact receivedTailMinor_eq_zero_of_many_ownerKernels6401
    sigma alpha u₀ u₁ q k d S hsigma kernel hkernel hnonzero hmass rows
theorem receivedTail_fractionRank_le_corankOne_of_manyOwnerKernels6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d : Nat)
    (S : Finset F) (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (kernel : F → (Fin (d + 1) ⊕ Fin (d + 1) → F))
    (hkernel : ∀ z ∈ S,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u₀ i + z * u₁ i) k d).mulVec (kernel z) = 0)
    (hnonzero : ∀ z ∈ S, kernel z ≠ 0)
    (hmass : (d + 1) * (q + 1) < S.card) :
    ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).map
      (algebraMap F[X] (FractionRing F[X]))).rank ≤ 2 * d + 1 := by
  exact receivedTail_fractionRank_le_of_manyOwnerKernels6401
    sigma alpha u₀ u₁ q k d (2 * d + 1)
      (receivedTailColumn_card_eq_corankOne6401 d)
      S hsigma kernel hkernel hnonzero hmass
theorem receivedTailFixedMinor_properties6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d h : Nat) (hq : 1 ≤ q)
    (col : Fin h ⊕ Unit ≃ (Fin (d + 1) ⊕ Fin (d + 1)))
    (row : Fin h → Fin (Fintype.card I - (k + d + 1)))
    (hrow : Function.Injective row)
    (hrank : (((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
      id col).map
        (algebraMap F[X] (FractionRing F[X]))).rank ≤ h)
    (hdet : (pivotMinor6401 h
      ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
        id col) row).det ≠ 0)
    (S : Finset F) :
    let V := receivedTailFixedMinorVector6401
      sigma alpha u₀ u₁ q k d h col row
    V ≠ 0 ∧
      (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec V = 0 ∧
      (∀ c, (V c).natDegree ≤ h * q) ∧
      (S.filter fun z ↦
        (fun c ↦ Polynomial.eval z (V c)) = 0).card ≤ h * q := by
  dsimp only
  let M := receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d
  let V := receivedTailFixedMinorVector6401
    sigma alpha u₀ u₁ q k d h col row
  have hV : V ≠ 0 :=
    fixedMinorKernelVector_ne_zero6401 M h col row hdet
  have hVK : M.mulVec V = 0 :=
    fixedMinorKernelVector_mulVec_eq_zero6401 M h col row hrow hrank hdet
  have hentry : ∀ i c, (M (row i) c).natDegree ≤ q := by
    intro i c
    exact (receivedTailMatrixZ_entry_natDegree_le6401
      sigma alpha u₀ u₁ q k d (row i) c).trans (by
        cases c <;> simp [hq])
  have hdeg : ∀ c, (V c).natDegree ≤ h * q := by
    intro c
    exact fixedMinorKernelVector_natDegree_le6401 M h q col row hentry c
  exact ⟨hV, hVK, hdeg,
    zeroSpecializations_fixedMinorKernel_card_le6401 S V (h * q) hV hdeg⟩
theorem receivedTailFixedMinor_ownerSemantics6401
    [DecidableEq F]
    (sigma : F →+* F) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (q k d h : Nat) (hq : 1 ≤ q)
    (col : Fin h ⊕ Unit ≃ (Fin (d + 1) ⊕ Fin (d + 1)))
    (row : Fin h → Fin (Fintype.card I - (k + d + 1)))
    (hrow : Function.Injective row)
    (hrank : (((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
      id col).map
        (algebraMap F[X] (FractionRing F[X]))).rank ≤ h)
    (hdet : (pivotMinor6401 h
      ((receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).submatrix
        id col) row).det ≠ 0)
    (S : Finset F) (hsigma : ∀ z ∈ S, sigma z = z ^ q)
    (P : F → F[X]) (agreements : F → Finset I)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hagree : ∀ z ∈ S, ∀ i ∈ agreements z,
      (P z).eval (alpha i) = u₀ i + z * u₁ i)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hwindow : k + d < Fintype.card I)
    (hroots : ∀ z ∈ S, k + d < (agreements z).card) :
    let V := receivedTailFixedMinorVector6401
      sigma alpha u₀ u₁ q k d h col row
    S.card - h * q ≤
        (S.filter fun z ↦ (fun c ↦ Polynomial.eval z (V c)) ≠ 0).card ∧
      ∀ z ∈ S, (fun c ↦ Polynomial.eval z (V c)) ≠ 0 →
        ∃ A B : F[X],
          (A ≠ 0 ∨ B ≠ 0) ∧ A.natDegree ≤ d ∧
          B.natDegree ≤ d ∧
          TwoLaneFailureRelation sigma alpha
            (fun i ↦ u₀ i + z * u₁ i - (P z).eval (alpha i)) A B := by
  dsimp only
  let V := receivedTailFixedMinorVector6401
    sigma alpha u₀ u₁ q k d h col row
  change S.card - h * q ≤
        (S.filter fun z ↦ (fun c ↦ Polynomial.eval z (V c)) ≠ 0).card ∧
      ∀ z ∈ S, (fun c ↦ Polynomial.eval z (V c)) ≠ 0 →
        ∃ A B : F[X],
          (A ≠ 0 ∨ B ≠ 0) ∧ A.natDegree ≤ d ∧
          B.natDegree ≤ d ∧
          TwoLaneFailureRelation sigma alpha
            (fun i ↦ u₀ i + z * u₁ i - (P z).eval (alpha i)) A B
  have hprops := receivedTailFixedMinor_properties6401
    sigma alpha u₀ u₁ q k d h hq col row hrow hrank hdet S
  change V ≠ 0 ∧
      (receivedTailMatrixZ6401 sigma alpha u₀ u₁ q k d).mulVec V = 0 ∧
      (∀ c, (V c).natDegree ≤ h * q) ∧
      (S.filter fun z ↦
        (fun c ↦ Polynomial.eval z (V c)) = 0).card ≤ h * q at hprops
  rcases hprops with ⟨hV, hVK, hdeg, hbad⟩
  have hpartition :
      (S.filter fun z ↦ (fun c ↦ Polynomial.eval z (V c)) ≠ 0).card +
        (S.filter fun z ↦ (fun c ↦ Polynomial.eval z (V c)) = 0).card =
          S.card := by
    simpa only [not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := S) (fun z ↦ (fun c ↦ Polynomial.eval z (V c)) ≠ 0))
  constructor
  · omega
  · intro z hz hVz
    exact exists_nonzero_failurePair_of_globalTailKernel6401
      sigma alpha u₀ u₁ q k d V hVK z (hsigma z hz) hVz
        (P z) (agreements z) hfixed (hagree z hz)
        (hPdegree z hz) hwindow (hroots z hz)
end ReceivedTail
theorem receivedTail_corankOne_exceptionCap6401 :
    45015 * q6401 = 95913750081495 ∧
      95913750081495 < 80251881527475554 := by
  native_decide
end BCHKSFrobeniusTailFixedMinor6401
end ProximityPrize.SubmissionLower
