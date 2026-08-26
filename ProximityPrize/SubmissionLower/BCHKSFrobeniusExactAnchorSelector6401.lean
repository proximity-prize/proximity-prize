import ProximityPrize.SubmissionLower.BCHKSFrobeniusGlobalMaxRankFork6401
import ProximityPrize.SubmissionLower.BCHKSMixedHermiteRowSpan6400

/-!
# A sound prefix-column anchor for the global maximal-rank fork

At an owner whose actual support size and full two-lane rank are both `rho`,
the ordinary `54282` rows are independent.  Finite matroid extension selects
exactly `rho - 54282` literal Frobenius rows completing them.  Since all
`rho` support columns are then the prefix columns, this produces the fixed
minor required by the global Cramer/root-incidence argument.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusExactAnchorSelector6401

open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSFrobeniusGenericRankFork6401
open BCHKSFrobeniusGenericMinor6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSMixedHermiteRowSpan6400
open BCHKSGaoSpecializationCore6400

set_option maxHeartbeats 2500000
set_option maxRecDepth 1000000

/-- Generic two-block row completion, with the left block retained in its
given order and the complement selected from literal right-block rows. -/
theorem exists_rightRowSelector_of_leftIndependent_fullRank
    {F : Type*} [Field F] {m rho s : Nat} (hm : m ≤ rho)
    (M : Matrix (Fin m ⊕ Fin m) (Fin s) F)
    (hleft : LinearIndependent F (fun i : Fin m ↦ M (Sum.inl i)))
    (hrank : M.rank = rho) :
    ∃ rightRow : Fin (rho - m) → Fin m,
      LinearIndependent F (fun row : Fin m ⊕ Fin (rho - m) ↦
        match row with
        | Sum.inl i => M (Sum.inl i)
        | Sum.inr j => M (Sum.inr (rightRow j))) := by
  classical
  let jet : Fin m → (Fin s → F) := fun i ↦ M (Sum.inl i)
  let row : (Fin m ⊕ Fin m) → (Fin s → F) := fun q ↦ M q
  have hmem : ∀ i, jet i ∈ Submodule.span F (Set.range row) := by
    intro i
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  obtain ⟨chosen, hjet, hchosenLI, hspan⟩ :=
    exists_augmented_basisFinset jet row (by simpa [jet] using hleft) hmem
  have hchosenCard : chosen.card = rho := by
    calc
      chosen.card = Fintype.card {q // q ∈ chosen} := by simp
      _ = Module.finrank F
          (Submodule.span F
            (Set.range (fun q : {q // q ∈ chosen} ↦
              augmentedFamily jet row q.1))) :=
        linearIndependent_iff_card_eq_finrank_span.mp hchosenLI
      _ = Module.finrank F (Submodule.span F (Set.range row)) := by
        rw [hspan]
      _ = M.rank := by
        rw [M.rank_eq_finrank_span_row]
        rfl
      _ = rho := hrank
  have hnoDuplicate : ∀ i : Fin m,
      Sum.inr (Sum.inl i) ∉ chosen := by
    intro i hi
    let a : {q // q ∈ chosen} := ⟨Sum.inl i, hjet i⟩
    let b : {q // q ∈ chosen} := ⟨Sum.inr (Sum.inl i), hi⟩
    have hab : augmentedFamily jet row a.1 =
        augmentedFamily jet row b.1 := by
      rfl
    have heq : a = b := hchosenLI.injective hab
    have : (Sum.inl i : Fin m ⊕ (Fin m ⊕ Fin m)) =
        Sum.inr (Sum.inl i) := congrArg Subtype.val heq
    exact Sum.inl_ne_inr this
  let rightChosen : Finset (Fin m) :=
    Finset.univ.filter fun j ↦ Sum.inr (Sum.inr j) ∈ chosen
  let splitChosen : {q // q ∈ chosen} ≃
      Fin m ⊕ {j // j ∈ rightChosen} :=
    { toFun := fun q ↦
        match hq : q.1 with
        | Sum.inl i => Sum.inl i
        | Sum.inr (Sum.inl i) => False.elim (hnoDuplicate i (hq ▸ q.2))
        | Sum.inr (Sum.inr j) => Sum.inr ⟨j, by
            simp only [rightChosen, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact hq ▸ q.2⟩
      invFun := fun q ↦
        match q with
        | Sum.inl i => ⟨Sum.inl i, hjet i⟩
        | Sum.inr j => ⟨Sum.inr (Sum.inr j.1), by
            simpa only [rightChosen, Finset.mem_filter, Finset.mem_univ,
              true_and] using j.2⟩
      left_inv := by
        rintro ⟨q, hq⟩
        cases q with
        | inl i => rfl
        | inr r =>
            cases r with
            | inl i => exact False.elim (hnoDuplicate i hq)
            | inr j => rfl
      right_inv := by
        intro q
        cases q with
        | inl i => rfl
        | inr j => rfl }
  have hrightCard : rightChosen.card = rho - m := by
    have hcard := Fintype.card_congr splitChosen
    simp only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  let eright : Fin (rho - m) ≃ {j // j ∈ rightChosen} :=
    (Finset.equivFinOfCardEq hrightCard).symm
  let rightRow : Fin (rho - m) → Fin m := fun j ↦ (eright j).1
  let chosenIndex : (Fin m ⊕ Fin (rho - m)) → {q // q ∈ chosen}
    | Sum.inl i => ⟨Sum.inl i, hjet i⟩
    | Sum.inr j => ⟨Sum.inr (Sum.inr (rightRow j)), by
        have hj := (eright j).2
        simpa only [rightChosen, Finset.mem_filter, Finset.mem_univ,
          true_and, rightRow] using hj⟩
  have hchosenIndex : Function.Injective chosenIndex := by
    intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            apply congrArg Sum.inl
            simpa [chosenIndex] using congrArg Subtype.val hab
        | inr j =>
            have hbad := congrArg Subtype.val hab
            simp [chosenIndex] at hbad
    | inr i =>
        cases b with
        | inl j =>
            have hbad := congrArg Subtype.val hab
            simp [chosenIndex] at hbad
        | inr j =>
            apply congrArg Sum.inr
            apply eright.injective
            apply Subtype.ext
            simpa [chosenIndex, rightRow] using congrArg Subtype.val hab
  refine ⟨rightRow, ?_⟩
  have hsub := hchosenLI.comp chosenIndex hchosenIndex
  have hfamily :
      ((fun q : {q // q ∈ chosen} ↦ augmentedFamily jet row q.1) ∘
          chosenIndex) =
        (fun r : Fin m ⊕ Fin (rho - m) ↦
          match r with
          | Sum.inl i => M (Sum.inl i)
          | Sum.inr j => M (Sum.inr (rightRow j))) := by
    funext r
    cases r <;> rfl
  rw [hfamily] at hsub
  exact hsub

/-- At exact support size `rho`, full stack rank `rho` produces a literal
Frobenius-row selector whose all-column (`prefix`) minor is nonsingular. -/
theorem exists_prefixMinor_of_exactSupport_fullRank6401
    {F : Type*} [Field F] {rho : Nat}
    (sigma : F →+* F) (alpha : Fin rho ↪ F) (beta E : Fin rho → F)
    (hrows : keyFirstLaneRows6401 ≤ rho)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hrank : (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
      alpha beta E).rank = rho) :
    ∃ frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
        Fin keyFirstLaneRows6401,
      ((fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        alpha beta E).submatrix
          (genericRankSelectedRow6401 rho frobeniusRow)
          (genericRankMinorColumnEquiv6401 rho)).det ≠ 0 := by
  classical
  let Full := fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
    alpha beta E
  let Ordinary := supportSyndromeMatrix keyFirstLaneRows6401 rho alpha
    (fun i ↦ beta i * E i)
  have hOrdinaryRank : Ordinary.rank = keyFirstLaneRows6401 := by
    dsimp [Ordinary]
    exact supportSyndromeMatrix_rank_eq_rows alpha
      (fun i ↦ beta i * E i) alpha.injective
      (fun i ↦ mul_ne_zero (hbeta i) (hE i)) hrows
  have hOrdinaryLI : LinearIndependent F Ordinary.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card (Fin keyFirstLaneRows6401) =
      Module.finrank F (Submodule.span F (Set.range Ordinary.row))
    rw [← Ordinary.rank_eq_finrank_span_row, hOrdinaryRank]
    simp
  have hleft : LinearIndependent F
      (fun i : Fin keyFirstLaneRows6401 ↦ Full (Sum.inl i)) := by
    have hfamily : (fun i : Fin keyFirstLaneRows6401 ↦
        Full (Sum.inl i)) = Ordinary.row := by
      funext i
      ext j
      rfl
    rw [hfamily]
    exact hOrdinaryLI
  obtain ⟨frobeniusRow, hselectedBase⟩ :=
    exists_rightRowSelector_of_leftIndependent_fullRank hrows Full hleft
      (by simpa [Full] using hrank)
  let rowEquiv : GenericRankMinorRow6401 rho ≃
      (Fin keyFirstLaneRows6401 ⊕
        Fin (rho - keyFirstLaneRows6401)) :=
    Equiv.sumCongr (finCongr (Nat.min_eq_left hrows)) (Equiv.refl _)
  have hselected := hselectedBase.comp rowEquiv rowEquiv.injective
  have hselected' : LinearIndependent F
      (fun row : GenericRankMinorRow6401 rho ↦
        Full (genericRankSelectedRow6401 rho frobeniusRow row)) := by
    convert hselected using 1
    funext row
    cases row with
    | inl i =>
        change Full (Sum.inl _) = Full (Sum.inl _)
        apply congrArg Full
        apply congrArg Sum.inl
        apply Fin.ext
        rfl
    | inr j => rfl
  let A : Matrix (Fin rho) (Fin rho) F := fun i j ↦
    Full (genericRankSelectedRow6401 rho frobeniusRow
      ((genericRankMinorColumnEquiv6401 rho).symm i)) j
  have hArows : LinearIndependent F A.row := by
    have hreindexed := hselected'.comp
      (genericRankMinorColumnEquiv6401 rho).symm
      (genericRankMinorColumnEquiv6401 rho).symm.injective
    convert hreindexed using 1
    funext i j
    rfl
  have hAdet : A.det ≠ 0 := by
    have hAunit : IsUnit A :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hArows
    exact (A.isUnit_iff_isUnit_det.mp hAunit).ne_zero
  have hminorEq :
      (Full.submatrix (genericRankSelectedRow6401 rho frobeniusRow)
        (genericRankMinorColumnEquiv6401 rho)) =
        A.submatrix (genericRankMinorColumnEquiv6401 rho)
          (genericRankMinorColumnEquiv6401 rho) := by
    ext i j
    simp [A]
  refine ⟨frobeniusRow, ?_⟩
  rw [hminorEq, Matrix.det_submatrix_equiv_self]
  exact hAdet

/-- Maximal-rank anchor with support possibly larger than `rho`.  The cheap
row selector still contains all ordinary rows; an arbitrary set of `rho`
literal support columns then gives a nonsingular minor.  This is the branch
used when no maximal-rank owner has exact support `rho`. -/
theorem exists_rowColumnMinor_of_support_fullRank6401
    {F : Type*} [Field F] {s rho : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F) (beta E : Fin s → F)
    (hrowsRho : keyFirstLaneRows6401 ≤ rho)
    (hbeta : ∀ i, beta i ≠ 0) (hE : ∀ i, E i ≠ 0)
    (hrank : (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
      alpha beta E).rank = rho) :
    ∃ frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
        Fin keyFirstLaneRows6401,
      ∃ supportColumn : GenericRankMinorRow6401 rho → Fin s,
        ((fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
          alpha beta E).submatrix
            (genericRankSelectedRow6401 rho frobeniusRow)
            supportColumn).det ≠ 0 := by
  classical
  let Full := fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
    alpha beta E
  have hrhoS : rho ≤ s := by
    rw [← hrank]
    simpa using Matrix.rank_le_card_width Full
  let Ordinary := supportSyndromeMatrix keyFirstLaneRows6401 s alpha
    (fun i ↦ beta i * E i)
  have hOrdinaryRank : Ordinary.rank = keyFirstLaneRows6401 := by
    dsimp [Ordinary]
    exact supportSyndromeMatrix_rank_eq_rows alpha
      (fun i ↦ beta i * E i) alpha.injective
      (fun i ↦ mul_ne_zero (hbeta i) (hE i))
      (hrowsRho.trans hrhoS)
  have hOrdinaryLI : LinearIndependent F Ordinary.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card (Fin keyFirstLaneRows6401) =
      Module.finrank F (Submodule.span F (Set.range Ordinary.row))
    rw [← Ordinary.rank_eq_finrank_span_row, hOrdinaryRank]
    simp
  have hleft : LinearIndependent F
      (fun i : Fin keyFirstLaneRows6401 ↦ Full (Sum.inl i)) := by
    have hfamily : (fun i : Fin keyFirstLaneRows6401 ↦
        Full (Sum.inl i)) = Ordinary.row := by
      funext i
      ext j
      rfl
    rw [hfamily]
    exact hOrdinaryLI
  obtain ⟨frobeniusRow, hselectedBase⟩ :=
    exists_rightRowSelector_of_leftIndependent_fullRank hrowsRho Full hleft
      (by simpa [Full] using hrank)
  let rowEquiv : GenericRankMinorRow6401 rho ≃
      (Fin keyFirstLaneRows6401 ⊕
        Fin (rho - keyFirstLaneRows6401)) :=
    Equiv.sumCongr (finCongr (Nat.min_eq_left hrowsRho)) (Equiv.refl _)
  have hselected := hselectedBase.comp rowEquiv rowEquiv.injective
  have hselected' : LinearIndependent F
      (fun row : GenericRankMinorRow6401 rho ↦
        Full (genericRankSelectedRow6401 rho frobeniusRow row)) := by
    convert hselected using 1
    funext row
    cases row with
    | inl i =>
        change Full (Sum.inl _) = Full (Sum.inl _)
        apply congrArg Full
        apply congrArg Sum.inl
        apply Fin.ext
        rfl
    | inr j => rfl
  let B : Matrix (GenericRankMinorRow6401 rho) (Fin s) F :=
    Full.submatrix (genericRankSelectedRow6401 rho frobeniusRow) id
  have hB : LinearIndependent F B.row := by
    convert hselected' using 1
    funext i j
    rfl
  obtain ⟨supportColumn, hminor⟩ :=
    exists_columns_det_ne_zero_of_rows_linearIndependent B hB
  refine ⟨frobeniusRow, supportColumn, ?_⟩
  simpa [B, Matrix.submatrix_submatrix] using hminor

/-! ## Arbitrary-column symbolic minor for the no-exact-anchor branch -/

noncomputable def arbitraryColumnKeyMinorZ6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (keyColumn : GenericRankMinorRow6401 rho → Fin keyErrors6401) :
    Matrix (GenericRankMinorRow6401 rho)
      (GenericRankMinorRow6401 rho) F[X] :=
  (fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).submatrix
    (genericRankSelectedRow6401 rho frobeniusRow) keyColumn

theorem arbitraryColumnKeyMinorZ_det_degree6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (keyColumn : GenericRankMinorRow6401 rho → Fin keyErrors6401) :
    (arbitraryColumnKeyMinorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow keyColumn).det.natDegree ≤
        genericRankMinorDegreeCap6401 rho := by
  calc
    _ ≤ ∑ row : GenericRankMinorRow6401 rho,
        genericRankMinorRowCap6401 rho row := by
      apply natDegree_det_le_sum_rowCaps _
      intro row col
      have hentry := fullTwoLaneKeyMatrixZ_entry_degree6401
        sigma alpha u₀ u₁
        (genericRankSelectedRow6401 rho frobeniusRow row) (keyColumn col)
      cases row with
      | inl i => simpa [arbitraryColumnKeyMinorZ6401,
          genericRankSelectedRow6401, genericRankMinorRowCap6401] using hentry
      | inr i => simpa [arbitraryColumnKeyMinorZ6401,
          genericRankSelectedRow6401, genericRankMinorRowCap6401] using hentry
    _ = _ := genericRankMinorRowCap_sum6401 rho

/-- The arbitrary fixed minor specializes to the corresponding literal
support minor. -/
theorem arbitraryColumnKeyMinorZ_eval_ownerError6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (hs : s ≤ keyErrors6401)
    (supportColumn : GenericRankMinorRow6401 rho → Fin s)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0) :
    (arbitraryColumnKeyMinorZ6401 sigma alpha u₀ u₁ rho
      frobeniusRow (fun col ↦ Fin.castLE hs (supportColumn col))).map
        (Polynomial.evalRingHom z) =
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a ↦ alpha (support a))
        (fun a ↦ syndromeWeight alpha (support a))
        (fun a ↦ u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a)))).submatrix
            (genericRankSelectedRow6401 rho frobeniusRow)
            supportColumn := by
  classical
  have hwhole := fullTwoLaneKeyMatrixZ_eval_eq_ownerErrorPrefix6401
    sigma alpha u₀ u₁ hfixed hs z hz P hPcheck support hout
  apply Matrix.ext
  intro row col
  have happ := congrArg (fun M ↦
    M (genericRankSelectedRow6401 rho frobeniusRow row)
      (supportColumn col)) hwhole
  simpa [arbitraryColumnKeyMinorZ6401] using happ

/-- Any good specialization of the arbitrary anchor minor has actual stack
rank exactly the global upper bound `rho`. -/
theorem ownerErrorStack_rank_eq_of_goodArbitraryMinor6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (hs : s ≤ keyErrors6401)
    (supportColumn : GenericRankMinorRow6401 rho → Fin s)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0)
    (hdet : Polynomial.eval z
      (arbitraryColumnKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow (fun col ↦ Fin.castLE hs (supportColumn col))).det ≠ 0)
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
  have hmatrix := arbitraryColumnKeyMinorZ_eval_ownerError6401 sigma alpha
    u₀ u₁ hfixed rho frobeniusRow hs supportColumn z hz P hPcheck
    support hout
  have hminor :
      (Full.submatrix (genericRankSelectedRow6401 rho frobeniusRow)
        supportColumn).det ≠ 0 := by
    rw [← hmatrix, ← eval_polynomialMatrix_det]
    exact hdet
  apply Nat.le_antisymm hrankUpper
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hminor
  have hminorRank :
      (Full.submatrix (genericRankSelectedRow6401 rho frobeniusRow)
        supportColumn).rank = rho := by
    calc
      _ = Fintype.card (GenericRankMinorRow6401 rho) :=
        LinearIndependent.rank_matrix hli
      _ = rho := by
        simp only [GenericRankMinorRow6401, Fintype.card_sum,
          Fintype.card_fin]
        exact genericRankMinorRows_add6401 rho
  have hsub := Matrix.rank_submatrix_le Full
    (genericRankSelectedRow6401 rho frobeniusRow) supportColumn
  rwa [hminorRank] at hsub

/-- Concrete arbitrary-column anchor constructor from one maximal-rank
received-word owner. -/
theorem exists_nonzero_arbitraryMinor_of_rankOwner6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    {s : Nat}
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrows : keyFirstLaneRows6401 ≤ rho)
    (hs : s ≤ keyErrors6401)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin s ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0)
    (hE : ∀ a,
      u₀ (support a) + z * u₁ (support a) -
        P.eval (alpha (support a)) ≠ 0)
    (hrank :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (fun a ↦ alpha (support a))
        (fun a ↦ syndromeWeight alpha (support a))
        (fun a ↦ u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a)))).rank = rho) :
    ∃ frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
        Fin keyFirstLaneRows6401,
      ∃ supportColumn : GenericRankMinorRow6401 rho → Fin s,
        let Delta := (arbitraryColumnKeyMinorZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow (fun col ↦ Fin.castLE hs (supportColumn col))).det
        Polynomial.eval z Delta ≠ 0 ∧ Delta ≠ 0 ∧
          Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho := by
  classical
  let alphaS : Fin s ↪ F := support.trans alpha
  let beta : Fin s → F := fun a ↦ syndromeWeight alpha (support a)
  let Err : Fin s → F := fun a ↦
    u₀ (support a) + z * u₁ (support a) -
      P.eval (alpha (support a))
  have halphaS : (alphaS : Fin s → F) =
      (fun a ↦ alpha (support a)) := by
    funext a
    rfl
  have hrank' :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        alphaS beta Err).rank = rho := by
    rw [halphaS]
    simpa [beta, Err] using hrank
  obtain ⟨frobeniusRow, supportColumn, hactualDet⟩ :=
    exists_rowColumnMinor_of_support_fullRank6401 sigma alphaS beta Err
      hrows (fun a ↦ syndromeWeight_ne_zero alpha (support a))
      (by simpa [Err] using hE) hrank'
  refine ⟨frobeniusRow, supportColumn, ?_, ?_,
    arbitraryColumnKeyMinorZ_det_degree6401 sigma alpha u₀ u₁ rho
      frobeniusRow (fun col ↦ Fin.castLE hs (supportColumn col))⟩
  · rw [eval_polynomialMatrix_det]
    rw [arbitraryColumnKeyMinorZ_eval_ownerError6401 sigma alpha u₀ u₁
      hfixed rho frobeniusRow hs supportColumn z hz P hPcheck support hout]
    rw [halphaS] at hactualDet
    simpa [beta, Err] using hactualDet
  · -- Nonzero specialization makes the polynomial determinant nonzero.
    intro hzero
    have heval : Polynomial.eval z
        (arbitraryColumnKeyMinorZ6401 sigma alpha u₀ u₁ rho
          frobeniusRow
            (fun col ↦ Fin.castLE hs (supportColumn col))).det ≠ 0 := by
      rw [eval_polynomialMatrix_det]
      rw [arbitraryColumnKeyMinorZ_eval_ownerError6401 sigma alpha u₀ u₁
        hfixed rho frobeniusRow hs supportColumn z hz P hPcheck support hout]
      rw [halphaS] at hactualDet
      simpa [beta, Err] using hactualDet
    rw [hzero, Polynomial.eval_zero] at heval
    exact heval rfl

/-- Concrete anchor constructor for the received-word pencil.  An owner with
exact support and rank `rho` supplies a nonzero specialization, hence a
globally nonzero fixed symbolic prefix determinant with the affordable row
degree cap. -/
theorem exists_nonzero_fixedPrefixMinor_of_exactRankOwner6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F) (u₀ u₁ : iota → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (hrows : keyFirstLaneRows6401 ≤ rho)
    (z : F) (hz : sigma z = z ^ q6401) (P : F[X])
    (hPcheck : ∀ j < keyRedundancy6401,
      P.natDegree + j < Fintype.card iota - 1)
    (support : Fin rho ↪ iota)
    (hout : ∀ i, i ∉ Set.range support →
      u₀ i + z * u₁ i - P.eval (alpha i) = 0)
    (hE : ∀ a,
      u₀ (support a) + z * u₁ (support a) -
        P.eval (alpha (support a)) ≠ 0)
    (hrank :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (support.trans alpha)
        (fun a ↦ syndromeWeight alpha (support a))
        (fun a ↦ u₀ (support a) + z * u₁ (support a) -
          P.eval (alpha (support a)))).rank = rho) :
    ∃ frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
        Fin keyFirstLaneRows6401,
      let Delta := (genericRankKeyMinorZ6401 sigma alpha u₀ u₁ rho
        frobeniusRow).det
      Polynomial.eval z Delta ≠ 0 ∧
        Delta ≠ 0 ∧
        Delta.natDegree ≤ genericRankMinorDegreeCap6401 rho := by
  classical
  let alphaS : Fin rho ↪ F := support.trans alpha
  let beta : Fin rho → F := fun a ↦ syndromeWeight alpha (support a)
  let Err : Fin rho → F := fun a ↦
    u₀ (support a) + z * u₁ (support a) -
      P.eval (alpha (support a))
  obtain ⟨frobeniusRow, hactualDet⟩ :=
    exists_prefixMinor_of_exactSupport_fullRank6401 sigma alphaS beta Err
      hrows (fun a ↦ syndromeWeight_ne_zero alpha (support a))
      (by simpa [Err] using hE) (by simpa [alphaS, beta, Err] using hrank)
  have halphaS : (alphaS : Fin rho → F) =
      (fun a ↦ alpha (support a)) := by
    funext a
    rfl
  rw [halphaS] at hactualDet
  refine ⟨frobeniusRow, ?_, ?_,
    genericRankKeyMinorZ_det_degree6401 sigma alpha u₀ u₁ rho
      frobeniusRow⟩
  · rw [eval_polynomialMatrix_det]
    rw [genericRankKeyMinorZ_eval_eq_ownerErrorSubmatrix6401 sigma alpha
      u₀ u₁ hfixed rho hrho frobeniusRow z hz P hPcheck support hout]
    simpa [alphaS, beta, Err, Function.comp_def] using hactualDet
  · apply genericRank_fixedMinor_nonzero_of_anchor6401 sigma alpha u₀ u₁
      rho frobeniusRow z
    rw [eval_polynomialMatrix_det]
    rw [genericRankKeyMinorZ_eval_eq_ownerErrorSubmatrix6401 sigma alpha
      u₀ u₁ hfixed rho hrho frobeniusRow z hz P hPcheck support hout]
    simpa [alphaS, beta, Err, Function.comp_def] using hactualDet

/-! ## The complementary no-anchor branch -/

/-- Under a global rank upper bound `rho` and support lower bound `rho`, the
only way not to be rank-deficient relative to support is to have both support
and rank exactly `rho`. -/
theorem rank_lt_support_of_not_exactMax6401
    (s r rho : Nat) (hs : rho ≤ s) (hr : r ≤ rho)
    (hnot : ¬ (s = rho ∧ r = rho)) :
    r < s := by
  omega

/-- Exhaustive sound split before choosing any minor.  The second branch is
strictly stronger than determinant filtering: if no exact-support maximal
rank owner exists, every owner in the original pool is already rank-defect. -/
theorem exactMaxOwner_or_allRankDefect6401
    {F : Type*} [DecidableEq F] (owners : Finset F)
    (supportSize rankAt : F → Nat) (rho : Nat)
    (hsupport : ∀ z ∈ owners, rho ≤ supportSize z)
    (hrank : ∀ z ∈ owners, rankAt z ≤ rho) :
    (∃ z ∈ owners, supportSize z = rho ∧ rankAt z = rho) ∨
      (∀ z ∈ owners, rankAt z < supportSize z) := by
  by_cases hanchor : ∃ z ∈ owners,
      supportSize z = rho ∧ rankAt z = rho
  · exact Or.inl hanchor
  right
  intro z hz
  apply rank_lt_support_of_not_exactMax6401
    (supportSize z) (rankAt z) rho (hsupport z hz) (hrank z hz)
  intro hexact
  exact hanchor ⟨z, hz, hexact⟩

/-- Typed endpoint for the no-exact-anchor side.  It preserves the entire
owner pool and returns the sharp dual-GRS degree window owner by owner; no
arbitrary-column determinant or root deletion is involved. -/
theorem allFailureRelations_of_noExactMaxOwner6401
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (owners : Finset F) (rho : Nat)
    (supportSize : F → Nat)
    (alphaS : (z : F) → Fin (supportSize z) ↪ F)
    (beta E : (z : F) → Fin (supportSize z) → F)
    (hsupport : ∀ z ∈ owners, rho ≤ supportSize z)
    (hrows : ∀ z ∈ owners,
      keyFirstLaneRows6401 ≤ supportSize z)
    (hbeta : ∀ z ∈ owners, ∀ i, beta z i ≠ 0)
    (hE : ∀ z ∈ owners, ∀ i, E z i ≠ 0)
    (hrankUpper : ∀ z ∈ owners,
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (alphaS z) (beta z) (E z)).rank ≤ rho)
    (hnoAnchor : ¬ ∃ z ∈ owners,
      supportSize z = rho ∧
        (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
          (alphaS z) (beta z) (E z)).rank = rho) :
    ∀ z ∈ owners,
      ∃ W₀ W₁ : F[X],
        W₀ ≠ 0 ∧
        W₀.degree <
          (supportSize z - keyFirstLaneRows6401 : Nat) ∧
        W₁.degree <
          (supportSize z - keyFirstLaneRows6401 : Nat) ∧
        TwoLaneFailureRelation sigma (alphaS z) (E z) W₀ W₁ := by
  intro z hz
  have hrankLt :
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (alphaS z) (beta z) (E z)).rank < supportSize z := by
    apply rank_lt_support_of_not_exactMax6401 _ _ rho
      (hsupport z hz) (hrankUpper z hz)
    intro hexact
    exact hnoAnchor ⟨z, hz, hexact⟩
  exact exists_failureRelation_of_fullTwoLane_rank_lt sigma (alphaS z)
    (beta z) (E z) (hrows z hz) (hbeta z hz) (hE z hz) hrankLt

end BCHKSFrobeniusExactAnchorSelector6401
end ProximityPrize.SubmissionLower
