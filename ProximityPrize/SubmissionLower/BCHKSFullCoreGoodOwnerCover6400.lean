import ProximityPrize.SubmissionLower.BCHKSFullCoreOwnerBridge6400
import ProximityPrize.SubmissionLower.BCHKSTranslatedLocalOrderBridge6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSFullCoreGoodOwnerCover6400
open Polynomial
open scoped BigOperators
open BCHKSSubstitutionVanish
open BCHKSFullOrderSlice6400
open BCHKSFullCoreOwnerBridge6400
open BCHKSBoundaryCoreArrangement6400
open BCHKSTranslatedLocalOrderBridge6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
noncomputable def fullCoreLeadingBadValues
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (lead : F → F[X]) : Finset F :=
  E.biUnion fun x ↦ (lead x).roots.toFinset
theorem fullCoreLeadingBadValues_card_le_sum_natDegree
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (lead : F → F[X]) :
    (fullCoreLeadingBadValues E lead).card ≤
      ∑ x ∈ E, (lead x).natDegree := by
  classical
  calc
    (fullCoreLeadingBadValues E lead).card ≤
        ∑ x ∈ E, (lead x).roots.toFinset.card := by
      unfold fullCoreLeadingBadValues
      exact Finset.card_biUnion_le
    _ ≤ ∑ x ∈ E, (lead x).roots.card := by
      apply Finset.sum_le_sum
      intro x hx
      exact Multiset.toFinset_card_le _
    _ ≤ ∑ x ∈ E, (lead x).natDegree := by
      apply Finset.sum_le_sum
      intro x hx
      exact Polynomial.card_roots' _
theorem eval_lead_ne_zero_of_not_mem_fullCoreLeadingBadValues
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) (lead : F → F[X])
    (hne : ∀ x ∈ E, lead x ≠ 0)
    {z : F} (hz : z ∉ fullCoreLeadingBadValues E lead) :
    ∀ x ∈ E, Polynomial.eval z (lead x) ≠ 0 := by
  intro x hx heval
  apply hz
  unfold fullCoreLeadingBadValues
  rw [Finset.mem_biUnion]
  refine ⟨x, hx, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hne x hx)]
  exact heval
theorem coeff_ne_zero_of_full_order_slice
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A)) (d : ℕ)
    (hS : S ≠ 0)
    (hslice : zeroXSlice S ≠ 0)
    (horder : BCHKSLocalValuation6400.localOrder S = d)
    (hdegree : (zeroXSlice S).natDegree ≤ d) :
    (zeroXSlice S).coeff d ≠ 0 := by
  have hlower : d ≤ (zeroXSlice S).natDegree := by
    rw [← horder]
    exact localOrder_le_natDegree_zeroXSlice S hS hslice
  have heq : (zeroXSlice S).natDegree = d := by omega
  rw [← heq, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hslice
theorem top_zeroXSlice_shift
    {A : Type*} [CommRing A] [Nontrivial A]
    (R : Polynomial (Polynomial A)) (x y : A) :
    (zeroXSlice (Polynomial.Bivariate.shift R x y)).coeff R.natDegree =
      Polynomial.eval x R.leadingCoeff := by
  have hq : (Polynomial.X + Polynomial.C (Polynomial.C y) :
      Polynomial (Polynomial A)).natDegree ≠ 0 := by simp
  have htop := Polynomial.coeff_comp_degree_mul_degree
    (p := R) (q := Polynomial.X + Polynomial.C (Polynomial.C y)) hq
  have hcoeff :
      (R.comp (Polynomial.X + Polynomial.C (Polynomial.C y))).coeff
          R.natDegree = R.leadingCoeff := by
    simpa using htop
  simp [zeroXSlice, Polynomial.Bivariate.shift, Polynomial.coeff_map,
    hcoeff]
theorem natDegree_eval_C_le_degreeX
    {F : Type*} [Field F]
    (p : Polynomial (Polynomial F)) (x : F) :
    (Polynomial.eval (Polynomial.C x) p).natDegree ≤
      Polynomial.Bivariate.degreeX p := by
  have heq : (Polynomial.Bivariate.swap p).map
      (Polynomial.evalRingHom x) = Polynomial.eval (Polynomial.C x) p := by
    rw [← Polynomial.Bivariate.evalX_eq_map]
    exact (Polynomial.Bivariate.evalY_eq_evalX_swap x p).symm
  rw [← heq]
  exact Polynomial.natDegree_map_le.trans (by
    rw [show (Polynomial.Bivariate.swap p).natDegree =
      Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap p) from rfl,
      Polynomial.Bivariate.natDegreeY_swap])
theorem fullOrder_lead_natDegree_le_yzSupportDegree
    {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (x : F) (yZ : Polynomial F) (hR : R ≠ 0) :
    ((zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x) yZ)).coeff
      R.natDegree).natDegree ≤ YZFactorCap.yzSupportDegree R 1 := by
  rw [top_zeroXSlice_shift]
  have heval := natDegree_eval_C_le_degreeX R.leadingCoeff x
  have hlead : R.coeff R.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hR
  have hweight := YZFactorCap.coeffWeight_le_of_ne
    R 1 R.natDegree hlead
  rw [Polynomial.coeff_natDegree] at hweight
  omega
theorem ne_zero_of_not_vertical
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A))
    (hvertical : ¬ (Polynomial.C (Polynomial.X : Polynomial A) ∣ S)) :
    S ≠ 0 := by
  intro hzero
  apply hvertical
  rw [hzero]
  exact dvd_zero _
theorem zeroXSlice_ne_of_not_vertical
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A))
    (hvertical : ¬ (Polynomial.C (Polynomial.X : Polynomial A) ∣ S)) :
    zeroXSlice S ≠ 0 := by
  intro hzero
  apply hvertical
  apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
  intro t
  rw [Polynomial.X_dvd_iff]
  have hz := congrArg (fun p : Polynomial A ↦ p.coeff t) hzero
  simpa [zeroXSlice_coeff] using hz
theorem zeroXSlice_natDegree_le
    {A : Type*} [CommSemiring A]
    (S : Polynomial (Polynomial A)) :
    (zeroXSlice S).natDegree ≤ S.natDegree := by
  unfold zeroXSlice
  exact Polynomial.natDegree_map_le
theorem fullOrder_slice_data_of_irreducible
    {A : Type*} [CommRing A] [IsDomain A]
    (R : Polynomial (Polynomial A)) (x y : A)
    (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hfull : BCHKSLocalValuation6400.localOrder
      (Polynomial.Bivariate.shift R x y) = R.natDegree) :
    Polynomial.Bivariate.shift R x y ≠ 0 ∧
      zeroXSlice (Polynomial.Bivariate.shift R x y) ≠ 0 ∧
      (zeroXSlice (Polynomial.Bivariate.shift R x y)).natDegree ≤
        R.natDegree ∧
      (zeroXSlice (Polynomial.Bivariate.shift R x y)).coeff
        R.natDegree ≠ 0 := by
  let S := Polynomial.Bivariate.shift R x y
  have hnotVertical : ¬ (Polynomial.C (Polynomial.X : Polynomial A) ∣ S) :=
    not_vertical_dvd_shift_of_irreducible R x y hirr hpos
  have hS : S ≠ 0 := ne_zero_of_not_vertical S hnotVertical
  have hslice : zeroXSlice S ≠ 0 :=
    zeroXSlice_ne_of_not_vertical S hnotVertical
  have hdegree : (zeroXSlice S).natDegree ≤ R.natDegree :=
    (zeroXSlice_natDegree_le S).trans (natDegree_shift_le R x y)
  have hcoeff : (zeroXSlice S).coeff R.natDegree ≠ 0 :=
    coeff_ne_zero_of_full_order_slice S R.natDegree hS hslice hfull hdegree
  exact ⟨hS, hslice, hdegree, hcoeff⟩
theorem normalized_owner_fullOrder_slice_data
    {F : Type*} [Field F]
    [NormalizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    [UniqueFactorizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    (Q q : Polynomial (Polynomial (Polynomial F)))
    (hqS : q ∈ BCHKSRadicalMultiplicityBridge6400.positiveNormalizedFactors Q)
    (omega : F) (yZ : Polynomial F)
    (hfull : BCHKSLocalValuation6400.localOrder
      (Polynomial.Bivariate.shift q (Polynomial.C omega) yZ) =
        q.natDegree) :
    Polynomial.Bivariate.shift q (Polynomial.C omega) yZ ≠ 0 ∧
      zeroXSlice
        (Polynomial.Bivariate.shift q (Polynomial.C omega) yZ) ≠ 0 ∧
      (zeroXSlice
        (Polynomial.Bivariate.shift q (Polynomial.C omega) yZ)).natDegree ≤
          q.natDegree ∧
      (zeroXSlice
        (Polynomial.Bivariate.shift q (Polynomial.C omega) yZ)).coeff
          q.natDegree ≠ 0 := by
  classical
  have hfilter : q ∈
      (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun H ↦ 0 < H.natDegree) := by
    simpa [BCHKSRadicalMultiplicityBridge6400.positiveNormalizedFactors]
      using hqS
  have hqmem : q ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp hfilter).1
  have hqirr : Irreducible q :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor q hqmem).irreducible
  have hqpos : 0 < q.natDegree := (Finset.mem_filter.mp hfilter).2
  exact fullOrder_slice_data_of_irreducible q (Polynomial.C omega) yZ
    hqirr hqpos hfull
theorem exists_fullOrderCore_of_defect_sum_le
    {I : Type*} [DecidableEq I]
    (A : Finset I) (order : I → ℕ)
    (d k g s : ℕ)
    (hcard : A.card = k + g)
    (hs : s ≤ k)
    (horder_le : ∀ i ∈ A, order i ≤ d)
    (hdefect : A.sum (fun i ↦ d - order i) ≤ g + s) :
    ∃ E : Finset I, E ⊆ A ∧ E.card + s = k ∧
      ∀ i ∈ E, order i = d := by
  classical
  let Full : Finset I := A.filter fun i ↦ order i = d
  let Bad : Finset I := A.filter fun i ↦ order i ≠ d
  have hBadSum : Bad.card ≤ Bad.sum (fun i ↦ d - order i) := by
    calc
      Bad.card = ∑ _i ∈ Bad, 1 := by simp
      _ ≤ Bad.sum (fun i ↦ d - order i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiA : i ∈ A := (Finset.mem_filter.mp hi).1
        have hine : order i ≠ d := (Finset.mem_filter.mp hi).2
        have hile := horder_le i hiA
        omega
  have hBadDefect : Bad.sum (fun i ↦ d - order i) ≤
      A.sum (fun i ↦ d - order i) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ (Finset.mem_filter.mp hi).1) (by simp)
  have hBad : Bad.card ≤ g + s :=
    hBadSum.trans (hBadDefect.trans hdefect)
  have hpartition : Full.card + Bad.card = A.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Full, Bad]
      tauto
    · exact Finset.disjoint_left.mpr (by
        intro i hiFull hiBad
        exact (Finset.mem_filter.mp hiBad).2
          (Finset.mem_filter.mp hiFull).2)
  have hFull : k - s ≤ Full.card := by omega
  obtain ⟨E, hEFull, hEcard⟩ := Finset.exists_subset_card_eq hFull
  refine ⟨E, ?_, ?_, ?_⟩
  · exact hEFull.trans (Finset.filter_subset _ _)
  · omega
  · intro i hi
    exact (Finset.mem_filter.mp (hEFull hi)).2
theorem exists_fullOrderCore_of_marginOne_profile
    {I : Type*} [DecidableEq I]
    (A : Finset I) (order : I → ℕ)
    (d w s : ℕ)
    (hcard : A.card = 185364)
    (hs : s ≤ 131071)
    (horder_le : ∀ i ∈ A, order i ≤ d)
    (hcredit : w + 1 ≤ A.sum order)
    (hweight : w + 54293 + s + 1 = d * 185364) :
    ∃ E : Finset I, E ⊆ A ∧ E.card + s = 131071 ∧
      ∀ i ∈ E, order i = d := by
  have hdefectEq : A.sum (fun i ↦ d - order i) =
      A.card * d - A.sum order := by
    rw [Finset.sum_tsub_distrib A horder_le]
    congr 1
    exact Finset.sum_const_nat (fun _i _hi ↦ rfl)
  have hdefect : A.sum (fun i ↦ d - order i) ≤ 54293 + s := by
    rw [hdefectEq, hcard]
    omega
  exact exists_fullOrderCore_of_defect_sum_le A order d 131071 54293 s
    (by omega) hs horder_le hdefect
theorem unclipped_owner_credit_of_clipped
    {I : Type*} [DecidableEq I]
    (A : Finset I) (nu : I → ℕ) (e m w : ℕ)
    (hcredit : e * w + 1 ≤ ∑ i ∈ A, min m (e * nu i)) :
    w + 1 ≤ ∑ i ∈ A, nu i := by
  have hclip : (∑ i ∈ A, min m (e * nu i)) ≤
      ∑ i ∈ A, e * nu i := by
    apply Finset.sum_le_sum
    intro i hi
    exact min_le_right _ _
  have hmul : (∑ i ∈ A, e * nu i) =
      e * ∑ i ∈ A, nu i := by
    rw [Finset.mul_sum]
  by_contra hnot
  have hsum : (∑ i ∈ A, nu i) ≤ w := by omega
  have hemul := Nat.mul_le_mul_left e hsum
  rw [← hmul] at hemul
  omega
theorem boundary_complement_card
    {I : Type*} [DecidableEq I]
    (D E : Finset I)
    (hDcard : D.card = 262144)
    (hEsub : E ⊆ D)
    (hEcard : E.card + bchksBoundaryCoreCodimension6400 = 131071) :
    (D \ E).card = bchksBoundaryTupleAmbient6400 := by
  rw [Finset.card_sdiff_of_subset hEsub]
  norm_num [bchksBoundaryCoreCodimension6400,
    bchksBoundaryTupleAmbient6400] at hEcard ⊢
  omega
theorem boundary_offCore_card_lower_bound
    {I : Type*} [DecidableEq I]
    (A E : Finset I)
    (hAcard : 185364 ≤ A.card)
    (hEcard : E.card + bchksBoundaryCoreCodimension6400 = 131071) :
    bchksBoundaryTupleIncidences6400 ≤ (A \ E).card := by
  have hdiff := Finset.le_card_sdiff E A
  norm_num [bchksBoundaryCoreCodimension6400,
    bchksBoundaryTupleIncidences6400] at hEcard ⊢
  omega
theorem sdiff_subset_complement
    {I : Type*} [DecidableEq I]
    (D A E : Finset I) (hA : A ⊆ D) :
    A \ E ⊆ D \ E := by
  intro x hx
  exact Finset.mem_sdiff.mpr
    ⟨hA (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
theorem sum_fullCoreLeadingBadValues_card_le_aggregate
    {F R : Type*} [Field F] [DecidableEq F] [DecidableEq R]
    (Rs : Finset R) (core : R → Finset F)
    (lead : R → F → F[X]) (zDegree : R → ℕ)
    (k zMass : ℕ)
    (hcore : ∀ r ∈ Rs, (core r).card ≤ k + 1)
    (hdegree : ∀ r ∈ Rs, ∀ x ∈ core r,
      (lead r x).natDegree ≤ zDegree r)
    (hmass : (∑ r ∈ Rs, zDegree r) ≤ zMass) :
    (∑ r ∈ Rs,
      (fullCoreLeadingBadValues (core r) (lead r)).card) ≤
        (k + 1) * zMass := by
  calc
    (∑ r ∈ Rs,
        (fullCoreLeadingBadValues (core r) (lead r)).card) ≤
        ∑ r ∈ Rs, ∑ x ∈ core r, (lead r x).natDegree := by
      apply Finset.sum_le_sum
      intro r hr
      exact fullCoreLeadingBadValues_card_le_sum_natDegree
        (core r) (lead r)
    _ ≤ ∑ r ∈ Rs, ∑ _x ∈ core r, zDegree r := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro x hx
      exact hdegree r hr x hx
    _ = ∑ r ∈ Rs, (core r).card * zDegree r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_const_nat (fun _x _hx ↦ rfl)
    _ ≤ ∑ r ∈ Rs, (k + 1) * zDegree r := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.mul_le_mul_right (zDegree r) (hcore r hr)
    _ = (k + 1) * ∑ r ∈ Rs, zDegree r := by
      rw [Finset.mul_sum]
    _ ≤ (k + 1) * zMass := Nat.mul_le_mul_left _ hmass
theorem bchks_fullCoreLeadingBadValues_ledger6400 :
    (131071 + 1) * (1688975429 - 1) = 221377387298816 := by
  norm_num
theorem ownerCard_le_leadingDegreeSum_add_codim24
    {F : Type*} [Field F] [DecidableEq F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (E U S : Finset F) (A : F → Finset F)
    (P : F → F[X]) (U0 U1 : F → F) (d : ℕ)
    (hEcard : E.card + bchksBoundaryCoreCodimension6400 = 131071)
    (hUcard : U.card = bchksBoundaryTupleAmbient6400)
    (hdisjoint : Disjoint E U)
    (hd : 1 ≤ d)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ 131071)
    (hshift : ∀ x ∈ E,
      Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x) ≠ 0)
    (horder : ∀ x ∈ E,
      BCHKSLocalValuation6400.localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x)) = d)
    (hsliceDegree : ∀ x ∈ E,
      (zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x))).natDegree ≤ d)
    (hlead_ne : ∀ x ∈ E,
      (zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x))).coeff d ≠ 0)
    (hroot : ∀ z ∈ S, triEval R z (P z) = 0)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hrow : ∀ z ∈ S,
      bchksBoundaryTupleIncidences6400 ≤ (A z).card)
    (hoffCoreMatch : ∀ z ∈ S, ∀ x ∈ A z,
      (P z).eval x = U0 x + z * U1 x)
    (hnonalignment : NoLargeAffineOwnerLine S P 131071
      bchksBoundaryErrors6400) :
    S.card ≤
      (∑ x ∈ E,
        ((zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x))).coeff d).natDegree) +
        bchksBoundaryCodim24PerFactorCap6400 := by
  classical
  let lead : F → F[X] := fun x ↦
    (zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
      (receivedLineAt U0 U1 x))).coeff d
  let Bad : Finset F := fullCoreLeadingBadValues E lead
  let Good : Finset F := S \ Bad
  have hBad : Bad.card ≤ ∑ x ∈ E, (lead x).natDegree := by
    exact fullCoreLeadingBadValues_card_le_sum_natDegree E lead
  have hGoodSub : Good ⊆ S := Finset.sdiff_subset
  have hGood : Good.card ≤ bchksBoundaryCodim24PerFactorCap6400 := by
    apply ownerCard_le_codim24_of_fullOrderCore
      R E U Good A P U0 U1 d hEcard hUcard hdisjoint hd
    · intro z hz
      exact hPdegree z (hGoodSub hz)
    · exact hshift
    · exact horder
    · exact hsliceDegree
    · intro z hz x hx
      have hzBad : z ∉ Bad := (Finset.mem_sdiff.mp hz).2
      exact eval_lead_ne_zero_of_not_mem_fullCoreLeadingBadValues
        E lead (by
          intro y hy
          exact hlead_ne y hy) hzBad x hx
    · intro z hz
      exact hroot z (hGoodSub hz)
    · intro z hz
      exact hsub z (hGoodSub hz)
    · intro z hz
      exact hrow z (hGoodSub hz)
    · intro z hz x hx
      exact hoffCoreMatch z (hGoodSub hz) x hx
    · intro T hT p0 p1 hp0 hp1 hline
      exact hnonalignment T (hT.trans hGoodSub) p0 p1 hp0 hp1 hline
  have hcover : S ⊆ Bad ∪ Good := by
    intro z hz
    by_cases hzBad : z ∈ Bad
    · exact Finset.mem_union_left _ hzBad
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hzBad⟩)
  calc
    S.card ≤ (Bad ∪ Good).card := Finset.card_le_card hcover
    _ ≤ Bad.card + Good.card := Finset.card_union_le _ _
    _ ≤ (∑ x ∈ E, (lead x).natDegree) +
        bchksBoundaryCodim24PerFactorCap6400 :=
      Nat.add_le_add hBad hGood
    _ = (∑ x ∈ E,
        ((zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x))).coeff d).natDegree) +
        bchksBoundaryCodim24PerFactorCap6400 := by rfl
theorem ownerCard_le_of_domain_fullOrderCore
    {F : Type*} [Field F] [DecidableEq F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (D E S : Finset F) (Agree : F → Finset F)
    (P : F → F[X]) (U0 U1 : F → F) (d : ℕ)
    (hDcard : D.card = 262144)
    (hEsub : E ⊆ D)
    (hEcard : E.card + bchksBoundaryCoreCodimension6400 = 131071)
    (hd : 1 ≤ d)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ 131071)
    (hshift : ∀ x ∈ E,
      Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x) ≠ 0)
    (horder : ∀ x ∈ E,
      BCHKSLocalValuation6400.localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x)) = d)
    (hsliceDegree : ∀ x ∈ E,
      (zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x))).natDegree ≤ d)
    (hlead_ne : ∀ x ∈ E,
      (zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
        (receivedLineAt U0 U1 x))).coeff d ≠ 0)
    (hroot : ∀ z ∈ S, triEval R z (P z) = 0)
    (hAgreeSub : ∀ z ∈ S, Agree z ⊆ D)
    (hAgreeCard : ∀ z ∈ S, 185364 ≤ (Agree z).card)
    (hAgreeMatch : ∀ z ∈ S, ∀ x ∈ Agree z,
      (P z).eval x = U0 x + z * U1 x)
    (hnonalignment : NoLargeAffineOwnerLine S P 131071
      bchksBoundaryErrors6400) :
    S.card ≤
      (∑ x ∈ E,
        ((zeroXSlice (Polynomial.Bivariate.shift R (Polynomial.C x)
          (receivedLineAt U0 U1 x))).coeff d).natDegree) +
        bchksBoundaryCodim24PerFactorCap6400 := by
  let U : Finset F := D \ E
  let A : F → Finset F := fun z ↦ Agree z \ E
  apply ownerCard_le_leadingDegreeSum_add_codim24
    R E U S A P U0 U1 d hEcard
  · exact boundary_complement_card D E hDcard hEsub hEcard
  · exact Finset.disjoint_sdiff
  · exact hd
  · exact hPdegree
  · exact hshift
  · exact horder
  · exact hsliceDegree
  · exact hlead_ne
  · exact hroot
  · intro z hz
    exact sdiff_subset_complement D (Agree z) E (hAgreeSub z hz)
  · intro z hz
    exact boundary_offCore_card_lower_bound (Agree z) E
      (hAgreeCard z hz) hEcard
  · intro z hz x hx
    exact hAgreeMatch z hz x (Finset.mem_sdiff.mp hx).1
  · exact hnonalignment
end BCHKSFullCoreGoodOwnerCover6400
end ProximityPrize.SubmissionLower
