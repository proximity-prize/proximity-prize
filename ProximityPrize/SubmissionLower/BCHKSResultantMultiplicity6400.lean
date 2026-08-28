import ProximityPrize.SubmissionLower.BCHKSResultantDegree

namespace ProximityPrize.SubmissionLower
namespace BCHKSResultantMultiplicity6400

open Polynomial
open Polynomial.Bivariate
open scoped BigOperators

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

/-- If every nonzero determinant term contains at least `N` copies of a
uniformizer, then so does the determinant. -/
theorem pow_dvd_det_of_permExponentSum
    {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (uniformizer : R) (M : Matrix I I R) (exponent : I → I → Nat)
    (N : Nat)
    (hentry : ∀ i j, uniformizer ^ exponent i j ∣ M i j)
    (hperm : ∀ sigma : Equiv.Perm I,
      (∀ i, M (sigma i) i ≠ 0) →
        N ≤ ∑ i, exponent (sigma i) i) :
    uniformizer ^ N ∣ M.det := by
  classical
  rw [Matrix.det_apply]
  apply Finset.dvd_sum
  intro sigma _
  suffices hproductDvd : uniformizer ^ N ∣ ∏ i : I, M (sigma i) i by
    rcases hproductDvd with ⟨C, hC⟩
    refine ⟨Equiv.Perm.sign sigma • C, ?_⟩
    rw [hC, mul_smul_comm]
  by_cases hzero : ∃ i : I, M (sigma i) i = 0
  · rcases hzero with ⟨i, hi⟩
    have hprod : (∏ i : I, M (sigma i) i) = 0 :=
      Finset.prod_eq_zero (s := Finset.univ) (by simp) hi
    simp [hprod]
  · have hselected (i : I) : M (sigma i) i ≠ 0 := by
      intro hi
      exact hzero ⟨i, hi⟩
    have hlargePower : uniformizer ^ N ∣
        uniformizer ^ (∑ i, exponent (sigma i) i) :=
      pow_dvd_pow uniformizer (hperm sigma hselected)
    have hproductPower :
        (∏ i : I, uniformizer ^ exponent (sigma i) i) ∣
          ∏ i : I, M (sigma i) i :=
      Finset.prod_dvd_prod_of_dvd _ _
        (fun i (_ : i ∈ Finset.univ) => hentry (sigma i) i)
    rw [Finset.prod_pow_eq_pow_sum] at hproductPower
    exact hlargePower.trans hproductPower

/-- The determinant of a polynomial matrix vanishes to at least the corank of
its specialization. -/
theorem X_sub_C_pow_corank_dvd_det
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (z : F) :
    (Polynomial.X - Polynomial.C z) ^
        (Fintype.card I - (M.map (Polynomial.evalRingHom z)).rank) ∣ M.det := by
  classical
  let N : Matrix I I F := M.map (Polynomial.evalRingHom z)
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form N
  let MC : Matrix I I F[X] := V.map Polynomial.C * M * U.map Polynomial.C
  let exponent : I → I → Nat := fun _ j ↦
    Sum.elim (fun _ : Fin N.rank ↦ 0)
      (fun _ : Fin (Fintype.card I - N.rank) ↦ 1) (e j)
  have hevalC :
      (Polynomial.evalRingHom z).comp (Polynomial.C : F →+* F[X]) =
        RingHom.id F := by
    ext x
    simp
  have hVmap :
      (V.map Polynomial.C).map (Polynomial.evalRingHom z) = V := by
    rw [Matrix.map_map]
    change V.map (((Polynomial.evalRingHom z).comp Polynomial.C) : F → F) = V
    rw [hevalC]
    rfl
  have hUmap :
      (U.map Polynomial.C).map (Polynomial.evalRingHom z) = U := by
    rw [Matrix.map_map]
    change U.map (((Polynomial.evalRingHom z).comp Polynomial.C) : F → F) = U
    rw [hevalC]
    rfl
  have hMCmap : MC.map (Polynomial.evalRingHom z) = V * N * U := by
    dsimp only [MC]
    rw [Matrix.map_mul, Matrix.map_mul, hVmap, hUmap]
  have hentry : ∀ i j,
      (Polynomial.X - Polynomial.C z) ^ exponent i j ∣ MC i j := by
    intro i j
    cases hej : e j with
    | inl j0 =>
        simp [exponent, hej]
    | inr j1 =>
        have hzero : Polynomial.eval z (MC i j) = 0 := by
          have hij := congrArg (fun A : Matrix I I F ↦ A i j) hMCmap
          rw [hnormal] at hij
          have hblock :
              ((Matrix.fromBlocks (1 : Matrix (Fin N.rank) (Fin N.rank) F)
                0 0 0).submatrix e e) i j = 0 := by
            cases hei : e i <;> simp [Matrix.submatrix, hej, hei]
          calc
            Polynomial.eval z (MC i j) =
                ((Matrix.fromBlocks
                  (1 : Matrix (Fin N.rank) (Fin N.rank) F)
                  0 0 0).submatrix e e) i j := hij
            _ = 0 := hblock
        have hdvd : Polynomial.X - Polynomial.C z ∣ MC i j := by
          rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
          exact hzero
        simpa [exponent, hej] using hdvd
  have hexponent :
      (∑ j : I, exponent j j) = Fintype.card I - N.rank := by
    change (∑ j : I,
      Sum.elim (fun _ : Fin N.rank ↦ 0)
        (fun _ : Fin (Fintype.card I - N.rank) ↦ 1) (e j)) = _
    rw [Equiv.sum_comp e]
    simp
  have hMCdvd :
      (Polynomial.X - Polynomial.C z) ^
          (Fintype.card I - N.rank) ∣ MC.det := by
    apply pow_dvd_det_of_permExponentSum
      (Polynomial.X - Polynomial.C z) MC exponent
        (Fintype.card I - N.rank) hentry
    intro sigma hsigma
    calc
      Fintype.card I - N.rank = ∑ j : I, exponent j j := hexponent.symm
      _ ≤ ∑ j : I, exponent (sigma j) j := by exact le_rfl
  have hdetMC : MC.det =
      Polynomial.C V.det * M.det * Polynomial.C U.det := by
    simp [MC, Matrix.det_mul, RingHom.map_det]
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  rw [hdetMC] at hMCdvd
  exact (Polynomial.isUnit_C.mpr hVdet).dvd_mul_left.mp
    ((Polynomial.isUnit_C.mpr hUdet).dvd_mul_right.mp hMCdvd)

/-- Syzygies contributed by a common factor, padded to declared Sylvester
degrees.  Requiring only the left cofactor to be nonzero lets the second
specialized polynomial vanish identically. -/
noncomputable def paddedCommonFactorSyzygyMap
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) :
    Polynomial.degreeLT F d.natDegree →ₗ[F]
      Polynomial.degreeLT F m × Polynomial.degreeLT F n where
  toFun T :=
    ⟨⟨T.1 * a, by
        rw [Polynomial.mem_degreeLT]
        by_cases hT : T.1 = 0
        · simp [hT]
        · apply (Polynomial.natDegree_lt_iff_degree_lt
            (mul_ne_zero hT ha)).1
          have hTmem := T.2
          rw [Polynomial.mem_degreeLT] at hTmem
          have hTdegree : T.1.natDegree < d.natDegree :=
            (Polynomial.natDegree_lt_iff_degree_lt hT).2 hTmem
          apply lt_of_lt_of_le _ hfm
          rw [hfa, Polynomial.natDegree_mul hd ha,
            Polynomial.natDegree_mul hT ha]
          omega⟩,
      ⟨-(T.1 * b), by
        rw [Polynomial.mem_degreeLT]
        by_cases hTb : T.1 * b = 0
        · simp [hTb]
        · rw [Polynomial.degree_neg]
          apply (Polynomial.natDegree_lt_iff_degree_lt hTb).1
          have hTne : T.1 ≠ 0 := fun hzero ↦ hTb (by simp [hzero])
          have hb : b ≠ 0 := fun hzero ↦ hTb (by simp [hzero])
          have hTmem := T.2
          rw [Polynomial.mem_degreeLT] at hTmem
          have hTdegree : T.1.natDegree < d.natDegree :=
            (Polynomial.natDegree_lt_iff_degree_lt hTne).2 hTmem
          apply lt_of_lt_of_le _ hgn
          rw [hgb, Polynomial.natDegree_mul hd hb,
            Polynomial.natDegree_mul hTne hb]
          omega⟩⟩
  map_add' T U := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> ring
  map_smul' c T := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> simp

theorem paddedCommonFactorSyzygyMap_injective
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) :
    Function.Injective
      (paddedCommonFactorSyzygyMap
        f g d a b m n hd ha hfa hgb hfm hgn) := by
  intro T U hTU
  apply Subtype.ext
  have hfirst := congrArg (fun p ↦ p.1.1) hTU
  dsimp [paddedCommonFactorSyzygyMap] at hfirst
  exact mul_right_cancel₀ ha hfirst

theorem paddedCommonFactorSyzygyMap_mem_kernel
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n)
    (T : Polynomial.degreeLT F d.natDegree) :
    Polynomial.sylvesterMap f g hfm hgn
      (paddedCommonFactorSyzygyMap
        f g d a b m n hd ha hfa hgb hfm hgn T) = 0 := by
  apply Subtype.ext
  dsimp [Polynomial.sylvesterMap, paddedCommonFactorSyzygyMap]
  rw [hfa, hgb]
  ring

theorem paddedSylvester_rank_le_add_sub_commonFactorDegree
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) :
    (Polynomial.sylvester f g m n).rank ≤ m + n - d.natDegree := by
  let L := paddedCommonFactorSyzygyMap
    f g d a b m n hd ha hfa hgb hfm hgn
  let S := Polynomial.sylvesterMap f g hfm hgn
  let LK : Polynomial.degreeLT F d.natDegree →ₗ[F]
      LinearMap.ker S := {
    toFun T := ⟨L T, by
      rw [LinearMap.mem_ker]
      exact paddedCommonFactorSyzygyMap_mem_kernel
        f g d a b m n hd ha hfa hgb hfm hgn T⟩
    map_add' T U := by
      apply Subtype.ext
      exact L.map_add T U
    map_smul' c T := by
      apply Subtype.ext
      exact L.map_smul c T
    }
  have hLKinj : Function.Injective LK := by
    intro T U hTU
    apply paddedCommonFactorSyzygyMap_injective
      f g d a b m n hd ha hfa hgb hfm hgn
    exact congrArg Subtype.val hTU
  have hsource : Module.finrank F
      (Polynomial.degreeLT F d.natDegree) = d.natDegree := by
    rw [Module.finrank_eq_card_basis
      (Polynomial.degreeLT.basis F d.natDegree)]
    simp
  have hker : d.natDegree ≤ Module.finrank F (LinearMap.ker S) := by
    rw [← hsource]
    exact LinearMap.finrank_le_finrank_of_injective hLKinj
  have hdomain : Module.finrank F
      (Polynomial.degreeLT F m × Polynomial.degreeLT F n) = m + n := by
    rw [Module.finrank_prod,
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F m),
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F n)]
    simp
  have hranknull := LinearMap.finrank_range_add_finrank_ker S
  have hrange : Module.finrank F (LinearMap.range S) ≤
      m + n - d.natDegree := by
    rw [hdomain] at hranknull
    omega
  let bin :=
    ((Polynomial.degreeLT.basis F m).prod
      (Polynomial.degreeLT.basis F n)).reindex finSumFinEquiv
  let bout := Polynomial.degreeLT.basis F (m + n)
  have hmatrix : Matrix.toLin bin bout
      (Polynomial.sylvester f g m n) = S := by
    rw [← Polynomial.toMatrix_sylvesterMap' f g hfm hgn]
    exact Matrix.toLin_toMatrix _ _ _
  rw [Matrix.rank_eq_finrank_range_toLin
    (Polynomial.sylvester f g m n) bout bin, hmatrix]
  exact hrange

/-- A common specialized factor of degree `d.natDegree` contributes that much
root multiplicity to the fixed-degree bivariate resultant.  Fixed declared
degrees make this valid even when either specialization loses degree. -/
theorem X_sub_C_pow_commonFactorDegree_dvd_resultant
    {F : Type*} [Field F]
    (B Q : F[X][X]) (m n : Nat) (z : F)
    (d a b : F[X])
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hBfactor : B.map (Polynomial.evalRingHom z) = d * a)
    (hQfactor : Q.map (Polynomial.evalRingHom z) = d * b)
    (hBdegree : (B.map (Polynomial.evalRingHom z)).natDegree ≤ m)
    (hQdegree : (Q.map (Polynomial.evalRingHom z)).natDegree ≤ n) :
    (Polynomial.X - Polynomial.C z) ^ d.natDegree ∣
      Polynomial.resultant B Q m n := by
  let f := B.map (Polynomial.evalRingHom z)
  let g := Q.map (Polynomial.evalRingHom z)
  have hfdegree : f.natDegree ≤ m := by simpa [f] using hBdegree
  have hgdegree : g.natDegree ≤ n := by simpa [g] using hQdegree
  have hrank : (Polynomial.sylvester f g m n).rank ≤
      m + n - d.natDegree :=
    paddedSylvester_rank_le_add_sub_commonFactorDegree
      f g d a b m n hd ha hBfactor hQfactor hfdegree hgdegree
  have hdle : d.natDegree ≤ m := by
    have hffactor : f = d * a := by simpa [f] using hBfactor
    calc
      d.natDegree ≤ f.natDegree := by
        rw [hffactor, Polynomial.natDegree_mul hd ha]
        omega
      _ ≤ m := hfdegree
  let M := Polynomial.sylvester B Q m n
  have hmap : M.map (Polynomial.evalRingHom z) =
      Polynomial.sylvester f g m n := by
    simpa [M, f, g] using
      (Polynomial.sylvester_map_map B Q m n
        (Polynomial.evalRingHom z)).symm
  have hcorank : d.natDegree ≤
      Fintype.card (Fin (m + n)) -
        (M.map (Polynomial.evalRingHom z)).rank := by
    rw [hmap]
    simp only [Fintype.card_fin]
    omega
  have hdet := X_sub_C_pow_corank_dvd_det M z
  have hsmall : (Polynomial.X - Polynomial.C z) ^ d.natDegree ∣
      (Polynomial.X - Polynomial.C z) ^
        (Fintype.card (Fin (m + n)) -
          (M.map (Polynomial.evalRingHom z)).rank) :=
    pow_dvd_pow _ hcorank
  exact hsmall.trans (by simpa [M, Polynomial.resultant] using hdet)

/-- Multiplicities at distinct injected roots sum to at most the degree of a
nonzero polynomial. -/
theorem sum_le_natDegree_of_rootMultiplicity
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : Polynomial F) (ω : ι ↪ F) (A : Finset ι) (μ : ι → ℕ)
    (hmult : ∀ i ∈ A, μ i ≤ R.rootMultiplicity (ω i)) :
    ∑ i ∈ A, μ i ≤ R.natDegree := by
  let xs : Finset F := A.map ω
  have hselected :
      ∑ x ∈ xs, Multiset.count x R.roots ≤ R.roots.card := by
    let all := xs ∪ R.roots.toFinset
    calc
      ∑ x ∈ xs, Multiset.count x R.roots ≤
          ∑ x ∈ all, Multiset.count x R.roots :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
      _ = ∑ x ∈ R.roots.toFinset, Multiset.count x R.roots := by
        symm
        apply Finset.sum_subset (Finset.subset_union_right)
        intro x hxall hxroots
        exact Multiset.count_eq_zero.mpr (by simpa using hxroots)
      _ = R.roots.card := Multiset.toFinset_sum_count_eq R.roots
  calc
    ∑ i ∈ A, μ i ≤ ∑ i ∈ A, R.rootMultiplicity (ω i) :=
      Finset.sum_le_sum fun i hi => hmult i hi
    _ = ∑ x ∈ xs, R.rootMultiplicity x := by
      symm
      exact Finset.sum_map A ω (fun x => R.rootMultiplicity x)
    _ = ∑ x ∈ xs, Multiset.count x R.roots := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Polynomial.count_roots R).symm
    _ ≤ R.roots.card := hselected
    _ ≤ R.natDegree := Polynomial.card_roots' R

theorem sum_localPowers_le_natDegree
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : F[X]) (hR : R ≠ 0) (ω : ι ↪ F) (S : Finset ι) (g : ι → Nat)
    (hlocal : ∀ i ∈ S,
      (Polynomial.X - Polynomial.C (ω i)) ^ g i ∣ R) :
    ∑ i ∈ S, g i ≤ R.natDegree := by
  apply sum_le_natDegree_of_rootMultiplicity R ω S g
  intro i hi
  rw [Polynomial.le_rootMultiplicity_iff hR]
  exact hlocal i hi

/-- Deleting the zeros of a nonzero polynomial from an injectively indexed
finite set costs at most its degree. -/
theorem card_le_filter_eval_ne_zero_add_natDegree
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (S : Finset ι) (ω : ι ↪ F) (P : F[X]) (hP : P ≠ 0) :
    S.card ≤ (S.filter (fun i ↦ P.eval (ω i) ≠ 0)).card + P.natDegree := by
  let Zeros : Finset ι := S.filter fun i ↦ P.eval (ω i) = 0
  have hzero : Zeros.card ≤ P.natDegree := by
    have hlocal : ∀ i ∈ Zeros,
        (Polynomial.X - Polynomial.C (ω i)) ^ 1 ∣ P := by
      intro i hi
      rw [pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
      exact (Finset.mem_filter.mp hi).2
    have hsum := sum_localPowers_le_natDegree
      P hP ω Zeros (fun _ ↦ 1) hlocal
    have hconst : (∑ i ∈ Zeros, (fun _ ↦ 1) i) = Zeros.card * 1 :=
      Finset.sum_const_nat (fun _ _ ↦ rfl)
    rw [hconst, Nat.mul_one] at hsum
    exact hsum
  have hpartition := Finset.card_filter_add_card_filter_not
    (fun i ↦ P.eval (ω i) ≠ 0) (s := S)
  have hzero' :
      (S.filter (fun i ↦ ¬P.eval (ω i) ≠ 0)).card ≤ P.natDegree := by
    simpa only [not_ne_iff, Zeros] using hzero
  omega

/-- Multiplicity-enhanced resultant counting along one specialization axis.
The leading coefficient removes all degree-drop fibres at a cost of at most
the transverse degree `t`. -/
theorem axis_multiplicity_bound
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    (H C : F[X][X]) (S : Finset ι) (ω : ι ↪ F)
    (d t n u : Nat)
    (hH : H ≠ 0)
    (hHY : H.natDegree = d)
    (hHX : degreeX H = t)
    (hCY : C.natDegree ≤ n)
    (hCX : degreeX C ≤ u)
    (hfiber : ∀ i ∈ S,
      H.map (Polynomial.evalRingHom (ω i)) ∣
        C.map (Polynomial.evalRingHom (ω i)))
    (hR : Polynomial.resultant H C d n ≠ 0) :
    d * S.card ≤ n * t + d * u + d * t := by
  let R : F[X] := Polynomial.resultant H C d n
  let a : F[X] := H.leadingCoeff
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact Polynomial.leadingCoeff_ne_zero.mpr hH
  let Good : Finset ι := S.filter fun i ↦ a.eval (ω i) ≠ 0
  have hGoodCardRaw :=
    card_le_filter_eval_ne_zero_add_natDegree S ω a ha
  change S.card ≤ Good.card + a.natDegree at hGoodCardRaw
  have hadegree : a.natDegree ≤ t := by
    dsimp only [a]
    exact (coeff_natDegree_le_degreeX H H.natDegree).trans_eq hHX
  have hGoodCard : S.card ≤ Good.card + t :=
    hGoodCardRaw.trans (Nat.add_le_add_left hadegree Good.card)
  have hlocal : ∀ i ∈ Good,
      (Polynomial.X - Polynomial.C (ω i)) ^ d ∣ R := by
    intro i hi
    have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
    have hlead :
        (Polynomial.evalRingHom (ω i)) H.leadingCoeff ≠ 0 := by
      simpa only [Polynomial.coe_evalRingHom, a] using
        (Finset.mem_filter.mp hi).2
    have hHdegree :
        (H.map (Polynomial.evalRingHom (ω i))).natDegree = d := by
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead]
      exact hHY
    have hHne : H.map (Polynomial.evalRingHom (ω i)) ≠ 0 := by
      rw [← Polynomial.leadingCoeff_ne_zero,
        Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlead]
      exact hlead
    obtain ⟨b, hb⟩ := hfiber i hiS
    have hpow := X_sub_C_pow_commonFactorDegree_dvd_resultant
      H C d n (ω i)
      (H.map (Polynomial.evalRingHom (ω i))) 1 b
      hHne one_ne_zero (by simp) hb
      hHdegree.le
      (Polynomial.natDegree_map_le.trans hCY)
    simpa only [R, hHdegree] using hpow
  have hsum : Good.card * d ≤ R.natDegree := by
    have hraw := sum_localPowers_le_natDegree
      R hR ω Good (fun _ ↦ d) hlocal
    have hconst : (∑ i ∈ Good, (fun _ ↦ d) i) = Good.card * d :=
      Finset.sum_const_nat (fun _ _ ↦ rfl)
    rw [hconst] at hraw
    exact hraw
  have hRdegree : R.natDegree ≤ n * t + d * u := by
    have hraw := bivariate_resultant_natDegree_le H C d n
    rw [hHX] at hraw
    exact hraw.trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left d hCX) (n * t))
  calc
    d * S.card ≤ d * (Good.card + t) := Nat.mul_le_mul_left d hGoodCard
    _ = Good.card * d + d * t := by
      rw [Nat.mul_add, Nat.mul_comm d Good.card]
    _ ≤ R.natDegree + d * t := Nat.add_le_add_right hsum _
    _ ≤ n * t + d * u + d * t := Nat.add_le_add_right hRdegree _

/-- Apply the same padded-resultant count in both variable directions.  The
second fibre hypothesis is deliberately stated after `swap`, making this a
clean interface for coordinate-evaluation identities. -/
theorem twoAxis_multiplicity_bounds
    {F ι κ : Type} [Field F]
    [DecidableEq F] [DecidableEq ι] [DecidableEq κ]
    (H C : F[X][X])
    (Owners : Finset ι) (owner : ι ↪ F)
    (Coords : Finset κ) (coord : κ ↪ F)
    (d t n u : Nat)
    (hH : H ≠ 0)
    (hHY : H.natDegree = d)
    (hHX : degreeX H = t)
    (hCY : C.natDegree ≤ n)
    (hCX : degreeX C ≤ u)
    (howner : ∀ i ∈ Owners,
      H.map (Polynomial.evalRingHom (owner i)) ∣
        C.map (Polynomial.evalRingHom (owner i)))
    (hcoord : ∀ i ∈ Coords,
      (swap H).map (Polynomial.evalRingHom (coord i)) ∣
        (swap C).map (Polynomial.evalRingHom (coord i)))
    (hOwnerR : Polynomial.resultant H C d n ≠ 0)
    (hCoordR : Polynomial.resultant (swap H) (swap C) t u ≠ 0) :
    d * Owners.card ≤ n * t + d * u + d * t ∧
      t * Coords.card ≤ u * d + t * n + t * d := by
  refine ⟨axis_multiplicity_bound H C Owners owner d t n u
    hH hHY hHX hCY hCX howner hOwnerR, ?_⟩
  apply axis_multiplicity_bound (swap H) (swap C) Coords coord t d u n
  · simpa using swap.injective.ne hH
  · change natDegreeY (swap H) = t
    exact (natDegreeY_swap H).trans hHX
  · exact (degreeX_swap H).trans hHY
  · change natDegreeY (swap C) ≤ u
    exact (natDegreeY_swap C).trans_le hCX
  · exact (degreeX_swap C).trans_le hCY
  · exact hcoord
  · exact hCoordR

end BCHKSResultantMultiplicity6400
end ProximityPrize.SubmissionLower
