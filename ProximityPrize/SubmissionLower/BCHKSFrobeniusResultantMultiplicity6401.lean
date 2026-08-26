import ProximityPrize.SubmissionLower.BCHKSNearFullDirectCoreBudget6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusResultantMultiplicity6401
open Polynomial
open scoped BigOperators
open BCHKSNearFullDirectCoreBudget6400
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
theorem X_sub_C_pow_corank_dvd_det6401
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X]) (z : F) :
    (Polynomial.X - Polynomial.C z) ^
        (Fintype.card I -
          (M.map (Polynomial.evalRingHom z)).rank) ∣ M.det := by
  classical
  let N : Matrix I I F := M.map (Polynomial.evalRingHom z)
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form N
  let MC : Matrix I I F[X] :=
    V.map Polynomial.C * M * U.map Polynomial.C
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
    rw [Matrix.map_mul, Matrix.map_mul]
    rw [hVmap, hUmap]
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
noncomputable def commonFactorSyzygyMap6401
    {F : Type*} [Field F]
    (f g d a b : F[X])
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b) :
    Polynomial.degreeLT F d.natDegree →ₗ[F]
      Polynomial.degreeLT F f.natDegree ×
        Polynomial.degreeLT F g.natDegree where
  toFun T :=
    ⟨⟨T.1 * a, by
        rw [Polynomial.mem_degreeLT]
        by_cases hT : T.1 = 0
        · simp [hT, hfa]
        · apply (Polynomial.natDegree_lt_iff_degree_lt
            (mul_ne_zero hT ha)).1
          have hTmem := T.2
          rw [Polynomial.mem_degreeLT] at hTmem
          have hTdegree : T.1.natDegree < d.natDegree :=
            (Polynomial.natDegree_lt_iff_degree_lt hT).2
              hTmem
          rw [Polynomial.natDegree_mul hT ha,
            hfa, Polynomial.natDegree_mul hd ha]
          omega⟩,
      ⟨-(T.1 * b), by
        rw [Polynomial.mem_degreeLT]
        by_cases hT : T.1 = 0
        · simp [hT, hgb]
        · have hprod : T.1 * b ≠ 0 := mul_ne_zero hT hb
          rw [Polynomial.degree_neg]
          apply (Polynomial.natDegree_lt_iff_degree_lt hprod).1
          have hTmem := T.2
          rw [Polynomial.mem_degreeLT] at hTmem
          have hTdegree : T.1.natDegree < d.natDegree :=
            (Polynomial.natDegree_lt_iff_degree_lt hT).2
              hTmem
          rw [Polynomial.natDegree_mul hT hb,
            hgb, Polynomial.natDegree_mul hd hb]
          omega⟩⟩
  map_add' T S := by
    apply Prod.ext <;> apply Subtype.ext <;>
      dsimp <;> ring
  map_smul' c T := by
    apply Prod.ext <;> apply Subtype.ext <;>
      dsimp <;> simp
theorem commonFactorSyzygyMap_injective6401
    {F : Type*} [Field F]
    (f g d a b : F[X])
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b) :
    Function.Injective
      (commonFactorSyzygyMap6401 f g d a b hd ha hb hfa hgb) := by
  intro T S hTS
  apply Subtype.ext
  have hfirst := congrArg (fun p ↦ p.1.1) hTS
  dsimp [commonFactorSyzygyMap6401] at hfirst
  exact mul_right_cancel₀ ha hfirst
theorem commonFactorSyzygyMap_mem_sylvesterKernel6401
    {F : Type*} [Field F]
    (f g d a b : F[X])
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (T : Polynomial.degreeLT F d.natDegree) :
    Polynomial.sylvesterMap f g le_rfl le_rfl
      (commonFactorSyzygyMap6401 f g d a b hd ha hb hfa hgb T) = 0 := by
  apply Subtype.ext
  dsimp [Polynomial.sylvesterMap, commonFactorSyzygyMap6401]
  rw [hfa, hgb]
  ring
theorem sylvester_rank_le_add_sub_commonFactorDegree6401
    {F : Type*} [Field F]
    (f g d a b : F[X])
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b) :
    (Polynomial.sylvester f g f.natDegree g.natDegree).rank ≤
      f.natDegree + g.natDegree - d.natDegree := by
  let S := Polynomial.sylvesterMap f g le_rfl le_rfl
  let L := commonFactorSyzygyMap6401 f g d a b hd ha hb hfa hgb
  let LK : Polynomial.degreeLT F d.natDegree →ₗ[F]
      LinearMap.ker S := {
    toFun T := ⟨L T, by
      rw [LinearMap.mem_ker]
      exact commonFactorSyzygyMap_mem_sylvesterKernel6401
        f g d a b hd ha hb hfa hgb T⟩
    map_add' T U := by
      apply Subtype.ext
      exact L.map_add T U
    map_smul' c T := by
      apply Subtype.ext
      exact L.map_smul c T
    }
  have hLKinj : Function.Injective LK := by
    intro T U hTU
    apply commonFactorSyzygyMap_injective6401
      f g d a b hd ha hb hfa hgb
    exact congrArg Subtype.val hTU
  have hsource :
      Module.finrank F (Polynomial.degreeLT F d.natDegree) = d.natDegree := by
    rw [Module.finrank_eq_card_basis
      (Polynomial.degreeLT.basis F d.natDegree)]
    simp
  have hker : d.natDegree ≤ Module.finrank F (LinearMap.ker S) := by
    rw [← hsource]
    exact LinearMap.finrank_le_finrank_of_injective hLKinj
  have hdomain : Module.finrank F
      (Polynomial.degreeLT F f.natDegree ×
        Polynomial.degreeLT F g.natDegree) =
      f.natDegree + g.natDegree := by
    rw [Module.finrank_prod,
      Module.finrank_eq_card_basis
        (Polynomial.degreeLT.basis F f.natDegree),
      Module.finrank_eq_card_basis
        (Polynomial.degreeLT.basis F g.natDegree)]
    simp
  have hranknull := LinearMap.finrank_range_add_finrank_ker S
  have hrange : Module.finrank F (LinearMap.range S) ≤
      f.natDegree + g.natDegree - d.natDegree := by
    rw [hdomain] at hranknull
    omega
  let bin :=
    ((Polynomial.degreeLT.basis F f.natDegree).prod
      (Polynomial.degreeLT.basis F g.natDegree)).reindex
        finSumFinEquiv
  let bout := Polynomial.degreeLT.basis F (f.natDegree + g.natDegree)
  have hmatrix : Matrix.toLin bin bout
      (Polynomial.sylvester f g f.natDegree g.natDegree) = S := by
    rw [← Polynomial.toMatrix_sylvesterMap' f g le_rfl le_rfl]
    exact Matrix.toLin_toMatrix _ _ _
  rw [Matrix.rank_eq_finrank_range_toLin
    (Polynomial.sylvester f g f.natDegree g.natDegree) bout bin,
    hmatrix]
  exact hrange
theorem X_sub_C_pow_commonFactorDegree_dvd_resultant6401
    {F : Type*} [Field F]
    (B H : F[X][X]) (bdeg : Nat) (z : F)
    (d a c : F[X])
    (hd : d ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hBfactor : B.map (Polynomial.evalRingHom z) = d * a)
    (hHfactor : H.map (Polynomial.evalRingHom z) = d * c)
    (hBdegree : (B.map (Polynomial.evalRingHom z)).natDegree = bdeg)
    (hHdegree : (H.map (Polynomial.evalRingHom z)).natDegree = bdeg) :
    (Polynomial.X - Polynomial.C z) ^ d.natDegree ∣
      Polynomial.resultant B H bdeg bdeg := by
  let f := B.map (Polynomial.evalRingHom z)
  let g := H.map (Polynomial.evalRingHom z)
  have hfdegree : f.natDegree = bdeg := by
    simpa [f] using hBdegree
  have hgdegree : g.natDegree = bdeg := by
    simpa [g] using hHdegree
  have hdle : d.natDegree ≤ bdeg := by
    rw [← hBdegree, hBfactor, Polynomial.natDegree_mul hd ha]
    omega
  have hrank : (Polynomial.sylvester f g bdeg bdeg).rank ≤
      2 * bdeg - d.natDegree := by
    have hraw := sylvester_rank_le_add_sub_commonFactorDegree6401
      f g d a c hd ha hc hBfactor hHfactor
    rw [hfdegree, hgdegree] at hraw
    simpa [two_mul] using hraw
  let M := Polynomial.sylvester B H bdeg bdeg
  have hmap : M.map (Polynomial.evalRingHom z) =
      Polynomial.sylvester f g bdeg bdeg := by
    simpa [M, f, g] using
      (Polynomial.sylvester_map_map B H bdeg bdeg
        (Polynomial.evalRingHom z)).symm
  have hcorank : d.natDegree ≤
      Fintype.card (Fin (bdeg + bdeg)) -
        (M.map (Polynomial.evalRingHom z)).rank := by
    rw [hmap]
    simp only [Fintype.card_fin]
    omega
  have hdet := X_sub_C_pow_corank_dvd_det6401 M z
  have hsmall : (Polynomial.X - Polynomial.C z) ^ d.natDegree ∣
      (Polynomial.X - Polynomial.C z) ^
        (Fintype.card (Fin (bdeg + bdeg)) -
          (M.map (Polynomial.evalRingHom z)).rank) :=
    pow_dvd_pow _ hcorank
  exact hsmall.trans (by simpa [M, Polynomial.resultant] using hdet)
theorem sum_localPowers_le_natDegree6401
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : F[X]) (hR : R ≠ 0) (ω : ι ↪ F) (S : Finset ι) (g : ι → Nat)
    (hlocal : ∀ i ∈ S,
      (Polynomial.X - Polynomial.C (ω i)) ^ g i ∣ R) :
    ∑ i ∈ S, g i ≤ R.natDegree := by
  apply BCHKSWeightedSubstitution.sum_le_natDegree_of_rootMultiplicity
    R ω S g
  intro i hi
  rw [Polynomial.le_rootMultiplicity_iff hR]
  exact hlocal i hi
def graphResultantDegreeUnit6401 : Nat :=
  65536 * (2130706433 + 1)
theorem graphResultantDegreeUnit_exact6401 :
    graphResultantDegreeUnit6401 = 139637976858624 := by
  native_decide
theorem graphResultantExcessCharge_thresholds6401 :
    graphResultantDegreeUnit6401 * 65536 / 115 <
        80251881527475554 ∧
      80251881527475554 ≤
        graphResultantDegreeUnit6401 * 65536 / 114 ∧
      graphResultantDegreeUnit6401 * 65536 / 53 <
        173591179194623459 ∧
      173591179194623459 ≤
        graphResultantDegreeUnit6401 * 65536 / 52 ∧
      graphResultantDegreeUnit6401 * 65536 / 34 <
        273591190752810939 ∧
      273591190752810939 ≤
        graphResultantDegreeUnit6401 * 65536 / 33 := by
  native_decide
end BCHKSFrobeniusResultantMultiplicity6401
end ProximityPrize.SubmissionLower
