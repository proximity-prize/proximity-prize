import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveInhomogeneousResultantFork6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusResultantMultiplicity6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTwoAxisMultiplicity6401
open Polynomial
open scoped BigOperators
open BCHKSFrobeniusResultantMultiplicity6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
noncomputable def paddedCommonFactorSyzygyMap6401
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree = m) (hgn : g.natDegree ≤ n) :
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
          rw [← hfm, hfa, Polynomial.natDegree_mul hd ha,
            Polynomial.natDegree_mul hT ha]
          omega⟩,
      ⟨-(T.1 * b), by
        rw [Polynomial.mem_degreeLT]
        by_cases hTb : T.1 * b = 0
        · simp [hTb]
        · rw [Polynomial.degree_neg]
          apply (Polynomial.natDegree_lt_iff_degree_lt hTb).1
          have hTne : T.1 ≠ 0 := fun hzero => hTb (by simp [hzero])
          have hb : b ≠ 0 := fun hzero => hTb (by simp [hzero])
          have hTmem := T.2
          rw [Polynomial.mem_degreeLT] at hTmem
          have hTdegree : T.1.natDegree < d.natDegree :=
            (Polynomial.natDegree_lt_iff_degree_lt hTne).2 hTmem
          apply lt_of_lt_of_le _ hgn
          rw [hgb, Polynomial.natDegree_mul hd hb,
            Polynomial.natDegree_mul hTne hb]
          omega⟩⟩
  map_add' T S := by
    apply Prod.ext <;> apply Subtype.ext <;>
      dsimp <;> ring
  map_smul' c T := by
    apply Prod.ext <;> apply Subtype.ext <;>
      dsimp <;> simp
theorem paddedCommonFactorSyzygyMap_injective6401
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree = m) (hgn : g.natDegree ≤ n) :
    Function.Injective
      (paddedCommonFactorSyzygyMap6401
        f g d a b m n hd ha hfa hgb hfm hgn) := by
  intro T S hTS
  apply Subtype.ext
  have hfirst := congrArg (fun p ↦ p.1.1) hTS
  dsimp [paddedCommonFactorSyzygyMap6401] at hfirst
  exact mul_right_cancel₀ ha hfirst
theorem paddedCommonFactorSyzygyMap_mem_sylvesterKernel6401
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree = m) (hgn : g.natDegree ≤ n)
    (T : Polynomial.degreeLT F d.natDegree) :
    Polynomial.sylvesterMap f g (hfm.le) hgn
      (paddedCommonFactorSyzygyMap6401
        f g d a b m n hd ha hfa hgb hfm hgn T) = 0 := by
  apply Subtype.ext
  dsimp [Polynomial.sylvesterMap, paddedCommonFactorSyzygyMap6401]
  rw [hfa, hgb]
  ring
theorem paddedSylvester_rank_le_add_sub_commonFactorDegree6401
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree = m) (hgn : g.natDegree ≤ n) :
    (Polynomial.sylvester f g m n).rank ≤ m + n - d.natDegree := by
  let S := Polynomial.sylvesterMap f g (hfm.le) hgn
  let L := paddedCommonFactorSyzygyMap6401
    f g d a b m n hd ha hfa hgb hfm hgn
  let LK : Polynomial.degreeLT F d.natDegree →ₗ[F]
      LinearMap.ker S := {
    toFun T := ⟨L T, by
      rw [LinearMap.mem_ker]
      exact paddedCommonFactorSyzygyMap_mem_sylvesterKernel6401
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
    apply paddedCommonFactorSyzygyMap_injective6401
      f g d a b m n hd ha hfa hgb hfm hgn
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
    rw [← Polynomial.toMatrix_sylvesterMap' f g (hfm.le) hgn]
    exact Matrix.toLin_toMatrix _ _ _
  rw [Matrix.rank_eq_finrank_range_toLin
    (Polynomial.sylvester f g m n) bout bin, hmatrix]
  exact hrange
theorem X_sub_C_pow_commonFactorDegree_dvd_resultant_unequal6401
    {F : Type*} [Field F]
    (B Q : F[X][X]) (m n : Nat) (z : F)
    (d a b : F[X])
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hBfactor : B.map (Polynomial.evalRingHom z) = d * a)
    (hQfactor : Q.map (Polynomial.evalRingHom z) = d * b)
    (hBdegree : (B.map (Polynomial.evalRingHom z)).natDegree = m)
    (hQdegree : (Q.map (Polynomial.evalRingHom z)).natDegree ≤ n) :
    (Polynomial.X - Polynomial.C z) ^ d.natDegree ∣
      Polynomial.resultant B Q m n := by
  let f := B.map (Polynomial.evalRingHom z)
  let g := Q.map (Polynomial.evalRingHom z)
  have hfdegree : f.natDegree = m := by simpa [f] using hBdegree
  have hgdegree : g.natDegree ≤ n := by simpa [g] using hQdegree
  have hrank : (Polynomial.sylvester f g m n).rank ≤
      m + n - d.natDegree :=
    paddedSylvester_rank_le_add_sub_commonFactorDegree6401
      f g d a b m n hd ha hBfactor hQfactor hfdegree hgdegree
  have hdle : d.natDegree ≤ m := by
    rw [← hBdegree, hBfactor, Polynomial.natDegree_mul hd ha]
    omega
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
  have hdet := X_sub_C_pow_corank_dvd_det6401 M z
  have hsmall : (Polynomial.X - Polynomial.C z) ^ d.natDegree ∣
      (Polynomial.X - Polynomial.C z) ^
        (Fintype.card (Fin (m + n)) -
          (M.map (Polynomial.evalRingHom z)).rank) :=
    pow_dvd_pow _ hcorank
  exact hsmall.trans (by simpa [M, Polynomial.resultant] using hdet)
end BCHKSExtremePrimitiveTwoAxisMultiplicity6401
end ProximityPrize.SubmissionLower
