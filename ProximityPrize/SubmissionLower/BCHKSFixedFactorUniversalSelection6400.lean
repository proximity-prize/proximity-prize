import ProximityPrize.SubmissionLower.BCHKSFixedFactorCover6400
import ProximityPrize.SubmissionLower.BCHKSUniversalSelection6399
import ProximityPrize.SubmissionLower.BCHKSUniversalResultantSelection

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace FixedFactorUniversalSelection6400

open FixedFactorCover6400

/-- Score-64 version of the aggregate-incidence conversion used by the
universal selector. -/
theorem exists_large_universal_coordinates_6400
    (T : Finset F)
    (Arow : F → Finset IRSProfile.Index)
    (resultantDegree : ℕ)
    (hrow : ∀ z ∈ T, 262144 - bchksErrors6400 ≤ (Arow z).card)
    (hincidence : (262144 - 131071) * resultantDegree <
      (262144 - bchksErrors6400 - 131071) * T.card) :
    ∃ Coord : Finset IRSProfile.Index,
      131072 ≤ Coord.card ∧
      ∀ i ∈ Coord, resultantDegree <
        (T.filter fun z => i ∈ Arow z).card := by
  classical
  let Coord : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    resultantDegree < (T.filter fun z => i ∈ Arow z).card
  have hcard : 131072 ≤ Coord.card := by
    simpa [Coord] using many_large_fibers T Arow 262144 bchksErrors6400
      131071 resultantDegree (by norm_num [IRSProfile.Index]) hrow
      (by simpa [Nat.mul_comm] using hincidence)
  exact ⟨Coord, hcard, fun i hi => (Finset.mem_filter.mp hi).2⟩

/-- Generic selected-factor assembly.  A branch-independent obstruction `G`
whose degree and common-root properties are supplied by the caller vanishes
modulo one fixed inner factor on at least `k+1` coordinates. -/
theorem exists_fixed_factor_coordinate_divisibility_6400
    (S : Finset F) (Pz : F → Polynomial F) (R : TriPoly)
    (Arow : F → Finset IRSProfile.Index)
    (G : F → BiPoly → IRSProfile.Index → BiPoly)
    (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (hd : R.natDegree ≤ 114) (D : ℕ) (hD : D ≤ 1898945373)
    (hYZ : RationalFunctions.HenselNumerators.ConcreteFiniteNumerators.YZCap R D)
    (hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 8325809424)
    (hroot : ∀ z ∈ S, triEval R z (Pz z) = 0)
    (hS : 144802557 * D < S.card)
    (hrow : ∀ z ∈ S,
      262144 - bchksErrors6400 ≤ (Arow z).card)
    (hGcaps : ∀ x₀ H, H ∈ innerFactors R x₀ → ∀ i,
      (G x₀ H i).natDegree ≤
          bchksUniversalExponent6399 * R.natDegree ∧
      Bivariate.degreeX (G x₀ H i) ≤
          bchksUniversalExponent6399 * D)
    (hGroot : ∀ x₀ z H, H ∈ innerFactors R x₀ →
      z ∈ S →
      innerRel Pz x₀ z H →
      Polynomial.eval ((Pz z).eval x₀)
        (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0 →
      ∀ i ∈ Arow z,
        biEval (G x₀ H i) ((Pz z).eval x₀) z = 0) :
    ∃ x₀ : F, ∃ Bad : Finset F, ∃ H : BiPoly,
      ∃ Coord : Finset IRSProfile.Index,
      Bad.card ≤ 2 * R.natDegree * D ∧
      (triSpecializeX R x₀).natDegree = R.natDegree ∧
      triSpecializeX R x₀ ≠ 0 ∧
      (triSpecializeX R x₀).IsPrimitive ∧
      (∀ z ∉ Bad, Polynomial.eval z
        (Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)) ≠ 0) ∧
      H ∈ innerFactors R x₀ ∧
      bchksErrors6400 + 1 < (innerFiber S Bad Pz x₀ H).card ∧
      131072 ≤ Coord.card ∧
      (∀ z ∈ innerFiber S Bad Pz x₀ H, innerRel Pz x₀ z H) ∧
      (∀ i ∈ Coord, H ∣ G x₀ H i) ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y
          (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  obtain ⟨x₀, Bad, H, hBad, hBdeg, hB0, hprim, hseed, hH, hfiber,
      hsimple⟩ :=
    exists_large_fixed_inner_factor_6400 S Pz R hR hpos hd D hD hYZ
      hweighted hroot hS
  let T := innerFiber S Bad Pz x₀ H
  let rdeg := innerResultantCapacity bchksUniversalExponent6399
    R.natDegree D H
  have hscaled := scaled_pair_capacity_implies_incidence
    (262144 - 131071) (262144 - bchksErrors6400 - 131071)
    rdeg bchksErrors6400 T.card bchks6400_gap_pos (by
      simpa [T, rdeg] using hfiber)
  have hTsub : T ⊆ S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hrowT : ∀ z ∈ T,
      262144 - bchksErrors6400 ≤ (Arow z).card := by
    intro z hz
    exact hrow z (hTsub hz)
  obtain ⟨Coord, hCoord, hlarge⟩ :=
    exists_large_universal_coordinates_6400 T Arow rdeg hrowT hscaled.1
  let Res : IRSProfile.Index → F[X] := fun i =>
    Polynomial.resultant (G x₀ H i) H
      (G x₀ H i).natDegree H.natDegree
  have hResdeg : ∀ i ∈ Coord, (Res i).natDegree ≤ rdeg := by
    intro i hi
    have hg := hGcaps x₀ H hH i
    calc
      (Res i).natDegree ≤
          H.natDegree * Bivariate.degreeX (G x₀ H i) +
            (G x₀ H i).natDegree * Bivariate.degreeX H :=
        bivariate_resultant_natDegree_le (G x₀ H i) H
          (G x₀ H i).natDegree H.natDegree
      _ ≤ H.natDegree * (bchksUniversalExponent6399 * D) +
          (bchksUniversalExponent6399 * R.natDegree) *
            Bivariate.degreeX H := by
        exact Nat.add_le_add (Nat.mul_le_mul_left H.natDegree hg.2)
          (Nat.mul_le_mul_right (Bivariate.degreeX H) hg.1)
      _ = rdeg := rfl
  have hrel : ∀ z ∈ T, innerRel Pz x₀ z H := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hResroot : ∀ i ∈ Coord, ∀ z ∈ T, i ∈ Arow z →
      (Res i).eval z = 0 := by
    intro i hi z hz hiz
    have hzBad : z ∉ Bad := (Finset.mem_sdiff.mp
      (Finset.mem_filter.mp hz).1).2
    have hslope := hsimple z hzBad ((Pz z).eval x₀) (by
      change Polynomial.eval ((Pz z).eval x₀)
        (biSpecializeZ (triSpecializeX R x₀) z) = 0
      change biEval (triSpecializeX R x₀) ((Pz z).eval x₀) z = 0
      rw [← eval_triEval_eq_biEval_triSpecializeX,
        hroot z (hTsub hz)]
      simp)
    have hHdata := Finset.mem_filter.mp hH
    have hHpos : 0 < H.natDegree := hHdata.2
    have hsize : 0 < (G x₀ H i).natDegree + H.natDegree :=
      Nat.add_pos_right _ hHpos
    exact bivariate_resultant_eval_eq_zero_of_common_root
      (G x₀ H i) H (G x₀ H i).natDegree H.natDegree
      z ((Pz z).eval x₀)
      Polynomial.natDegree_map_le Polynomial.natDegree_map_le hsize
      (hGroot x₀ z H hH (hTsub hz) (hrel z hz) hslope i hiz)
      (by
        change biEval H ((Pz z).eval x₀) z = 0
        exact hrel z hz)
  have hReszero : ∀ i ∈ Coord, Res i = 0 :=
    universal_coordinate_obstructions_eq_zero T Arow Coord rdeg Res
      hlarge hResdeg hResroot
  have hHirr : Irreducible H :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hH).1)).irreducible
  have hdiv : ∀ i ∈ Coord, H ∣ G x₀ H i := by
    intro i hi
    apply irreducible_dvd_of_resultant_eq_zero_nonmonic
      (G x₀ H i) H hHirr (Finset.mem_filter.mp hH).2
    simpa only [Res] using hReszero i hi
  exact ⟨x₀, Bad, H, Coord, hBad, hBdeg, hB0, hprim, hseed, hH,
    by simpa [T] using hscaled.2, hCoord,
    by simpa [T] using hrel, hdiv, hsimple⟩

end FixedFactorUniversalSelection6400

end ProximityPrize.SubmissionLower
