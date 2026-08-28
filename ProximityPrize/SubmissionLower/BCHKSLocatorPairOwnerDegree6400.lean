import ProximityPrize.SubmissionLower.BCHKSLocatorPairToCode6400

/-!
# Degree of the semilinear owner expression
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

private theorem locatorPairComponent_natDegree_lt
    (d : ℕ) (hd : 0 < d)
    (P : Polynomial.degreeLT IRSProfile.Field d) :
    P.1.natDegree < d := by
  by_cases hP : P.1 = 0
  · simpa only [hP, Polynomial.natDegree_zero] using hd
  · exact (Polynomial.natDegree_lt_iff_degree_lt hP).2
      (Polynomial.mem_degreeLT.mp P.2)

theorem locatorPairOwnerPolynomial_natDegree_lt
    (u : PolynomialPairSpace IRSProfile.Field locatorOrdinaryRows6400
      locatorFrobeniusRows6400)
    (P : IRSProfile.Field[X])
    (hPdegree : P.natDegree ≤ 131071) :
    (u.1.1 * P +
      u.2.1 * P.map koalaSexticFrobenius.toRingHom).natDegree < 185363 := by
  have hu₀degree : u.1.1.natDegree < locatorOrdinaryRows6400 :=
    locatorPairComponent_natDegree_lt locatorOrdinaryRows6400 (by norm_num)
      u.1
  have hu₁degree : u.2.1.natDegree < locatorFrobeniusRows6400 :=
    locatorPairComponent_natDegree_lt locatorFrobeniusRows6400 (by norm_num)
      u.2
  have hmapDegree :
      (P.map koalaSexticFrobenius.toRingHom).natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le
  apply (Polynomial.natDegree_add_le _ _).trans_lt
  apply max_lt
  · apply (Polynomial.natDegree_mul_le).trans_lt
    norm_num [locatorOrdinaryRows6400] at hu₀degree ⊢
    omega
  · apply (Polynomial.natDegree_mul_le).trans_lt
    norm_num [locatorFrobeniusRows6400] at hu₁degree ⊢
    omega

end ProximityPrize.SubmissionLower
