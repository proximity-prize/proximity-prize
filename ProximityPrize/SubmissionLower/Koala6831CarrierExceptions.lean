import ProximityPrize.SubmissionLower.Koala6831BivariateSeeds
import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831CarrierExceptions

open Polynomial Koala6831BivariateSeeds
open scoped BigOperators Classical Polynomial

variable {K : Type*} [Field K]

theorem frobenius_degree_le_total (p : ℕ) (hp : 0 < p) (F : SeedPolynomial K) :
    (frobeniusHom p F).natDegree ≤ p * F.totalDegree := by
  change (MvPolynomial.eval₂ (Polynomial.C : K →+* K[X])
    (coordinates Polynomial.X (Polynomial.X ^ p)) F).natDegree ≤ _
  rw [MvPolynomial.eval₂_eq']
  apply natDegree_sum_le_of_forall_le
  intro d hd
  rw [Fin.prod_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [coordinates, ite_true, if_neg h10, ← pow_mul, ← pow_add]
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_X_pow]
  have hdtotal : d 0 + d 1 ≤ F.totalDegree := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using MvPolynomial.le_totalDegree hd
  calc
    d 0 + p * d 1 ≤ p * d 0 + p * d 1 :=
      Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right (d 0) (Nat.succ_le_of_lt hp)) _
    _ = p * (d 0 + d 1) := by ring
    _ ≤ p * F.totalDegree := Nat.mul_le_mul_left p hdtotal

theorem seed_card_le_of_total_degree {p : ℕ} {F : SeedPolynomial K}
    (hF : F ≠ 0) (hsmall : F.totalDegree < p)
    (seeds : Finset K)
    (hzero : ∀ g ∈ seeds, MvPolynomial.eval (coordinates g (g ^ p)) F = 0) :
    seeds.card ≤ p * F.totalDegree := by
  have hp : 0 < p := Nat.zero_lt_of_lt hsmall
  have hencoded : frobeniusHom p F ≠ 0 :=
    frobeniusHom_nonzero (b := F.totalDegree + 1) (c := F.totalDegree + 1)
      hp (Nat.succ_le_of_lt hsmall) hF
      ((MvPolynomial.degreeOf_le_totalDegree _ _).trans_lt (Nat.lt_succ_self _))
      ((MvPolynomial.degreeOf_le_totalDegree _ _).trans_lt (Nat.lt_succ_self _))
  apply le_trans _ (frobenius_degree_le_total p hp F)
  apply card_le_degree_of_subset_roots
  intro g hg
  exact (mem_roots hencoded).mpr ((eval_frobeniusHom p F g).trans (hzero g hg))

theorem resultant_total_degree_le (G H : (SeedPolynomial K)[X]) (m n t : ℕ)
    (hG : ∀ i, (G.coeff i).totalDegree ≤ t)
    (hH : ∀ i, (H.coeff i).totalDegree ≤ t) :
    (Polynomial.resultant G H m n).totalDegree ≤ (m + n) * t := by
  rw [Polynomial.resultant, Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro σ _
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ j, ((Polynomial.sylvester G H m n) (σ j) j).totalDegree) ≤
        ∑ _j : Fin (m + n), t := by
      apply Finset.sum_le_sum
      intro j _
      induction j using Fin.addCases
      · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        split
        · exact hH _
        · simp
      · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        split
        · exact hG _
        · simp
    _ = (m + n) * t := by simp

theorem resultant_eval_eq_zero (G H : (SeedPolynomial K)[X]) (m n : ℕ)
    (hG : G.natDegree ≤ m) (hH : H.natDegree ≤ n) (hpos : m ≠ 0 ∨ n ≠ 0)
    (z : Fin 2 → K) (v : K)
    (hGzero : G.eval₂ (MvPolynomial.eval z) v = 0)
    (hHzero : H.eval₂ (MvPolynomial.eval z) v = 0) :
    MvPolynomial.eval z (Polynomial.resultant G H m n) = 0 := by
  obtain ⟨U, V, _, _, hidentity⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    G H hG hH hpos
  have heval := congrArg (fun P : (SeedPolynomial K)[X] ↦ P.eval₂ (MvPolynomial.eval z) v) hidentity
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    hGzero, hHzero, zero_mul, mul_zero, zero_add] using heval.symm

private theorem derivative_total_degree_le (G : (SeedPolynomial K)[X]) (t : ℕ)
    (hG : ∀ i, (G.coeff i).totalDegree ≤ t) :
    ∀ i, (G.derivative.coeff i).totalDegree ≤ t := by
  intro i
  rw [Polynomial.coeff_derivative]
  have hcast : ((i : SeedPolynomial K) + 1).totalDegree = 0 := by
    rw [← Nat.cast_succ]
    rw [show (↑(i + 1) : SeedPolynomial K) = MvPolynomial.C (↑(i + 1) : K) by simp,
      MvPolynomial.totalDegree_C]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [hcast, Nat.add_zero] using hG (i + 1))

private theorem derivative_ne_zero_of_degree_lt_char {p : ℕ} [CharP K p]
    (G : (SeedPolynomial K)[X]) (hpos : 0 < G.natDegree) (hsmall : G.natDegree < p) :
    G.derivative ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun H : (SeedPolynomial K)[X] ↦ H.coeff (G.natDegree - 1)) hzero
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero,
    Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)] at hcoeff
  rw [← Nat.cast_succ, show (G.natDegree - 1).succ = G.natDegree by omega] at hcoeff
  have hG : G ≠ 0 := by
    intro heq
    rw [heq, Polynomial.natDegree_zero] at hpos
    exact Nat.lt_irrefl _ hpos
  have hlead : G.coeff G.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hG
  have hcast : (G.natDegree : SeedPolynomial K) ≠ 0 := by
    intro hz
    have hdvd := (CharP.cast_eq_zero_iff (SeedPolynomial K) p _).mp hz
    exact (not_le_of_gt hsmall) (Nat.le_of_dvd hpos hdvd)
  exact (mul_ne_zero hlead hcast) hcoeff

theorem singular_seed_count {p : ℕ} [CharP K p] (G : (SeedPolynomial K)[X])
    (hirr : Irreducible G) (hpos : 0 < G.natDegree) (hchar : G.natDegree < p)
    (t : ℕ) (hcoeff : ∀ i, (G.coeff i).totalDegree ≤ t)
    (hsmall : (2 * G.natDegree - 1) * t < p)
    (seeds : Finset K) (values : K → K)
    (hroot : ∀ g ∈ seeds, G.eval₂ (MvPolynomial.eval (coordinates g (g ^ p))) (values g) = 0)
    (hsing : ∀ g ∈ seeds, G.derivative.eval₂ (MvPolynomial.eval (coordinates g (g ^ p)))
      (values g) = 0) :
    seeds.card ≤ p * ((2 * G.natDegree - 1) * t) := by
  have hderivative := derivative_ne_zero_of_degree_lt_char G hpos hchar
  have hproper : ¬ G ∣ G.derivative := by
    intro hdiv
    have hle := Polynomial.natDegree_le_of_dvd hdiv hderivative
    have hdeg := Polynomial.natDegree_derivative_le G
    omega
  let R := Polynomial.resultant G G.derivative G.natDegree G.derivative.natDegree
  have hR : R ≠ 0 := RCN290.irreducible_resultant_nonzero G G.derivative hirr hpos hproper
  have hRdeg : R.totalDegree ≤ (2 * G.natDegree - 1) * t := by
    apply (resultant_total_degree_le G G.derivative _ _ t hcoeff
      (derivative_total_degree_le G t hcoeff)).trans
    apply Nat.mul_le_mul_right
    have he := Polynomial.natDegree_derivative_le G
    omega
  refine (seed_card_le_of_total_degree hR (hRdeg.trans_lt hsmall) seeds ?_).trans
    (Nat.mul_le_mul_left p hRdeg)
  intro g hg
  exact resultant_eval_eq_zero G G.derivative _ _ le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpos))
    _ (values g) (hroot g hg) (hsing g hg)

end ProximityPrize.SubmissionLower.Koala6831CarrierExceptions
