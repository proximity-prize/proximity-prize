import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped BigOperators
open RCN234 RCN347 RCN348 RCN233

noncomputable section

set_option maxHeartbeats 1400000

variable {K L : Type*} [Field K] [Field L]

theorem natDegree_eval₂Hom_le_wt
    (weights : Fin 4 → ℕ) (F : MvPolynomial (Fin 4) K)
    (coefficient : K →+* L) (p : Fin 4 → Polynomial L)
    (hdeg : ∀ i, (p i).natDegree ≤ weights i) :
    (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficient) p F).natDegree ≤ wt weights F := by
  classical
  let eval := MvPolynomial.eval₂Hom (Polynomial.C.comp coefficient) p
  change (eval F).natDegree ≤ wt weights F
  have hterm : ∀ d ∈ F.support,
      (eval (MvPolynomial.monomial d (F.coeff d))).natDegree ≤ wt weights F := by
    intro d hd
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_mul]
    have hC : (eval (MvPolynomial.C (F.coeff d))).natDegree ≤ 0 := by
      simp [eval]
    have heval : eval (∏ i : Fin 4, MvPolynomial.X i ^ d i) = ∏ i : Fin 4, p i ^ d i := by
      simp [eval]
    have hprod : (eval (∏ i : Fin 4, MvPolynomial.X i ^ d i)).natDegree ≤ wt weights F := by
      rw [heval]
      refine le_trans (Polynomial.natDegree_prod_le Finset.univ _) ?_
      calc
        (∑ i : Fin 4, (p i ^ d i).natDegree) ≤ ∑ i : Fin 4, d i * weights i :=
          Finset.sum_le_sum (fun i _ => Polynomial.natDegree_pow_le_of_le _ (hdeg i))
        _ = Finsupp.weight weights d := by
          rw [RCN081.weight_fin4]
          simp [Fin.sum_univ_succ, Nat.add_assoc]
        _ ≤ wt weights F := MvPolynomial.le_weightedTotalDegree weights hd
    simpa only [Nat.zero_add] using Polynomial.natDegree_mul_le_of_le hC hprod
  conv_lhs => rw [MvPolynomial.as_sum F, map_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le F.support _ hterm

def centeredGraph (v : Fin 4 → L) (P : Polynomial L) : Fin 4 → Polynomial L :=
  ![Polynomial.C (v 0) + Polynomial.X, P, Polynomial.C (v 2), Polynomial.C (v 3)]

variable {A : Type*} [CommRing A] [Algebra K A]

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
