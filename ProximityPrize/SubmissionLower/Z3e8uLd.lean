import ProximityPrize.SubmissionLower.A0
set_option Elab.async false
namespace aZa
noncomputable section
open K1 cu DQ MvPolynomial
open vq (ZC)
open scoped Polynomial BigOperators
variable {n:ℕ}
private abbrev incl:=algebraMap L[X] FX
private theorem ayL (S:K[X]) : (S.map jz).eval center=kr S:= by
  rw [Polynomial.eval_map]
  change S.eval₂ (incl.comp (Polynomial.C.comp (algebraMap K L))) (incl Polynomial.X) =
    incl (S.map (algebraMap K L))
  rw [← Polynomial.hom_eval₂,← Polynomial.eval₂_map,Polynomial.eval₂_C_X]
private theorem factorial_ne_zero {i:ℕ} (hi:i<p) : (i.factorial:FX)≠0:= by
  let:CharP FX p:=charP_of_injective_ringHom jz.injective p
  induction i with
  | zero=>simp
  | succ i ih =>
    have hc: ((i+1 :ℕ) :FX)≠0:= by
      intro h
      exact (not_le_of_gt hi) (Nat.le_of_dvd (Nat.succ_pos i) ((CharP.cast_eq_zero_iff FX p _).mp h))
    simpa only [Nat.factorial_succ,Nat.cast_mul] using mul_ne_zero hc (ih (Nat.lt_of_succ_lt hi))
private def weight (x :K) (i:ℕ) :FX :=
  (i.factorial:FX)⁻¹*(jz x - center)^i
private theorem gAQ (S:K[X]) (x :K) (i:ℕ) (hi:i<p) :
    (Polynomial.taylor center (S.map jz)).coeff i*(jz x - center)^i =
      ZC S i*weight x i:= by
  rw [Polynomial.taylor_coeff,Polynomial.hasseDeriv_map,ayL]
  have h:=congrFun (Polynomial.factorial_smul_hasseDeriv (R:=K) i) S
  have hfactor :ZC S i=(i.factorial:FX)*kr (Polynomial.hasseDeriv i S) := by
    dsimp only [ZC]
    rw [← h,LinearMap.smul_apply]
    simp only [nsmul_eq_mul,kr,j9,Polynomial.map_mul,
      Polynomial.map_natCast,map_mul,map_natCast]
  rw [hfactor,weight]
  symm
  calc
    _=(kr (Polynomial.hasseDeriv i S)*(jz x - center)^i) *
        ((i.factorial:FX)*(i.factorial:FX)⁻¹) := by ring
    _ = _:= by rw [mul_inv_cancel₀ (factorial_ne_zero hi),mul_one]
private theorem bds {d:ℕ} (hdp:d<p) (S:K[X]) (hS:S.natDegree≤d) (x :K) :
    jz (S.eval x)=kr S +
      ∑ i∈Finset.range d,ZC S (i+1)*weight x (i+1) := by
  have hd: (Polynomial.taylor center (S.map jz)).natDegree<d+1 := by
    rw [Polynomial.natDegree_taylor]
    exact (Polynomial.natDegree_map_le.trans hS).trans_lt (Nat.lt_succ_self _)
  calc
    _=(Polynomial.taylor center (S.map jz)).eval (jz x - center) := by
      rw [Polynomial.taylor_eval_sub,Polynomial.eval_map_apply]
    _ = _:= by
      rw [Polynomial.eval_eq_sum_range' hd,Finset.sum_range_succ']
      simp only [Polynomial.taylor_coeff_zero,ayL,pow_zero,mul_one]
      rw [add_comm]
      refine congrArg (fun v :FX=>kr S+v) (Finset.sum_congr rfl ?_)
      intro i hi
      exact gAQ S x _ ((Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans_lt hdp)
end
end aZa
