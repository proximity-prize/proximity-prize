import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A9
namespace ProximityPrize.SubmissionLower.RCN204
open scoped Classical BigOperators WithZero
open RCN095 RCN114
open RCN207 RCN212
open RCN295 RCN187
open RCN002 RCN344
open RCN064
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
private theorem flag_eq {p q:FlagDegree} (hx:p.zOnly=q.zOnly)
   (hy:p.yz=q.yz) (hz:p.all=q.all):p=q:=by
 cases p;cases q;simp_all
theorem coefficient_flag_eq (a b s k:ℕ) (C:FlagDegree)
   (c:Fin (k+1) → FlagDegree)
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (j:Fin (k+1)):
   c j=C+k • (⟨a,b,s⟩:FlagDegree)+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag:=by
 have hx:=congrArg FlagDegree.zOnly (hc j)
 have hy:=congrArg FlagDegree.yz (hc j)
 have hz:=congrArg FlagDegree.all (hc j)
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 apply flag_eq
 all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all,
   unitAllFlag,unitYZFlag] at*
 all_goals nlinarith
variable {K L:Type*} [Field K] [Field L]
theorem filteredCut_div_pow (k:ℕ) (B:Fin (k+1) → L) (H G:L) (hH:H≠0):
   filteredCut k B H G/H^k=∑ j,B j*(G/H)^j.val:=by
 apply (div_eq_iff (pow_ne_zero k hH)).mpr
 have hrel:H*(G/H)=(1:L)*G:=by field_simp
 have h:=binary_clearing k B H G 1 (G/H) hrel
 simpa [filteredCut,mul_comm,mul_left_comm,mul_assoc] using h.symm
def flagPole (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p:FlagDegree):ℤ:=
 (p.zOnly:ℤ)*poleOrder v (x 2)+
 (p.yz:ℤ)*max (poleOrder v (x 0)) (poleOrder v (x 2))+
 (p.all:ℤ)*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2)))
theorem flagPole_nonneg (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p:FlagDegree):0 ≤ flagPole v x p:=by
 unfold flagPole poleOrder
 positivity
@[simp] theorem flagPole_add (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p q:FlagDegree):
   flagPole v x (p+q)=flagPole v x p+flagPole v x q:=by
 simp only [flagPole,add_zOnly,add_yz,add_all,Nat.cast_add]
 ring
@[simp] theorem flagPole_nsmul (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (k:ℕ) (p:FlagDegree):
   flagPole v x (k • p)=(k:ℤ)*flagPole v x p:=by
 simp only [flagPole,nsmul_zOnly,nsmul_yz,nsmul_all,Nat.cast_mul]
 ring
@[simp] theorem flagPole_unitAll (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L):flagPole v x unitAllFlag=
     max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 simp [flagPole,unitAllFlag]
@[simp] theorem flagPole_unitYZ (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L):flagPole v x unitYZFlag=
     max (poleOrder v (x 0)) (poleOrder v (x 2)):=by
 simp [flagPole,unitYZFlag]
theorem valuation_eval_le_flag (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (p:FlagDegree) (B:MvPolynomial (Fin 3) K) (hB:PolynomialInFlag p B):
   v (MvPolynomial.eval₂Hom coeff x B) ≤ WithZero.exp (flagPole v x p):=
 (valuation_eval_le_exp_exponentSet v coeff hcoeff x (flagSupport p) B
   ((support_subset_flagSupport_iff _ _).mpr hB)).trans
   (WithZero.exp_le_exp.mpr (exponentSetPoleWeight_flagSupport_le v x p))
private theorem mixed_weight_le (r j k:ℕ) (h:r+j=k) (A B:ℤ):
   (r:ℤ)*A+(j:ℤ)*B ≤ (k:ℤ)*max A B:=by
 calc
   _ ≤ (r:ℤ)*max A B+(j:ℤ)*max A B:=add_le_add
     (mul_le_mul_of_nonneg_left (le_max_left _ _) (Int.natCast_nonneg _))
     (mul_le_mul_of_nonneg_left (le_max_right _ _) (Int.natCast_nonneg _))
   _=((r+j:ℕ):ℤ)*max A B:=by push_cast;ring
   _=_:=by rw [h]
theorem valuation_polynomialInW_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (w:L) (k:ℕ) (C N:FlagDegree) (B:Fin (k+1) → MvPolynomial (Fin 3) K)
   (hB:∀ j,PolynomialInFlag
     (C+k • N+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag) (B j)):
   v (∑ j,MvPolynomial.eval₂Hom coeff x (B j)*w^j.val) ≤
     WithZero.exp (flagPole v x C+(k:ℤ)*(flagPole v x N+
       max (2*flagPole v x unitAllFlag) (flagPole v x unitYZFlag+poleOrder v w))):=by
 apply v.map_sum_le
 intro j _
 let p:=C+k • N+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag
 have hBj:=valuation_eval_le_flag v coeff hcoeff x p (B j) (hB j)
 have hw:v w ≤ WithZero.exp (poleOrder v w):=
   WithZero.le_exp_of_log_le (le_max_right _ _)
 have hpow:v (w^j.val) ≤ WithZero.exp ((j.val:ℤ)*poleOrder v w):=by
   rw [map_pow]
   simpa only [←WithZero.exp_nsmul,nsmul_eq_mul] using
     pow_le_pow_left₀ (show (0:WithZero (Multiplicative ℤ)) ≤ v w from zero_le) hw j.val
 calc
   v (MvPolynomial.eval₂Hom coeff x (B j)*w^j.val) ≤
       WithZero.exp (flagPole v x p)*WithZero.exp ((j.val:ℤ)*poleOrder v w):=by
     rw [map_mul]
     exact mul_le_mul' hBj hpow
   _=WithZero.exp (flagPole v x p+(j.val:ℤ)*poleOrder v w):=by rw [WithZero.exp_add]
   _ ≤ _:=by
     apply WithZero.exp_le_exp.mpr
     have hm:=mixed_weight_le (k-j.val) j.val k
       (Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt))
       (2*flagPole v x unitAllFlag) (flagPole v x unitYZFlag+poleOrder v w)
     simp only [p,flagPole_add,flagPole_nsmul,Nat.cast_ofNat]
     nlinarith
private theorem poleOrder_le_of_value_le_exp (v:Valuation L (WithZero (Multiplicative ℤ)))
   (z:L) (q:ℤ) (hq:0 ≤ q) (hz:v z ≤ WithZero.exp q):poleOrder v z ≤ q:=by
 apply max_le hq
 by_cases hv:v z=0
 · simpa [hv] using hq
 · simpa only [WithZero.log_exp] using (WithZero.log_le_log hv WithZero.exp_ne_zero).mpr hz
theorem poleOrder_filteredCut_div_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (a b s k:ℕ) (C:FlagDegree) (B:Fin (k+1) → MvPolynomial (Fin 3) K)
   (H G:MvPolynomial (Fin 3) K) (c:Fin (k+1) → FlagDegree)
   (hH:MvPolynomial.eval₂Hom coeff x H≠0)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   poleOrder v (MvPolynomial.eval₂Hom coeff x (filteredCut k B H G)/
     (MvPolynomial.eval₂Hom coeff x H)^k) ≤
   flagPole v x C+(k:ℤ)*(flagPole v x (⟨a,b,s⟩:FlagDegree)+
     max (2*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))+
         poleOrder v (MvPolynomial.eval₂Hom coeff x G/MvPolynomial.eval₂Hom coeff x H))):=by
 rw [map_filteredCut,filteredCut_div_pow k _ _ _ hH]
 apply poleOrder_le_of_value_le_exp
 · have hC:=flagPole_nonneg v x C
   have hN:=flagPole_nonneg v x (⟨a,b,s⟩:FlagDegree)
   dsimp [poleOrder]
   positivity
 · simpa only [flagPole_unitAll,flagPole_unitYZ] using
     valuation_polynomialInW_le v coeff hcoeff x
       (MvPolynomial.eval₂Hom coeff x G/MvPolynomial.eval₂Hom coeff x H)
       k C (⟨a,b,s⟩:FlagDegree) B (fun j↦by
         rw [←coefficient_flag_eq a b s k C c hc j]
         exact hB j)
theorem coordinate_filteredCut_pole_le {Ω:Type} [Field Ω]
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (v:Place Ω (CoordinateField Ω P)) (a b s k:ℕ) (C:FlagDegree)
   (B:Fin (k+1) → MvPolynomial (Fin 3) Ω) (H G:MvPolynomial (Fin 3) Ω)
   (c:Fin (k+1) → FlagDegree) (hH:coordinateEvaluation Ω P H≠0)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   poleOrder v.val (coordinateEvaluation Ω P (filteredCut k B H G)/
     (coordinateEvaluation Ω P H)^k) ≤
     flagPole v.val (coordinate Ω P) C+(k:ℤ)*
       (flagPole v.val (coordinate Ω P) (⟨a,b,s⟩:FlagDegree)+movingPoleTarget P H G v):=by
 have h:=poleOrder_filteredCut_div_le v.val (algebraMap Ω (CoordinateField Ω P))
   (constant_value_le_one Ω (CoordinateField Ω P) v) (coordinate Ω P)
   a b s k C B H G c (by
     simpa only [coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom] using hH) hB hc
 simpa only [coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom,
   movingPoleTarget,movingRatio] using h
end
end ProximityPrize.SubmissionLower.RCN204
