import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Z5
import ProximityPrize.SubmissionLower.P
namespace ProximityPrize.SubmissionLower.RCN205
open scoped Classical WithZero
open RCN187 RCN295
open RCN095 RCN114
open RCN162
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K L:Type} [Field K] [Field L] [Algebra K L]
abbrev DV (L:Type) [Field L]:=Valuation L (WithZero (Multiplicative ℤ))
def zPole (ν:DV L) (x:Fin 3 → L):ℤ:=poleOrder ν (x 2)
def yzPole (ν:DV L) (x:Fin 3 → L):ℤ:=
 max (poleOrder ν (x 0)) (poleOrder ν (x 2))
def allPole (ν:DV L) (x:Fin 3 → L):ℤ:=
 max (poleOrder ν (x 1)) (yzPole ν x)
def movingPole (ν:DV L) (x:Fin 3 → L) (W:L):ℤ:=
 max (2*allPole ν x) (yzPole ν x+poleOrder ν W)
private theorem pole_nonneg (ν:DV L) (x:L):0 ≤ poleOrder ν x:=
 le_max_left _ _
private theorem val_le_exp_pole (ν:DV L) (x:L):
   ν x ≤ WithZero.exp (poleOrder ν x):=by
 have hn:max 1 (ν x)≠0:=ne_of_gt
   (zero_lt_one.trans_le (le_max_left _ _))
 rw [poleOrder, ←log_max_one,WithZero.exp_log hn]
 exact le_max_right _ _
private theorem pole_le_of_val_le (ν:DV L) (x:L) (n:ℤ)
   (hn:0 ≤ n) (h:ν x ≤ WithZero.exp n):poleOrder ν x ≤ n:=by
 have h1:(1:WithZero (Multiplicative ℤ)) ≤ WithZero.exp n:=by
   rw [←WithZero.exp_zero,WithZero.exp_le_exp]
   exact hn
 have hnz:max 1 (ν x)≠0:=ne_of_gt
   (zero_lt_one.trans_le (le_max_left _ _))
 have hh:=(WithZero.log_le_log hnz WithZero.exp_ne_zero).2 (max_le h1 h)
 simpa only [log_max_one,WithZero.log_exp,poleOrder] using hh
theorem pole_add_le (ν:DV L) (x y:L):
   poleOrder ν (x+y) ≤ max (poleOrder ν x) (poleOrder ν y):=by
 apply pole_le_of_val_le ν _ _ ((pole_nonneg ν x).trans (le_max_left _ _))
 exact (ν.map_add x y).trans (max_le
   ((val_le_exp_pole ν x).trans ((WithZero.exp_le_exp).2 (le_max_left _ _)))
   ((val_le_exp_pole ν y).trans ((WithZero.exp_le_exp).2 (le_max_right _ _))))
theorem pole_const_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1) (c:K):
   poleOrder ν (algebraMap K L c) ≤ 0:=by
 apply pole_le_of_val_le ν _ _ le_rfl
 simpa using hν c
theorem pole_const_mul_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1) (c:K) (x:L):
   poleOrder ν (algebraMap K L c*x) ≤ poleOrder ν x:=by
 apply pole_le_of_val_le ν _ _ (pole_nonneg ν x)
 rw [map_mul]
 exact (mul_le_mul' (hν c) (val_le_exp_pole ν x)).trans_eq (one_mul _)
theorem pole_neg (ν:DV L) (x:L):poleOrder ν (-x)=poleOrder ν x:=by
 simp [poleOrder]
def forward (aY v bY aS bS cS:K) (x:Fin 3 → L):Fin 3 → L:=
 forwardResidualPoint (algebraMap K L aY) (algebraMap K L v)
   (algebraMap K L bY) (algebraMap K L aS) (algebraMap K L bS)
   (algebraMap K L cS) x
theorem forward_unit_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (x:Fin 3 → L):
   zPole ν (forward aY v bY aS bS cS x)=zPole ν x∧
   yzPole ν (forward aY v bY aS bS cS x) ≤ yzPole ν x∧
   allPole ν (forward aY v bY aS bS cS x) ≤ allPole ν x:=by
 let A:=algebraMap K L
 have hY:poleOrder ν (A aY+A v*x 0+A bY*x 2) ≤ yzPole ν x:=by
   have h0:=pole_add_le ν (A aY+A v*x 0) (A bY*x 2)
   have h1:=pole_add_le ν (A aY) (A v*x 0)
   have h2:=pole_const_le ν hν aY
   have h3:=pole_const_mul_le ν hν v (x 0)
   have h4:=pole_const_mul_le ν hν bY (x 2)
   have h5:=pole_nonneg ν (x 0)
   dsimp [A] at*
   unfold yzPole
   omega
 have hS:poleOrder ν (A aS+A v*x 1+A bS*x 0+A cS*x 2) ≤
     allPole ν x:=by
   have h0:=pole_add_le ν (A aS+A v*x 1+A bS*x 0) (A cS*x 2)
   have h1:=pole_add_le ν (A aS+A v*x 1) (A bS*x 0)
   have h2:=pole_add_le ν (A aS) (A v*x 1)
   have h3:=pole_const_le ν hν aS
   have h4:=pole_const_mul_le ν hν v (x 1)
   have h5:=pole_const_mul_le ν hν bS (x 0)
   have h6:=pole_const_mul_le ν hν cS (x 2)
   have h7:=pole_nonneg ν (x 1)
   dsimp [A] at*
   unfold allPole yzPole
   omega
 refine ⟨rfl,?_,?_⟩
 · change max (poleOrder ν (A aY+A v*x 0+A bY*x 2))
     (poleOrder ν (x 2)) ≤ yzPole ν x
   exact max_le hY (le_max_right _ _)
 · change max (poleOrder ν (A aS+A v*x 1+A bS*x 0+A cS*x 2))
     (max (poleOrder ν (A aY+A v*x 0+A bY*x 2))
       (poleOrder ν (x 2))) ≤ allPole ν x
   exact max_le hS ((max_le hY (le_max_right _ _)).trans (le_max_right _ _))
theorem forward_inverse (aY v bY aS bS cS:K) (hv:v≠0)
   (x:Fin 3 → L):
   forward (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
     (-v⁻¹*aS+v⁻¹*bS*v⁻¹*aY) (-v⁻¹*bS*v⁻¹)
     (v⁻¹*bS*v⁻¹*bY-v⁻¹*cS) (forward aY v bY aS bS cS x)=x:=by
 have hvL:algebraMap K L v≠0:=(map_ne_zero (algebraMap K L)).2 hv
 funext i
 fin_cases i <;> simp [forward,forwardResidualPoint,map_inv₀] <;>
   field_simp [hvL] <;> ring
theorem forward_unit_invariant (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (hv:v≠0) (x:Fin 3 → L):
   zPole ν (forward aY v bY aS bS cS x)=zPole ν x∧
   yzPole ν (forward aY v bY aS bS cS x)=yzPole ν x∧
   allPole ν (forward aY v bY aS bS cS x)=allPole ν x:=by
 have h:=forward_unit_le ν hν aY v bY aS bS cS x
 have hi:=forward_unit_le ν hν (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
   (-v⁻¹*aS+v⁻¹*bS*v⁻¹*aY) (-v⁻¹*bS*v⁻¹)
   (v⁻¹*bS*v⁻¹*bY-v⁻¹*cS) (forward aY v bY aS bS cS x)
 rw [forward_inverse aY v bY aS bS cS hv x] at hi
 exact ⟨h.1,le_antisymm h.2.1 hi.2.1,le_antisymm h.2.2 hi.2.2⟩
theorem unitAll_eval_pole_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (x:Fin 3 → L) (P:MvPolynomial (Fin 3) K)
   (hP:RCN125.PolynomialInFlag unitAllFlag P):
   poleOrder ν (MvPolynomial.eval₂Hom (algebraMap K L) x P) ≤ allPole ν x:=by
 have h:=(poleOrder_eval_le_support ν (algebraMap K L) hν x P).trans
   (supportPoleWeight_le_exponentSetPoleWeight ν x P (flagSupport unitAllFlag)
     ((support_subset_flagSupport_iff _ _).2 hP))
 simpa only [exponentSetPoleWeight_unitAll,allPole,yzPole] using h
theorem unit_flag_poles_invariant (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (hv:v≠0) (x:Fin 3 → L):
   exponentSetPoleWeight ν (forward aY v bY aS bS cS x) (flagSupport unitZFlag)=
     exponentSetPoleWeight ν x (flagSupport unitZFlag)∧
   exponentSetPoleWeight ν (forward aY v bY aS bS cS x) (flagSupport unitYZFlag)=
     exponentSetPoleWeight ν x (flagSupport unitYZFlag)∧
   exponentSetPoleWeight ν (forward aY v bY aS bS cS x) (flagSupport unitAllFlag)=
     exponentSetPoleWeight ν x (flagSupport unitAllFlag):=by
 simpa only [exponentSetPoleWeight_unitZ,exponentSetPoleWeight_unitYZ,
   exponentSetPoleWeight_unitAll,zPole,yzPole,allPole] using
   forward_unit_invariant ν hν aY v bY aS bS cS hv x
theorem moving_pole_invariant (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (hv:v≠0) (x:Fin 3 → L)
   (c:K) (hc:c≠0) (P:MvPolynomial (Fin 3) K)
   (hP:RCN125.PolynomialInFlag unitAllFlag P)
   (W W':L)
   (hW:W'=algebraMap K L c*W+
     MvPolynomial.eval₂Hom (algebraMap K L) x P):
   movingPole ν (forward aY v bY aS bS cS x) W'=movingPole ν x W:=by
 let t:=MvPolynomial.eval₂Hom (algebraMap K L) x P
 have ht:=unitAll_eval_pole_le ν hν x P hP
 have hplus:=pole_add_le ν (algebraMap K L c*W) t
 have hmul:=pole_const_mul_le ν hν c W
 have hcL:algebraMap K L c≠0:=(map_ne_zero (algebraMap K L)).2 hc
 have hinv:algebraMap K L c⁻¹*(W'-t)=W:=by
   rw [hW]
   simp [t,map_inv₀,hcL]
 have hback:=pole_const_mul_le ν hν c⁻¹ (W'-t)
 rw [hinv] at hback
 have hsub:=pole_add_le ν W' (-t)
 rw [pole_neg] at hsub
 have hu:=forward_unit_invariant ν hν aY v bY aS bS cS hv x
 unfold movingPole
 rw [hu.2.1,hu.2.2]
 have hab:yzPole ν x ≤ allPole ν x:=le_max_right _ _
 have hn:0 ≤ allPole ν x:=(pole_nonneg ν (x 1)).trans (le_max_left _ _)
 have hw:poleOrder ν W' ≤ max (poleOrder ν W) (poleOrder ν t):=by
   rw [hW]
   exact hplus.trans (max_le_max hmul le_rfl)
 change poleOrder ν t ≤ allPole ν x at ht
 rw [sub_eq_add_neg] at hback
 omega
theorem actual_forward_moving_pole_invariant (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (hv:v≠0) (x:Fin 3 → L)
   (c:K) (hc:c≠0) (P:MvPolynomial (Fin 3) K)
   (hP:RCN125.PolynomialInFlag unitAllFlag P)
   (W W':L)
   (hW:W'=algebraMap K L c*W+
     MvPolynomial.eval₂Hom (algebraMap K L) x P):
   movingPole ν
     (forwardResidualPoint (algebraMap K L aY) (algebraMap K L v)
       (algebraMap K L bY) (algebraMap K L aS) (algebraMap K L bS)
       (algebraMap K L cS) x) W'=movingPole ν x W:=
 moving_pole_invariant ν hν aY v bY aS bS cS hv x c hc P hP W W' hW
end
end ProximityPrize.SubmissionLower.RCN205
