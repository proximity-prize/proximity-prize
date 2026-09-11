import ProximityPrize.SubmissionLower.PartF003_06
section Compact_PackedLegacyCore1
section PackedLegacy_AH
namespace ProximityPrize.SubmissionLower.RCN295
open scoped Classical BigOperators WithZero
open RCN187
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
local instance:DecidableEq K:=Classical.decEq K

theorem valuation_eval_le_exp_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     WithZero.exp (supportPoleWeight v x F):=by
 classical
 conv_lhs => rw [MvPolynomial.as_sum F,map_sum]
 apply v.map_sum_le
 intro d hd
 exact valuation_monomial_le_exp_support v coeff hcoeff x F d hd
   (F.coeff d)
theorem valuation_eval_le_exp_exponentSet
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (F:MvPolynomial σ K)
   (hFE:F.support ⊆ E):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     WithZero.exp (exponentSetPoleWeight v x E):=by
 exact (valuation_eval_le_exp_support v coeff hcoeff x F).trans
   ((WithZero.exp_le_exp).2
     (supportPoleWeight_le_exponentSetPoleWeight v x F E hFE))
theorem poleOrder_eval_le_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K):
   poleOrder v (MvPolynomial.eval₂Hom coeff x F) ≤
     supportPoleWeight v x F:=by
 classical
 have heval:=valuation_eval_le_exp_support v coeff hcoeff x F
 have hone:(1:WithZero (Multiplicative ℤ)) ≤
     WithZero.exp (supportPoleWeight v x F):=by
   rw [←WithZero.exp_zero,WithZero.exp_le_exp]
   exact supportPoleWeight_nonneg v x F
 have hmax:max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≤
     WithZero.exp (supportPoleWeight v x F):=max_le hone heval
 have hleft0:max 1 (v (MvPolynomial.eval₂Hom coeff x F))≠0:=
   ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
 have hlog:=(WithZero.log_le_log hleft0 WithZero.exp_ne_zero).2 hmax
 rw [log_max_one,WithZero.log_exp] at hlog
 simpa only [poleOrder] using hlog
theorem weighted_poleOrder_eval_le_exponentSet
   {τ:Type*} (S:Finset τ) (weight:τ → ℕ)
   (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L)
   (hcoeff:∀ t∈S,∀ c:K,v t (coeff c) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (F:MvPolynomial σ K)
   (hFE:F.support ⊆ E):
   (∑ t∈S,(weight t:ℤ)*
     poleOrder (v t) (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∑ t∈S,(weight t:ℤ)*exponentSetPoleWeight (v t) x E:=by
 classical
 apply Finset.sum_le_sum
 intro t ht
 apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
 exact (poleOrder_eval_le_support (v t) coeff (hcoeff t ht) x F).trans
   (supportPoleWeight_le_exponentSetPoleWeight (v t) x F E hFE)
end
end ProximityPrize.SubmissionLower.RCN295
end PackedLegacy_AH

/-! Packed from ProximityPrize.SubmissionLower.D. -/
section PackedLegacy_D
namespace ProximityPrize.SubmissionLower.RCN095
open scoped BigOperators
open ProximityPrize.SubmissionLower.RCN295
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
structure FlagDegree where
 zOnly:ℕ
 yz:ℕ
 all:ℕ
 deriving DecidableEq,Repr
instance:Add FlagDegree:=⟨fun p q↦
 ⟨p.zOnly+q.zOnly,p.yz+q.yz,p.all+q.all⟩⟩
instance:SMul ℕ FlagDegree:=⟨fun n p↦
 ⟨n*p.zOnly,n*p.yz,n*p.all⟩⟩
@[simp] theorem add_zOnly (p q:FlagDegree):
   (p+q).zOnly=p.zOnly+q.zOnly:=rfl
@[simp] theorem add_yz (p q:FlagDegree):
   (p+q).yz=p.yz+q.yz:=rfl
@[simp] theorem add_all (p q:FlagDegree):
   (p+q).all=p.all+q.all:=rfl
@[simp] theorem nsmul_zOnly (n:ℕ) (p:FlagDegree):
   (n • p).zOnly=n*p.zOnly:=rfl
@[simp] theorem nsmul_yz (n:ℕ) (p:FlagDegree):
   (n • p).yz=n*p.yz:=rfl
@[simp] theorem nsmul_all (n:ℕ) (p:FlagDegree):
   (n • p).all=n*p.all:=rfl
def InFlag (p:FlagDegree) (d:Fin 3 →₀ ℕ):Prop:=
 d 1 ≤ p.all∧
   d 0+d 1 ≤ p.yz+p.all∧
   d 0+d 1+d 2 ≤ p.zOnly+p.yz+p.all
theorem inFlag_zero (p:FlagDegree):InFlag p 0:=by
 simp [InFlag]
theorem inFlag_add {p q:FlagDegree} {d e:Fin 3 →₀ ℕ}
   (hd:InFlag p d) (he:InFlag q e):InFlag (p+q) (d+e):=by
 rcases hd with ⟨hdS,hdYS,hdTot⟩
 rcases he with ⟨heS,heYS,heTot⟩
 simp only [InFlag,Finsupp.add_apply,add_zOnly,add_yz,add_all]
 omega
noncomputable def exponentOfTriple (t:ℕ × ℕ × ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 t.1+Finsupp.single 1 t.2.1+
   Finsupp.single 2 t.2.2
noncomputable def flagSupport (p:FlagDegree):Finset (Fin 3 →₀ ℕ):=
 by
   classical
   exact (((((Finset.range (p.zOnly+p.yz+p.all+1)).product
       (Finset.range (p.all+1))).product
       (Finset.range (p.zOnly+p.yz+p.all+1))).image
         (fun t↦exponentOfTriple (t.1.1,t.1.2,t.2))).filter (InFlag p))
theorem mem_flagSupport_iff (p:FlagDegree) (d:Fin 3 →₀ ℕ):
   d∈flagSupport p ↔ InFlag p d:=by
 classical
 constructor
 · intro hd
   unfold flagSupport at hd
   exact (Finset.mem_filter.mp hd).2
 · intro hd
   unfold flagSupport
   rw [Finset.mem_filter]
   refine ⟨?_,hd⟩
   apply Finset.mem_image.mpr
   rcases hd with ⟨hS,hYS,htotal⟩
   refine ⟨((d 0,d 1),d 2),?_,?_⟩
   · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
       ⟨Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega),
         Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega)⟩,
       Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega)⟩
   · ext i
     fin_cases i <;> simp [exponentOfTriple]
theorem zero_mem_flagSupport (p:FlagDegree):
   (0:Fin 3 →₀ ℕ)∈flagSupport p:=by
 rw [mem_flagSupport_iff]
 exact inFlag_zero p
theorem flagSupport_downwardClosed (p:FlagDegree):
   ExponentSetDownwardClosed (flagSupport p):=by
 intro d hd e he
 rw [mem_flagSupport_iff] at hd ⊢
 rcases hd with ⟨hdS,hdYS,hdtotal⟩
 have h0:=he 0
 have h1:=he 1
 have h2:=he 2
 exact ⟨h1.trans hdS,by omega,by omega⟩
def PolynomialInFlag {K:Type*} [Field K]
   (p:FlagDegree) (A:MvPolynomial (Fin 3) K):Prop:=
 ∀ d∈A.support,InFlag p d
theorem support_subset_flagSupport_iff {K:Type*} [Field K]
   (p:FlagDegree) (A:MvPolynomial (Fin 3) K):
   A.support ⊆ flagSupport p ↔ PolynomialInFlag p A:=by
 simp only [PolynomialInFlag,Finset.subset_iff,mem_flagSupport_iff]
def flagSWeights:Fin 3 → ℕ:=![0,1,0]
def flagYSWeights:Fin 3 → ℕ:=![1,1,0]
def flagTotalWeights:Fin 3 → ℕ:=![1,1,1]
theorem flag_weight_fin3 (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 rw [hd,map_add,map_add]
 simp [Finsupp.weight_single,Nat.mul_comm]
def flagMixed (p q r:FlagDegree):ℕ:=
 p.all*q.all*r.all+
 (p.zOnly*q.all*r.all+q.zOnly*p.all*r.all+
   r.zOnly*p.all*q.all)+
 (p.yz*q.all*r.all+q.yz*p.all*r.all+
   r.yz*p.all*q.all)+
 (p.all*q.yz*r.yz+q.all*p.yz*r.yz+
   r.all*p.yz*q.yz)+
 (p.zOnly*q.yz*r.all+p.zOnly*r.yz*q.all+
   q.zOnly*p.yz*r.all+q.zOnly*r.yz*p.all+
   r.zOnly*p.yz*q.all+r.zOnly*q.yz*p.all)
def unitZFlag:FlagDegree:=⟨1,0,0⟩
def unitYZFlag:FlagDegree:=⟨0,1,0⟩
def unitAllFlag:FlagDegree:=⟨0,0,1⟩
def seedFlag:FlagDegree:=unitYZFlag
private def legacyN:ℕ:=262144
private def legacyW:ℕ:=131071
private def legacyErrors:ℕ:=78210
private def legacyAgreements:ℕ:=legacyN-legacyErrors
private def legacyGap:ℕ:=legacyAgreements-legacyW
private def legacyAlignmentBudget:ℕ:=100000000000000000
private def legacyShearedWholeMixedCap:ℕ:=16230040480658160
private def legacySingularNumerator:ℕ:=8043405963321174171
private def legacyGapSquared:ℕ:=legacyGap^2
def shearedSurfaceFlag:FlagDegree:=⟨350,21,5⟩
def shearedDerivativeFlag:FlagDegree:=⟨350,21,4⟩
def shearedAgreementFlag:FlagDegree:=
 seedFlag+legacyW • (shearedSurfaceFlag+shearedDerivativeFlag)
theorem shearedAgreementFlag_value:
   shearedAgreementFlag=⟨91749700,5504983,1179639⟩:=by
 change (⟨0+131071*(350+350),
     1+131071*(21+21),
     0+131071*(5+4)⟩:FlagDegree)=_
 norm_num
def flagWholeMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag shearedAgreementFlag
def flagZMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitZFlag
def flagYZMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitYZFlag
def flagAllMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitAllFlag
theorem flag_mixed_values:
   flagWholeMixedCap=16236998221509765∧
     flagZMixedCap=58195529∧
     flagYZMixedCap=929817679∧
     flagAllMixedCap=4898910072:=by
 norm_num [flagWholeMixedCap,flagZMixedCap,flagMixed,
   flagYZMixedCap,flagAllMixedCap,
   shearedSurfaceFlag,shearedAgreementFlag,shearedDerivativeFlag,
   seedFlag,unitZFlag,unitYZFlag,unitAllFlag,legacyW]
theorem flag_projection_decomposition:
   flagWholeMixedCap=
     shearedAgreementFlag.zOnly*flagZMixedCap+
     shearedAgreementFlag.yz*flagYZMixedCap+
     shearedAgreementFlag.all*flagAllMixedCap:=by
 norm_num [flagWholeMixedCap,flagZMixedCap,flagYZMixedCap,
   flagAllMixedCap,flagMixed,shearedSurfaceFlag,
   shearedAgreementFlag,shearedDerivativeFlag,seedFlag,
   unitZFlag,unitYZFlag,unitAllFlag,legacyW]
def flagWholeNumerator:ℕ:=
 (legacyN-legacyW)^2*flagWholeMixedCap+
   (legacyErrors+1)*(legacyN-legacyW)*legacyGap*flagZMixedCap
def flagTotalNumerator:ℕ:=
 flagWholeNumerator+legacyGap*legacySingularNumerator
def flagLedgerCeiling:ℕ:=
 (flagTotalNumerator+legacyGapSquared-1)/legacyGapSquared
end ProximityPrize.SubmissionLower.RCN095
end PackedLegacy_D

/-! Packed from ProximityPrize.SubmissionLower.BO. -/
section PackedLegacy_BO
namespace ProximityPrize.SubmissionLower.RCN156
open scoped Classical BigOperators
open RCN157 RCN234 RCN235 RCN095 RCN136 RCN313
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
def residualPullWeights (weights:Fin 4 → ℕ):Fin 4 → ℕ:=
 ![weights 0,
   max (weights 1) (weights 3),
   max (weights 2) (max (weights 1) (weights 3)),
   weights 3]
theorem wt_embedX_zero (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (P:Polynomial K):
   wt weights (embedX K P)=0:=by
 induction P using Polynomial.induction_on' with
 | add P Q hP hQ =>
     rw [map_add]
     apply Nat.eq_zero_of_le_zero
     exact (wt_add_le weights (embedX K P) (embedX K Q)).trans
       (by simpa only [hP,hQ,max_self] using (Nat.le_refl 0))
 | monomial n a =>
     have hembed:embedX K (Polynomial.monomial n a)=
         MvPolynomial.C a*MvPolynomial.X (0:Fin 4)^n:=by
       simp [embedX]
     rw [hembed]
     apply Nat.eq_zero_of_le_zero
     have hm:=wt_mul_le weights (MvPolynomial.C a:Poly4 K)
       (MvPolynomial.X (0:Fin 4)^n)
     have hp:=wt_pow_le weights (MvPolynomial.X (0:Fin 4):Poly4 K) n
     rw [wt_C] at hm
     rw [wt_X,hX,Nat.mul_zero] at hp
     omega
theorem globalResidualImage_wt_le
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (P0 P1 V:Polynomial K) (i:Fin 4):
   wt weights (globalResidualImage P0 P1 V i) ≤
     residualPullWeights weights i:=by
 fin_cases i
 · simp [globalResidualImage,residualPullWeights,wt_X]
 · dsimp [globalResidualImage,residualPullWeights]
   have hP0:=wt_embedX_zero weights hX P0
   have hP1:=wt_embedX_zero weights hX P1
   have hV:=wt_embedX_zero weights hX V
   have hz:=wt_mul_le weights
     (MvPolynomial.X (3:Fin 4):Poly4 K) (embedX K P1)
   have hy:=wt_mul_le weights (embedX K V)
     (MvPolynomial.X (1:Fin 4):Poly4 K)
   rw [wt_X,hP1,Nat.add_zero] at hz
   rw [hV,wt_X,Nat.zero_add] at hy
   have h01:=wt_add_le weights (embedX K P0)
     (MvPolynomial.X (3:Fin 4)*embedX K P1)
   have h012:=wt_add_le weights
     (embedX K P0+MvPolynomial.X (3:Fin 4)*embedX K P1)
     (embedX K V*MvPolynomial.X (1:Fin 4))
   omega
 · dsimp [globalResidualImage,residualPullWeights]
   have hP0:=wt_embedX_zero weights hX P0.derivative
   have hP1:=wt_embedX_zero weights hX P1.derivative
   have hV':=wt_embedX_zero weights hX V.derivative
   have hV:=wt_embedX_zero weights hX V
   have hz:=wt_mul_le weights
     (MvPolynomial.X (3:Fin 4):Poly4 K) (embedX K P1.derivative)
   have hy:=wt_mul_le weights (embedX K V.derivative)
     (MvPolynomial.X (1:Fin 4):Poly4 K)
   have hr:=wt_mul_le weights (embedX K V)
     (MvPolynomial.X (2:Fin 4):Poly4 K)
   rw [wt_X,hP1,Nat.add_zero] at hz
   rw [hV',wt_X,Nat.zero_add] at hy
   rw [hV,wt_X,Nat.zero_add] at hr
   have h01:=wt_add_le weights (embedX K P0.derivative)
     (MvPolynomial.X (3:Fin 4)*embedX K P1.derivative)
   have h012:=wt_add_le weights
     (embedX K P0.derivative+
       MvPolynomial.X (3:Fin 4)*embedX K P1.derivative)
     (embedX K V.derivative*MvPolynomial.X (1:Fin 4))
   have h0123:=wt_add_le weights
     (embedX K P0.derivative+
       MvPolynomial.X (3:Fin 4)*embedX K P1.derivative+
       embedX K V.derivative*MvPolynomial.X (1:Fin 4))
     (embedX K V*MvPolynomial.X (2:Fin 4))
   omega
 · simp [globalResidualImage,residualPullWeights,wt_X]
theorem globalResidual_monomial_product_wt_le
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (P0 P1 V:Polynomial K) (d:Fin 4 →₀ ℕ):
   wt weights
       (∏ i∈d.support,globalResidualImage P0 P1 V i^d i) ≤
     Finsupp.weight (residualPullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦globalResidualImage P0 P1 V i^d i)).trans
 calc
   (∑ i∈d.support,
       wt weights (globalResidualImage P0 P1 V i^d i)) ≤
       ∑ i∈d.support,d i*residualPullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (globalResidualImage P0 P1 V i) (d i)).trans
       (Nat.mul_le_mul_left _
         (globalResidualImage_wt_le weights hX P0 P1 V i))
   _=Finsupp.weight (residualPullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem globalResidualHom_wt_le_pulled
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (P0 P1 V:Polynomial K) (F:Poly4 K):
   wt weights (globalResidualHom P0 P1 V F) ≤
     wt (residualPullWeights weights) F:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C
       (globalResidualImage P0 P1 V) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=globalResidual_monomial_product_wt_le
   weights hX P0 P1 V d
 have hcoeff:wt weights
     (MvPolynomial.C (F.coeff d):Poly4 K)=0:=wt_C weights _
 have hmul:=wt_mul_le weights
   (MvPolynomial.C (F.coeff d):Poly4 K)
   (∏ i∈d.support,globalResidualImage P0 P1 V i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree
     (residualPullWeights weights) hd))
def residualSWeights:Fin 4 → ℕ:=![0,0,1,0]
def residualYSWeights:Fin 4 → ℕ:=![0,1,1,0]
def residualTotalWeights:Fin 4 → ℕ:=![0,1,1,1]
theorem residualPullWeights_s:
   residualPullWeights residualSWeights=residualSWeights:=by
 funext i
 fin_cases i <;> rfl
theorem residualPullWeights_ys:
   residualPullWeights residualYSWeights=residualYSWeights:=by
 funext i
 fin_cases i <;> rfl
theorem residualPullWeights_total:
   residualPullWeights residualTotalWeights=residualTotalWeights:=by
 funext i
 fin_cases i <;> rfl
def residualAgreementFlag (d:ℕ):FlagDegree:=
 ⟨920*d,1+70*d,15*d⟩
end
end ProximityPrize.SubmissionLower.RCN156
end PackedLegacy_BO

/-! Packed from ProximityPrize.SubmissionLower.D5. -/
section PackedLegacy_D5
namespace ProximityPrize.SubmissionLower.RCN215
open RCN095 RCN156 RCN213
def surfaceFlag6600:FlagDegree:=⟨460,35,8⟩
def derivativeFlag6600:FlagDegree:=⟨460,35,7⟩
def agreementDirection6600:FlagDegree:=⟨920,70,15⟩
end ProximityPrize.SubmissionLower.RCN215
end PackedLegacy_D5

/-! Packed from ProximityPrize.SubmissionLower.D4. -/
section PackedLegacy_D4
namespace ProximityPrize.SubmissionLower.RCN214
open scoped BigOperators
open RCN095 RCN213 RCN215
set_option maxHeartbeats 1000000
def factorPrimary (p:FlagDegree):ℕ:=
 flagMixed p agreementDirection6600 agreementDirection6600*degreeIncidence^2+
   2*flagMixed p agreementDirection6600 unitYZFlag*
     degreeIncidence*unitIncidence+
   flagMixed p unitYZFlag unitYZFlag*unitIncidence^2
def factorZTail (p:FlagDegree):ℕ:=
 (errors+1)*gap*
   (flagMixed p agreementDirection6600 unitZFlag*degreeIncidence+
     flagMixed p unitYZFlag unitZFlag*unitIncidence)
def factorAllTail (p:FlagDegree):ℕ:=
 (errors+1)*gap*
   (flagMixed p agreementDirection6600 unitAllFlag*degreeIncidence+
     flagMixed p unitYZFlag unitAllFlag*unitIncidence)
def factorRegularLedger (p:FlagDegree):ℕ:=
 factorPrimary p+factorZTail p+factorAllTail p
theorem factorRegularLedger_projection_decomposition (p:FlagDegree):
   factorRegularLedger p=
     p.zOnly*factorRegularLedger unitZFlag+
     p.yz*factorRegularLedger unitYZFlag+
     p.all*factorRegularLedger unitAllFlag:=by
 cases p
 simp [factorRegularLedger,factorPrimary,factorZTail,factorAllTail,flagMixed,
   unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem sum_factorRegularLedger_le_flag
   {I:Type} [Fintype I] (p:I → FlagDegree) (cap:FlagDegree)
   (hz:(∑ i,(p i).zOnly) ≤ cap.zOnly)
   (hyz:(∑ i,(p i).yz) ≤ cap.yz)
   (hall:(∑ i,(p i).all) ≤ cap.all):
   (∑ i,factorRegularLedger (p i)) ≤ factorRegularLedger cap:=by
 classical
 calc
   (∑ i,factorRegularLedger (p i))=
       ∑ i,((p i).zOnly*factorRegularLedger unitZFlag+
         (p i).yz*factorRegularLedger unitYZFlag+
         (p i).all*factorRegularLedger unitAllFlag):=by
     apply Finset.sum_congr rfl
     intro i _
     exact factorRegularLedger_projection_decomposition (p i)
   _=
       (∑ i,(p i).zOnly)*factorRegularLedger unitZFlag+
       (∑ i,(p i).yz)*factorRegularLedger unitYZFlag+
       (∑ i,(p i).all)*factorRegularLedger unitAllFlag:=by
     simp only [Finset.sum_add_distrib,Finset.sum_mul]
   _ ≤ cap.zOnly*factorRegularLedger unitZFlag+
       cap.yz*factorRegularLedger unitYZFlag+
       cap.all*factorRegularLedger unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_right _ hz)
         (Nat.mul_le_mul_right _ hyz))
       (Nat.mul_le_mul_right _ hall)
   _=factorRegularLedger cap:=
     (factorRegularLedger_projection_decomposition cap).symm
def rectangularSurfaceFlag6600:FlagDegree:=⟨495,43,8⟩
def rectangularRegularNumerator:ℕ:=
 factorRegularLedger rectangularSurfaceFlag6600
def rectangularTotalNumerator:ℕ:=
 rectangularRegularNumerator+retainedSingularContribution
def rectangularLedgerCeiling:ℕ:=
 (rectangularTotalNumerator+gap^2-1)/gap^2
theorem sum_factorRegularLedger_rectangular_le
   {I:Type} [Fintype I] (p:I → FlagDegree)
   (hz:(∑ i,(p i).zOnly) ≤ 495)
   (hyz:(∑ i,(p i).yz) ≤ 43)
   (hall:(∑ i,(p i).all) ≤ 8):
   (∑ i,factorRegularLedger (p i)) ≤ rectangularRegularNumerator:=by
 exact sum_factorRegularLedger_le_flag p rectangularSurfaceFlag6600 hz hyz hall
theorem sum_factor_counts_rectangular_le
   {I:Type} [Fintype I] (count:I → ℕ) (p:I → FlagDegree)
   (hcount:∀ i,count i*gap^2 ≤ factorRegularLedger (p i))
   (hz:(∑ i,(p i).zOnly) ≤ 495)
   (hyz:(∑ i,(p i).yz) ≤ 43)
   (hall:(∑ i,(p i).all) ≤ 8):
   (∑ i,count i)*gap^2 ≤ rectangularRegularNumerator:=by
 calc
   (∑ i,count i)*gap^2=∑ i,count i*gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ i,factorRegularLedger (p i):=
     Finset.sum_le_sum (fun i _↦hcount i)
   _ ≤ rectangularRegularNumerator:=
     sum_factorRegularLedger_rectangular_le p hz hyz hall
end ProximityPrize.SubmissionLower.RCN214
end PackedLegacy_D4

/-! Packed from ProximityPrize.SubmissionLower.AC. -/
section PackedLegacy_AC
namespace ProximityPrize.SubmissionLower.RCN266
open scoped BigOperators
open RCN223 RCN286 RCN167 RCN174 RCN136 RCN095
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
abbrev RegularIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(positiveRFactors Q)
def regularFlag (Q:MvPolynomial (Fin 4) K) (F:RegularIndex Q):
   FlagDegree:=
 ⟨F.1.degreeOf (3:Fin 4),F.1.degreeOf (1:Fin 4),
   F.1.degreeOf (2:Fin 4)⟩
theorem regularFlag_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap):
   (∑ F:RegularIndex Q,(regularFlag Q F).zOnly) ≤ 495∧
     (∑ F:RegularIndex Q,(regularFlag Q F).yz) ≤ 43∧
     (∑ F:RegularIndex Q,(regularFlag Q F).all) ≤ 8:=by
 classical
 have hb:=directFactor_input_budgets Q hQ
   weightedCap w seedTotalCap slopeCap (by norm_num [w]) hbox
 simp only [regularFlag,Finset.sum_coe_sort]
 refine ⟨?_,?_,?_⟩
 · simpa [seedTotalCap] using hb.2.2
 · have hy:(weightedCap-1)/w=43:=by
     norm_num [RCN223.weightedCap,
       RCN223.multiplicity,
       RCN223.agreements,
       RCN223.n,
       RCN223.errors,
       RCN223.w]
   simpa only [hy] using hb.1
 · simpa [slopeCap] using hb.2.1
end
end ProximityPrize.SubmissionLower.RCN266
end PackedLegacy_AC

/-! Packed from ProximityPrize.SubmissionLower.I3. -/
section PackedLegacy_I3
namespace ProximityPrize.SubmissionLower.RCN069
open RCN223 RCN174 RCN136 RCN068 RCN238
noncomputable section
def legacyVector (v:RCN223.DegreeVector):
   RCN051.DegreeVector:=⟨v.y,v.r,v.z⟩
variable {K Omega:Type} [Field K] [Field Omega]
theorem fixed_implicit_agreement_caps
   (phi:Polynomial K →+*Omega) (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ implicitYCap)
   (hR:F.degreeOf 2 ≤ 1) (hZ:F.degreeOf 3 ≤ algebraicCap)
   (x u0 u1:K):
   HasCaps (agreementPolynomial phi F w x u0 u1)
     (legacyVector liftedAgreement):=by
 have h:=surface_agreement_caps phi F implicitYCap 1 algebraicCap
   (by decide) hY hR hZ w (fun j => (j.factorial:K)⁻¹) x u0 u1
 simpa [agreementPolynomial,agreementCaps,legacyVector,
   liftedAgreement] using h
theorem fixed_implicit_surface_caps_below_characteristic:
   forall j,capAt (legacyVector liftedSurface) j < prime:=by
 intro j
 fin_cases j <;>
   norm_num [capAt,legacyVector,liftedSurface,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
theorem fixed_implicit_characteristic_gates
   (G T:MvPolynomial (Fin 3) Omega)
   (hG:HasCaps G (legacyVector liftedSurface))
   (hT:HasCaps T (legacyVector implicitCut)):
   (forall j,G.degreeOf j < prime)∧
     forall j k:Fin 3,j≠k->
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < prime:=by
 apply actual_characteristic_gates G T _ _ prime hG hT
   fixed_implicit_surface_caps_below_characteristic
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitY,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitR,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitZ,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
end
end ProximityPrize.SubmissionLower.RCN069
end PackedLegacy_I3

/-! Packed from ProximityPrize.SubmissionLower.K6. -/
section PackedLegacy_K6
namespace ProximityPrize.SubmissionLower.RCN171
open scoped Classical BigOperators
open RCN223 RCN294 RCN069 RCN068 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001
noncomputable section
variable {K:Type} [Field K]
def pairCost (A G:MvPolynomial (Fin 4) K):RCN223.DegreeVector:=
 ⟨RCN169.pairYCost ⟨A,G⟩,
   RCN169.pairRCost ⟨A,G⟩,
   RCN169.pairZCost ⟨A,G⟩⟩
variable {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound_fixed
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (hAbox:A∈globalCoefficientBox K implicitWeightedCap w algebraicCap 0)
   (hGbox:G∈globalCoefficientBox K implicitWeightedCap w algebraicCap 1)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K prime]
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     agreements ≤ (nodes.filter (fun i =>
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
   Γ.card*gap ≤ (n-w)*dot liftedAgreement (pairCost A G)+
     (errors+1)*gap*RCN169.pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitWeightedCap w algebraicCap 0
   (by norm_num [w]) hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitWeightedCap w algebraicCap 1
   (by norm_num [w]) hGbox
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) (legacyVector implicitCut):=by
   intro i
   fin_cases i
   · simpa [legacyVector,RCN068.capAt,implicitCut,implicitYCap] using
       (surfaceMap_degreeOf_le φ A 0).trans hAGcaps.1
   · simpa [legacyVector,RCN068.capAt,implicitCut] using
       (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · simpa [legacyVector,RCN068.capAt,implicitCut] using
       (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ (polynomialEmbedding_injective K)
     G hG.ne_zero (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*gap ≤
       (n-w)*(∑ i:Fin 3,
         capAt (legacyVector liftedAgreement) i*
           capAt (RCN170.geometricPairCost A g) i)+
         (errors+1)*gap*
           capAt (RCN170.geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g (legacyVector liftedSurface):=by
     intro i
     fin_cases i
     · simpa [legacyVector,RCN068.capAt,liftedSurface,implicitYCap] using
         (hfacdegree 0).trans hGGcaps.1
     · simpa [legacyVector,RCN068.capAt,liftedSurface] using
         (hfacdegree 1).trans hGGcaps.2.1
     · simpa [legacyVector,RCN068.capAt,liftedSurface] using
         (hfacdegree 2).trans hGGcaps.2.2
   have hgates:=fixed_implicit_characteristic_gates g (surfaceMap φ A) hgcaps hAcaps
   have hreg:∀ γ∈seedsFor g,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (RCN231.polynomialPoint (φ.comp Polynomial.C)
         (selected γ) γ (φ Polynomial.X)) (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i))
       (legacyVector liftedAgreement):=
     RCN069.fixed_implicit_agreement_caps φ G
       hGGcaps.1 hGGcaps.2.1 hGGcaps.2.2 (x i) (u₀ i) (u₁ i)
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (RCN170.geometric_factor_proper_cut A G hG hGR hproper g hg)
     selected (seedsFor g) nodes x u₀ u₁ hinj prime w agreements errors
     (by norm_num [w]) (by norm_num [w,prime])
     (by norm_num [w,agreements,n,errors])
     (by rw [hnodes];norm_num [agreements,n,errors]) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w errors (hsub g) hnoPencil)
     (capAt (legacyVector liftedAgreement)) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=
     RCN170.coordinateMixedDegree_le_geometricPairCost φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt (legacyVector liftedAgreement) i) (hδ i))))
     (Nat.mul_le_mul_left ((errors+1)*gap) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,
       capAt (RCN170.geometricPairCost A g) i) ≤
         capAt (RCN170.pairCost A G) i:=
   RCN170.sum_geometricPairCost_le φ
     (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
         capAt (RCN170.geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*gap ≤ (∑ g∈factors,(seedsFor g).card)*gap:=
     Nat.mul_le_mul_right gap hcard
   _=∑ g∈factors,(seedsFor g).card*gap:=by rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt (legacyVector liftedAgreement) i*
         capAt (RCN170.geometricPairCost A g) i)+
       (errors+1)*gap*
         capAt (RCN170.geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
       (∑ g∈factors,
         capAt (RCN170.geometricPairCost A g) i))+
       (errors+1)*gap*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*(∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
       capAt (RCN170.pairCost A G) i)+
       (errors+1)*gap*capAt (RCN170.pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt (legacyVector liftedAgreement) i)
         (hbudget i))))
       (Nat.mul_le_mul_left ((errors+1)*gap) (hbudget 2))
   _=(n-w)*dot liftedAgreement (pairCost A G)+
       (errors+1)*gap*RCN169.pairZCost ⟨A,G⟩:=by
     simp [Fin.sum_univ_three,RCN068.capAt,legacyVector,
       RCN170.pairCost,pairCost,
       RCN169.pairYCost,RCN169.pairRCost,
       RCN169.pairZCost,dot]
end
end ProximityPrize.SubmissionLower.RCN171
end PackedLegacy_K6

/-! Packed from ProximityPrize.SubmissionLower.F1. -/
section PackedLegacy_F1
namespace ProximityPrize.SubmissionLower.RCN291
open scoped BigOperators
open RCN223 RCN294 RCN286 RCN169 RCN167 RCN290 RCN293 RCN174 RCN319 RCN171 RCN081 RCN238 RCN243
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev ImplicitIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(implicitPairSet (singularAuxiliary Q))
def implicitSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):Finset K:=by
 classical
 exact Gamma.filter (fun gamma => LiftedSolutionPair q.1 (selected gamma) gamma)
def implicitVector (Q:MvPolynomial (Fin 4) K)
   (q:ImplicitIndex Q):DegreeVector:=
 ⟨pairYCost q.1,pairRCost q.1,pairZCost q.1⟩
def singularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K):Finset K:=by
 classical
 exact Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
   exceptionalSeeds (singularAuxiliary Q) Gamma selected
theorem implicitSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):implicitSeeds Q selected Gamma q ⊆ Gamma:=by
 classical
 exact Finset.filter_subset _ _
theorem implicitSeeds_solution (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q) (gamma:K)
   (hgamma:gamma∈implicitSeeds Q selected Gamma q):
   LiftedSolutionPair q.1 (selected gamma) gamma:=by
 classical
 exact (Finset.mem_filter.mp hgamma).2
theorem singularSeeds_card_le_sum
   (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K):
   (singularSeeds Q selected Gamma).card ≤
     (∑ q:ImplicitIndex Q,(implicitSeeds Q selected Gamma q).card)+
       (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card:=by
 classical
 unfold singularSeeds
 exact (Finset.card_union_le _ _).trans
   (Nat.add_le_add_right Finset.card_biUnion_le _)
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN291
end PackedLegacy_F1

/-! Packed from ProximityPrize.SubmissionLower.Z4. -/
section PackedLegacy_Z4
namespace ProximityPrize.SubmissionLower.RCN140
open scoped Classical BigOperators
open RCN223 RCN286 RCN167 RCN174 RCN319 RCN081 RCN266 RCN291 RCN214 RCN238
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def regularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RCN266.RegularIndex Q):Finset K:=
 Gamma.filter (fun gamma↦RegularSolution F.1 (selected gamma) gamma)
theorem regularSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RCN266.RegularIndex Q):
   regularSeeds Q selected Gamma F ⊆ Gamma:=
 Finset.filter_subset _ _
theorem card_le_regular_sum_add_singular
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0):
   Gamma.card ≤
     (∑ F:RCN266.RegularIndex Q,
       (regularSeeds Q selected Gamma F).card)+
     (singularSeeds Q selected Gamma).card:=by
 classical
 let regularUnion:=Finset.univ.biUnion (regularSeeds Q selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩ | hexc:=
     solution_three_way Q hQ weightedCap w seedTotalCap slopeCap prime
       (by norm_num [slopeCap]) characteristic_gates.2.2.2
       (by norm_num [w])
       (by norm_num [RCN223.w,
         RCN223.weightedCap,
         RCN223.multiplicity,
         RCN223.agreements,
         RCN223.n,
         RCN223.errors,
         RCN223.slopeCap])
       hbox (selected gamma) gamma (hsolution gamma hgamma)
   · apply Finset.mem_union.mpr
     left
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨F,hF⟩,Finset.mem_univ _,
       Finset.mem_filter.mpr ⟨hgamma,hreg⟩⟩
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     left
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨q,hq⟩,Finset.mem_univ _,
       Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     right
     exact Finset.mem_filter.mpr ⟨hgamma,hexc⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RCN266.RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
end
end ProximityPrize.SubmissionLower.RCN140
end PackedLegacy_Z4

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.BC. -/
section PackedLegacy_BC
namespace ProximityPrize.SubmissionLower.RCN119
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def slopeDifference:Poly K:=MvPolynomial.X 0-MvPolynomial.X 1
private def plusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X i
private def minusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0-MvPolynomial.X 1 else MvPolynomial.X i
def shiftPlus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (plusVariables K)
def shiftMinus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (minusVariables K)
theorem shiftMinus_comp_shiftPlus:
   (shiftMinus K).comp (shiftPlus K)=AlgHom.id K (Poly K):=by
 ext i
 fin_cases i <;> simp [shiftPlus,shiftMinus,plusVariables,minusVariables]
theorem shiftPlus_comp_shiftMinus:
   (shiftPlus K).comp (shiftMinus K)=AlgHom.id K (Poly K):=by
 ext i
 fin_cases i <;> simp [shiftPlus,shiftMinus,plusVariables,minusVariables]
@[simp] theorem shiftMinus_shiftPlus (f:Poly K):
   shiftMinus K (shiftPlus K f)=f:=
 DFunLike.congr_fun (shiftMinus_comp_shiftPlus K) f
@[simp] theorem shiftPlus_shiftMinus (f:Poly K):
   shiftPlus K (shiftMinus K f)=f:=
 DFunLike.congr_fun (shiftPlus_comp_shiftMinus K) f
@[simp] theorem shiftPlus_slopeDifference:
   shiftPlus K (slopeDifference K)=MvPolynomial.X 0:=by
 simp [slopeDifference,shiftPlus,plusVariables]
@[simp] theorem shiftMinus_X_zero:
   shiftMinus K (MvPolynomial.X 0)=slopeDifference K:=by
 simp [shiftMinus,minusVariables,slopeDifference]
theorem slopeDifference_ne_zero:slopeDifference K≠0:=by
 intro h
 have hh:=congrArg (shiftPlus K) h
 simpa using hh
def monomialRemainder (d:Fin 3 →₀ ℕ):Poly K →ₗ[K] Poly K where
 toFun f:=f.modMonomial d
 map_add' f g:=by
   ext e
   by_cases he:d ≤ e
   · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
   · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
 map_smul' c f:=by
   ext e
   by_cases he:d ≤ e
   · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
   · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
def contactJet (h:ℕ):Poly K →ₗ[K] Poly K:=
 (monomialRemainder K (Finsupp.single 0 h)).comp (shiftPlus K).toLinearMap
theorem contactJet_apply (h:ℕ) (f:Poly K):
   contactJet K h f=(shiftPlus K f).modMonomial (Finsupp.single 0 h):=rfl
theorem contactJet_eq_zero_iff (h:ℕ) (f:Poly K):
   contactJet K h f=0 ↔ slopeDifference K^h∣f:=by
 rw [contactJet_apply,
   ←MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero,
   ←MvPolynomial.X_pow_eq_monomial]
 constructor
 · rintro ⟨q,hq⟩
   refine ⟨shiftMinus K q,?_⟩
   have hh:=congrArg (shiftMinus K) hq
   simpa only [shiftMinus_shiftPlus,map_mul,map_pow,shiftMinus_X_zero] using hh
 · rintro ⟨q,rfl⟩
   exact ⟨shiftPlus K q,by simp⟩
theorem contactJet_mul_slopeDifference (h:ℕ) (q:Poly K):
   contactJet K h (slopeDifference K^h*q)=0:=
 (contactJet_eq_zero_iff K h _).2 ⟨q,rfl⟩
theorem contactJet_eq_zero_iff_coeff (h:ℕ) (f:Poly K):
   contactJet K h f=0 ↔
     ∀ d:Fin 3 →₀ ℕ,d 0 < h → MvPolynomial.coeff d (shiftPlus K f)=0:=by
 constructor
 · intro hf d hd
   have hnot:¬ Finsupp.single (0:Fin 3) h ≤ d:=by
     intro hle
     have hh:=hle 0
     simp only [Finsupp.single_eq_same] at hh
     omega
   have hh:=congrArg (MvPolynomial.coeff d) hf
   simpa [contactJet_apply,MvPolynomial.coeff_modMonomial_of_not_le _ hnot] using hh
 · intro hf
   ext d
   by_cases hle:Finsupp.single (0:Fin 3) h ≤ d
   · simp [contactJet_apply,MvPolynomial.coeff_modMonomial_of_le _ hle]
   · have hd:d 0 < h:=by
       by_contra hnot
       apply hle
       intro i
       by_cases hi:i=0
       · subst i
         simp only [Finsupp.single_eq_same]
         omega
       · simp [Finsupp.single_eq_of_ne hi]
     simp [contactJet_apply,MvPolynomial.coeff_modMonomial_of_not_le _ hle,hf d hd]
def boxExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 1+d 2 ≤ L∧d 1 ≤ s}
def coefficientBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (boxExponents M L s)
theorem mem_coefficientBox_iff (M L s:ℕ) (f:Poly K):
   f∈coefficientBox K M L s ↔
     ∀ d∈f.support,d 0 ≤ M∧d 0+d 1+d 2 ≤ L∧d 1 ≤ s:=by
 rfl
theorem coefficientBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈coefficientBox K M L s)
   (hg:g∈coefficientBox K M' L' s'):
   f*g∈coefficientBox K (M+M') (L+L') (s+s'):=by
 have hset:boxExponents M L s+boxExponents M' L' s' ⊆
     boxExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hdTotal,hd1⟩
   rcases he with ⟨he0,heTotal,he1⟩
   simp only [boxExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   omega
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
theorem slopeDifference_mem_coefficientBox:
   slopeDifference K∈coefficientBox K 1 1 1:=by
 apply (coefficientBox K 1 1 1).sub_mem
 · change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · change MvPolynomial.monomial (Finsupp.single 1 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem slopeDifference_pow_mem_coefficientBox (h:ℕ):
   slopeDifference K^h∈coefficientBox K h h h:=by
 induction h with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ h ih =>
     simpa only [pow_succ] using coefficientBox_mul K ih (slopeDifference_mem_coefficientBox K)
theorem slopeDifference_mul_mem_coefficientBox
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s)
   {q:Poly K} (hq:q∈coefficientBox K (M-h) (L-h) (s-h)):
   slopeDifference K^h*q∈coefficientBox K M L s:=by
 have hh:=coefficientBox_mul K (slopeDifference_pow_mem_coefficientBox K h) hq
 simpa only [Nat.add_sub_of_le hM,Nat.add_sub_of_le hL,Nat.add_sub_of_le hs] using hh
private def exponentTriple (i j z:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j+Finsupp.single 2 z
@[simp] private theorem exponentTriple_zero (i j z:ℕ):
   exponentTriple i j z 0=i:=by simp [exponentTriple]
@[simp] private theorem exponentTriple_one (i j z:ℕ):
   exponentTriple i j z 1=j:=by simp [exponentTriple]
@[simp] private theorem exponentTriple_two (i j z:ℕ):
   exponentTriple i j z 2=z:=by simp [exponentTriple]
private theorem exponentTriple_eta (d:Fin 3 →₀ ℕ):
   exponentTriple (d 0) (d 1) (d 2)=d:=by
 ext i
 fin_cases i <;> simp
private theorem finPair_heq_of_val_eq
   {n a b:ℕ} {i j:Fin n} {u:Fin a} {v:Fin b}
   (hab:a=b) (hij:i.val=j.val) (huv:u.val=v.val):
   HEq (i,u) (j,v):=by
 subst b
 have hi:i=j:=Fin.ext hij
 have hu:u=v:=Fin.ext huv
 cases hi
 cases hu
 rfl
private theorem finSigma_heq_of_val_eq
   {n:ℕ} {a b:Fin n → ℕ}
   {i j:Fin n} {u:Fin (a i)} {v:Fin (b j)}
   (hab:a=b) (hij:i.val=j.val) (huv:u.val=v.val):
   HEq (⟨i,u⟩:(k:Fin n) × Fin (a k))
     (⟨j,v⟩:(k:Fin n) × Fin (b k)):=by
 subst b
 have hi:i=j:=Fin.ext hij
 subst j
 have hu:u=v:=Fin.ext huv
 subst v
 rfl
abbrev BoxIndex (M L s:ℕ):=
 (i:Fin (M+1)) ×
   (j:Fin (s+1)) × Fin (L+1-i.val-j.val)
def boxExponentsEquivIndex (M L s:ℕ):
   boxExponents M L s ≃ BoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,by
       rcases d.property with ⟨hM,hL,hs⟩
       omega⟩,
     ⟨⟨d.val 1,by
       rcases d.property with ⟨hM,hL,hs⟩
       omega⟩,
     ⟨d.val 2,by
       rcases d.property with ⟨hM,hL,hs⟩
       change d.val 2 < L+1-d.val 0-d.val 1
       omega⟩⟩⟩
 invFun q:=
   ⟨exponentTriple q.1.val q.2.1.val q.2.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.1.isLt
     have hz:=q.2.2.isLt
     simp only [boxExponents,Set.mem_setOf_eq,exponentTriple_zero,
       exponentTriple_one,exponentTriple_two]
     omega⟩
 left_inv d:=Subtype.ext (exponentTriple_eta d.val)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨⟨j,hj⟩,⟨z,hz⟩⟩⟩
   apply Sigma.ext
   · apply Fin.ext
     exact exponentTriple_zero i j z
   · dsimp only
     apply @finSigma_heq_of_val_eq (s+1)
       (fun k↦L+1-(exponentTriple i j z) 0-k.val)
       (fun k↦L+1-i-k.val) _ _ _ _
     · funext k
       simp only [exponentTriple_zero]
     · exact exponentTriple_one i j z
     · exact exponentTriple_two i j z
instance boxExponentsFintype (M L s:ℕ):Fintype (boxExponents M L s):=
 Fintype.ofEquiv (BoxIndex M L s) (boxExponentsEquivIndex M L s).symm
instance coefficientBoxFinite (M L s:ℕ):
   Module.Finite K (coefficientBox K M L s):=
 Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boxExponents M L s))
theorem coefficientBox_finrank (M L s:ℕ):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 change Module.finrank K (MvPolynomial.restrictSupport K (boxExponents M L s))=_
 rw [Module.finrank_eq_card_basis
   (MvPolynomial.basisRestrictSupport K (boxExponents M L s))]
 rw [Fintype.card_congr (boxExponentsEquivIndex M L s)]
 simp [BoxIndex,Fintype.card_sigma]
theorem coefficientBox_finrank_of_le (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 exact coefficientBox_finrank K M L s
def multiplyIntoBox {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   coefficientBox K (M-h) (L-h) (s-h) →ₗ[K]
     coefficientBox K M L s where
 toFun q:=⟨slopeDifference K^h*q.val,
   slopeDifference_mul_mem_coefficientBox K hM hL hs q.property⟩
 map_add' q r:=by
   apply Subtype.ext
   simp [mul_add]
 map_smul' c q:=by
   apply Subtype.ext
   simp [mul_smul_comm]
theorem multiplyIntoBox_injective
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (multiplyIntoBox K hM hL hs):=by
 intro q r heq
 apply Subtype.ext
 have hh:slopeDifference K^h*q.val=slopeDifference K^h*r.val:=
   congrArg Subtype.val heq
 exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh
def blockJet (M L s h:ℕ):coefficientBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (coefficientBox K M L s).subtype
def kernelEmbedding {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   coefficientBox K (M-h) (L-h) (s-h) →ₗ[K]
     LinearMap.ker (blockJet K M L s h):=
 LinearMap.codRestrict (LinearMap.ker (blockJet K M L s h))
   (multiplyIntoBox K hM hL hs) (fun q => by
     change contactJet K h (slopeDifference K^h*q.val)=0
     exact contactJet_mul_slopeDifference K h q.val)
theorem kernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (kernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoBox_injective K hM hL hs
 exact congrArg Subtype.val heq
theorem blockJet_rank_add_quotient_finrank_le {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h))+
       Module.finrank K (coefficientBox K (M-h) (L-h) (s-h)) ≤
     Module.finrank K (coefficientBox K M L s):=by
 have hker:=LinearMap.finrank_le_finrank_of_injective
   (kernelEmbedding_injective K hM hL hs)
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 omega
theorem blockJet_rank_le_triangle_difference {M L s h:ℕ}
   (hML:M ≤ L) (hM:h ≤ M) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     (∑ i:Fin (M+1),
         ∑ j:Fin (s+1),(L+1-i.val-j.val))-
       (∑ i:Fin (M-h+1),
         ∑ j:Fin (s-h+1),(L-h+1-i.val-j.val)):=by
 have hineq:=blockJet_rank_add_quotient_finrank_le K hM (hM.trans hML) hs
 rw [coefficientBox_finrank_of_le K M L s hML,
   coefficientBox_finrank_of_le K (M-h) (L-h) (s-h)
     (Nat.sub_le_sub_right hML h)] at hineq
 omega
theorem blockJet_rank_le_input (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 rw [coefficientBox_finrank_of_le K M L s hML] at hsum
 omega
theorem coefficientBox_finrank_range (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i∈Finset.range (M+1),
       ∑ j∈Finset.range (s+1),(L+1-i-j):=by
 rw [coefficientBox_finrank_of_le K M L s hML]
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro i hi
 rw [Finset.sum_range]
def blockInputCount (M L s:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1),
   ∑ j∈Finset.range (s+1),(L+1-i-j)
def blockKernelLowerBound (M L s h:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1-h),
   ∑ j∈Finset.range (s+1-h),(L+1-h-i-j)
def contactRankBound (M L s h:ℕ):ℕ:=
 blockInputCount M L s-blockKernelLowerBound M L s h
theorem blockJet_rank_le_contactRankBound (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     contactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hineq:=blockJet_rank_add_quotient_finrank_le K hM hL hs
     rw [coefficientBox_finrank_range K M L s hML,
       coefficientBox_finrank_range K (M-h) (L-h) (s-h)
         (Nat.sub_le_sub_right hML h)] at hineq
     have hMeq:M-h+1=M+1-h:=by omega
     have hLeq:L-h+1=L+1-h:=by omega
     have hseq:s-h+1=s+1-h:=by omega
     rw [hMeq,hLeq,hseq] at hineq
     unfold contactRankBound blockInputCount blockKernelLowerBound
     omega
   · have hzero:s+1-h=0:=by omega
     have hinput:=blockJet_rank_le_input K M L s h hML
     simpa [contactRankBound,blockKernelLowerBound,blockInputCount,
       hzero,Finset.sum_range] using hinput
 · have hzero:M+1-h=0:=by omega
   have hinput:=blockJet_rank_le_input K M L s h hML
   simpa [contactRankBound,blockKernelLowerBound,blockInputCount,
     hzero,Finset.sum_range] using hinput
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   contactRankBound (min r L) L s (min (r+1) (m-r))
theorem sum_blockJet_ranks_le_localRankBound (m L s:ℕ):
   (∑ r∈Finset.range m,
     Module.finrank K (LinearMap.range
       (blockJet K (min r L) L s (min (r+1) (m-r))))) ≤
     localRankBound m L s:=by
 apply Finset.sum_le_sum
 intro r hr
 exact blockJet_rank_le_contactRankBound K (min r L) L s
   (min (r+1) (m-r)) (min_le_right r L)
end
end ProximityPrize.SubmissionLower.RCN119
end PackedLegacy_BC

/-! Packed from ProximityPrize.SubmissionLower.C1. -/
section PackedLegacy_C1
namespace ProximityPrize.SubmissionLower.RCN100
open RCN119 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
theorem coefficientBox_mono {M L s M' L' s':ℕ}
   (hM:M ≤ M') (hL:L ≤ L') (hs:s ≤ s'):
   coefficientBox K M L s ≤ coefficientBox K M' L' s':=by
 apply MvPolynomial.restrictSupport_mono
 intro d hd
 exact ⟨hd.1.trans hM,hd.2.1.trans hL,hd.2.2.trans hs⟩
def localMonomial (f j z:ℕ):Poly K:=
 MvPolynomial.monomial
   (Finsupp.single 0 f+Finsupp.single 1 j+Finsupp.single 2 z) 1
theorem localMonomial_mem (f j z:ℕ):
   localMonomial K f j z∈coefficientBox K f (f+j+z) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [boxExponents]
def seedAffine (u₀ u₁:K):Poly K:=
 MvPolynomial.C u₀+MvPolynomial.monomial (Finsupp.single 2 1) u₁
theorem seedAffine_mem (u₀ u₁:K):
   seedAffine K u₀ u₁∈coefficientBox K 0 1 0:=by
 apply (coefficientBox K 0 1 0).add_mem
 · change MvPolynomial.monomial 0 u₀∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem seedAffine_pow_mem (u₀ u₁:K) (t:ℕ):
   seedAffine K u₀ u₁^t∈coefficientBox K 0 t 0:=by
 induction t with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ t ih =>
     simpa only [pow_succ,Nat.zero_add] using
       coefficientBox_mul K ih (seedAffine_mem K u₀ u₁)
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (L+1-i.val-j.val) ×
     Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ} (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val+Finsupp.single 3 c.2.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 0=c.2.2.2.val:=by simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 1=c.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 2=c.2.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 3=c.2.2.1.val:=by simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 have hz:=congrArg (fun e:Fin 4 →₀ ℕ => e 3) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 simp only [columnExponent_z] at hz
 subst di
 subst dj
 subst dz
 subst de
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 2+d 3 ≤ L∧d 2 ≤ s∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):
   Submodule K (MvPolynomial (Fin 4) K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have hz:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 simp only [globalExponents,Set.mem_setOf_eq,columnExponent_x,
   columnExponent_y,columnExponent_r,columnExponent_z]
 omega
def reconstruct (D w L s:ℕ) (θ:CoefficientIndex D w L s → K):
   MvPolynomial (Fin 4) K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (θ c)
theorem reconstruct_coeff (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s θ)=θ c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro θ η h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (hθ:θ≠0):
   reconstruct K D w L s θ≠0:=by
 intro hzero
 apply hθ
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hzero
theorem reconstruct_mem_globalCoefficientBox (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   reconstruct K D w L s θ∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (θ c)
theorem reconstruct_support_caps (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   ∀ d∈(reconstruct K D w L s θ).support,
     d 1+d 2+d 3 ≤ L∧d 2 ≤ s∧
       d 0+w*d 1+(w-1)*d 2 < D:=
 reconstruct_mem_globalCoefficientBox K D w L s θ
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     (L+1-i-j)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,Finset.sum_range]
def blockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):Poly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     (((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)) •
         (seedAffine K u₀ u₁^(c.1.val-f.val)*
           localMonomial K f.val c.2.1.val c.2.2.1.val)
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u₀ u₁ c r∈
     coefficientBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (coefficientBox K (min r L) L s).smul_mem
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have hz:=c.2.2.1.isLt
   have hfi:=f.isLt
   have hmul:=coefficientBox_mul K
     (seedAffine_pow_mem K u₀ u₁ (c.1.val-f.val))
     (localMonomial_mem K f.val c.2.1.val c.2.2.1.val)
   apply coefficientBox_mono K (show 0+f.val ≤ min r L by omega)
     (show c.1.val-f.val+
         (f.val+c.2.1.val+c.2.2.1.val) ≤ L by omega)
     (show 0+c.2.1.val ≤ s by omega)
   exact hmul
 · exact (coefficientBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   coefficientBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u₀ u₁ c r,
   blockEntry_mem K D w L s x u₀ u₁ c r⟩
def extractBlock (D w L s:ℕ) (x u₀ u₁:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     coefficientBox K (min r L) L s where
 toFun θ:=∑ c:CoefficientIndex D w L s,
   θ c • boundedBlockEntry K D w L s x u₀ u₁ c r
 map_add' θ η:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a θ:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]
theorem full_contactRankBound_eq (r m L s:ℕ):
   contactRankBound (min r L) L s (m-r)=
     contactRankBound (min r L) L s (min (r+1) (m-r)):=by
 by_cases h:r+1 ≤ m-r
 · have hM:min r L ≤ r:=min_le_left r L
   have hzero:min r L+1-(m-r)=0:=by omega
   have hzero':min r L+1-(r+1)=0:=by omega
   simp only [Nat.min_eq_left h,contactRankBound,blockKernelLowerBound,
     hzero,hzero',Finset.range_zero,Finset.sum_empty,mul_zero,Nat.sub_zero]
 · have h':m-r ≤ r+1:=by omega
   rw [Nat.min_eq_right h']
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 have hh:=blockJet_rank_le_contactRankBound K (min r.val L) L s (m-r.val)
   (min_le_right r.val L)
 rw [full_contactRankBound_eq] at hh
 exact hh
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
theorem globalTarget_finrank_le {I:Type*} [Fintype I] (m L s:ℕ):
   Module.finrank K (GlobalTarget K I m L s) ≤
     Fintype.card I*localRankBound m L s:=by
 change Module.finrank K (I → LocalTarget K m L s) ≤ _
 rw [Module.finrank_pi_fintype]
 calc
   (∑ _i:I,Module.finrank K (LocalTarget K m L s)) ≤
       ∑ _i:I,localRankBound m L s:=by
     apply Finset.sum_le_sum
     intro i hi
     exact localTarget_finrank_le K m L s
   _=Fintype.card I*localRankBound m L s:=by simp
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (blockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val)
theorem constraintMap_apply {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (θ:CoefficientIndex D w L s → K) (i:I) (r:Fin m):
   ((constraintMap K D w L s m nodes u₀ u₁ θ i r):Poly K)=
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K):=rfl
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,
     θ≠0∧constraintMap K D w L s m nodes u₀ u₁ θ=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective (constraintMap K D w L s m nodes u₀ u₁):=by
   intro θ η heq
   by_contra hne
   apply hnone
   refine ⟨θ-η,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have hupper:=globalTarget_finrank_le K (I:=I) m L s
 exact (Nat.not_le_of_gt hgate) (hdim.trans hupper)
theorem exists_nonzero_block_equations {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,θ≠0∧
     ∀ (i:I) (r:Fin m),
       contactJet K (m-r.val)
         ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K)=0:=by
 obtain ⟨θ,hθ,hzero⟩:=exists_nonzero_kernel_array K D w L s m nodes u₀ u₁ hgate
 refine ⟨θ,hθ,?_⟩
 intro i r
 have hh:=congrArg (fun t:GlobalTarget K I m L s => ((t i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K)=0 at hh
 exact hh
end
end ProximityPrize.SubmissionLower.RCN100
end PackedLegacy_C1
end Compact_PackedLegacyCore1
