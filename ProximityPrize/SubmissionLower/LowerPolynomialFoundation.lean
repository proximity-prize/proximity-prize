import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.RegularLocalRing.Defs
set_option linter.all false

section PackedLegacy_Z7
namespace ProximityPrize.SubmissionLower.RCN187
open scoped BigOperators
noncomputable section
section Multiplicative
variable {K L σ Γ₀:Type*} [Field K] [Field L] [Fintype σ]
 [LinearOrderedCommGroupWithZero Γ₀]
theorem valuation_monomial_le (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (d:σ →₀ ℕ) (c:K) (hd:∀ i,d i ≤ cap i):
   v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 rw [MvPolynomial.eval₂Hom_monomial,
   Finsupp.prod_fintype _ _ (fun _ => pow_zero _),map_mul,map_prod]
 simp only [map_pow]
 calc
   v (coeff c)*(∏ i,v (x i)^d i) ≤
       1*(∏ i,max 1 (v (x i))^cap i):=by
     apply mul_le_mul' (hcoeff c)
     apply Finset.prod_le_prod₀ (fun _ _ => zero_le)
     intro i _
     exact (pow_le_pow_left₀ zero_le (le_max_right _ _) (d i)).trans
       (pow_le_pow_right₀ (le_max_left _ _) (hd i))
   _=_:=one_mul _
theorem valuation_eval_le_box (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 conv_lhs => rw [MvPolynomial.as_sum F,map_sum]
 apply v.map_sum_le
 intro d hd
 apply valuation_monomial_le v coeff hcoeff x cap d
 intro i
 exact (MvPolynomial.monomial_le_degreeOf i hd).trans (hcap i)
theorem max_one_valuation_eval_le_box (v:Valuation L Γ₀) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∏ i,max 1 (v (x i))^cap i:=by
 classical
 apply max_le
 · exact Finset.one_le_prod fun _ _ => one_le_pow₀ (le_max_left _ _)
 · exact valuation_eval_le_box v coeff hcoeff x cap F hcap
end Multiplicative
section IntegerPole
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
def poleOrder (v:Valuation L (WithZero (Multiplicative ℤ))) (x:L):ℤ:=
 max 0 (v x).log
theorem log_max_one (z:WithZero (Multiplicative ℤ)):
   (max 1 z).log=max 0 z.log:=by
 by_cases hz:z=0
 · simp [hz]
 rcases le_total 1 z with h | h
 · have hlog:(0:ℤ) ≤ z.log:=by
     simpa using (WithZero.log_le_log (by simp) hz).2 h
   simp only [max_eq_right h,max_eq_right hlog]
 · have hlog:z.log ≤ (0:ℤ):=by
     simpa using (WithZero.log_le_log hz (by simp)).2 h
   simp only [max_eq_left h,WithZero.log_one,max_eq_left hlog]
theorem log_prod_of_one_le {ι:Type*} (s:Finset ι)
   (f:ι → WithZero (Multiplicative ℤ)):
   (∀ i∈s,1 ≤ f i) →
     (∏ i∈s,f i).log=∑ i∈s,(f i).log:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 induction s using Finset.induction_on with
 | empty => intro _;simp
 | @insert i s hi ih =>
     intro hf
     have hfi:1 ≤ f i:=hf i (Finset.mem_insert_self i s)
     have hfs:∀ j∈s,1 ≤ f j:=
       fun j hj => hf j (Finset.mem_insert_of_mem hj)
     have hfi0:f i≠0:=ne_of_gt (zero_lt_one.trans_le hfi)
     have hprod0:(∏ j∈s,f j)≠0:=
       ne_of_gt (zero_lt_one.trans_le (Finset.one_le_prod hfs))
     rw [Finset.prod_insert hi,WithZero.log_mul hfi0 hprod0,
       Finset.sum_insert hi,ih hfs]
theorem poleOrder_eval_le_box
   (v:Valuation L (WithZero (Multiplicative ℤ))) (coeff:K →+*L)
   (hcoeff:∀ c:K,v (coeff c) ≤ 1) (x:σ → L)
   (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   poleOrder v (MvPolynomial.eval₂Hom coeff x F) ≤
     ∑ i,(cap i:ℤ)*poleOrder v (x i):=by
 classical
 have hfactor:∀ i∈(Finset.univ:Finset σ),
     1 ≤ max 1 (v (x i))^cap i:=
   fun _ _ => one_le_pow₀ (le_max_left _ _)
 have hleft0:max 1 (v (MvPolynomial.eval₂Hom coeff x F))≠0:=
   ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
 have hright0:(∏ i,max 1 (v (x i))^cap i)≠0:=
   ne_of_gt (zero_lt_one.trans_le (Finset.one_le_prod hfactor))
 have hlog:=(WithZero.log_le_log hleft0 hright0).2
   (max_one_valuation_eval_le_box v coeff hcoeff x cap F hcap)
 rw [log_prod_of_one_le Finset.univ _ hfactor] at hlog
 simpa only [WithZero.log_pow,log_max_one,nsmul_eq_mul,poleOrder] using hlog
theorem weighted_poleOrder_eval_le_box {τ:Type*} (S:Finset τ)
   (weight:τ → ℕ) (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ t∈S,∀ c:K,v t (coeff c) ≤ 1)
   (x:σ → L) (cap:σ → ℕ) (F:MvPolynomial σ K)
   (hcap:∀ i,F.degreeOf i ≤ cap i):
   (∑ t∈S,(weight t:ℤ)*poleOrder (v t) (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∑ i,(cap i:ℤ)*(∑ t∈S,(weight t:ℤ)*poleOrder (v t) (x i)):=by
 classical
 calc
   _ ≤ ∑ t∈S,(weight t:ℤ)*
       (∑ i,(cap i:ℤ)*poleOrder (v t) (x i)):=by
     apply Finset.sum_le_sum
     intro t ht
     exact mul_le_mul_of_nonneg_left
       (poleOrder_eval_le_box (v t) coeff (hcoeff t ht) x cap F hcap)
       (Int.natCast_nonneg (weight t))
   _=_:=by
     simp_rw [Finset.mul_sum]
     rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro i _
     apply Finset.sum_congr rfl
     intro t _
     ring
end IntegerPole
end
end ProximityPrize.SubmissionLower.RCN187
end PackedLegacy_Z7

section PackedLegacy_BM
namespace ProximityPrize.SubmissionLower.RCN147
noncomputable section
variable {K L:Type*} [Field K] [Field L]
theorem degree_lt_card_of_natDegree_le {ι:Type*}
   (I:Finset ι) (w:ℕ) (hw:w < I.card) (P:Polynomial L)
   (hP:P.natDegree ≤ w):P.degree < (I.card:WithBot ℕ):=
 lt_of_le_of_lt Polynomial.degree_le_natDegree
   (WithBot.coe_lt_coe.mpr (hP.trans_lt hw))
theorem mapped_affine_pencil_natDegree_le
   (coefficients:K →+*L) (P₀ P₁:Polynomial K) (w:ℕ)
   (h₀:P₀.natDegree ≤ w) (h₁:P₁.natDegree ≤ w) (γ:L):
   (P₀.map coefficients+Polynomial.C γ*P₁.map coefficients).natDegree ≤ w:=by
 apply (Polynomial.natDegree_add_le _ _).trans
 exact max_le (Polynomial.natDegree_map_le.trans h₀)
   ((Polynomial.natDegree_C_mul_le γ _).trans (Polynomial.natDegree_map_le.trans h₁))
theorem exists_basefield_affine_pencil_of_identity_nodes {ι τ:Type*}
   (coefficients:K →+*L) (I:Finset ι) (x u₀ u₁:ι → K)
   (w:ℕ) (hw:w < I.card) (hinj:Set.InjOn x I)
   (γ:τ → L) (P:τ → Polynomial L)
   (hdegree:∀ t,(P t).natDegree ≤ w)
   (hvalues:∀ t i,i∈I →
     (P t).eval (coefficients (x i))=coefficients (u₀ i)+γ t*coefficients (u₁ i)):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     ∀ t,P t=P₀.map coefficients+Polynomial.C (γ t)*P₁.map coefficients:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 obtain ⟨S,hSI,hcard⟩:=Finset.exists_subset_card_eq (show w+1 ≤ I.card by omega)
 have hxS:Set.InjOn x S:=by
   intro i hi j hj hij
   exact hinj (hSI hi) (hSI hj) hij
 let P₀:Polynomial K:=Lagrange.interpolate S x u₀
 let P₁:Polynomial K:=Lagrange.interpolate S x u₁
 have h₀:P₀.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   simpa only [hcard,Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₀ hxS
 have h₁:P₁.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   simpa only [hcard,Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₁ hxS
 have heval₀:∀ i∈S,P₀.eval (x i)=u₀ i:=by
   intro i hi
   exact Lagrange.eval_interpolate_at_node u₀ hxS hi
 have heval₁:∀ i∈S,P₁.eval (x i)=u₁ i:=by
   intro i hi
   exact Lagrange.eval_interpolate_at_node u₁ hxS hi
 have hnodes:Set.InjOn (fun i => coefficients (x i)) S:=by
   intro i hi j hj hij
   exact hxS hi hj (coefficients.injective hij)
 have hws:w < S.card:=by omega
 refine ⟨P₀,P₁,h₀,h₁,?_⟩
 intro t
 apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hnodes
   (degree_lt_card_of_natDegree_le S w hws (P t) (hdegree t))
   (degree_lt_card_of_natDegree_le S w hws _
     (mapped_affine_pencil_natDegree_le coefficients P₀ P₁ w h₀ h₁ (γ t)))
 intro i hi
 simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_map_apply,heval₀ i hi,heval₁ i hi] using hvalues t i (hSI hi)
end
end ProximityPrize.SubmissionLower.RCN147
end PackedLegacy_BM

section PackedLegacy_E
namespace ProximityPrize.SubmissionLower.RCN136
noncomputable section
variable {K L:Type*} [Field K] [Field L]
def collectX (K:Type*) [Field K]:
   MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 3) (Polynomial K):=
 (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 3)).trans
   (MvPolynomial.optionEquivRight K (Fin 3))
@[simp] theorem collectX_C (a:K):
   collectX K (MvPolynomial.C a)=MvPolynomial.C (Polynomial.C a):=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
@[simp] theorem collectX_X_zero:
   collectX K (MvPolynomial.X (0:Fin 4))=MvPolynomial.C Polynomial.X:=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
@[simp] theorem collectX_X_succ (i:Fin 3):
   collectX K (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [collectX,MvPolynomial.renameEquiv_apply]
def surfaceMap (φ:Polynomial K →+*L):
   MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 3) L:=
 (MvPolynomial.map φ).comp (collectX K).toRingHom
@[simp] theorem surfaceMap_C (φ:Polynomial K →+*L) (a:K):
   surfaceMap φ (MvPolynomial.C a)=MvPolynomial.C (φ (Polynomial.C a)):=by
 simp [surfaceMap]
@[simp] theorem surfaceMap_X_zero (φ:Polynomial K →+*L):
   surfaceMap φ (MvPolynomial.X (0:Fin 4))=MvPolynomial.C (φ Polynomial.X):=by
 simp [surfaceMap]
@[simp] theorem surfaceMap_X_succ (φ:Polynomial K →+*L) (i:Fin 3):
   surfaceMap φ (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [surfaceMap]
theorem surfaceMap_injective (φ:Polynomial K →+*L) (hφ:Function.Injective φ):
   Function.Injective (surfaceMap φ):=
 (MvPolynomial.map_injective φ hφ).comp (collectX K).injective
theorem surfaceMap_ne_zero (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):surfaceMap φ Q≠0:=by
 intro h
 apply hQ
 apply surfaceMap_injective φ hφ
 simpa only [map_zero] using h
theorem surfaceMap_eq_eval₂Hom (φ:Polynomial K →+*L):
   surfaceMap φ=
     MvPolynomial.eval₂Hom (MvPolynomial.C.comp (φ.comp Polynomial.C))
       (Fin.cases (MvPolynomial.C (φ Polynomial.X)) MvPolynomial.X):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp
 · intro i
   refine Fin.cases ?_ (fun j => ?_) i <;> simp
theorem eval_surfaceMap (φ:Polynomial K →+*L)
   (v:Fin 3 → L) (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval v (surfaceMap φ Q)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C) (Fin.cases (φ Polynomial.X) v) Q:=by
 have hhom:(MvPolynomial.eval v).comp (surfaceMap φ)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C) (Fin.cases (φ Polynomial.X) v):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp
   · intro i
     refine Fin.cases ?_ (fun j => ?_) i <;> simp
 exact RingHom.congr_fun hhom Q
theorem surfaceMap_monomial (φ:Polynomial K →+*L)
   (d:Fin 4 →₀ ℕ) (a:K):
   surfaceMap φ (MvPolynomial.monomial d a)=
     MvPolynomial.monomial d.tail (φ (Polynomial.C a)*(φ Polynomial.X)^d 0):=by
 rw [surfaceMap_eq_eval₂Hom,MvPolynomial.eval₂Hom_monomial]
 simp only [RingHom.comp_apply,Finsupp.prod_pow,Fin.prod_univ_succ,Fin.cases_zero,
   Fin.cases_succ,MvPolynomial.monomial_eq,Finsupp.tail_apply,
   map_mul,map_pow]
 ring
theorem support_surfaceMap_subset (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K):
   (surfaceMap φ Q).support ⊆ Q.support.image Finsupp.tail:=by
 classical
 have hsum:surfaceMap φ Q=
     ∑ d∈Q.support,surfaceMap φ (MvPolynomial.monomial d (AddMonoidAlgebra.coeff Q d)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 intro e he
 rw [hsum] at he
 obtain ⟨d,hd,hed⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
 rw [surfaceMap_monomial] at hed
 have heq:e=d.tail:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
 exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
theorem surfaceMap_degreeOf_le (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K) (i:Fin 3):
   (surfaceMap φ Q).degreeOf i ≤ Q.degreeOf i.succ:=by
 classical
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro e he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
 exact MvPolynomial.monomial_le_degreeOf i.succ hd
theorem surfaceMap_separated_caps (φ:Polynomial K →+*L)
   (Q:MvPolynomial (Fin 4) K) (ell s zcap:ℕ)
   (hy:Q.degreeOf 1 ≤ ell) (hr:Q.degreeOf 2 ≤ s) (hz:Q.degreeOf 3 ≤ zcap):
   (surfaceMap φ Q).degreeOf 0 ≤ ell∧
     (surfaceMap φ Q).degreeOf 1 ≤ s∧
     (surfaceMap φ Q).degreeOf 2 ≤ zcap:=
 ⟨(surfaceMap_degreeOf_le φ Q 0).trans hy,
   (surfaceMap_degreeOf_le φ Q 1).trans hr,
   (surfaceMap_degreeOf_le φ Q 2).trans hz⟩
end
end ProximityPrize.SubmissionLower.RCN136
end PackedLegacy_E

section PackedLegacy_R3
namespace ProximityPrize.SubmissionLower.RCN347
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section Derivation
variable {K A:Type*} [CommRing K] [CommRing A] [Algebra K A]
theorem leibniz_product (D:Derivation K A A) (a b:A):
   D (a*b)=D a*b+a*D b:=by
 calc
   D (a*b)=a*D b+b*D a:=by
     simpa only [smul_eq_mul] using D.leibniz a b
   _=D a*b+a*D b:=by ac_rfl
theorem iterate_zero (D:Derivation K A A) (n:ℕ):D^[n] (0:A)=0:=by
 induction n with
 | zero => rfl
 | succ n ih => simp [Function.iterate_succ_apply',ih]
theorem iterate_add (D:Derivation K A A) (n:ℕ) (a b:A):
   D^[n] (a+b)=D^[n] a+D^[n] b:=by
 induction n with
 | zero => rfl
 | succ n ih => simp [Function.iterate_succ_apply',ih,map_add]
theorem iterate_one_of_ne_zero (D:Derivation K A A) (n:ℕ) (hn:n≠0):
   D^[n] (1:A)=0:=by
 cases n with
 | zero => exact (hn rfl).elim
 | succ n =>
   rw [Function.iterate_succ_apply,D.map_one_eq_zero]
   exact iterate_zero D n
theorem iterate_product (D:Derivation K A A) (n:ℕ) (a b:A):
   D^[n] (a*b)=
     ∑ ij∈antidiagonal n,
       n.choose ij.1 • (D^[ij.1] a*D^[ij.2] b):=by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [sum_antidiagonal_choose_succ_nsmul (M:=A)
     (fun i j => D^[i] a*D^[j] b) n]
   simp only [Function.iterate_succ_apply',ih,map_sum,map_nsmul,
     leibniz_product,smul_add,sum_add_distrib]
   rw [add_comm,add_right_inj]
   refine sum_congr rfl fun ⟨i,j⟩ hij => ?_
   rw [n.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]
end Derivation
section NormalizedCoefficients
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem factorial_cast_ne_zero_below_characteristic
   (p:ℕ) [CharP L p]:∀ n:ℕ,n < p → (n.factorial:L)≠0:=by
 intro n
 induction n with
 | zero =>
   intro hn
   simp
 | succ n ih =>
   intro hn
   have hcast:((n+1:ℕ):L)≠0:=by
     intro hz
     have hdiv:p∣n+1:=(CharP.cast_eq_zero_iff L p (n+1)).mp hz
     exact (Nat.not_le_of_gt hn) (Nat.le_of_dvd (Nat.succ_pos n) hdiv)
   rw [Nat.factorial_succ,Nat.cast_mul]
   exact mul_ne_zero hcast (ih (by omega))
noncomputable def jetCoefficient
   (D:Derivation K A A) (value:A →+*L) (a:A) (n:ℕ):L:=
 value (D^[n] a)/(n.factorial:L)
theorem factorial_term_product
   (n i j:ℕ) (hij:i+j=n) (x y:L)
   (hn:(n.factorial:L)≠0)
   (hi:(i.factorial:L)≠0)
   (hj:(j.factorial:L)≠0):
   (n.choose i:L)*(x*y)/(n.factorial:L)=
     (x/(i.factorial:L))*(y/(j.factorial:L)):=by
 have hle:i ≤ n:=by omega
 have hsub:n-i=j:=by omega
 have hnat:=Nat.choose_mul_factorial_mul_factorial hle
 rw [hsub] at hnat
 have hcast:(n.choose i:L)*(i.factorial:L)*(j.factorial:L)=
     (n.factorial:L):=by
   simpa only [Nat.cast_mul] using congrArg (fun k:ℕ => (k:L)) hnat
 field_simp
 linear_combination (x*y)*hcast
theorem jetCoefficient_zero (D:Derivation K A A) (value:A →+*L) (n:ℕ):
   jetCoefficient D value 0 n=0:=by
 simp [jetCoefficient,iterate_zero]
theorem jetCoefficient_one (D:Derivation K A A) (value:A →+*L) (n:ℕ):
   jetCoefficient D value 1 n=if n=0 then 1 else 0:=by
 by_cases hn:n=0
 · subst n
   simp [jetCoefficient]
 · simp [jetCoefficient,iterate_one_of_ne_zero D n hn,hn]
theorem jetCoefficient_add
   (D:Derivation K A A) (value:A →+*L) (a b:A) (n:ℕ):
   jetCoefficient D value (a+b) n=
     jetCoefficient D value a n+jetCoefficient D value b n:=by
 simp only [jetCoefficient,iterate_add,map_add,add_div]
theorem jetCoefficient_product
   (D:Derivation K A A) (value:A →+*L) (a b:A) (n:ℕ)
   (hfactorial:∀ i ≤ n,(i.factorial:L)≠0):
   jetCoefficient D value (a*b) n=
     ∑ ij∈antidiagonal n,
       jetCoefficient D value a ij.1*jetCoefficient D value b ij.2:=by
 unfold jetCoefficient
 rw [iterate_product,map_sum,Finset.sum_div]
 apply Finset.sum_congr rfl
 intro ij hij
 have hsum:ij.1+ij.2=n:=mem_antidiagonal.mp hij
 have hi:ij.1 ≤ n:=by omega
 have hj:ij.2 ≤ n:=by omega
 rw [map_nsmul,nsmul_eq_mul,map_mul]
 exact factorial_term_product n ij.1 ij.2 hsum
   (value (D^[ij.1] a)) (value (D^[ij.2] b))
   (hfactorial n le_rfl) (hfactorial ij.1 hi) (hfactorial ij.2 hj)
noncomputable def jetPolynomial
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A):Polynomial L:=
 ∑ j∈range bound,Polynomial.monomial j (jetCoefficient D value a j)
theorem jetPolynomial_coeff
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A) (j:ℕ):
   (jetPolynomial D value bound a).coeff j=
     if j < bound then jetCoefficient D value a j else 0:=by
 classical
 simp [jetPolynomial,Polynomial.coeff_monomial]
theorem jetPolynomial_zero
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ):
   jetPolynomial D value bound 0=0:=by
 ext j
 simp [jetPolynomial_coeff,jetCoefficient_zero]
theorem jetPolynomial_one
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (hbound:0 < bound):
   jetPolynomial D value bound 1=1:=by
 ext j
 by_cases hj:j=0
 · subst j
   simp [jetPolynomial_coeff,jetCoefficient_one,hbound]
 · simp [jetPolynomial_coeff,jetCoefficient_one,hj,Polynomial.coeff_one]
theorem jetPolynomial_add
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a b:A):
   jetPolynomial D value bound (a+b)=
     jetPolynomial D value bound a+jetPolynomial D value bound b:=by
 ext j
 by_cases hj:j < bound <;>
   simp [jetPolynomial_coeff,jetCoefficient_add,hj]
theorem X_pow_dvd_jetPolynomial_product_error
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a b:A)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0):
   (Polynomial.X:Polynomial L)^bound∣
     jetPolynomial D value bound (a*b)-
       jetPolynomial D value bound a*jetPolynomial D value bound b:=by
 rw [Polynomial.X_pow_dvd_iff]
 intro j hj
 rw [Polynomial.coeff_sub]
 apply sub_eq_zero.mpr
 rw [jetPolynomial_coeff,if_pos hj,Polynomial.coeff_mul,
   jetCoefficient_product D value a b j (fun k hk =>
     hfactorial k (lt_of_le_of_lt hk hj))]
 apply Finset.sum_congr rfl
 intro ij hij
 have hsum:ij.1+ij.2=j:=mem_antidiagonal.mp hij
 have hi:ij.1 < bound:=by omega
 have hk:ij.2 < bound:=by omega
 rw [jetPolynomial_coeff,if_pos hi,jetPolynomial_coeff,if_pos hk]
end NormalizedCoefficients
end ProximityPrize.SubmissionLower.RCN347
end PackedLegacy_R3

section PackedLegacy_B5
namespace ProximityPrize.SubmissionLower.RCN077
open RCN347
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section StableIdeals
variable {K A:Type*} [CommRing K] [CommRing A] [Algebra K A]
theorem derivation_preserves_span
   (D:Derivation K A A) (generators:Set A)
   (hgenerators:∀ x∈generators,D x∈Ideal.span generators):
   ∀ x∈Ideal.span generators,D x∈Ideal.span generators:=by
 intro x hx
 induction hx using Submodule.span_induction with
 | mem x hx => exact hgenerators x hx
 | zero => simpa only [map_zero] using (Ideal.span generators).zero_mem
 | add x y hx hy hDx hDy =>
   simpa only [map_add] using (Ideal.span generators).add_mem hDx hDy
 | smul c x hx hDx =>
   change D (c*x)∈Ideal.span generators
   rw [leibniz_product]
   exact (Ideal.span generators).add_mem
     ((Ideal.span generators).mul_mem_left (D c) hx)
     ((Ideal.span generators).mul_mem_left c hDx)
noncomputable def quotientDerivation
   (D:Derivation K A A) (I:Ideal A)
   (hstable:∀ x∈I,D x∈I):
   Derivation K (A ⧸ I) (A ⧸ I):=
 Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective K I)
   (d:=D) (fun x hx => by
     change Ideal.Quotient.mk I (D x)=0
     change Ideal.Quotient.mk I x=0 at hx
     exact Ideal.Quotient.eq_zero_iff_mem.mpr
       (hstable x (Ideal.Quotient.eq_zero_iff_mem.mp hx)))
theorem quotientDerivation_mk
   (D:Derivation K A A) (I:Ideal A)
   (hstable:∀ x∈I,D x∈I) (x:A):
   quotientDerivation D I hstable (Ideal.Quotient.mk I x)=
     Ideal.Quotient.mk I (D x):=by
 unfold quotientDerivation
 exact Derivation.liftOfSurjective_apply _ _ x
end StableIdeals
section PolynomialVectorField
variable (K:Type*) [CommRing K]
abbrev Poly4:=MvPolynomial (Fin 4) K
abbrev Poly5:=MvPolynomial (Fin 5) K
noncomputable def liftFour (F:Poly4 K):Poly5 K:=
 MvPolynomial.rename Fin.castSucc F
theorem partial_extra_liftFour (F:Poly4 K):
   MvPolynomial.pderiv (4:Fin 5) (liftFour K F)=0:=by
 induction F using MvPolynomial.induction_on with
 | C c => simp [liftFour]
 | add F G hF hG =>
   dsimp only [liftFour] at hF hG
   change MvPolynomial.pderiv (4:Fin 5)
     (MvPolynomial.rename Fin.castSucc (F+G))=0
   rw [map_add,map_add,hF,hG,add_zero]
 | mul_X F i hF =>
   dsimp only [liftFour] at hF
   have hne:(i.castSucc:Fin 5)≠4:=by
     intro h
     have hv:i.val=4:=congrArg Fin.val h
     have hi:=i.isLt
     omega
   change MvPolynomial.pderiv (4:Fin 5)
     (MvPolynomial.rename Fin.castSucc (F*MvPolynomial.X i))=0
   rw [map_mul,MvPolynomial.rename_X,leibniz_product,hF,
     MvPolynomial.pderiv_X_of_ne hne,zero_mul,mul_zero,add_zero]
theorem partial_liftFour (F:Poly4 K) (i:Fin 4):
   MvPolynomial.pderiv i.castSucc (liftFour K F)=
     liftFour K (MvPolynomial.pderiv i F):=by
 have hinj:Function.Injective (Fin.castSucc:Fin 4 → Fin 5):=by
   intro i j hij
   apply Fin.ext
   exact congrArg (fun x:Fin 5 => x.val) hij
 exact MvPolynomial.pderiv_rename hinj i F
noncomputable def inverseRelation (H:Poly5 K):Poly5 K:=
 H*MvPolynomial.X (4:Fin 5)-1
noncomputable def inverseDerivative (G H:Poly5 K):Poly5 K:=
 MvPolynomial.pderiv (0:Fin 5) H+
   MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) H+
   G*MvPolynomial.X (4:Fin 5)*MvPolynomial.pderiv (2:Fin 5) H
noncomputable def inverseVectorField (G H:Poly5 K):
   Derivation K (Poly5 K) (Poly5 K):=
 (MvPolynomial.pderiv (0:Fin 5):Derivation K (Poly5 K) (Poly5 K))+
   (MvPolynomial.X (2:Fin 5):Poly5 K) • MvPolynomial.pderiv (1:Fin 5)+
   (G*MvPolynomial.X (4:Fin 5)) • MvPolynomial.pderiv (2:Fin 5)-
   ((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H) •
     MvPolynomial.pderiv (4:Fin 5)
theorem inverseVectorField_apply (G H P:Poly5 K):
   inverseVectorField K G H P=
     MvPolynomial.pderiv (0:Fin 5) P+
       MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) P+
       G*MvPolynomial.X (4:Fin 5)*MvPolynomial.pderiv (2:Fin 5) P-
       ((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H)*
         MvPolynomial.pderiv (4:Fin 5) P:=by
 simp only [inverseVectorField,Derivation.add_apply,Derivation.sub_apply,
   Derivation.smul_apply,smul_eq_mul]
theorem inverseVectorField_X (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (0:Fin 5))=1:=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_Y (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (1:Fin 5))=
     MvPolynomial.X (2:Fin 5):=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_Z (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (3:Fin 5))=0:=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_U (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (4:Fin 5))=
     -((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H):=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_H (G H:Poly5 K)
   (hH:MvPolynomial.pderiv (4:Fin 5) H=0):
   inverseVectorField K G H H=inverseDerivative K G H:=by
 rw [inverseVectorField_apply,hH,mul_zero,sub_zero]
 rfl
theorem inverseVectorField_inverseRelation (G H:Poly5 K)
   (hH:MvPolynomial.pderiv (4:Fin 5) H=0):
   inverseVectorField K G H (inverseRelation K H)=
     -(inverseDerivative K G H*MvPolynomial.X (4:Fin 5))*
       inverseRelation K H:=by
 rw [inverseRelation,map_sub,(inverseVectorField K G H).map_one_eq_zero,
   sub_zero,leibniz_product,inverseVectorField_H K G H hH,inverseVectorField_U]
 ring
noncomputable def contactH (F:Poly4 K):Poly5 K:=
 MvPolynomial.pderiv (2:Fin 5) (liftFour K F)
noncomputable def contactG (F:Poly4 K):Poly5 K:=
 -(MvPolynomial.pderiv (0:Fin 5) (liftFour K F)+
     MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) (liftFour K F))
noncomputable def contactVectorField (F:Poly4 K):
   Derivation K (Poly5 K) (Poly5 K):=
 inverseVectorField K (contactG K F) (contactH K F)
theorem partial_extra_contactH (F:Poly4 K):
   MvPolynomial.pderiv (4:Fin 5) (contactH K F)=0:=by
 have h:=partial_liftFour K F (2:Fin 4)
 change contactH K F=liftFour K (MvPolynomial.pderiv (2:Fin 4) F) at h
 rw [h]
 exact partial_extra_liftFour K _
theorem contactVectorField_F (F:Poly4 K):
   contactVectorField K F (liftFour K F)=
     contactG K F*inverseRelation K (contactH K F):=by
 rw [contactVectorField,inverseVectorField_apply,partial_extra_liftFour,
   mul_zero,sub_zero]
 unfold contactG contactH inverseRelation
 ring
noncomputable def contactIdeal (F:Poly4 K):Ideal (Poly5 K):=
 Ideal.span ({liftFour K F,inverseRelation K (contactH K F)}:Set (Poly5 K))
theorem contactIdeal_stable (F:Poly4 K):
   ∀ P∈contactIdeal K F,contactVectorField K F P∈contactIdeal K F:=by
 apply derivation_preserves_span
 intro P hP
 have hrel:inverseRelation K (contactH K F)∈contactIdeal K F:=
   Ideal.subset_span (by simp)
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP
 rcases hP with rfl | rfl
 · rw [contactVectorField_F]
   exact (contactIdeal K F).mul_mem_left _ hrel
 · rw [contactVectorField,
     inverseVectorField_inverseRelation K _ _ (partial_extra_contactH K F)]
   exact (contactIdeal K F).mul_mem_left _ hrel
abbrev ContactRing (F:Poly4 K):=Poly5 K ⧸ contactIdeal K F
noncomputable def contactDerivation (F:Poly4 K):
   Derivation K (ContactRing K F) (ContactRing K F):=
 quotientDerivation (contactVectorField K F) (contactIdeal K F) (contactIdeal_stable K F)
theorem contactDerivation_mk (F:Poly4 K) (P:Poly5 K):
   contactDerivation K F (Ideal.Quotient.mk (contactIdeal K F) P)=
     Ideal.Quotient.mk (contactIdeal K F) (contactVectorField K F P):=
 quotientDerivation_mk _ _ _ P
theorem contactRing_relation (F:Poly4 K):
   Ideal.Quotient.mk (contactIdeal K F) (liftFour K F)=0:=by
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 exact Ideal.subset_span (by simp)
theorem contactRing_inverse (F:Poly4 K):
   Ideal.Quotient.mk (contactIdeal K F) (contactH K F)*
     Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))=1:=by
 have hrel:Ideal.Quotient.mk (contactIdeal K F)
     (inverseRelation K (contactH K F))=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
 simpa only [inverseRelation,map_sub,map_mul,map_one,sub_eq_zero] using hrel
end PolynomialVectorField
end ProximityPrize.SubmissionLower.RCN077
end PackedLegacy_B5

section PackedLegacy_W
namespace ProximityPrize.SubmissionLower.RCN313
open RCN077 RCN347
noncomputable section
section AlgebraicStep
variable {K A B:Type*} [CommRing K] [CommRing A] [CommRing B] [Algebra K A]
def clearedStep (n:ℕ) (m mx my mr r g h hx hy hr:A):A:=
 h^2*mx+r*h^2*my+g*h*mr-
   (n:A)*m*(h*hx+r*h*hy+g*hr)
theorem map_clearedStep (φ:A →+*B) (n:ℕ) (m mx my mr r g h hx hy hr:A):
   φ (clearedStep n m mx my mr r g h hx hy hr)=
     clearedStep n (φ m) (φ mx) (φ my) (φ mr) (φ r) (φ g) (φ h)
       (φ hx) (φ hy) (φ hr):=by
 simp only [clearedStep,map_sub,map_add,map_mul,map_pow,map_natCast]
theorem derivation_inverse_power
   (D:Derivation K A A) (u a:A) (hU:D u= -(u^2*a)) (n:ℕ):
   D (u^n)= -(n:A)*u^(n+1)*a:=by
 induction n with
 | zero =>
     simp only [pow_zero,D.map_one_eq_zero,Nat.cast_zero,neg_zero,zero_mul]
 | succ n ih =>
     rw [pow_succ,leibniz_product,ih,hU]
     simp only [Nat.cast_succ,pow_succ]
     ring
theorem differentiated_fraction_step
   (D:Derivation K A A) (n:ℕ) (m mx my mr r g h hx hy hr u:A)
   (hHU:h*u=1)
   (hM:D m=mx+r*my+g*u*mr)
   (hU:D u= -(u^2*(hx+r*hy+g*u*hr))):
   D (m*u^n)=clearedStep n m mx my mr r g h hx hy hr*u^(n+2):=by
 rw [leibniz_product,hM,
   derivation_inverse_power D u (hx+r*hy+g*u*hr) hU n]
 simp only [pow_add,pow_one]
 unfold clearedStep
 linear_combination
   -(u^n)*((1+h*u)*(mx+r*my)+g*u*mr-
     (n:A)*m*u*(hx+r*hy))*hHU
end AlgebraicStep
section ContactQuotient
variable (K:Type*) [CommRing K]
def polyH (F:Poly4 K):Poly4 K:=MvPolynomial.pderiv (2:Fin 4) F
def polyG (F:Poly4 K):Poly4 K:=
 -(MvPolynomial.pderiv (0:Fin 4) F+
   MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) F)
theorem partial_liftFour_zero (P:Poly4 K):
   MvPolynomial.pderiv (0:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (0:Fin 4) P):=
 partial_liftFour K P (0:Fin 4)
theorem partial_liftFour_one (P:Poly4 K):
   MvPolynomial.pderiv (1:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (1:Fin 4) P):=
 partial_liftFour K P (1:Fin 4)
theorem partial_liftFour_two (P:Poly4 K):
   MvPolynomial.pderiv (2:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (2:Fin 4) P):=
 partial_liftFour K P (2:Fin 4)
theorem castSucc_two:(2:Fin 4).castSucc=(2:Fin 5):=rfl
theorem contactH_eq_lift (F:Poly4 K):
   contactH K F=liftFour K (polyH K F):=
 partial_liftFour K F (2:Fin 4)
theorem contactG_eq_lift (F:Poly4 K):
   contactG K F=liftFour K (polyG K F):=by
 unfold contactG polyG
 rw [partial_liftFour_zero,partial_liftFour_one]
 simp only [liftFour,map_neg,map_add,map_mul,MvPolynomial.rename_X,
   castSucc_two]
def polyImage (F:Poly4 K):Poly4 K →+*ContactRing K F:=
 (Ideal.Quotient.mk (contactIdeal K F)).comp
   (MvPolynomial.rename (R:=K) (Fin.castSucc:Fin 4 → Fin 5)).toRingHom
theorem polyImage_apply (F P:Poly4 K):
   polyImage K F P=Ideal.Quotient.mk (contactIdeal K F) (liftFour K P):=rfl
@[simp] theorem polyImage_X (F:Poly4 K) (i:Fin 4):
   polyImage K F (MvPolynomial.X i)=
     Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X i.castSucc):=by
 rw [polyImage_apply]
 simp only [liftFour,MvPolynomial.rename_X]
def inverseCoordinate (F:Poly4 K):ContactRing K F:=
 Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))
theorem polyImage_H_mul_inverse (F:Poly4 K):
   polyImage K F (polyH K F)*inverseCoordinate K F=1:=by
 change Ideal.Quotient.mk (contactIdeal K F) (liftFour K (polyH K F))*
   Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))=1
 rw [←contactH_eq_lift]
 exact contactRing_inverse K F
theorem contactDerivation_polyImage (F P:Poly4 K):
   contactDerivation K F (polyImage K F P)=
     polyImage K F (MvPolynomial.pderiv (0:Fin 4) P)+
       polyImage K F (MvPolynomial.X (2:Fin 4))*
         polyImage K F (MvPolynomial.pderiv (1:Fin 4) P)+
       polyImage K F (polyG K F)*inverseCoordinate K F*
         polyImage K F (MvPolynomial.pderiv (2:Fin 4) P):=by
 rw [polyImage_apply,contactDerivation_mk,contactVectorField,
   inverseVectorField_apply,partial_extra_liftFour,mul_zero,sub_zero]
 rw [partial_liftFour_zero,partial_liftFour_one,partial_liftFour_two,contactG_eq_lift]
 simp only [map_add,map_mul,polyImage_apply,inverseCoordinate,
   liftFour,MvPolynomial.rename_X,castSucc_two]
theorem contactDerivation_inverseCoordinate (F:Poly4 K):
   contactDerivation K F (inverseCoordinate K F)=
     -(inverseCoordinate K F^2*
       (polyImage K F (MvPolynomial.pderiv (0:Fin 4) (polyH K F))+
         polyImage K F (MvPolynomial.X (2:Fin 4))*
           polyImage K F (MvPolynomial.pderiv (1:Fin 4) (polyH K F))+
         polyImage K F (polyG K F)*inverseCoordinate K F*
           polyImage K F (MvPolynomial.pderiv (2:Fin 4) (polyH K F)))):=by
 rw [inverseCoordinate,contactDerivation_mk,contactVectorField,inverseVectorField_U]
 rw [contactG_eq_lift,contactH_eq_lift]
 unfold inverseDerivative
 rw [partial_liftFour_zero,partial_liftFour_one,partial_liftFour_two]
 simp only [map_neg,map_mul,map_pow,map_add,polyImage_apply,
   inverseCoordinate,liftFour,MvPolynomial.rename_X,castSucc_two]
def numeratorStep (F:Poly4 K) (b:ℕ) (M:Poly4 K):Poly4 K:=
 clearedStep (2*b) M
   (MvPolynomial.pderiv (0:Fin 4) M)
   (MvPolynomial.pderiv (1:Fin 4) M)
   (MvPolynomial.pderiv (2:Fin 4) M)
   (MvPolynomial.X (2:Fin 4)) (polyG K F) (polyH K F)
   (MvPolynomial.pderiv (0:Fin 4) (polyH K F))
   (MvPolynomial.pderiv (1:Fin 4) (polyH K F))
   (MvPolynomial.pderiv (2:Fin 4) (polyH K F))
def numerator (F:Poly4 K):ℕ → Poly4 K
 | 0 => MvPolynomial.X (1:Fin 4)
 | b+1 => numeratorStep K F b (numerator F b)
@[simp] theorem numerator_zero (F:Poly4 K):
   numerator K F 0=MvPolynomial.X (1:Fin 4):=rfl
@[simp] theorem numerator_succ (F:Poly4 K) (b:ℕ):
   numerator K F (b+1)=numeratorStep K F b (numerator K F b):=rfl
theorem iterate_Y_eq_numerator (F:Poly4 K) (b:ℕ):
   (contactDerivation K F)^[b] (polyImage K F (MvPolynomial.X (1:Fin 4)))=
     polyImage K F (numerator K F b)*inverseCoordinate K F^(2*b):=by
 induction b with
 | zero => simp
 | succ b ih =>
     rw [Function.iterate_succ_apply',ih,numerator_succ,numeratorStep,
       map_clearedStep]
     have hexp:2*(b+1)=2*b+2:=by omega
     rw [hexp]
     apply differentiated_fraction_step
     · exact polyImage_H_mul_inverse K F
     · exact contactDerivation_polyImage K F (numerator K F b)
     · exact contactDerivation_inverseCoordinate K F
end ContactQuotient
section DegreeBounds
variable {K:Type*} [Field K]
theorem support_before_pderiv (i:Fin 4) (P:Poly4 K) (d:Fin 4 →₀ ℕ)
   (hd:d∈(MvPolynomial.pderiv i P).support):
   d+Finsupp.single i 1∈P.support:=by
 apply MvPolynomial.mem_support_iff.mpr
 intro hzero
 have hne:=MvPolynomial.mem_support_iff.mp hd
 apply hne
 rw [MvPolynomial.coeff_pderiv,hzero,zero_mul]
theorem pderiv_degree_bound (i j:Fin 4) (P:Poly4 K) (a:ℕ)
   (hP:P.degreeOf j ≤ a):(MvPolynomial.pderiv i P).degreeOf j ≤ a:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hh:=MvPolynomial.degreeOf_le_iff.mp hP
   (d+Finsupp.single i 1) (support_before_pderiv i P d hd)
 simp only [Finsupp.add_apply] at hh
 omega
theorem pderiv_same_degree_bound (i:Fin 4) (P:Poly4 K) (a:ℕ)
   (hP:P.degreeOf i ≤ a):(MvPolynomial.pderiv i P).degreeOf i ≤ a-1:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hh:=MvPolynomial.degreeOf_le_iff.mp hP
   (d+Finsupp.single i 1) (support_before_pderiv i P d hd)
 simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
 omega
theorem pderiv_eq_zero_of_degree_bound_zero (i:Fin 4) (P:Poly4 K)
   (hP:P.degreeOf i ≤ 0):MvPolynomial.pderiv i P=0:=by
 ext d
 rw [MvPolynomial.coeff_zero,MvPolynomial.coeff_pderiv]
 have hzero:AddMonoidAlgebra.coeff P (d+Finsupp.single i 1)=0:=by
   by_contra hne
   have hh:=MvPolynomial.degreeOf_le_iff.mp hP
     (d+Finsupp.single i 1) (MvPolynomial.mem_support_iff.mpr hne)
   simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
   omega
 rw [hzero,zero_mul]
 simp
theorem degree_mul_bound (i:Fin 4) {P Q:Poly4 K} {a b:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ b):
   (P*Q).degreeOf i ≤ a+b:=
 (MvPolynomial.degreeOf_mul_le i P Q).trans (Nat.add_le_add hP hQ)
theorem degree_add_bound (i:Fin 4) {P Q:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ a):
   (P+Q).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_add_le i P Q).trans (max_le hP hQ)
theorem degree_sub_bound (i:Fin 4) {P Q:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ a):
   (P-Q).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_sub_le i P Q).trans (max_le hP hQ)
theorem degree_pow_bound (i:Fin 4) (n:ℕ) {P:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a):(P^n).degreeOf i ≤ n*a:=
 (MvPolynomial.degreeOf_pow_le i P n).trans (Nat.mul_le_mul_left n hP)
theorem degree_natCast_eq_zero (i:Fin 4) (n:ℕ):
   (n:Poly4 K).degreeOf i=0:=by
 rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K) n]
 exact MvPolynomial.degreeOf_C (n:K) i
theorem polyG_degree_bound (i:Fin 4) (F:Poly4 K) (a r:ℕ)
   (hF:F.degreeOf i ≤ a) (hR:(MvPolynomial.X (2:Fin 4):Poly4 K).degreeOf i ≤ r):
   (polyG K F).degreeOf i ≤ a+r:=by
 unfold polyG
 rw [MvPolynomial.degreeOf_neg]
 apply degree_add_bound i
 · have hh:=pderiv_degree_bound (0:Fin 4) i F a hF
   omega
 · have hh:=degree_mul_bound i hR (pderiv_degree_bound (1:Fin 4) i F a hF)
   simpa only [Nat.add_comm] using hh
theorem numeratorStep_nonR_degree_bound
   (i:Fin 4) (hi:i≠2) (F M:Poly4 K) (b a c:ℕ)
   (hF:F.degreeOf i ≤ c) (hM:M.degreeOf i ≤ a):
   (numeratorStep K F b M).degreeOf i ≤ a+2*c:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf i ≤ 0:=by
   simp only [R,MvPolynomial.degreeOf_X_of_ne hi,le_refl]
 have hH:H.degreeOf i ≤ c:=pderiv_degree_bound (2:Fin 4) i F c hF
 have hG:G.degreeOf i ≤ c:=by
   simpa only [Nat.add_zero] using polyG_degree_bound i F c 0 hF hR
 have hH2:=degree_pow_bound i 2 hH
 have hMX:=pderiv_degree_bound (0:Fin 4) i M a hM
 have hMY:=pderiv_degree_bound (1:Fin 4) i M a hM
 have hMR:=pderiv_degree_bound (2:Fin 4) i M a hM
 have hHX:=pderiv_degree_bound (0:Fin 4) i H c hH
 have hHY:=pderiv_degree_bound (1:Fin 4) i H c hH
 have hHR:=pderiv_degree_bound (2:Fin 4) i H c hH
 have h1:(H^2*MvPolynomial.pderiv (0:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i hH2 hMX
   omega
 have h2:(R*H^2*MvPolynomial.pderiv (1:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hR hH2) hMY
   omega
 have h3:(G*H*MvPolynomial.pderiv (2:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hG hH) hMR
   omega
 have hbx:(H*MvPolynomial.pderiv (0:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i hH hHX
   omega
 have hby:(R*H*MvPolynomial.pderiv (1:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hR hH) hHY
   omega
 have hbr:(G*MvPolynomial.pderiv (2:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i hG hHR
   omega
 have hbrace:=degree_add_bound i (degree_add_bound i hbx hby) hbr
 have hn:(((2*b:ℕ):Poly4 K)).degreeOf i ≤ 0:=
   le_of_eq (degree_natCast_eq_zero i (2*b))
 have hnM:(((2*b:ℕ):Poly4 K)*M).degreeOf i ≤ a:=by
   simpa only [Nat.zero_add] using degree_mul_bound i hn hM
 have h4:=degree_mul_bound i hnM hbrace
 change (H^2*MvPolynomial.pderiv (0:Fin 4) M+
     R*H^2*MvPolynomial.pderiv (1:Fin 4) M+
     G*H*MvPolynomial.pderiv (2:Fin 4) M-
     ((2*b:ℕ):Poly4 K)*M*
       (H*MvPolynomial.pderiv (0:Fin 4) H+
         R*H*MvPolynomial.pderiv (1:Fin 4) H+
         G*MvPolynomial.pderiv (2:Fin 4) H)).degreeOf i ≤ a+2*c
 exact degree_sub_bound i (degree_add_bound i (degree_add_bound i h1 h2) h3) h4
theorem numeratorStep_R_degree_bound
   (F M:Poly4 K) (b a s:ℕ) (hs:1 ≤ s)
   (hF:F.degreeOf (2:Fin 4) ≤ s) (hM:M.degreeOf (2:Fin 4) ≤ a):
   (numeratorStep K F b M).degreeOf (2:Fin 4) ≤ a+(2*s-1):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s-1:=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s+1:=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hH2:=degree_pow_bound (2:Fin 4) 2 hH
 have hMX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) M a hM
 have hMY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) M a hM
 have hMR:=pderiv_same_degree_bound (2:Fin 4) M a hM
 have hHX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) H (s-1) hH
 have hHY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) H (s-1) hH
 have hHR:=pderiv_same_degree_bound (2:Fin 4) H (s-1) hH
 have h1:(H^2*MvPolynomial.pderiv (0:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   have hh:=degree_mul_bound (2:Fin 4) hH2 hMX
   omega
 have h2:(R*H^2*MvPolynomial.pderiv (1:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH2) hMY
   omega
 have h3:(G*H*MvPolynomial.pderiv (2:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   by_cases ha:a=0
   · have hz:MvPolynomial.pderiv (2:Fin 4) M=0:=
       pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) M (by simpa only [ha] using hM)
     rw [hz,mul_zero,MvPolynomial.degreeOf_zero]
     exact Nat.zero_le _
   · have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hG hH) hMR
     omega
 have hbx:(H*MvPolynomial.pderiv (0:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   have hh:=degree_mul_bound (2:Fin 4) hH hHX
   omega
 have hby:(R*H*MvPolynomial.pderiv (1:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH) hHY
   omega
 have hbr:(G*MvPolynomial.pderiv (2:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   by_cases hsone:s=1
   · have hz:MvPolynomial.pderiv (2:Fin 4) H=0:=
       pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) H (by simpa [hsone] using hH)
     rw [hz,mul_zero,MvPolynomial.degreeOf_zero]
     exact Nat.zero_le _
   · have hh:=degree_mul_bound (2:Fin 4) hG hHR
     omega
 have hbrace:=degree_add_bound (2:Fin 4)
   (degree_add_bound (2:Fin 4) hbx hby) hbr
 have hn:(((2*b:ℕ):Poly4 K)).degreeOf (2:Fin 4) ≤ 0:=
   le_of_eq (degree_natCast_eq_zero (2:Fin 4) (2*b))
 have hnM:(((2*b:ℕ):Poly4 K)*M).degreeOf (2:Fin 4) ≤ a:=by
   simpa only [Nat.zero_add] using degree_mul_bound (2:Fin 4) hn hM
 have h4:=degree_mul_bound (2:Fin 4) hnM hbrace
 change (H^2*MvPolynomial.pderiv (0:Fin 4) M+
     R*H^2*MvPolynomial.pderiv (1:Fin 4) M+
     G*H*MvPolynomial.pderiv (2:Fin 4) M-
     ((2*b:ℕ):Poly4 K)*M*
       (H*MvPolynomial.pderiv (0:Fin 4) H+
         R*H*MvPolynomial.pderiv (1:Fin 4) H+
         G*MvPolynomial.pderiv (2:Fin 4) H)).degreeOf (2:Fin 4) ≤ a+(2*s-1)
 exact degree_sub_bound (2:Fin 4)
   (degree_add_bound (2:Fin 4) (degree_add_bound (2:Fin 4) h1 h2) h3) h4
theorem numerator_nonR_degree_bound
   (i:Fin 4) (hi:i≠2) (F:Poly4 K) (c a₀:ℕ)
   (hF:F.degreeOf i ≤ c) (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (b:ℕ):(numerator K F b).degreeOf i ≤ a₀+2*b*c:=by
 induction b with
 | zero => simpa only [numerator_zero,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] using hbase
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_nonR_degree_bound i hi F (numerator K F b) b
       (a₀+2*b*c) c hF ih
     have heq:a₀+2*(b+1)*c=(a₀+2*b*c)+2*c:=by ring
     rw [heq]
     exact hh
theorem numerator_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) (b:ℕ):
   (numerator K F b).degreeOf (2:Fin 4) ≤ b*(2*s-1):=by
 induction b with
 | zero => simp [numerator_zero,MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4)≠1)]
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_R_degree_bound F (numerator K F b) b
       (b*(2*s-1)) s hs hF ih
     simpa only [Nat.add_mul,Nat.one_mul] using hh
end DegreeBounds
section AgreementNumerators
variable {K:Type*} [Field K]
def commonNumeratorTerm (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x:K) (j:ℕ):
   Poly4 K:=
 MvPolynomial.C (c j)*numerator K F j*
   polyH K F^(2*(w-j))*
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j
def clearedTaylorNumerator (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x:K):Poly4 K:=
 ∑ j∈Finset.range (w+1),commonNumeratorTerm F w c x j
def affineSeedPolynomial (u₀ u₁:K):Poly4 K:=
 MvPolynomial.C u₀+MvPolynomial.X (3:Fin 4)*MvPolynomial.C u₁
def agreementNumerator (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   Poly4 K:=
 clearedTaylorNumerator F w c x-affineSeedPolynomial u₀ u₁*polyH K F^(2*w)
theorem shiftedX_degree_bound (i:Fin 4) (hi:i≠0) (x:K):
   (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K).degreeOf i ≤ 0:=by
 apply degree_sub_bound i
 · simp only [MvPolynomial.degreeOf_C,le_refl]
 · simp only [MvPolynomial.degreeOf_X_of_ne hi,le_refl]
theorem degree_sum_bound (i:Fin 4) (I:Finset ℕ) (f:ℕ → Poly4 K) (a:ℕ)
   (hf:∀ j∈I,(f j).degreeOf i ≤ a):
   (∑ j∈I,f j).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_sum_le i I f).trans (Finset.sup_le hf)
theorem commonNumeratorTerm_nonR_degree_bound
   (i:Fin 4) (hi₀:i≠0) (hi₂:i≠2)
   (F:Poly4 K) (cap a₀:ℕ) (hF:F.degreeOf i ≤ cap)
   (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K):
   (commonNumeratorTerm F w c x j).degreeOf i ≤ a₀+2*w*cap:=by
 have hM:=numerator_nonR_degree_bound i hi₂ F cap a₀ hF hbase j
 have hCM:(MvPolynomial.C (c j)*numerator K F j).degreeOf i ≤ a₀+2*j*cap:=
   (MvPolynomial.degreeOf_C_mul_le (numerator K F j) i (c j)).trans hM
 have hH:(polyH K F).degreeOf i ≤ cap:=
   pderiv_degree_bound (2:Fin 4) i F cap hF
 have hHP:=degree_pow_bound i (2*(w-j)) hH
 have hXP:((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j).degreeOf i ≤ 0:=by
   simpa only [Nat.mul_zero] using degree_pow_bound i j (shiftedX_degree_bound i hi₀ x)
 have hterm:=degree_mul_bound i (degree_mul_bound i hCM hHP) hXP
 have hw:j+(w-j)=w:=by omega
 have heq:(a₀+2*j*cap)+2*(w-j)*cap+0=a₀+2*w*cap:=by
   calc
     (a₀+2*j*cap)+2*(w-j)*cap+0=a₀+2*(j+(w-j))*cap:=by ring
     _=a₀+2*w*cap:=by rw [hw]
 exact hterm.trans (le_of_eq heq)
theorem commonNumeratorTerm_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K):
   (commonNumeratorTerm F w c x j).degreeOf (2:Fin 4) ≤ w*(2*s-1):=by
 have hM:=numerator_R_degree_bound F s hs hF j
 have hCM:(MvPolynomial.C (c j)*numerator K F j).degreeOf (2:Fin 4) ≤ j*(2*s-1):=
   (MvPolynomial.degreeOf_C_mul_le (numerator K F j) (2:Fin 4) (c j)).trans hM
 have hH:(polyH K F).degreeOf (2:Fin 4) ≤ s-1:=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hHP:=degree_pow_bound (2:Fin 4) (2*(w-j)) hH
 have hXP:((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j).degreeOf (2:Fin 4) ≤ 0:=by
   simpa only [Nat.mul_zero] using
     degree_pow_bound (2:Fin 4) j (shiftedX_degree_bound (2:Fin 4) (by decide) x)
 have hterm:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hCM hHP) hXP
 have hw:j+(w-j)=w:=by omega
 have hs':2*s-1=2*(s-1)+1:=by omega
 have hcap:j*(2*s-1)+2*(w-j)*(s-1) ≤ w*(2*s-1):=by
   rw [hs']
   calc
     j*(2*(s-1)+1)+2*(w-j)*(s-1)=
         2*(j+(w-j))*(s-1)+j:=by ring
     _=2*w*(s-1)+j:=by rw [hw]
     _ ≤ 2*w*(s-1)+w:=Nat.add_le_add_left hj _
     _=w*(2*(s-1)+1):=by ring
 have hterm':(commonNumeratorTerm F w c x j).degreeOf (2:Fin 4) ≤
     j*(2*s-1)+2*(w-j)*(s-1):=by
   simpa only [commonNumeratorTerm,Nat.add_zero] using hterm
 exact hterm'.trans hcap
theorem clearedTaylorNumerator_nonR_degree_bound
   (i:Fin 4) (hi₀:i≠0) (hi₂:i≠2)
   (F:Poly4 K) (cap a₀:ℕ) (hF:F.degreeOf i ≤ cap)
   (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (w:ℕ) (c:ℕ → K) (x:K):
   (clearedTaylorNumerator F w c x).degreeOf i ≤ a₀+2*w*cap:=by
 unfold clearedTaylorNumerator
 apply degree_sum_bound i
 intro j hj
 exact commonNumeratorTerm_nonR_degree_bound i hi₀ hi₂ F cap a₀ hF hbase w j
   (by have hh:=Finset.mem_range.mp hj;omega) c x
theorem clearedTaylorNumerator_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x:K):
   (clearedTaylorNumerator F w c x).degreeOf (2:Fin 4) ≤ w*(2*s-1):=by
 unfold clearedTaylorNumerator
 apply degree_sum_bound (2:Fin 4)
 intro j hj
 exact commonNumeratorTerm_R_degree_bound F s hs hF w j
   (by have hh:=Finset.mem_range.mp hj;omega) c x
theorem affineSeedPolynomial_degree_bound (i:Fin 4) (cap:ℕ)
   (hZ:(MvPolynomial.X (3:Fin 4):Poly4 K).degreeOf i ≤ cap) (u₀ u₁:K):
   (affineSeedPolynomial u₀ u₁).degreeOf i ≤ cap:=by
 unfold affineSeedPolynomial
 apply degree_add_bound i
 · simp only [MvPolynomial.degreeOf_C,Nat.zero_le]
 · have hC:(MvPolynomial.C u₁:Poly4 K).degreeOf i ≤ 0:=by
     simp only [MvPolynomial.degreeOf_C,le_refl]
   simpa only [Nat.add_zero] using degree_mul_bound i hZ hC
theorem agreementNumerator_degree_bounds
   (F:Poly4 K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf (1:Fin 4) ≤ ell)
   (hR:F.degreeOf (2:Fin 4) ≤ s)
   (hZ:F.degreeOf (3:Fin 4) ≤ L)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   (agreementNumerator F w c x u₀ u₁).degreeOf (1:Fin 4) ≤ 1+2*w*ell∧
   (agreementNumerator F w c x u₀ u₁).degreeOf (2:Fin 4) ≤ w*(2*s-1)∧
   (agreementNumerator F w c x u₀ u₁).degreeOf (3:Fin 4) ≤ 2*w*L+1:=by
 unfold agreementNumerator
 refine ⟨?_,?_,?_⟩
 · apply degree_sub_bound (1:Fin 4)
   · exact clearedTaylorNumerator_nonR_degree_bound (1:Fin 4) (by decide) (by decide)
       F ell 1 hY (by simp) w c x
   · have ha:=affineSeedPolynomial_degree_bound (1:Fin 4) 0
       (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 4)≠3)]) u₀ u₁
     have hH:(polyH K F).degreeOf (1:Fin 4) ≤ ell:=
       pderiv_degree_bound (2:Fin 4) (1:Fin 4) F ell hY
     have hh:=degree_mul_bound (1:Fin 4) ha (degree_pow_bound (1:Fin 4) (2*w) hH)
     omega
 · apply degree_sub_bound (2:Fin 4)
   · exact clearedTaylorNumerator_R_degree_bound F s hs hR w c x
   · have ha:=affineSeedPolynomial_degree_bound (2:Fin 4) 0
       (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4)≠3)]) u₀ u₁
     have hH:=pderiv_same_degree_bound (2:Fin 4) F s hR
     have hh:=degree_mul_bound (2:Fin 4) ha (degree_pow_bound (2:Fin 4) (2*w) hH)
     have hs':2*s-1=2*(s-1)+1:=by omega
     have hcap:0+(2*w)*(s-1) ≤ w*(2*s-1):=by
       rw [hs']
       calc
         0+(2*w)*(s-1) ≤ 2*w*(s-1)+w:=by omega
         _=w*(2*(s-1)+1):=by ring
     exact hh.trans hcap
 · apply degree_sub_bound (3:Fin 4)
   · have hh:=clearedTaylorNumerator_nonR_degree_bound (3:Fin 4) (by decide) (by decide)
       F L 0 hZ
         (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(3:Fin 4)≠1)]) w c x
     omega
   · have ha:=affineSeedPolynomial_degree_bound (3:Fin 4) 1 (by simp) u₀ u₁
     have hH:(polyH K F).degreeOf (3:Fin 4) ≤ L:=
       pderiv_degree_bound (2:Fin 4) (3:Fin 4) F L hZ
     have hh:=degree_mul_bound (3:Fin 4) ha (degree_pow_bound (3:Fin 4) (2*w) hH)
     omega
end AgreementNumerators
end
end ProximityPrize.SubmissionLower.RCN313
end PackedLegacy_W

section PackedLegacy_N4
namespace ProximityPrize.SubmissionLower.RCN256
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def slopeDifference:Poly K:=MvPolynomial.X 0-MvPolynomial.X 1
private def plusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X i
def shiftPlus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (plusVariables K)
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
def boxExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 2 ≤ L∧d 1 ≤ s}
def coefficientBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (boxExponents M L s)
theorem coefficientBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈coefficientBox K M L s)
   (hg:g∈coefficientBox K M' L' s'):
   f*g∈coefficientBox K (M+M') (L+L') (s+s'):=by
 have hset:boxExponents M L s+boxExponents M' L' s' ⊆
     boxExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hd2,hd1⟩
   rcases he with ⟨he0,he2,he1⟩
   simp only [boxExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   omega
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
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
abbrev BoxIndex (M L s:ℕ):=
 (i:Fin (min M L+1)) × (Fin (s+1) × Fin (L-i.val+1))
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
         change d.val 2 < L-d.val 0+1
         rcases d.property with ⟨hM,hL,hs⟩
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
   simp
   apply finPair_heq_of_val_eq
   · simp [exponentTriple]
   · rfl
   · rfl
instance boxExponentsFintype (M L s:ℕ):Fintype (boxExponents M L s):=
 Fintype.ofEquiv (BoxIndex M L s) (boxExponentsEquivIndex M L s).symm
instance coefficientBoxFinite (M L s:ℕ):
   Module.Finite K (coefficientBox K M L s):=
 Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boxExponents M L s))
def blockJet (M L s h:ℕ):coefficientBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (coefficientBox K M L s).subtype
end
end ProximityPrize.SubmissionLower.RCN256
end PackedLegacy_N4

section PackedLegacy_Q
namespace ProximityPrize.SubmissionLower.RCN174
open RCN256 
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
   localMonomial K f j z∈coefficientBox K f (f+z) j:=by
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
   (Fin (L+1-i.val) × Fin (D-w*i.val-(w-1)*j.val))
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 3 ≤ L∧d 2 ≤ s∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):
   Submodule K (MvPolynomial (Fin 4) K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
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
     (show c.1.val-f.val+(f.val+c.2.2.1.val) ≤ L by omega)
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
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))
end
end ProximityPrize.SubmissionLower.RCN174
end PackedLegacy_Q

section PackedLegacy_DC
namespace ProximityPrize.SubmissionLower
namespace BCHKSSubstitutionVanish
theorem mul_card_le_natDegree_of_rootMultiplicity
   {F ι:Type*} [Field F] [DecidableEq F] [DecidableEq ι]
   (R:Polynomial F) (ω:ι ↪ F) (A:Finset ι) (m:Nat)
   (hmult:∀ i∈A,m ≤ R.rootMultiplicity (ω i)):
   m*A.card ≤ R.natDegree:=by
 let xs:Finset F:=A.map ω
 have hselected:
     ∑ x∈xs,Multiset.count x R.roots ≤ R.roots.card:=by
   let all:=xs ∪ R.roots.toFinset
   calc
     ∑ x∈xs,Multiset.count x R.roots ≤
         ∑ x∈all,Multiset.count x R.roots:=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
     _=∑ x∈R.roots.toFinset,Multiset.count x R.roots:=by
       symm
       apply Finset.sum_subset (Finset.subset_union_right)
       intro x hxall hxroots
       exact Multiset.count_eq_zero.mpr (by simpa using hxroots)
     _=R.roots.card:=Multiset.toFinset_sum_count_eq R.roots
 calc
   m*A.card=∑ i∈A,m:=by simp [Nat.mul_comm]
   _ ≤ ∑ i∈A,R.rootMultiplicity (ω i):=
     Finset.sum_le_sum fun i hi => hmult i hi
   _=∑ x∈xs,R.rootMultiplicity x:=by
     symm
     exact Finset.sum_map A ω (fun x => R.rootMultiplicity x)
   _=∑ x∈xs,Multiset.count x R.roots:=by
     apply Finset.sum_congr rfl
     intro x hx
     exact (Polynomial.count_roots R).symm
   _ ≤ R.roots.card:=hselected
   _ ≤ R.natDegree:=Polynomial.card_roots' R
end BCHKSSubstitutionVanish
end ProximityPrize.SubmissionLower
end PackedLegacy_DC

section PackedLegacy_C6
namespace ProximityPrize.SubmissionLower.RCN185
open Polynomial
section LocalRing
variable {F:Type*} [CommRing F]
theorem shifted_power_dvd_iff_taylor_coeff_zero
   (P:F[X]) (x:F) (h:ℕ):
   (Polynomial.X-Polynomial.C x)^h∣P ↔
     ∀ j < h,(taylor x P).coeff j=0:=by
 have hshift:taylor x ((Polynomial.X-Polynomial.C x)^h)=
     (Polynomial.X:F[X])^h:=by
   rw [taylor_pow,map_sub,taylor_X,taylor_C,add_sub_cancel_right]
 have hdiv:=map_dvd_iff (taylorEquiv x)
   (a:=((Polynomial.X:F[X])-Polynomial.C x)^h) (b:=P)
 change taylor x ((Polynomial.X-Polynomial.C x)^h)∣taylor x P ↔
   (Polynomial.X-Polynomial.C x)^h∣P at hdiv
 rw [hshift] at hdiv
 exact hdiv.symm.trans (Polynomial.X_pow_dvd_iff (f:=taylor x P) (n:=h))
noncomputable def contactResidual (P:F[X]) (x:F):F[X]:=
 taylor x P-Polynomial.C (P.eval x)-
   Polynomial.X*taylor x P.derivative
theorem X_sq_dvd_contactResidual (P:F[X]) (x:F):
   (Polynomial.X:F[X])^2∣contactResidual P x:=by
 rw [X_pow_dvd_iff]
 intro j hj
 have hcases:j=0∨j=1:=by omega
 rcases hcases with rfl | rfl
 · simp [contactResidual]
 · simp [contactResidual,coeff_X_mul]
end LocalRing
section GlobalVanishing
variable {F I J:Type*} [Field F] [DecidableEq F] [DecidableEq I]
end GlobalVanishing
end ProximityPrize.SubmissionLower.RCN185
end PackedLegacy_C6

section PackedLegacy_K
namespace ProximityPrize.SubmissionLower.RCN319
open RCN256 RCN174 
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
abbrev LocalPolynomial:=Polynomial (Poly K)
def translationVariables (x u₀ u₁:K):Fin 4 → LocalPolynomial K:=
 ![Polynomial.X+Polynomial.C (MvPolynomial.C x),
   Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
     Polynomial.C (seedAffine K u₀ u₁),
   Polynomial.C (MvPolynomial.X 1),
   Polynomial.C (MvPolynomial.X 2)]
def homogenizedTranslation (x u₀ u₁:K):
   MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K:=
 MvPolynomial.aeval (translationVariables K x u₀ u₁)
def contactEvaluation (R B:Polynomial K) (γ:K):Poly K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![R+Polynomial.X*B,R,Polynomial.C γ]
def outerEvaluation (R B:Polynomial K) (γ:K):
   LocalPolynomial K →+*Polynomial K:=
 Polynomial.eval₂RingHom (contactEvaluation K R B γ).toRingHom Polynomial.X
@[simp] theorem contactEvaluation_slopeDifference (R B:Polynomial K) (γ:K):
   contactEvaluation K R B γ (slopeDifference K)=Polynomial.X*B:=by
 simp [contactEvaluation,slopeDifference]
theorem outerEvaluation_contact_dvd
   (H:LocalPolynomial K) (m:ℕ) (R B:Polynomial K) (γ:K)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣H.coeff r):
   (Polynomial.X:Polynomial K)^m∣outerEvaluation K R B γ H:=by
 classical
 change (Polynomial.X:Polynomial K)^m∣
   H.eval₂ (contactEvaluation K R B γ).toRingHom Polynomial.X
 rw [Polynomial.eval₂_eq_sum]
 change (Polynomial.X:Polynomial K)^m∣
   ∑ r∈H.support,contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r
 apply Finset.dvd_sum
 intro r hr
 have hlocal:(Polynomial.X:Polynomial K)^(m-r)∣
     contactEvaluation K R B γ (H.coeff r):=by
   obtain ⟨q,hq⟩:=hcoeff r
   refine ⟨B^(m-r)*contactEvaluation K R B γ q,?_⟩
   simp only [hq,map_mul,map_pow,contactEvaluation_slopeDifference,
     mul_pow,mul_assoc]
 have hprod:=mul_dvd_mul hlocal
   (dvd_refl ((Polynomial.X:Polynomial K)^r))
 have htotal:(Polynomial.X:Polynomial K)^((m-r)+r)∣
     contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r:=by
   simpa only [pow_add] using hprod
 exact (pow_dvd_pow Polynomial.X (show m ≤ (m-r)+r by omega)).trans htotal
def specialization (P:Polynomial K) (γ:K):
   MvPolynomial (Fin 4) K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![Polynomial.X,P,P.derivative,Polynomial.C γ]
theorem outerEvaluation_translation
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (B:Polynomial K)
   (hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B)):
   outerEvaluation K (Polynomial.taylor x P.derivative) B γ
       (homogenizedTranslation K x u₀ u₁ Q)=
     Polynomial.taylor x (specialization K P γ Q):=by
 have hhom:
     (outerEvaluation K (Polynomial.taylor x P.derivative) B γ).comp
       (homogenizedTranslation K x u₀ u₁).toRingHom=
     (Polynomial.taylorAlgHom x).toRingHom.comp
       (specialization K P γ).toRingHom:=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
       homogenizedTranslation,specialization,Polynomial.algebraMap_apply,
       MvPolynomial.algebraMap_eq]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
         homogenizedTranslation,translationVariables,specialization,
         seedAffine,MvPolynomial.aeval_monomial,Polynomial.algebraMap_apply,
         MvPolynomial.algebraMap_eq,hP] <;> ring
 exact DFunLike.congr_fun hhom Q
theorem X_pow_dvd_taylor_specialization
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (m:ℕ)
   (hvalue:P.eval x=u₀+γ*u₁)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K x u₀ u₁ Q).coeff r):
   (Polynomial.X:Polynomial K)^m∣
     Polynomial.taylor x (specialization K P γ Q):=by
 obtain ⟨B,hB⟩:=RCN185.X_sq_dvd_contactResidual P x
 have hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B):=by
   change Polynomial.taylor x P-Polynomial.C (P.eval x)-
     Polynomial.X*Polynomial.taylor x P.derivative=Polynomial.X^2*B at hB
   rw [hvalue] at hB
   linear_combination hB
 have hh:=outerEvaluation_contact_dvd K
   (homogenizedTranslation K x u₀ u₁ Q) m (Polynomial.taylor x P.derivative) B γ hcoeff
 rw [outerEvaluation_translation K Q P x u₀ u₁ γ B hP] at hh
 exact hh
theorem specialization_eq_zero_of_contact_and_degree
   [DecidableEq K] {I:Type*} [DecidableEq I]
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (nodes:I ↪ K) (u₀ u₁:I → K) (support:Finset I) (m:ℕ)
   (hcontact:∀ i∈support,∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K (nodes i) (u₀ i) (u₁ i) Q).coeff r)
   (hvalues:∀ i∈support,P.eval (nodes i)=u₀ i+γ*u₁ i)
   (hdegree:(specialization K P γ Q).natDegree < m*support.card):
   specialization K P γ Q=0:=by
 by_contra hnonzero
 have hmult:∀ i∈support,
     m ≤ (specialization K P γ Q).rootMultiplicity (nodes i):=by
   intro i hi
   have hlocal:=X_pow_dvd_taylor_specialization K Q P
     (nodes i) (u₀ i) (u₁ i) γ m (hvalues i hi) (hcontact i hi)
   have hshifted:(Polynomial.X-Polynomial.C (nodes i))^m∣
       specialization K P γ Q:=
     (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
       (specialization K P γ Q) (nodes i) m).mpr (Polynomial.X_pow_dvd_iff.mp hlocal)
   exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
 have hh:=BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
   (specialization K P γ Q) nodes support m hmult
 exact (Nat.not_le_of_gt hdegree) hh
theorem monomial_eq (d:Fin 4 →₀ ℕ) (a:K):
   MvPolynomial.monomial d a=
     MvPolynomial.C a*MvPolynomial.X 0^d 0*MvPolynomial.X 1^d 1*
       MvPolynomial.X 2^d 2*MvPolynomial.X 3^d 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 conv_lhs => rw [hd]
 rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem specialization_monomial
   (P:Polynomial K) (γ:K) (d:Fin 4 →₀ ℕ) (a:K):
   specialization K P γ (MvPolynomial.monomial d a)=
     Polynomial.C a*Polynomial.X^d 0*P^d 1*P.derivative^d 2*
       Polynomial.C γ^d 3:=by
 rw [monomial_eq K d a]
 simp [specialization,Polynomial.algebraMap_eq]
theorem specialization_monomial_natDegree_le
   (P:Polynomial K) (γ:K) (w:ℕ) (hP:P.natDegree ≤ w)
   (d:Fin 4 →₀ ℕ) (a:K):
   (specialization K P γ (MvPolynomial.monomial d a)).natDegree ≤
     d 0+w*d 1+(w-1)*d 2:=by
 rw [specialization_monomial]
 have hc:(Polynomial.C a:Polynomial K).natDegree ≤ 0:=by simp
 have hx:((Polynomial.X:Polynomial K)^d 0).natDegree ≤ d 0:=by simp
 have hy:(P^d 1).natDegree ≤ d 1*w:=
   Polynomial.natDegree_pow_le_of_le (d 1) hP
 have hderiv:P.derivative.natDegree ≤ w-1:=
   (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)
 have hr:(P.derivative^d 2).natDegree ≤ d 2*(w-1):=
   Polynomial.natDegree_pow_le_of_le (d 2) hderiv
 have hz:((Polynomial.C γ:Polynomial K)^d 3).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 3)
     (show (Polynomial.C γ:Polynomial K).natDegree ≤ 0 by simp)
 have hh:=Polynomial.natDegree_mul_le_of_le
   (Polynomial.natDegree_mul_le_of_le
     (Polynomial.natDegree_mul_le_of_le
       (Polynomial.natDegree_mul_le_of_le hc hx) hy) hr) hz
 simpa only [Nat.zero_add,Nat.add_zero,Nat.mul_comm] using hh
theorem specialization_natDegree_lt
   (D w L s:ℕ) (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (hD:0 < D) (hcaps:Q∈globalCoefficientBox K D w L s)
   (hP:P.natDegree ≤ w):
   (specialization K P γ Q).natDegree < D:=by
 classical
 have hsupport:∀ d∈Q.support,
     d 1+d 3 ≤ L∧d 2 ≤ s∧d 0+w*d 1+(w-1)*d 2 < D:=hcaps
 have hterms:∀ d∈Q.support,
     (specialization K P γ (MvPolynomial.monomial d (AddMonoidAlgebra.coeff Q d))).natDegree ≤
       D-1:=by
   intro d hd
   have hweight:=(hsupport d hd).2.2
   have hh:=specialization_monomial_natDegree_le K P γ w hP d (AddMonoidAlgebra.coeff Q d)
   omega
 rw [MvPolynomial.as_sum Q,map_sum]
 have hh:=Polynomial.natDegree_sum_le_of_forall_le Q.support
   (fun d => specialization K P γ (MvPolynomial.monomial d (AddMonoidAlgebra.coeff Q d))) hterms
 exact lt_of_le_of_lt hh (by omega)
end
end ProximityPrize.SubmissionLower.RCN319
end PackedLegacy_K

section PackedLegacy_C
namespace ProximityPrize.SubmissionLower.RCN081
open RCN174
noncomputable section
def weightEmbed (weights:Fin 4 → ℕ):(Fin 4 →₀ ℕ) →+(Fin 5 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+
   Finsupp.single 4 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed_castSucc (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ) (i:Fin 4):
   weightEmbed weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed]
theorem weightEmbed_last (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   weightEmbed weights d (4:Fin 5)=Finsupp.weight weights d:=by
 simp [weightEmbed]
theorem weightEmbed_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightEmbed weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 5 →₀ ℕ => a i.castSucc) h
 simpa only [weightEmbed_castSucc] using hi
variable {K:Type*} [Field K]
def weightedLift (K:Type*) [Field K] (weights:Fin 4 → ℕ):
   MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 5) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)
theorem weightedLift_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightedLift K weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)
theorem weightedLift_ne_zero (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K)
   (hP:P≠0):weightedLift K weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift_injective weights
 simpa only [map_zero] using hzero
theorem support_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).support=P.support.image (weightEmbed weights):=by
 change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _
theorem degree_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).degreeOf (4:Fin 5)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift K weights P).degreeOf (4:Fin 5)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift,Finset.sup_image]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
 funext d
 exact weightEmbed_last weights d
theorem weightedTotalDegree_mul (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift K weights (P*Q)).degreeOf (4:Fin 5):=
     (degree_weightedLift weights (P*Q)).symm
   _=(weightedLift K weights P*weightedLift K weights Q).degreeOf (4:Fin 5):=by
     rw [map_mul]
   _=(weightedLift K weights P).degreeOf (4:Fin 5)+
       (weightedLift K weights Q).degreeOf (4:Fin 5):=
     MvPolynomial.degreeOf_mul_eq (weightedLift_ne_zero weights P hP)
       (weightedLift_ne_zero weights Q hQ)
   _=MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
     rw [degree_weightedLift,degree_weightedLift]
theorem weightedTotalDegree_le_of_dvd (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hdiv:P∣Q) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights P ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hP,hG⟩
 rw [weightedTotalDegree_mul weights P G hP hG]
 exact Nat.le_add_right _ _
theorem weightedTotalDegree_le_iff (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (cap:ℕ):
   MvPolynomial.weightedTotalDegree weights P ≤ cap ↔
     ∀ d∈P.support,Finsupp.weight weights d ≤ cap:=by
 simp only [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
theorem weight_fin4 (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2+d 3*weights 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 calc
   Finsupp.weight weights d=Finsupp.weight weights
       (Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
         Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)):=congrArg _ hd
   _=_:=by simp only [map_add,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id]
def seedWeights:Fin 4 → ℕ:=![0,1,0,1]
def slopeWeights:Fin 4 → ℕ:=![0,0,1,0]
def contactWeights (w:ℕ):Fin 4 → ℕ:=![1,w,w-1,0]
theorem seed_weight (d:Fin 4 →₀ ℕ):Finsupp.weight seedWeights d=d 1+d 3:=by
 rw [weight_fin4]
 simp [seedWeights]
theorem slope_weight (d:Fin 4 →₀ ℕ):Finsupp.weight slopeWeights d=d 2:=by
 rw [weight_fin4]
 simp [slopeWeights]
theorem contact_weight (w:ℕ) (d:Fin 4 →₀ ℕ):
   Finsupp.weight (contactWeights w) d=d 0+w*d 1+(w-1)*d 2:=by
 rw [weight_fin4]
 simp [contactWeights,Nat.mul_comm]
theorem mem_globalCoefficientBox_iff (P:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hD:0 < D):
   P∈globalCoefficientBox K D w L s ↔
     MvPolynomial.weightedTotalDegree seedWeights P ≤ L∧
     MvPolynomial.weightedTotalDegree slopeWeights P ≤ s∧
     MvPolynomial.weightedTotalDegree (contactWeights w) P ≤ D-1:=by
 constructor
 · intro h
   refine ⟨?_,?_,?_⟩
   · apply (weightedTotalDegree_le_iff seedWeights P L).mpr
     intro d hd
     rw [seed_weight]
     exact (h hd).1
   · apply (weightedTotalDegree_le_iff slopeWeights P s).mpr
     intro d hd
     rw [slope_weight]
     exact (h hd).2.1
   · apply (weightedTotalDegree_le_iff (contactWeights w) P (D-1)).mpr
     intro d hd
     rw [contact_weight]
     have hh:=(h hd).2.2
     omega
 · rintro ⟨hseed,hslope,hcontact⟩ d hd
   have hs:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hseed
   have hr:=(MvPolynomial.le_weightedTotalDegree slopeWeights hd).trans hslope
   have hc:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hcontact
   rw [seed_weight] at hs
   rw [slope_weight] at hr
   rw [contact_weight] at hc
   exact ⟨hs,hr,by omega⟩
theorem mem_globalCoefficientBox_of_dvd
   (F Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
   (hQ:Q≠0) (hdiv:F∣Q)
   (hbox:Q∈globalCoefficientBox K D w L s):
   F∈globalCoefficientBox K D w L s:=by
 have hD:0 < D:=by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have hh:=(hbox hd).2.2
   omega
 have hcaps:=(mem_globalCoefficientBox_iff Q D w L s hD).mp hbox
 apply (mem_globalCoefficientBox_iff F D w L s hD).mpr
 exact ⟨(weightedTotalDegree_le_of_dvd seedWeights F Q hdiv hQ).trans hcaps.1,
   (weightedTotalDegree_le_of_dvd slopeWeights F Q hdiv hQ).trans hcaps.2.1,
   (weightedTotalDegree_le_of_dvd (contactWeights w) F Q hdiv hQ).trans hcaps.2.2⟩
theorem degreeOf_le_of_dvd (i:Fin 4) (F Q:MvPolynomial (Fin 4) K)
   (hdiv:F∣Q) (hQ:Q≠0):F.degreeOf i ≤ Q.degreeOf i:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hF,hG⟩
 rw [MvPolynomial.degreeOf_mul_eq hF hG]
 exact Nat.le_add_right _ _
theorem degreeOf_R_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (2:Fin 4) ≤ s:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (hbox hd).2.1
end
end ProximityPrize.SubmissionLower.RCN081
end PackedLegacy_C

section PackedLegacy_J1
namespace ProximityPrize.SubmissionLower.RCN082
open UniqueFactorizationMonoid RCN136 RCN174
noncomputable section
variable {K L:Type*} [Field K] [Field L]
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
 UniqueFactorizationMonoid.strongNormalizationMonoid
def activeFactors (Q:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (normalizedFactors Q).toFinset.filter
   (fun F => 0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
theorem activeFactors_spec (Q F:MvPolynomial (Fin 4) K)
   (hF:F∈activeFactors Q):
   Irreducible F∧F∣Q∧0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
 classical
 obtain ⟨hm,hp⟩:=Finset.mem_filter.mp hF
 have hmem:F∈normalizedFactors Q:=Multiset.mem_toFinset.mp hm
 exact ⟨irreducible_of_normalized_factor F hmem,
   dvd_of_mem_normalizedFactors hmem,hp⟩
theorem exists_normalized_factor_of_map_zero
   {A:Type*} [CommRing A] [IsDomain A]
   (ψ:MvPolynomial (Fin 4) K →+*A)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (hzero:ψ Q=0):
   ∃ F∈normalizedFactors Q,ψ F=0:=by
 have hassoc:=Associated.map ψ (prod_normalizedFactors hQ)
 rw [hzero] at hassoc
 have hp:ψ (normalizedFactors Q).prod=0:=
   (associated_zero_iff_eq_zero _).mp hassoc
 rw [map_multiset_prod] at hp
 exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
theorem eq_C_of_all_degreeOf_zero (P:MvPolynomial (Fin 3) L)
   (h:∀ i,P.degreeOf i=0):P=MvPolynomial.C (P.coeff 0):=by
 classical
 apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
 apply Nat.eq_zero_of_le_zero
 rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
 intro d hd
 have hd0:d=0:=by
   ext i
   have hi:=MvPolynomial.monomial_le_degreeOf i hd
   rw [h i] at hi
   exact Nat.eq_zero_of_le_zero hi
 simp [hd0]
theorem positive_seed_degree_of_surface_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ F)=0):
   0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
 by_contra hn
 have hy:F.degreeOf 1 ≤ 0:=by omega
 have hr:F.degreeOf 2 ≤ 0:=by omega
 have hz:F.degreeOf 3 ≤ 0:=by omega
 have hc:=surfaceMap_separated_caps φ F 0 0 0 hy hr hz
 have hconst:surfaceMap φ F=MvPolynomial.C ((surfaceMap φ F).coeff 0):=by
   apply eq_C_of_all_degreeOf_zero
   intro i
   fin_cases i
   · exact Nat.eq_zero_of_le_zero hc.1
   · exact Nat.eq_zero_of_le_zero hc.2.1
   · exact Nat.eq_zero_of_le_zero hc.2.2
 have hvalue:=hzero
 rw [hconst,MvPolynomial.eval_C] at hvalue
 apply surfaceMap_ne_zero φ hφ F hF
 rw [hconst,hvalue,map_zero]
theorem exists_active_factor_of_surface_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
   ∃ F∈activeFactors Q,MvPolynomial.eval v (surfaceMap φ F)=0:=by
 classical
 obtain ⟨F,hmem,hz⟩:=exists_normalized_factor_of_map_zero
   ((MvPolynomial.eval v).comp (surfaceMap φ)) Q hQ hzero
 have hF:=ne_zero_of_mem_normalizedFactors hmem
 have hpos:=positive_seed_degree_of_surface_zero φ hφ F hF v hz
 exact ⟨F,Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem,hpos⟩,hz⟩
theorem activeFactors_product_dvd (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
   (∏ F∈activeFactors Q,F)∣Q:=by
 classical
 apply (Finset.prod_dvd_prod_of_subset (activeFactors Q)
   (normalizedFactors Q).toFinset id (Finset.filter_subset _ _)).trans
 exact (normalizedFactors Q).toFinset_prod_dvd_prod.trans (prod_normalizedFactors hQ).dvd
end
end ProximityPrize.SubmissionLower.RCN082
end PackedLegacy_J1

section PackedLegacy_BS
namespace ProximityPrize.SubmissionLower.RCN167
open RCN081 RCN082 RCN313 RCN136 RCN319 
noncomputable section
variable {K:Type*} [Field K]
theorem weighted_mul_le (weights:Fin 4 → ℕ) (P Q:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree weights (P*Q) ≤
     MvPolynomial.weightedTotalDegree weights P+MvPolynomial.weightedTotalDegree weights Q:=by
 rw [←degree_weightedLift,map_mul]
 simpa only [degree_weightedLift] using
   (MvPolynomial.degreeOf_mul_le (4:Fin 5) (weightedLift K weights P) (weightedLift K weights Q))
theorem weighted_add_le (weights:Fin 4 → ℕ) (P Q:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree weights (P+Q) ≤
     max (MvPolynomial.weightedTotalDegree weights P) (MvPolynomial.weightedTotalDegree weights Q):=by
 rw [←degree_weightedLift,map_add]
 simpa only [degree_weightedLift] using
   (MvPolynomial.degreeOf_add_le (4:Fin 5) (weightedLift K weights P) (weightedLift K weights Q))
theorem weighted_X (weights:Fin 4 → ℕ) (i:Fin 4):
   MvPolynomial.weightedTotalDegree weights (MvPolynomial.X i:MvPolynomial (Fin 4) K)=weights i:=by
 simp [MvPolynomial.weightedTotalDegree,MvPolynomial.support_X,Finsupp.weight_single]
theorem pderiv_weight_sub_bound (weights:Fin 4 → ℕ)
   (A:MvPolynomial (Fin 4) K) (i:Fin 4) (B:ℕ)
   (hA:MvPolynomial.weightedTotalDegree weights A ≤ B):
   MvPolynomial.weightedTotalDegree weights (MvPolynomial.pderiv i A) ≤ B-weights i:=by
 apply (weightedTotalDegree_le_iff weights _ _).mpr
 intro d hd
 have hh:=(MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i A d hd)).trans hA
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 omega
def positiveRFactors (F:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (activeFactors F).filter (fun G => 0 < G.degreeOf 2)
theorem positiveRFactors_spec (F G:MvPolynomial (Fin 4) K)
   (hG:G∈positiveRFactors F):Irreducible G∧G∣F∧0 < G.degreeOf 2:=by
 classical
 obtain ⟨hmem,hpos⟩:=Finset.mem_filter.mp hG
 have hh:=activeFactors_spec F G hmem
 exact ⟨hh.1,hh.2.1,hpos⟩
theorem positiveRFactors_product_dvd (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∏ G∈positiveRFactors F,G)∣F:=by
 classical
 exact (Finset.prod_dvd_prod_of_subset (positiveRFactors F) (activeFactors F) id
   (Finset.filter_subset _ _)).trans (activeFactors_product_dvd F hF)
section SurfacePoints
variable {T:Type*} [Field T]
end SurfacePoints
end
end ProximityPrize.SubmissionLower.RCN167
end PackedLegacy_BS

section PackedLegacy_AA
namespace ProximityPrize.SubmissionLower.RCN234
open scoped BigOperators
open RCN081 RCN167 RCN313
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def wt (weights:Fin 4 → ℕ) (P:Poly4 K):ℕ:=
 MvPolynomial.weightedTotalDegree weights P
theorem wt_mul_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P*Q) ≤ wt weights P+wt weights Q:=
 weighted_mul_le weights P Q
theorem wt_add_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P+Q) ≤ max (wt weights P) (wt weights Q):=
 weighted_add_le weights P Q
theorem wt_sub_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P-Q) ≤ max (wt weights P) (wt weights Q):=by
 unfold wt
 rw [←degree_weightedLift,map_sub]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_sub_le (4:Fin 5)
     (weightedLift K weights P) (weightedLift K weights Q)
theorem wt_neg (weights:Fin 4 → ℕ) (P:Poly4 K):
   wt weights (-P)=wt weights P:=by
 unfold wt
 rw [←degree_weightedLift,map_neg,MvPolynomial.degreeOf_neg,
   degree_weightedLift]
theorem wt_pow_le (weights:Fin 4 → ℕ) (P:Poly4 K) (n:ℕ):
   wt weights (P^n) ≤ n*wt weights P:=by
 unfold wt
 rw [←degree_weightedLift,map_pow]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_pow_le (4:Fin 5) (weightedLift K weights P) n
theorem wt_C (weights:Fin 4 → ℕ) (c:K):
   wt weights (MvPolynomial.C c:Poly4 K)=0:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp
theorem wt_X (weights:Fin 4 → ℕ) (i:Fin 4):
   wt weights (MvPolynomial.X i:Poly4 K)=weights i:=by
 unfold wt
 exact weighted_X weights i
theorem wt_natCast (weights:Fin 4 → ℕ) (n:ℕ):
   wt weights (n:Poly4 K)=0:=by
 rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K),wt_C]
theorem wt_sum_le (weights:Fin 4 → ℕ) (I:Finset ℕ)
   (f:ℕ → Poly4 K) (a:ℕ) (hf:∀ i∈I,wt weights (f i) ≤ a):
   wt weights (∑ i∈I,f i) ≤ a:=by
 unfold wt
 rw [←degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [degree_weightedLift]
 exact hf i hi
theorem wt_pderiv_le (weights:Fin 4 → ℕ) (P:Poly4 K)
   (i:Fin 4) (A:ℕ) (hP:wt weights P ≤ A):
   wt weights (MvPolynomial.pderiv i P) ≤ A-weights i:=
 pderiv_weight_sub_bound weights P i A hP
theorem wt_polyH_le (weights:Fin 4 → ℕ) (F:Poly4 K)
   (C:ℕ) (hF:wt weights F ≤ C):
   wt weights (polyH K F) ≤ C-weights 2:=
 wt_pderiv_le weights F 2 C hF
theorem wt_polyG_le (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hF:wt weights F ≤ C):
   wt weights (polyG K F) ≤ C+weights 2:=by
 have hx:=wt_pderiv_le weights F 0 C hF
 have hy:=wt_pderiv_le weights F 1 C hF
 have hR:wt weights (MvPolynomial.X (2:Fin 4):Poly4 K)=weights 2:=
   weighted_X weights 2
 have hm:=wt_mul_le weights (MvPolynomial.X (2:Fin 4):Poly4 K)
   (MvPolynomial.pderiv 1 F)
 have hsum:=wt_add_le weights (MvPolynomial.pderiv 0 F)
   (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv 1 F)
 unfold polyG
 rw [wt_neg]
 exact hsum.trans (max_le (by omega) (by omega))
theorem shiftedX_wt_eq_zero (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (x:K):
   wt weights (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)=0:=by
 apply Nat.eq_zero_of_le_zero
 apply (wt_sub_le weights _ _).trans
 rw [wt_C,wt_X,hX]
 simp
theorem affineSeedPolynomial_wt_le (weights:Fin 4 → ℕ) (u₀ u₁:K):
   wt weights (affineSeedPolynomial u₀ u₁) ≤ weights 3:=by
 unfold affineSeedPolynomial
 apply (wt_add_le weights _ _).trans
 apply max_le
 · rw [wt_C]
   exact Nat.zero_le _
 · have hm:=wt_mul_le weights (MvPolynomial.X (3:Fin 4):Poly4 K)
     (MvPolynomial.C u₁)
   rw [wt_X,wt_C,Nat.add_zero] at hm
   exact hm
end
end ProximityPrize.SubmissionLower.RCN234
end PackedLegacy_AA

section PackedLegacy_FO
namespace ProximityPrize.SubmissionLower.RCN235
open scoped BigOperators Matrix
open ProximityPrize.SubmissionLower.RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem wt_finset_sum_le {ι:Type*} [DecidableEq ι]
   (weights:Fin 4 → ℕ) (I:Finset ι) (f:ι → Poly4 K) (cap:ℕ)
   (hf:∀ i∈I,wt weights (f i) ≤ cap):
   wt weights (∑ i∈I,f i) ≤ cap:=by
 unfold wt
 rw [←RCN081.degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => RCN081.weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [RCN081.degree_weightedLift]
 exact hf i hi
end
end ProximityPrize.SubmissionLower.RCN235
end PackedLegacy_FO

section PackedLegacy_AH
namespace ProximityPrize.SubmissionLower.RCN295
open scoped Classical BigOperators WithZero
open RCN187
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
local instance:DecidableEq K:=Classical.decEq K
def exponentPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):ℤ:=
 ∑ i,(d i:ℤ)*poleOrder v (x i)
def exponentValuationWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):ℤ:=
 ∑ i,(d i:ℤ)*(v (x i)).log
def ExponentSetDownwardClosed (E:Finset (σ →₀ ℕ)):Prop:=
 ∀ d∈E,∀ e:σ →₀ ℕ,e ≤ d → e∈E
def exponentSetPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):ℤ:=
 (insert (0:ℤ) (E.image (exponentPoleWeight v x))).max'
   ⟨0,Finset.mem_insert_self (0:ℤ) _⟩
def supportPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):ℤ:=
 exponentSetPoleWeight v x F.support
theorem supportPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):
   0 ≤ supportPoleWeight v x F:=by
 unfold supportPoleWeight exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem exponentPoleWeight_le_supportPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K)
   (d:σ →₀ ℕ) (hd:d∈F.support):
   exponentPoleWeight v x d ≤ supportPoleWeight v x F:=by
 unfold supportPoleWeight exponentSetPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
theorem exponentSetPoleWeight_mono
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) {E D:Finset (σ →₀ ℕ)} (hED:E ⊆ D):
   exponentSetPoleWeight v x E ≤ exponentSetPoleWeight v x D:=by
 unfold exponentSetPoleWeight
 apply Finset.max'_le
 intro z hz
 obtain rfl | hz:=Finset.mem_insert.mp hz
 · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
 · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   apply Finset.le_max'
   exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hED hd,rfl⟩)
theorem supportPoleWeight_le_exponentSetPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K) (E:Finset (σ →₀ ℕ))
   (hFE:F.support ⊆ E):
   supportPoleWeight v x F ≤ exponentSetPoleWeight v x E:=
 exponentSetPoleWeight_mono v x hFE
theorem valuation_monomial_le_exp_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K)
   (d:σ →₀ ℕ) (hd:d∈F.support) (c:K):
   v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
     WithZero.exp (supportPoleWeight v x F):=by
 classical
 apply WithZero.le_exp_of_log_le
 calc
   (v (MvPolynomial.eval₂Hom coeff x
       (MvPolynomial.monomial d c))).log ≤
       poleOrder v (MvPolynomial.eval₂Hom coeff x
         (MvPolynomial.monomial d c)):=
     le_max_right _ _
   _ ≤ exponentPoleWeight v x d:=by
     by_cases hc:c=0
     · subst c
       simp [exponentPoleWeight,poleOrder]
       positivity
     · have hmono:=poleOrder_eval_le_box v coeff hcoeff x
         (fun i↦d i) (MvPolynomial.monomial d c) (fun i↦by
           rw [MvPolynomial.degreeOf_monomial_eq d i hc])
       simpa only [exponentPoleWeight] using hmono
   _ ≤ supportPoleWeight v x F:=
     exponentPoleWeight_le_supportPoleWeight v x F d hd
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

section PackedLegacy_BO
namespace ProximityPrize.SubmissionLower.RCN156
open scoped Classical BigOperators
open RCN234 RCN235 RCN136 RCN313
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
def residualSWeights:Fin 4 → ℕ:=![0,0,1,0]
def residualYSWeights:Fin 4 → ℕ:=![0,1,1,0]
def residualTotalWeights:Fin 4 → ℕ:=![0,1,1,1]
end
end ProximityPrize.SubmissionLower.RCN156
end PackedLegacy_BO

section PackedLegacy_CH
namespace ProximityPrize.SubmissionLower.RCN324
open IsLocalRing
variable {K R:Type*} [CommRing K] [CommRing R] [Algebra K R]
private theorem prime_dvd_factorial:∀ {n p:ℕ},p.Prime → (p∣n.factorial ↔ p ≤ n)
 | 0,_,hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
 | n+1,p,hp => by
     rw [Nat.factorial_succ,hp.dvd_mul,prime_dvd_factorial hp]
     exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
       fun h => (_root_.lt_or_eq_of_le h).elim
         (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩
theorem derivation_pow_mul (D:Derivation K R R) (pi u:R) (mu:ℕ)
   (hmu:1 ≤ mu):
   D (pi^mu*u)=
     pi^(mu-1)*((mu:R)*u*D pi+pi*D u):=by
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_pow_mul (D:Derivation K R R) (pi u a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a):
   D (pi^mu*u)=pi^mu*((mu:R)*a*u+D u):=by
 rw [derivation_pow_mul D pi u mu hmu,htangent]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_preserves_divisibility (D:Derivation K R R) (pi a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a) (f:R) (hf:pi^mu∣f):
   pi^mu∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [tangent_pow_mul D pi u a mu hmu htangent]
 exact dvd_mul_right _ _
theorem iterate_pow_mul_expansion (D:Derivation K R R) (pi u:R)
   (mu r:ℕ) (hr:r ≤ mu):
   ∃ error:R,
     (D:R → R)^[r] (pi^mu*u)=
       (mu.descFactorial r:R)*pi^(mu-r)*u*(D pi)^r+
         pi^(mu-r+1)*error:=by
 induction r with
 | zero =>
     refine ⟨0,?_⟩
     simp
 | succ r ih =>
     have hr0:r ≤ mu:=le_trans (Nat.le_succ r) hr
     obtain ⟨error,herror⟩:=ih hr0
     obtain ⟨k,hk⟩:∃ k,mu-r=k+1:=by
       have hpos:0 < mu-r:=Nat.sub_pos_of_lt (Nat.lt_of_succ_le hr)
       exact Nat.exists_eq_succ_of_ne_zero hpos.ne'
     have hnext:mu-(r+1)=k:=by omega
     let q:=D pi
     let nextError:R:=
       (mu.descFactorial r:R)*D u*q^r+
       (mu.descFactorial r:R)*u*(r:R)*q^(r-1)*D q+
       (k+2:R)*q*error+pi*D error
     refine ⟨nextError,?_⟩
     rw [Function.iterate_succ_apply',herror,map_add]
     simp only [D.leibniz,Derivation.leibniz_pow,D.map_natCast,
       nsmul_eq_mul,smul_eq_mul]
     rw [hk,hnext,Nat.descFactorial_succ]
     have hmur:mu-r=k+1:=hk
     push_cast [hmur]
     dsimp only [q,nextError]
     ring
theorem isUnit_add_of_isUnit_of_not_isUnit [IsLocalRing R]
   {a b:R} (ha:IsUnit a) (hb:¬ IsUnit b):IsUnit (a+b):=by
 by_contra hab
 have hnb:¬ IsUnit (-b):=by simpa using hb
 have hs:=IsLocalRing.nonunits_add hab hnb
 apply hs
 simpa [add_assoc] using ha
section DVR
variable [IsDomain R] [IsDiscreteValuationRing R]
theorem addVal_iterate_eq_sub_of_transverse
   (D:Derivation K R R) (pi u:R) (mu r p:ℕ)
   [CharP R p] (hp:p.Prime) (hmu:mu < p) (hr:r ≤ mu)
   (hpi:Irreducible pi) (hu:IsUnit u) (htrans:IsUnit (D pi)):
   IsDiscreteValuationRing.addVal R ((D:R → R)^[r] (pi^mu*u))=mu-r:=by
 obtain ⟨error,herror⟩:=iterate_pow_mul_expansion D pi u mu r hr
 have hdescDvd:mu.descFactorial r∣mu.factorial:=by
   refine ⟨(mu-r).factorial,?_⟩
   rw [mul_comm,Nat.factorial_mul_descFactorial hr]
 have hnot:¬p∣mu.descFactorial r:=by
   intro hd
   have hpf:p∣mu.factorial:=hd.trans hdescDvd
   rw [prime_dvd_factorial hp] at hpf
   omega
 have hc:IsUnit (mu.descFactorial r:R):=
   (CharP.isUnit_natCast_iff hp).2 hnot
 have hlead:IsUnit ((mu.descFactorial r:R)*u*(D pi)^r):=
   (hc.mul hu).mul (htrans.pow r)
 let lead:R:=(mu.descFactorial r:R)*u*(D pi)^r
 have hpiError:¬IsUnit (pi*error):=
   not_isUnit_of_not_isUnit_dvd hpi.not_isUnit (dvd_mul_right pi error)
 have hbracket:IsUnit (lead+pi*error):=
   isUnit_add_of_isUnit_of_not_isUnit hlead hpiError
 have hfactor:
     (D:R → R)^[r] (pi^mu*u)=pi^(mu-r)*(lead+pi*error):=by
   rw [herror]
   simp only [lead]
   ring
 rw [hfactor,IsDiscreteValuationRing.addVal_mul,
   IsDiscreteValuationRing.addVal_pow,
   IsDiscreteValuationRing.addVal_uniformizer hpi,
   IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hbracket]
 simp
end DVR
theorem isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one
   [IsDomain R] [IsRegularLocalRing R] (hdim:ringKrullDim R=1):
   IsDiscreteValuationRing R:=by
 have hfin':=(IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
   (inferInstance:IsRegularLocalRing R)
 rw [hdim] at hfin'
 have hfin:Module.finrank (ResidueField R) (CotangentSpace R)=1:=by
   exact_mod_cast hfin'
 exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfin
end ProximityPrize.SubmissionLower.RCN324
end PackedLegacy_CH

