import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Z8
namespace ProximityPrize.SubmissionLower.RCN086
open scoped Classical BigOperators
open RCN313 RCN136 RCN238
open RCN053 RCN054
open RCN095 RCN207
open RCN234
open RCN198
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 35000
variable {K Ω:Type} [Field K] [Field Ω]
def tailSelector (d j:ℕ):K:=if j=d then 1 else 0
theorem selected_term_identity (F:MvPolynomial (Fin 4) K) (d:ℕ):
   agreementNumerator F d (tailSelector d) 0 0 0=
     numerator K F d*(-MvPolynomial.X (0:Fin 4))^d:=by
 classical
 unfold agreementNumerator clearedTaylorNumerator
 rw [Finset.sum_eq_single d]
 · simp [commonNumeratorTerm,tailSelector,affineSeedPolynomial]
 · intro j _ hj
   simp [commonNumeratorTerm,tailSelector,hj]
 · intro hd
   exact (hd (Finset.mem_range.mpr (Nat.lt_succ_self d))).elim
def globalTailCut (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (d:ℕ):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (agreementNumerator F d (tailSelector d) 0 0 0)
theorem globalTailCut_eq (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (d:ℕ):
   globalTailCut φ F d=
     surfaceMap φ (numerator K F d)*MvPolynomial.C ((-φ Polynomial.X)^d):=by
 simp [globalTailCut,selected_term_identity,map_mul,map_pow,map_neg]
theorem tail_scalar_ne_zero (φ:Polynomial K →+*Ω)
   (hφ:Function.Injective φ) (d:ℕ):(-φ Polynomial.X)^d≠0:=by
 apply pow_ne_zero
 apply neg_ne_zero.mpr
 intro h
 have hX:(Polynomial.X:Polynomial K)=0:=hφ (by simpa using h)
 exact Polynomial.X_ne_zero hX
theorem globalTailCut_dvd_iff (φ:Polynomial K →+*Ω)
   (hφ:Function.Injective φ) (F:MvPolynomial (Fin 4) K) (d:ℕ)
   (G:MvPolynomial (Fin 3) Ω):
   G∣globalTailCut φ F d ↔ G∣surfaceMap φ (numerator K F d):=by
 rw [globalTailCut_eq]
 let c:Ω:=(-φ Polynomial.X)^d
 have hc:c≠0:=tail_scalar_ne_zero φ hφ d
 constructor
 · intro h
   have hh:=h.mul_right (MvPolynomial.C c⁻¹)
   simpa only [c,mul_assoc, ←map_mul,mul_inv_cancel₀ hc,map_one,mul_one] using hh
 · intro h
   exact h.mul_right _
theorem selected_globalTailCut_zero (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (selectedPoint φ selected γ) (globalTailCut φ F (w+1))=0:=by
 rw [globalTailCut_eq,map_mul]
 have hzero:=RCN068.selected_firstTail_zero φ F selected γ w hdegree hsolution
 change MvPolynomial.aeval _ (surfaceMap φ (numerator K F (w+1)))=0 at hzero
 rw [hzero,zero_mul]
theorem globalTailCut_in_sharp_flag (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3) (d:ℕ):
   PolynomialInFlag
     (RCN287.sharpResidualAgreementFlag (support a b s) d)
     (globalTailCut φ F d):=by
 exact RCN287.surfaceMap_agreement_in_sharp_flag
   (P:=support a b s) (by change s+2 < b+s+3;omega) φ
   (support_data a b s F hR hYR hAll) d (tailSelector d) 0 0 0
theorem exists_filtered_certificate (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3)
   (d:ℕ) (hd:2 ≤ d) (coeffs:ℕ → K) (x u0 u1:K):
   ∃ (B:Fin (d-1+1) → MvPolynomial (Fin 3) Ω)
     (c:Fin (d-1+1) → FlagDegree),
     surfaceMap φ (agreementNumerator F d coeffs x u0 u1)=
       filteredCut (d-1) B (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F))∧
     (∀ j,PolynomialInFlag (c j) (B j))∧
     (∀ j,c j+(d-1-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
       j.val • (⟨a,b,s+3⟩:FlagDegree)=center a b s+(d-1) • direction a b s):=by
 classical
 let B0:=fun j => surfaceMap φ (agreementCoefficients F d coeffs x u0 u1 j)
 refine ⟨(fun j => B0 j.val),(fun j => coefficientFlag a (b+1) (s+2) d j.val),?_,?_,?_⟩
 · rw [surfaceMap_agreementNumerator_eq_coefficient_sum φ F d hd]
   have hk:d-1+1=d:=by omega
   calc
     _=∑ j:Fin (d-1+1),surfaceMap φ (polyH K F)^(d-1-j.val)*
         surfaceMap φ (polyG K F)^j.val*B0 j.val:=by
       let f:=fun j:ℕ => surfaceMap φ (polyH K F)^(d-1-j)*
         surfaceMap φ (polyG K F)^j*B0 j
       change (∑ j∈Finset.range d,f j)=∑ j:Fin (d-1+1),f j.val
       rw [Finset.sum_range]
       let E:Fin d ≃ Fin (d-1+1):={
         toFun:=fun j => ⟨j.val,by have:=j.isLt;omega⟩
         invFun:=fun j => ⟨j.val,by have:=j.isLt;omega⟩
         left_inv:=fun j => rfl
         right_inv:=fun j => rfl}
       exact Fintype.sum_equiv E _ _ (fun _ => rfl)
     _=_:=by
       unfold filteredCut
       apply Finset.sum_congr rfl
       intro j _
       ring
 · intro j
   apply surfaceMap_agreementCoefficients_in_flag φ F a (b+1) (s+2)
     (by omega) (by omega) hR (by omega) (by omega) d hd coeffs x u0 u1 j.val
   have:=j.isLt
   omega
 · intro j
   have hj:j.val<d:=by have:=j.isLt;omega
   have h:=coefficientFlag_add_baseMonomial a (b+1) (s+2) d j.val
     (by omega) (by omega) hj
   rw [(shifted_flags a b s).1,(shifted_flags a b s).2.1,
     (shifted_flags a b s).2.2] at h
   refine h.trans ?_
   have hk:d-1+1=d:=by omega
   simpa only [hk] using class_total a b s (d-1)
theorem globalTailCut_certificate (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3)
   (w:ℕ) (hw:1 ≤ w):
   ∃ (B:Fin (w+1) → MvPolynomial (Fin 3) Ω)
     (c:Fin (w+1) → FlagDegree),
     globalTailCut φ F (w+1)=
       filteredCut w B (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F))∧
     (∀ j,PolynomialInFlag (c j) (B j))∧
     (∀ j,c j+(w-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
       j.val • (⟨a,b,s+3⟩:FlagDegree)=center a b s+w • direction a b s):=by
 have h:=exists_filtered_certificate φ a b s F hR hYR hAll (w+1) (by omega)
   (tailSelector (w+1)) 0 0 0
 rw [show w+1-1=w by omega] at h
 exact h
end
end ProximityPrize.SubmissionLower.RCN086
