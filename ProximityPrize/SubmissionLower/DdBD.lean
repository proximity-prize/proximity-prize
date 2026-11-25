import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank
import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator
import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
import ArkLib.Data.MvPolynomial.RadicalSplit.Separable
import ArkLib.Data.MvPolynomial.WeightedDegree.Products
import ArkLib.Data.Polynomial.Differential.OrderZeroPresentation
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.Data.Int.Star
import ProximityPrize.SubmissionLower.DdBC
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming AddMonoidAlgebra.mapDomain → zTd, AddMonoidAlgebra.mapDomainRingHom → zXo, AlgEquiv.apply_symm_apply → zIH, AlgEquiv.trans_apply → zfq, CommRing → za6, CoreDefinitions.AffineLineGenerator → z7S, DecidableEq → zRw, Field → zrb, Fin.last → zym, Fin.sum_univ_succ → zCS, Finset → zJe, Finset.card_erase_add_one → z0k, Finset.card_image_of_injective → ze7, Finset.exists_subset_card_eq → zo4, Finset.mem_univ → zTc, Finset.mul_sum → zxw, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sup_le → zf9, Finset.univ → zdB, Finsupp.sum_fintype → z9d, Finsupp.weight → ztN, Finsupp.weight_apply → zDM, Finsupp.weight_optionElim → zVB, Finsupp.weight_single → zTy, Fintype → z85, Fintype.card → zhP, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.annihilator_quotient → zsb, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_left → zKg, Ideal.mem_sup_right → zs0, Ideal.mul_mem_mul → zgK, Ideal.mul_mono → zIS, Ideal.ofList → zGX, Ideal.ofList_cons → z2L, Ideal.pow_mem_pow → z2s, Ideal.radical_mono → zks, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, Ideal.span_singleton_pow → zNi, IsAssociatedPrime → zOA, IsLocalRing → znQ, IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal → zq3
open _root_ renaming IsLocalRing.maximalIdeal → zrY, IsLocalRing.maximalIdeal.isMaximal → zHl, IsLocalRing.mem_maximalIdeal → z0F, IsNoetherian.noetherian → zLU, IsSMulRegular → ziO, LinearMap.finrank_range_of_inj → z0K, LinearMap.ker → z83, LinearMap.range → zWl, List.mem_cons_of_mem → zrw, List.perm_append_comm → ztt, Matrix → z30, Matrix.det_transpose → zgP, Matrix.fromCols → zE7, Matrix.fromCols_mulVec → zIR, Matrix.map_apply → zAg, Matrix.mulVec → zeQ, Matrix.mulVec_mulVec → zbx, Matrix.mulVec_zero → zvf, Module.Finite → zAa, Module.annihilator → zM1, Module.card_eq_pow_finrank → zbA, Module.finrank → zsE, Module.length → zKQ, ModuleCat.of → zbv, MvPolynomial → z3y, MvPolynomial.C_mem_restrictWeightedDegree → zzE, MvPolynomial.X → z9v, MvPolynomial.X_mem_restrictWeightedDegree → zCH, MvPolynomial.aeval → zIe, MvPolynomial.coeff_weightedTruncation → zjG, MvPolynomial.finSuccEquiv → z8s, MvPolynomial.induction_on → z5i, MvPolynomial.le_weightedTotalDegree → z6P, MvPolynomial.mem_restrictSupport_iff → zUj, MvPolynomial.mem_support_coeff_optionEquivLeft → zVT, MvPolynomial.mul_mem_restrictWeightedDegree → zD1, MvPolynomial.natDegree_optionEquivLeft → zgM, MvPolynomial.optionEquivLeft → zpj, MvPolynomial.ordinaryRootPolynomial → zrL, MvPolynomial.radicalContent → zXw, MvPolynomial.radicalPrimPart → zhc, MvPolynomial.renameEquiv → zGY, MvPolynomial.renameEquiv_apply → zyk, MvPolynomial.restrictCappedDegree → zVE, MvPolynomial.restrictWeightedDegree → zAp, MvPolynomial.restrictWeightedOrder → zlK, MvPolynomial.uniqueAlgEquiv → zpe, MvPolynomial.weightedTotalDegree → zXg
open _root_ renaming MvPolynomial.weightedTotalDegree_aeval_le_of_le → zZ0, MvPolynomial.weightedTotalDegree_mul → zmN, MvPolynomial.weightedTotalDegree_mul_le → zku, MvPolynomial.weightedTotalDegree_pow_le → zvm, MvPolynomial.weightedTotalDegree_rename_of_injective → z8E, MvPolynomial.weightedTruncation → za1, Nat.add_comm → zg2, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.exists_eq_add_of_le → zWX, Nat.mul_le_mul_left → zBI, Nat.sub_add_cancel → zxt, Nat.sub_le_sub_right → zIu, Nat.zero_le → zD0, Option → zNO, Pi.single → znV, Pi.single_apply → zOw, Pi.smul_apply → zD4, Pi.zero_apply → zbd, Polynomial → zM2, Polynomial.C → z1z, Polynomial.C_mul_X_pow_eq_monomial → zoT, Polynomial.X → z7y, Polynomial.coeff_map → z0b, Polynomial.coeff_monomial → zQm, Polynomial.coeff_smul → zmM, Polynomial.degreeLT → z3F, Polynomial.degreeLTEquiv → zAj, Polynomial.eq_C_of_natDegree_eq_zero → zr7, Polynomial.evalRingHom → zhy, Polynomial.eval₂ → zmH, Polynomial.eval₂_C → zJU, Polynomial.eval₂_mul → zxy, Polynomial.finsetSum_coeff → zaW, Polynomial.hasseDeriv → z75, Polynomial.le_natTrailingDegree → zKd, Polynomial.map_mul → zNl, Polynomial.map_pow → z5m, Polynomial.monomial → zdM, Polynomial.natDegree_mul → zNh, Polynomial.natDegree_sum_le_of_forall_le → zMZ, Polynomial.natTrailingDegree_le_of_ne_zero → zxD, Polynomial.resultant → zSp, Polynomial.smul_eq_C_mul → zQI, PolynomialDifferential.DifferentialPolynomial → zQp, PolynomialDifferential.JetVariable → zxV, PolynomialDifferential.differentialSpecialization → zho, PolynomialDifferential.differentialSpecializationHom → zfh
open _root_ renaming PolynomialDifferential.initialJetSeparant → zZ9, PolynomialDifferential.jetDegree → zJP, PolynomialDifferential.jetDegreeWeight → zb7, PolynomialDifferential.jetTotalDegree → zTv, PolynomialDifferential.orderZeroAsPolynomial → zMP, PolynomialDifferential.rationalTaylorNumerator → zm0, PolynomialDifferential.universalTaylorResidual → zgz, ReedSolomon.HiddenDerivative.globalPointTranslation → zh6, ReedSolomon.HiddenDerivative.unscaledLocalSubstitution → zxm, Semiring → z0Y, Set.mem_singleton_iff → zpV, Submodule → zpI, Submodule.add_mem → zcy, Submodule.finrank_lt → zYs, Subsingleton → zOt, Subtype.ext → zkt, Sum.inr → znU, add_sub_cancel_right → zY6, associatedPrimes → zMd, associatedPrimes.finite → zrB, biUnion_associatedPrimes_eq_compl_regular → zC8, congrArg → zPw, congrFun → zTC, dotProduct → zKe, if_pos → z3d, le_antisymm → zWs, le_rfl → zs1, le_sup_left → zPQ, le_sup_right → ztJ, map_add → zrl, map_mul → zok, map_sum → zdo, map_zero → zhd, mul_assoc → ztg, mul_comm → zDE, mul_left_cancel₀ → zyS, mul_one → zqe, mul_smul_comm → zGx, one_mul → zkF, pow_succ' → zdG, ringChar → zUy, smul_eq_mul → zs5, sup_le → zbX, zero_add → zOP
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F row:Type*} [zrb F] [z85 row]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {R S row col:Type*} [za6 R] [za6 S] [z85 col]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {K:Type*} [zrb K]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {R row:Type*} [za6 R]
variable {K:Type*} [zrb K]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {K:Type*} [zrb K]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {K:Type*} [zrb K]
variable {F ι:Type} [zrb F] [z85 ι] [zRw ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F ι:Type*} [zrb F] [z85 ι] [zRw ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace bz5
open Polynomial Matrix Finset
open gR
open scoped BigOperators
variable {E :Type*} [zrb E] {r s :ℕ}
variable {F:Type*} [zrb F]
end bz5
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K row col:Type*} [zrb F] [zrb K] [z85 col] [zRw col]
end
end gR.Principal
end
section
namespace ana
noncomputable section
open MvPolynomial
open scoped BigOperators
theorem aVQ {F:Type*} [zrb F] (g:z3y (Fin 2) F) {j r :ℕ}
  (hj:g.totalDegree≤j) (hr :g.degreeOf 1≤ r) :
  g∈zVE (Fin 2) F 1 j r := by
 intro m hm
 exact ⟨(le_totalDegree hm).trans hj,(monomial_le_degreeOf 1 hm).trans hr⟩
end
end ana
end
section
namespace bzO
open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R:Type u} [za6 R] [IsNoetherianRing R] [znQ R]
end bzO
end
section
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial
variable {F σ:Type*} [zrb F]
def a2U (v :σ→ℕ) : (σ →₀ ℕ) →+ (zNO σ →₀ ℕ) where
 toFun e :=e.optionElim (e.weight v)
 map_zero' := by ext i; cases i <;> simp
 map_add' e f := by ext i; cases i <;> simp
end
end wT
end
section
namespace yP.Xf
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def aks (d:ℕ) :zxV (d+1) ≃ zNO (zxV d) :=
 (Equiv.optionCongr (finSuccEquiv' (zym (d+1)))).trans (Equiv.swap none (some none))
@[simp] theorem gRW (d:ℕ) :aks d none=some none := by
  simp [aks]
@[simp] theorem bO5 (d:ℕ) :
   aks d (some (zym (d+1)))=none := by
  simp [aks]
@[simp] theorem gRV (d:ℕ) (j:Fin (d+1)) :
   aks d (some j.castSucc)=some (some j) := by
  have hj:j.castSucc<zym (d+1) :=Fin.castSucc_lt_last j
  simp [aks,finSuccEquiv'_below hj,Equiv.swap_apply_def]
variable {E :Type*} [za6 E]
def HC (d:ℕ) :zQp E (d+1) ≃ₐ[E]
    z3y (zNO (zxV d)) E :=zGY E (aks d)
def Wz (d:ℕ) :zQp E (d+1) ≃ₐ[E]
    zM2 (zQp E d) :=
  (HC d).trans (zpj E (zxV d))
def a7V (d:ℕ) :zNO (zxV d)→ℕ:= fun v ↦ v.elim 1 zb7
theorem dhx (d:ℕ) (Q:zQp E (d+1)) :
   (HC d Q).weightedTotalDegree (a7V d)=zTv Q:= by
 rw [HC,zyk,z8E
   (aks d).injective,zTv]
 congr 1
 funext v
 rcases v with _ | j
 · simp [a7V,zb7]
 · induction j using Fin.lastCases with
   | last=>simp [a7V,jetDegreeWeight]
   | cast j=>simp [a7V,jetDegreeWeight]
theorem ctM (d:ℕ) (Q:zQp E (d+1)) :
  degreeOf none (HC d Q)=zJP Q (zym (d+1)) := by
 have h:=degreeOf_rename_of_injective (p:= Q) (aks d).injective
  (some (zym (d+1)))
 simpa only [HC,zyk,bO5,zJP] using h
theorem ctL (d:ℕ) (Q:zQp E (d+1)) :
  (Wz d Q).natDegree=zJP Q (zym (d+1)) := by
 rw [Wz,zfq,zgM,ctM]
theorem gCb (d:ℕ) (Q:zQp E (d+1)) :
  pderiv none (HC d Q)=HC d (separant Q (zym (d+1))) := by
 have h:=pderiv_rename (aks d).injective (some (zym (d+1))) Q
 simpa only [HC,zyk,bO5,separant] using h
theorem dhw (d:ℕ) (Q:zQp E (d+1)) :
  (Wz d Q).derivative=Wz d (separant Q (zym (d+1))) := by
 change (zpj E (zxV d) (HC d Q)).derivative= _
 rw [← optionEquivLeft_pderiv_none,gCb]
 rfl
theorem dME {σ:Type*} (w:σ→ℕ)
  (Q:z3y (zNO σ) E) (i:ℕ) (hi:i≤degreeOf none Q) :
  i+((zpj E σ Q).coeff i).weightedTotalDegree w ≤
    Q.weightedTotalDegree (fun v ↦ v.elim 1 w) := by
 classical
 have hiB:i≤Q.weightedTotalDegree (fun v ↦ v.elim 1 w) :=
  hi.trans (degreeOf_le_weightedTotalDegree _ none (by simp) Q)
 have hh: ((zpj E σ Q).coeff i).weightedTotalDegree w ≤
    Q.weightedTotalDegree (fun v ↦ v.elim 1 w) - i:= by
  apply Finset.sup_le_iff.mpr
  intro u hu
  have hs :=(zVT E).mp hu
  have hw:=z6P (fun v :zNO σ ↦ v.elim 1 w) hs
  rw [zVB,zkF] at hw
  omega
 omega
theorem bxT (d:ℕ) (Q:zQp E (d+1)) (P:(Polynomial E)) :
    (Wz d Q).eval₂ (zfh (d:=d) P).toRingHom
      (z75 (d+1) P)=zho Q P:= by
  induction Q using z5i with
  | C a=>simp [Wz,HC,differentialSpecialization_C]
  | add Q R hQ hR =>
    simp only [zrl,Polynomial.eval₂_add,zho,
      zrl,hQ,hR]
  | mul_X Q v hQ =>
    have hv : (Wz d (z9v v)).eval₂
        (zfh (d:=d) P).toRingHom
        (z75 (d+1) P) =
        zho (z9v v) P:= by
      rcases v with _ | j
      · simp [Wz,HC]
      · induction j using Fin.lastCases with
        | last=>simp [Wz,HC]
        | cast j=>simp [Wz,HC]
    simp only [zok,zxy,zho,
      zok,hQ,hv]
end
end yP.Xf
end
section
namespace yP.Xf
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E :Type*} [zrb E]
def Pe (d:ℕ) (Q:zQp E (d+1)) :
    zQp E (d+1) :=
  (HC d).symm (zhc none (HC d Q))
def avu (d:ℕ) (Q:zQp E (d+1)) :zQp E d :=
 (zpj E (zxV d) (zXw none (HC d Q))).coeff 0
theorem bYI (d:ℕ) (Q:zQp E (d+1)) :
   zpj E (zxV d) (zXw none (HC d Q)) =
     z1z (avu d Q) := by
 apply zr7
 rw [zgM,degreeOf_radicalContent]
theorem eGO {σ:Type*} (T:z3y σ E) :
   zpj E σ (rename some T)=z1z T:= by
 induction T using z5i with
 | C a=>simp
 | add p q hp hq=>simp [hp,hq]
 | mul_X p j hp=>simp [hp]
theorem dPv (d:ℕ) (Q:zQp E (d+1)) :
  zXw none (HC d Q)=rename some (avu d Q) := by
 apply (zpj E (zxV d)).injective
 rw [bYI,eGO]
theorem dPx (d:ℕ) (Q:zQp E (d+1)) :
   (zXw none (HC d Q)).weightedTotalDegree (a7V d) =
     zTv (avu d Q) := by
 rw [dPv,z8E (Option.some_injective (zxV d))]
 rfl
theorem c7Y (d:ℕ) (Q:zQp E (d+1)) :
  (zhc none (HC d Q)).weightedTotalDegree (a7V d) =
    zTv (Pe d Q) := by
 have h:=dhx d (Pe d Q)
 simpa only [Pe,zIH] using h
theorem dfk (d:ℕ) (Q:zQp E (d+1)) :
  zTv (avu d Q)+jetTotalDegree (Pe d Q)≤zTv Q:= by
 have h:=map_radicalContent_add_map_radicalPrimPart_le
  (d:= fun T ↦ T.weightedTotalDegree (a7V d))
  (fun x y hx hy ↦ zmN _ x y hx hy) none (HC d Q)
 rwa [dPx,c7Y,dhx] at h
theorem cY6 (d:ℕ) (Q:zQp E (d+1)) :
  avu d Q≠0:= by
 intro hz
 have h:=bYI d Q
 rw [hz,Polynomial.C_0] at h
 apply radicalContent_ne_zero none (HC d Q)
 apply (zpj E (zxV d)).injective
 simpa only [zhd] using h
theorem ce0 (d:ℕ) (Q:zQp E (d+1)) :
  Wz d (Pe d Q)=zrL (HC d Q) := by
 simp [Wz,Pe,zrL]
def cfy (d:ℕ) (P:(Polynomial E)) :
    z3y (zNO (zxV d)) E →+* (Polynomial E) :=
  (zfh (d:=d+1) P).toRingHom.comp (HC d).symm.toRingHom
theorem fXP (d:ℕ) (Q:zQp E (d+1)) (P:(Polynomial E)) :
    cfy d P (zXw none (HC d Q)) =
      zho (avu d Q) P:= by
  have h:=bxT d
    ((HC d).symm (zXw none (HC d Q))) P
  rw [show Wz d ((HC d).symm (zXw none (HC d Q))) =
      z1z (avu d Q) by
        simp only [Wz,zfq,zIH,
          bYI]] at h
  change zho
    ((HC d).symm (zXw none (HC d Q))) P= _
  simpa only [zJU,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,zho] using h.symm
theorem c8V (d:ℕ) (Q:zQp E (d+1)) (hQ:Q≠0) (P:(Polynomial E))
   (hroot :zho Q P=0) :
   zho (avu d Q) P=0 ∨
     zho (Pe d Q) P=0:= by
 have hQr :HC d Q≠0 :=
   (map_ne_zero_iff (HC d) (HC d).injective).mpr hQ
 have hz :=(map_radicalContent_mul_radicalPrimPart_eq_zero_iff
   (cfy d P) none hQr).mpr (by simpa [cfy] using hroot)
 rw [zok,fXP,mul_eq_zero] at hz
 exact hz
theorem fVD (d:ℕ) (Q:zQp E (d+1))
   (hdeg:zJP (Pe d Q) (zym (d+1))=0) :
   Pe d Q=1 := by
 have hd:degreeOf none (zhc none (HC d Q))=0:= by
   simpa only [Pe,zIH] using
     (ctM d (Pe d Q)).trans hdeg
 rw [Pe,radicalPrimPart_eq_one_of_degreeOf_eq_zero none _ hd,map_one]
def bhl (d:ℕ) (Q:zQp E (d+1)) :zQp E d :=
 let f :=zrL (HC d Q)
 zSp f f.derivative f.natDegree (f.natDegree - 1)
theorem grf (d:ℕ) (Q:zQp E (d+1))
  (hchar :zUy E=0∨zJP Q (zym (d+1))< zUy E) :
  bhl d Q≠0:= by
 apply Polynomial.resultant_derivative_ne_zero_ordinaryRootPolynomial
 rwa [ctM]
end
end yP.Xf
end
section
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial
variable {F σ ι:Type*} [zrb F]
end
end wT
end
section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open Finset MvPolynomial
end
end wT
end
section
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open Finset MvPolynomial
variable {F σ:Type*} [zrb F]
end
end wT
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial
variable {F:Type*} [zrb F]
end
end wT
end
section
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial Finset
variable {F:Type*} [zrb F]
end
end wT
end
section
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial
variable {F:Type*} [zrb F]
end
end wT
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial Polynomial
variable {F:Type*} [zrb F]
end
end wT
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial Finset
variable {F:Type*} [zrb F]
theorem aHG {ι:Type*} (S:zJe ι) (x :ι→F)
   (hx :zq4 x) (m:ℕ) (Q:zM2 F)
   (hcontact : ∀ i∈S,(z7y-Polynomial.C (x i))^m∣Q)
   (hdeg:Q.natDegree<m*S.card) :Q=0:= by
 classical
 by_contra hQ
 have hp: (∏ i∈S,(z7y-Polynomial.C (x i))^m)∣Q:= by
   apply Finset.prod_dvd_of_coprime
   · intro i hi j hj hij
     exact (Polynomial.pairwise_coprime_X_sub_C hx hij).pow
   · exact hcontact
 have hd:=Polynomial.natDegree_le_of_dvd hp hQ
 have hne : ∀ i∈S,(z7y-Polynomial.C (x i))^m≠0:= by
   intro i hi
   exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
 rw [Polynomial.natDegree_prod _ _ hne] at hd
 simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,Nat.mul_one,
   Finset.sum_const,zs5] at hd
 nlinarith
end
end wT
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
namespace wT
noncomputable section
open MvPolynomial
variable {F:Type*} [zrb F]
end
end wT
end
section
namespace amZ
open MvPolynomial PolynomialDifferential
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000
def kO (a b n:ℕ) :zNO (Fin n)→ℕ :=
 fun i=>i.elim 0 (fun j=>a+b*j.val)
def U6 (a b n:ℕ) :Fin n→ℕ:= fun j=>a+b*j.val
def aUb (b n:ℕ) :zNO (Fin n)→ℕ :=
 fun i=>i.elim b (fun _=>0)
variable {F:Type*}
section Semiring
variable [CommSemiring F]
theorem cuu (a b K j:ℕ) :
  SupportWeightOffset (ztN (kO a b K))
   (ztN (aUb b K)) (a+b*j)
   (universalTaylorJet (F:=F) K j) := by
 classical
 apply SupportWeightOffset.sum
 intro l hl
 apply SupportWeightOffset.monomial
 have hj:=(Finset.mem_filter.mp hl).2
 simp only [zrl,zTy,zs5,
  kO,aUb,Option.elim_some,Option.elim_none,
  mul_zero,zOP,zkF,add_zero]
 have hsub:l.val - j+j=l.val :=zxt hj
 nlinarith
theorem gG4 {r :ℕ} (a b K:ℕ) (center :F)
   (Q:zQp F r) :
   SupportWeightOffset (ztN (kO a b K))
     (ztN (aUb b K))
     (Q.weightedTotalDegree (kO a b (r+1)))
     (zgz K center Q) := by
 apply supportWeightOffset_aeval
 intro i
 cases i with
 | none =>
   apply SupportWeightOffset.add
   · exact SupportWeightOffset.C center
   · apply SupportWeightOffset.monomial
     simp [kO,aUb,zTy]
 | some j=>exact cuu a b K j.val
theorem cfh {r :ℕ} (a b K:ℕ) (center :F)
  (Q:zQp F r) (h:ℕ) (m:Fin K →₀ ℕ)
  (hm:m∈((zpj F (Fin K)
    (zgz K center Q)).coeff h).support) :
  ztN (U6 a b K) m ≤
    b*h+Q.weightedTotalDegree (kO a b (r+1)) := by
 have hb:=gG4 a b K center Q (m.optionElim h)
  ((zVT F).mp hm)
 change ztN (fun i:zNO (Fin K)=>i.elim 0 (U6 a b K))
  (m.optionElim h) ≤
  ztN (fun i:zNO (Fin K)=>i.elim b (fun _=>0))
    (m.optionElim h)+_ at hb
 simp only [zVB,zero_mul,zOP] at hb
 simpa [zDM,Nat.mul_comm] using hb
theorem b6g {r :ℕ} [Nontrivial F]
    (a b:ℕ) (center :F) (Q:zQp F r) :
    (zZ9 center Q).weightedTotalDegree (U6 a b (r+1)) ≤
      Q.weightedTotalDegree (kO a b (r+1))-(a+b*r) := by
  apply le_trans (zZ0
    (kO a b (r+1)) (U6 a b (r+1)) _ _ ?_)
  · simpa [zZ9,separant,kO] using
      weightedTotalDegree_pderiv_le_sub (kO a b (r+1))
        (some (zym r)) Q
  · intro i
    cases i with
    | none=>simp [kO]
    | some j =>
        change (z9v j:z3y (Fin (r+1)) F).weightedTotalDegree
          (U6 a b (r+1))≤a+b*j.val
        rw [z9v,weightedTotalDegree_monomial _ _ 1 one_ne_zero]
        simp [zTy,U6]
end Semiring
section Field
variable [zrb F]
theorem fTG {r :ℕ} (a b V:ℕ) (center :F)
    (Q:zQp F r)
    (hV:a+b*r≤V)
    (hQ:Q.weightedTotalDegree (kO a b (r+1))≤V) (l:ℕ) :
    (zm0 center Q l).weightedTotalDegree (U6 a b (r+1)) ≤
      (2*(l-r)-1)*(V-(a+b*r))+a+b*l:= by
  have hs :=(b6g a b center Q).trans
    (zIu hQ (a+b*r))
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    rw [zm0]
    split_ifs with hl
    · have he :2*(l-r)-1=0:= by omega
      rw [he,X,weightedTotalDegree_monomial _ _ 1 one_ne_zero]
      simp [zTy,U6]
    · have hlr :r<l:= by omega
      have hden : ∀ m∈((zpj F (Fin l)
          (zgz l center Q)).coeff (l-r)).support,
          ztN (fun i:Fin l=>2*(i.val-r)-1) m≤2*(l-r)-2 := by
        intro m hm
        exact denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r :=r) (K:=l) (h:=l-r) (by omega) center Q m hm
      have hw : ∀ m∈((zpj F (Fin l)
          (zgz l center Q)).coeff (l-r)).support,
          (C (((zpj F (Fin l)
            (zgz l center Q)).coeff (l-r)).coeff m) :
            z3y (Fin (r+1)) F).weightedTotalDegree (U6 a b (r+1)) +
          ztN (U6 a b l) m≤b*(l-r)+V:= by
        intro m hm
        simpa using (cfh a b l center Q (l-r) m hm).trans
          (z3b hQ _)
      have hd:=weightedTotalDegree_clearedSubstitution_le_of_coeff C
        (zZ9 center Q)
        (fun i:Fin l=>zm0 center Q i.val)
        (fun i=>2*(i.val-r)-1) (U6 a b l) (U6 a b (r+1))
        (2*(l-r)-2) (V-(a+b*r)) (b*(l-r)+V)
        ((zpj F (Fin l) (zgz l center Q)).coeff (l-r))
        hs (fun i=> by simpa [U6,Nat.add_assoc] using ih i.val i.isLt) hden hw
      have hm:=zku (U6 a b (r+1))
        (-C ((l.choose r :F)⁻¹))
        (clearedSubstitution C (zZ9 center Q)
          (fun i:Fin l=>zm0 center Q i.val)
          (fun i=>2*(i.val-r)-1) (2*(l-r)-2)
          ((zpj F (Fin l) (zgz l center Q)).coeff (l-r)))
      have hc: (-C ((l.choose r :F)⁻¹) :z3y (Fin (r+1)) F).weightedTotalDegree
          (U6 a b (r+1))=0:= by
        rw [← map_neg C]
        exact weightedTotalDegree_C _ _
      rw [hc,zOP] at hm
      apply hm.trans (hd.trans ?_)
      have he :2*(l-r)-1=(2*(l-r)-2)+1 := by omega
      have hsub:=zxt hV
      have hlsub:l-r+r=l:=zxt (Nat.le_of_lt hlr)
      rw [he]
      nlinarith
theorem dN8 {r :ℕ} (a b V K τ:ℕ) (center :F)
  (Q:zQp F r) (hτ:TaylorExponentSufficient r K τ)
  (hV:a+b*r≤V)
  (hQ:Q.weightedTotalDegree (kO a b (r+1))≤V) (l:Fin K) :
  (commonTaylorNumerator center Q τ l.val).weightedTotalDegree (U6 a b (r+1)) ≤
    τ*(V-(a+b*r))+a+b*l.val := by
 have hd:=fTG a b V center Q hV hQ l.val
 have hs :=(b6g a b center Q).trans
  (zIu hQ (a+b*r))
 have hp:=(zvm (U6 a b (r+1))
  (zZ9 center Q) (τ-(2*(l.val-r)-1))).trans
    (zBI _ hs)
 have hm:=zku (U6 a b (r+1))
  (zm0 center Q l.val)
  (zZ9 center Q^(τ-(2*(l.val-r)-1)))
 have he :=zxt (hτ l)
 unfold commonTaylorNumerator
 nlinarith
end Field
end
end amZ
end
section
namespace yP.C58
open Polynomial
noncomputable section
variable {σ R:Type*} [za6 R]
def bpP (w:σ→ℕ) : (σ →₀ ℕ) →+ (zNO σ →₀ ℕ) where
 toFun d:=d.optionElim (ztN w d)
 map_zero' := by ext i; cases i <;> simp
 map_add' d e := by ext i; cases i <;> simp
theorem d5f (w:σ→ℕ) :zq4 (bpP w) := by
 intro d e h
 have :=zPw Finsupp.some h
 simpa [bpP] using this
def bPW (w:σ→ℕ) :
    z3y σ R →+* z3y (zNO σ) R :=
  zXo R (bpP w)
theorem dVi (w:σ→ℕ) (p:z3y σ R) :
  (bPW w p).degreeOf none=p.weightedTotalDegree w:= by
 classical
 have hs : (bPW w p).support=p.support.image (bpP w) :=
  Finsupp.mapDomain_support_of_injective (d5f w) _
 rw [MvPolynomial.degreeOf_eq_sup,hs,Finset.sup_image]
 simp [Function.comp_def,bpP,zXg]
def cJN (w:σ→ℕ) :z3y σ R →+* zM2 (z3y σ R) :=
 (zpj R σ).toRingHom.comp (bPW w)
theorem c1d (w:σ→ℕ) (p:z3y σ R) :
  (cJN w p).natDegree=p.weightedTotalDegree w:= by
 change (zpj R σ (bPW w p)).natDegree= _
 rw [zgM,dVi]
theorem gMi
   (w:σ→ℕ) (f :zM2 (z3y σ R)) (b nu:ℕ)
   (hf : ∀ i≤b,i+(f.coeff i).weightedTotalDegree w≤nu) :
   (zSp f f.derivative b (b-1)).weightedTotalDegree w+b^2 ≤
     (2*b-1)*nu:= by
 let phi:=cJN (R:=R) w
 have hf' : ∀ i≤b,i+((f.map phi).coeff i).natDegree≤nu:= by
   intro i hi
   simpa only [z0b,phi,c1d] using hf i hi
 have h:=Polynomial.natDegree_resultant_derivative_padded_add_sq_le (f.map phi) b nu hf'
 rw [Polynomial.derivative_map,Polynomial.resultant_map_map,c1d] at h
 exact h
theorem gMj
   (w:σ→ℕ) (f :zM2 (z3y σ R)) (b nu:ℕ)
   (hf : ∀ i≤b,i+(f.coeff i).weightedTotalDegree w≤nu) :
   (zSp f f.derivative b (b-1)).weightedTotalDegree w≤nu*(nu-1) := by
 have h:=gMi w f b nu hf
 have hb:b≤nu:=(Nat.le_add_right b _).trans (hf b zs1)
 obtain ⟨c,rfl⟩:=zWX hb
 cases b with
 | zero =>
   have hz : (zSp f f.derivative 0 (0-1)).weightedTotalDegree w≤0:= by
     simpa using h
   exact hz.trans (zD0 _)
 | succ b =>
   have h1 :2*(b+1)-1=2*b+1 := by omega
   have h2 :b+1+c-1=b+c:= by omega
   simp only [h1,h2] at h ⊢
   nlinarith [zD0 (c*c)]
end
end yP.C58
end
section
namespace aFY
noncomputable section
open IsLocalRing
end
end aFY
end
section
namespace yP.C42
noncomputable section
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
variable {F:Type*} [zrb F]
theorem dPU (m:ℕ) (center received :F) (Q:zQp F 2) :
   localConstraintCoordinatesAt m center received Q =
     localConstraintCoordinatesAt m 0 0 (zh6 center received Q) := by
 have he :zxm 2 0 0 (zh6 center received Q) =
     zxm 2 center received Q:= by
   change ((zxm 2 0 0).comp (zh6 center received)) Q= _
   rw [unscaledLocalSubstitution_comp_globalPointTranslation]
   simp
 ext row
 change (zxm 2 center received Q).coeff row.val =
   (zxm 2 0 0 (zh6 center received Q)).coeff row.val
 rw [he]
end
end yP.C42
end
section
namespace yP.aLT
open Polynomial
variable {F K:Type*} [zrb F] [zrb K]
end yP.aLT
end
section
namespace yP
open Finset Module
end yP
end
section
namespace yP.a92
noncomputable section
open scoped BigOperators
variable {K I R:Type*} [zrb K] [z85 K] [z85 R]
end
end yP.a92
end
section
namespace yP.bQq
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
theorem map_resultant_eq_zero_of_common_root
  {R S:Type*} [za6 R] [za6 S]
  (phi:R →+* S) (f g:(Polynomial R)) (m n:ℕ)
  (hf :f.natDegree≤ m) (hg:g.natDegree≤n) (hsize :m≠0∨n≠0)
  (z :S) (hfroot :f.eval₂ phi z=0) (hgroot :g.eval₂ phi z=0) :
  phi (f.resultant g m n)=0:= by
 obtain ⟨p,q,_hp,_hq,hbezout⟩ :=
  Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hsize
 have he :=zPw (fun t:(Polynomial R) ↦ t.eval₂ phi z) hbezout
 simpa only [eval₂_add,zxy,zJU,hfroot,hgroot,zero_mul,zOP] using he.symm
theorem c1j {E :Type*} [zrb E] [CharP E 2130706433]
  (r :ℕ) (_hr :r≤2) (i:ℕ) (hri:r< i) (hi:i<131073) :
  (i.choose r :E)≠0:= by
 have h:=natCast_choose_ne_zero_of_ringChar (D:=131072) (s :=r)
  (Or.inr (by rw [ringChar.eq E 2130706433]; norm_num)) (i - r)
  (by omega)
 simpa only [zxt (Nat.le_of_lt hri)] using h
end yP.bQq
end
section
namespace yP.Xf
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E :Type*} [zrb E]
theorem grh (d:ℕ) (Q:zQp E (d+1)) :
  zTv (bhl d Q) ≤
    zTv (Pe d Q)*(zTv (Pe d Q) - 1) := by
 unfold bhl zTv
 apply yP.C58.gMj
 intro i hi
 have hi' : i≤degreeOf none (zhc none (HC d Q)) := by
  simpa only [zrL,zgM] using hi
 have h:=dME zb7
  (zhc none (HC d Q)) i hi'
 change i+((zpj E (zxV d)
  (zhc none (HC d Q))).coeff i).weightedTotalDegree zb7≤_
 exact h.trans_eq (c7Y d Q)
theorem grg (d:ℕ) (Q:zQp E (d+1)) (P:(Polynomial E))
   (hpos :0<zJP (Pe d Q) (zym (d+1)))
   (hroot :zho (Pe d Q) P=0)
   (hsep:zho (separant (Pe d Q) (zym (d+1))) P=0) :
   zho (bhl d Q) P=0:= by
 let f :=zrL (HC d Q)
 have hb:f.natDegree=zJP (Pe d Q) (zym (d+1)) := by
   change (zrL (HC d Q)).natDegree= _
   rw [← ce0 d Q,ctL]
 change (zfh P).toRingHom
   (zSp f f.derivative f.natDegree (f.natDegree - 1))=0
 apply yP.bQq.map_resultant_eq_zero_of_common_root
   (zfh P).toRingHom f f.derivative f.natDegree (f.natDegree - 1)
   zs1 (Polynomial.natDegree_derivative_le f) (Or.inl (by omega))
   (z75 (d+1) P)
 · change f.eval₂ _ _=0
   rw [show f=Wz d (Pe d Q) from (ce0 d Q).symm,
     bxT]
   exact hroot
 · change f.derivative.eval₂ _ _=0
   rw [show f=Wz d (Pe d Q) from (ce0 d Q).symm,
     dhw,bxT]
   exact hsep
def a3N (d:ℕ) (Q:zQp E (d+1)) :
    DifferentialPolynomial E d:=avu d Q*bhl d Q
theorem d3N (d:ℕ) (Q:zQp E (d+1))
  (hchar :zUy E=0∨zJP Q (zym (d+1))< zUy E) :
  a3N d Q≠0 :=
 mul_ne_zero (cY6 d Q) (grf d Q hchar)
theorem fX4 (d:ℕ) (Q:zQp E (d+1))
    (hQ:Q≠0) (P:(Polynomial E)) (hroot :zho Q P=0)
    (hpos :0<zJP (Pe d Q) (zym (d+1))) :
    (zho (Pe d Q) P=0 ∧
      zho (separant (Pe d Q) (zym (d+1))) P≠0) ∨
    zho (a3N d Q) P=0:= by
  rcases c8V d Q hQ P hroot with hc | hr
  · right
    simp only [a3N,zho,zok]
    change zho (avu d Q) P*_=0
    rw [hc,zero_mul]
  · by_cases hs :zho
        (separant (Pe d Q) (zym (d+1))) P=0
    · right
      have hz :=grg d Q P hpos hr hs
      simp only [a3N,zho,zok]
      change _ *zho (bhl d Q) P=0
      rw [hz,mul_zero]
    · exact Or.inl ⟨hr,hs⟩
theorem d3O (d:ℕ) (Q:zQp E (d+1)) :
  zTv (a3N d Q)≤zTv (avu d Q) +
   zTv (Pe d Q)*(zTv (Pe d Q) - 1) := by
 apply (zku zb7 _ _).trans
 exact z3b (grh d Q) _
theorem dVn (c v h:ℕ) (hv :0<v) (hb:c+v≤h) :
   c+v*(v - 1)≤h*(h - 1) := by
 have hvh:v≤h:= by omega
 obtain ⟨t,rfl⟩:=zWX hvh
 have hct :c≤t:= by omega
 cases v with
 | zero=>omega
 | succ v =>
   have hs :v+1+t - 1=v+t:= by omega
   simp only [Nat.succ_sub_one,hs]
   nlinarith [zD0 (v*t),zD0 (t*t)]
theorem d3P (d:ℕ) (Q:zQp E (d+1)) (h:ℕ)
   (hweight:zTv Q≤h) (hpos :0<zTv (Pe d Q)) :
   zTv (a3N d Q)≤h*(h - 1) :=
 (d3O d Q).trans (dVn _ _ _ hpos ((dfk d Q).trans hweight))
end
end yP.Xf
end
section
namespace yP.Xf
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E :Type*} [zrb E]
theorem c2A :
  zq4 (zMP (F:=E)) := by
 intro Q R h
 apply (zGY E orderZeroVariableEquiv).injective
 apply (z8s E 1).injective
 apply Polynomial.map_injective (zpe E (Fin 1)).toRingHom
  (zpe E (Fin 1)).injective
 exact h
theorem eHs (Q:zQp E 0) :
  (zMP Q).natDegree=zTv Q:= by
 have hleft:orderZeroOfPolynomial (zMP Q)= Q:= by
  apply c2A
  exact orderZeroAsPolynomial_orderZeroOfPolynomial _
 simpa only [hleft] using (orderZeroOfPolynomial_jetTotalDegree (zMP Q)).symm
section Native
variable [CharP E 2130706433]
end Native
end
end yP.Xf
end
section
namespace yP.aLT
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
variable {F K I:Type} [zrb F] [zrb K] [z85 K] [z85 I]
end
end yP.aLT
end
section
namespace yP.FM
open Code LinearCode CoreDefinitions
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {K I R:Type} [zrb K] [z85 K] [z85 I] [z85 R]
end
end yP.FM
end
