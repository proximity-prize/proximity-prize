import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdBC
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_HiddenDerivative_Interpolation_Local_GradedRank
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_ProximityGenerator_AffineGenerator
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_ReedSolomon_ListDecodability_Capacity_CurveCertificate
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_MvPolynomial_RadicalSplit_Separable
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_MvPolynomial_WeightedDegree_Products
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_MvPolynomial_WeightedOrder
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Polynomial_Differential_OrderZeroPresentation
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Matrix_ColumnRowPartitioned
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_FLT_MasonStothers

section Merged6967_DdBD
set_option Elab.async false











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
      rw [he,«X»,weightedTotalDegree_monomial _ _ 1 one_ne_zero]
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

end Merged6967_DdBD

section Merged6967_Fast006
set_option Elab.async false





set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_5_5_2_3
noncomputable section
open scoped BigOperators Polynomial
set_option linter.style.haveILetI false
section
variable {R A B : Type} [CommRing R] [CommRing A] [IsDomain A] [CommRing B]
variable (ρ : (Polynomial R) →+* A) (τ : R →+* B) (s : A →+* B)
private theorem independent_of_specialization (hw : ρ Polynomial.X ≠ 0)
    (hs : s.comp ρ = τ.comp (Polynomial.evalRingHom 0)) {n : ℕ} (v : Fin n → A) :
    letI : Module (Polynomial R) A := Module.compHom A ρ
    letI : Module R B := Module.compHom B τ
    LinearIndependent R (s ∘ v) → LinearIndependent (Polynomial R) v := by
  classical
  letI : Module (Polynomial R) A := Module.compHom A ρ
  letI : Module R B := Module.compHom B τ
  change LinearIndependent R (s ∘ v) → LinearIndependent (Polynomial R) v
  intro hv
  have specialize (f : Fin n → (Polynomial R)) (hf : ∑ i, ρ (f i) * v i = 0) :
      ∀ i, (f i).coeff 0 = 0 := by
    have hcompat (p : (Polynomial R)) : s (ρ p) = τ (p.coeff 0) := by
      simpa only [RingHom.comp_apply, Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coe_evalRingHom] using
        DFunLike.congr_fun hs p
    have h := congrArg s hf
    rw [map_sum, map_zero] at h
    simp only [map_mul, hcompat] at h
    exact Fintype.linearIndependent_iff.mp hv (fun i => (f i).coeff 0) h
  have allCoeffs (k : ℕ) (f : Fin n → (Polynomial R)) (hf : ∑ i, ρ (f i) * v i = 0) :
      ∀ i, (f i).coeff k = 0 := by
    induction k generalizing f with
    | zero => exact specialize f hf
    | succ k ih =>
      have hdiv (i : Fin n) : Polynomial.X * (f i).divX = f i := by
        simpa [specialize f hf i] using Polynomial.X_mul_divX_add (f i)
      have hprod : ρ Polynomial.X * ∑ i, ρ ((f i).divX) * v i = 0 := by
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, ← map_mul, hdiv]
        exact hf
      have hrel := (mul_eq_zero.mp hprod).resolve_left hw
      intro i
      simpa only [Polynomial.coeff_divX] using ih (fun i => (f i).divX) hrel i
  refine Fintype.linearIndependent_iff.mpr fun f hf i => ?_
  ext k
  rw [Polynomial.coeff_zero]
  exact allCoeffs k f hf i
theorem rank_le_of_specialization [Nontrivial R] (hw : ρ Polynomial.X ≠ 0)
    (hs : s.comp ρ = τ.comp (Polynomial.evalRingHom 0))
    (hsurj : Function.Surjective s) (n : ℕ) :
    letI : Module (Polynomial R) A := Module.compHom A ρ
    letI : Module R B := Module.compHom B τ
    Module.rank (Polynomial R) A ≤ (n : Cardinal) → Module.rank R B ≤ (n : Cardinal) := by
  classical
  letI : Module (Polynomial R) A := Module.compHom A ρ
  letI : Module R B := Module.compHom B τ
  change Module.rank (Polynomial R) A ≤ (n : Cardinal) → Module.rank R B ≤ (n : Cardinal)
  intro hrank
  by_contra! h
  have hlarge : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank R B := by
    rwa [Nat.cast_add_one, Cardinal.natCast_add_one_le_iff]
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hlarge
  choose u hu using fun i => hsurj (v i)
  have hu' : s ∘ u = v := funext hu
  have hind := independent_of_specialization ρ τ s hw hs u (hu' ▸ hv)
  have hsmall : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank (Polynomial R) A :=
    Module.le_rank_iff.mpr ⟨u, hind⟩
  exact (Nat.not_succ_le_self n) (by exact_mod_cast hsmall.trans hrank)
end
theorem rank_le_of_recovery {R A B : Type} [CommRing R] [IsDomain R]
    [CommRing A] [CommRing B] [IsDomain B] (ρ : R →+* A) (τ : R →+* B) (s : A →+* B)
    (hs : s.comp ρ = τ) (b : A) (hb : s b ≠ 0)
    (hrec : ∀ a : B, ∃ q : A, ∃ m : ℕ, s q = s b ^ m * a) (n : ℕ) :
    letI : Module R A := Module.compHom A ρ
    letI : Module R B := Module.compHom B τ
    Module.rank R A ≤ (n : Cardinal) → Module.rank R B ≤ (n : Cardinal) := by
  classical
  letI : Module R A := Module.compHom A ρ
  letI : Module R B := Module.compHom B τ
  change Module.rank R A ≤ (n : Cardinal) → Module.rank R B ≤ (n : Cardinal)
  intro hrank
  by_contra! h
  have hlarge : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank R B := by
    rwa [Nat.cast_add_one, Cardinal.natCast_add_one_le_iff]
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hlarge
  choose q m hm using fun i => hrec (v i)
  let k := Finset.univ.sup m
  let u (i : Fin (n + 1)) := b ^ (k - m i) * q i
  have hu (i : Fin (n + 1)) : s (u i) = s b ^ k * v i := by
    have hi : m i ≤ k := Finset.le_sup (Finset.mem_univ i)
    change s (b ^ (k - m i) * q i) = s b ^ k * v i
    rw [map_mul, map_pow, hm, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  have hind : LinearIndependent R u := by
    refine Fintype.linearIndependent_iff.mpr fun f hf => ?_
    have hf' : ∑ i, ρ (f i) * u i = 0 := hf
    have h := congrArg s hf'
    have hcomp (r : R) : s (ρ r) = τ r := DFunLike.congr_fun hs r
    rw [map_sum, map_zero] at h
    simp only [map_mul, hu, hcomp] at h
    have hprod : s b ^ k * ∑ i, τ (f i) * v i = 0 := by
      simpa only [Finset.mul_sum, mul_left_comm] using h
    exact Fintype.linearIndependent_iff.mp hv f
      ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ hb))
  have hsmall : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank R A :=
    Module.le_rank_iff.mpr ⟨u, hind⟩
  exact (Nat.not_succ_le_self n) (by exact_mod_cast hsmall.trans hrank)
end
end K1_13_5_5_2_3
end
section
namespace K1_13_5_5_2_3_1
noncomputable section
open scoped BigOperators Polynomial
variable {F R S σ : Type} [Field F] [CommRing R] [CommRing S]
def homogeneousEval (f : F →+* R) (g : MvPolynomial σ F) (x : σ → R) (w : R) : R :=
  ∑ d ∈ g.support, f (g.coeff d) * (∏ i ∈ d.support, x i ^ d i) *
    w ^ (g.totalDegree - d.degree)
theorem map_homogeneousEval (k : R →+* S) (f : F →+* R) (g : MvPolynomial σ F)
    (x : σ → R) (w : R) :
    k (homogeneousEval f g x w) = homogeneousEval (k.comp f) g (k ∘ x) (k w) := by
  simp [homogeneousEval, map_sum, map_prod]
theorem homogeneousEval_zero (f : F →+* R) (g : MvPolynomial σ F) (x : σ → R) :
    homogeneousEval f g x 0 = (MvPolynomial.homogeneousComponent g.totalDegree g).eval₂ f x := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply, MvPolynomial.eval₂_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d.degree ≤ g.totalDegree := MvPolynomial.le_totalDegree hd
  by_cases he : d.degree = g.totalDegree
  · simp [he, MvPolynomial.eval₂_monomial, Finsupp.prod]
  · simp [he, zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hle he))]
theorem homogeneousEval_scaled (f : F →+* R) (g : MvPolynomial σ F) (x : σ → R) (w : R) :
    homogeneousEval f g (fun i => x i * w) w = g.eval₂ f x * w ^ g.totalDegree := by
  rw [homogeneousEval, MvPolynomial.eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d.degree ≤ g.totalDegree := MvPolynomial.le_totalDegree hd
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_apply]
  rw [← mul_assoc (f _), mul_assoc (f _ * ∏ i ∈ d.support, x i ^ d i),
    ← pow_add, Nat.add_sub_of_le hle]
open Polynomial in
private theorem coeff_prod_at_sum {ι : Type} (s : Finset ι) (p : ι → (Polynomial R)) (n : ι → ℕ)
    (h : ∀ i ∈ s, (p i).natDegree ≤ n i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (p i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, (p j).natDegree ≤ n j := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self i s))
        ((natDegree_prod_le s p).trans (Finset.sum_le_sum hs)), ih hs]
def lineEquation (f : F →+* R) (g : MvPolynomial σ F)
    (v : σ → F) (a : σ → R) (w : R) : (Polynomial R) :=
  homogeneousEval (Polynomial.C.comp f) g
    (fun i => Polynomial.C (a i) + Polynomial.C (f (v i)) * Polynomial.X) (Polynomial.C w)
open Polynomial in
theorem lineEquation_degree (f : F →+* R) (g : MvPolynomial σ F)
    (v : σ → F) (a : σ → R) (w : R) :
    (lineEquation f g v a w).natDegree ≤ g.totalDegree ∧
    (lineEquation f g v a w).coeff g.totalDegree =
      f (MvPolynomial.eval v (MvPolynomial.homogeneousComponent g.totalDegree g)) := by
  classical
  let q : σ → (Polynomial R) := fun i => C (a i) + C (f (v i)) * «X»
  have hq (i : σ) : (q i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · simpa only [pow_one] using natDegree_C_mul_X_pow_le (f (v i)) 1
  have hqcoeff (i : σ) : (q i).coeff 1 = f (v i) := by
    simp [q, coeff_add]
  let term (d : σ →₀ ℕ) : (Polynomial R) :=
    C (f (g.coeff d) * w ^ (g.totalDegree - d.degree)) * ∏ i ∈ d.support, q i ^ d i
  have hterm (d : σ →₀ ℕ) : (term d).natDegree ≤ d.degree := by
    apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => by
      simpa using natDegree_pow_le_of_le (d i) (hq i))
  have hsum : lineEquation f g v a w = ∑ d ∈ g.support, term d := by
    unfold lineEquation homogeneousEval
    apply Finset.sum_congr rfl
    intro d _
    simp only [term, RingHom.comp_apply, map_mul, map_pow]
    ring
  rw [hsum]
  refine ⟨natDegree_sum_le_of_forall_le _ _ (fun d hd => (hterm d).trans
    (MvPolynomial.le_totalDegree hd)), ?_⟩
  rw [finsetSum_coeff, MvPolynomial.homogeneousComponent_apply, map_sum, map_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d.degree ≤ g.totalDegree := MvPolynomial.le_totalDegree hd
  by_cases he : d.degree = g.totalDegree
  · have hprod :
        (∏ i ∈ d.support, q i ^ d i).coeff d.degree =
          ∏ i ∈ d.support, f (v i ^ d i) := by
      rw [Finsupp.degree_apply, coeff_prod_at_sum d.support (fun i => q i ^ d i) d
        (fun i _ => by simpa using natDegree_pow_le_of_le (d i) (hq i))]
      apply Finset.prod_congr rfl
      intro i _
      simpa [hqcoeff, Nat.mul_one] using
        (coeff_pow_of_natDegree_le (m := d i) (hq i))
    simp only [he, ↓reduceIte, Nat.sub_self, pow_zero, mul_one, term, coeff_C_mul]
    rw [← he, hprod]
    simp [MvPolynomial.eval_monomial, Finsupp.prod, map_mul, map_prod]
  · simp [he, coeff_eq_zero_of_natDegree_lt ((hterm d).trans_lt (lt_of_le_of_ne hle he))]
def monicEquation (f : F →+* R) (g : MvPolynomial σ F)
    (v : σ → F) (a : σ → R) (w : R) : (Polynomial R) :=
  Polynomial.C (f (MvPolynomial.eval v (MvPolynomial.homogeneousComponent g.totalDegree g))⁻¹) *
    lineEquation f g v a w
open Polynomial in
theorem monicEquation_spec [Nontrivial R] (f : F →+* R) (g : MvPolynomial σ F)
    (v : σ → F) (a : σ → R) (w : R)
    (hv : MvPolynomial.eval v (MvPolynomial.homogeneousComponent g.totalDegree g) ≠ 0) :
    (monicEquation f g v a w).Monic ∧ (monicEquation f g v a w).natDegree = g.totalDegree := by
  obtain ⟨hd, hc⟩ := lineEquation_degree f g v a w
  have hcoeff : (monicEquation f g v a w).coeff g.totalDegree = 1 := by
    rw [monicEquation, coeff_C_mul, hc, ← map_mul, inv_mul_cancel₀ hv, map_one]
  have hdeg : (monicEquation f g v a w).natDegree = g.totalDegree :=
    natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_C_mul_le _ _).trans hd)
      (by rw [hcoeff]; exact one_ne_zero)
  exact ⟨by rwa [Monic, leadingCoeff, hdeg], hdeg⟩
open Polynomial in
theorem monicEquation_root (f : F →+* R) (g : MvPolynomial σ F) (v : σ → F)
    (a : σ → R) (w : R) (ρ : R →+* S) (z : S)
    (h : homogeneousEval (ρ.comp f) g (fun i => ρ (a i) + ρ (f (v i)) * z) (ρ w) = 0) :
    (monicEquation f g v a w).eval₂ ρ z = 0 := by
  have hf : (eval₂RingHom ρ z).comp (C.comp f) = ρ.comp f := by
    ext r
    simp [eval₂_C]
  have hline : (eval₂RingHom ρ z) (lineEquation f g v a w) = 0 := by
    rw [lineEquation, map_homogeneousEval, hf]
    simpa [Function.comp_def, map_add, map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X] using h
  change (eval₂RingHom ρ z) (monicEquation f g v a w) = 0
  rw [monicEquation, map_mul, hline, mul_zero]
end
end K1_13_5_5_2_3_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_1_1
noncomputable section
open MvPolynomial
theorem eliminateConstantParameter {A τ : Type*} [CommRing A] [Nontrivial A]
    (s : Finset τ) (c : τ) (hc : c ∈ s) (v : τ → A) (hv : v c = 1) :
    let g : MvPolynomial τ A := ∑ m ∈ s, MvPolynomial.X m * MvPolynomial.C (v m)
    g ≠ 0 ∧
      ∃ f : MvPolynomial τ A →+* MvPolynomial {m // m ≠ c} A,
        RingHom.ker f = Ideal.span {g} ∧ f.comp MvPolynomial.C = MvPolynomial.C := by
  classical
  let B := MvPolynomial {m // m ≠ c} A
  let e : MvPolynomial τ A ≃ₐ[A] Polynomial B :=
    (renameEquiv A (Equiv.optionSubtypeNe c).symm).trans (optionEquivLeft A _)
  let g : MvPolynomial τ A := ∑ m ∈ s, MvPolynomial.X m * MvPolynomial.C (v m)
  let y : B := ∑ m ∈ s.erase c, if hm : m ≠ c then MvPolynomial.X ⟨m, hm⟩ * MvPolynomial.C (v m) else 0
  have eC (a : A) : e (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
    change optionEquivLeft A _ (rename (Equiv.optionSubtypeNe c).symm (MvPolynomial.C a)) = _
    rw [rename_C, optionEquivLeft_C]
  have eX (m : τ) : e (MvPolynomial.X m) = match (Equiv.optionSubtypeNe c).symm m with
      | none => Polynomial.X
      | some n => Polynomial.C (MvPolynomial.X n) := by
    change optionEquivLeft A _ (rename (Equiv.optionSubtypeNe c).symm (MvPolynomial.X m)) = _
    rw [rename_X]
    cases (Equiv.optionSubtypeNe c).symm m with
    | none => exact optionEquivLeft_X_none A _
    | some n => exact optionEquivLeft_X_some A _ n
  have eg : e g = Polynomial.X + Polynomial.C y := by
    dsimp only [g, y]
    rw [← Finset.sum_erase_add _ _ hc, map_add, map_sum, map_sum, add_comm]
    congr 1
    · rw [hv, map_one, mul_one, eX, Equiv.optionSubtypeNe_symm_self]
    · apply Finset.sum_congr rfl
      intro m hm
      have hmc := Finset.ne_of_mem_erase hm
      rw [dite_eq_left hmc, map_mul, eX, Equiv.optionSubtypeNe_symm_of_ne hmc, eC, map_mul]
  change g ≠ 0 ∧ _
  refine ⟨?_, (Polynomial.evalRingHom (-y)).comp e.toRingHom, ?_, ?_⟩
  · intro hg
    have h := congrArg (fun p : Polynomial B => p.coeff 1) (eg.symm.trans (hg ▸ e.map_zero))
    simp at h
  · rw [← RingHom.comap_ker, Polynomial.ker_evalRingHom]
    have hh : Polynomial.X - Polynomial.C (-y) = e.toRingHom g := by
      change Polynomial.X - Polynomial.C (-y) = e g
      rw [eg, map_neg, sub_neg_eq_add]
    rw [hh, ← Set.image_singleton (f := e.toRingHom) (a := g), ← Ideal.map_span]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  · apply RingHom.ext
    intro a
    change Polynomial.eval (-y) (e (MvPolynomial.C a)) = MvPolynomial.C a
    rw [eC, Polynomial.eval_C]
end
end K1_13_6_1_4_1_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_3
noncomputable section
private theorem contract_sup_span_strictMono {R S : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit (algebraMap R S a)) :
    StrictMono (fun J : Ideal S => J.under R ⊔ Ideal.span {a}) := by
  intro J K hJK
  have hle := (IsLocalization.orderEmbedding M S).monotone hJK.le
  refine lt_of_le_of_ne (sup_le_sup_right hle _) ?_
  intro heq
  change J.under R ⊔ Ideal.span {a} = K.under R ⊔ Ideal.span {a} at heq
  have hcontain : K.under R ≤ J.under R ⊔ Ideal.span {a} * K.under R := by
    intro b hb
    have hb' : b ∈ J.under R ⊔ Ideal.span {a} := by
      rw [heq]
      exact Ideal.mem_sup_left hb
    obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hb'
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
    have had : a * d ∈ K.under R := by
      rw [← add_sub_cancel_left j (a * d)]
      exact (K.under R).sub_mem hb (hle hj)
    have hd : d ∈ K.under R := by
      change algebraMap R S d ∈ K
      have hh : algebraMap R S a * algebraMap R S d ∈ K := by
        rw [← map_mul]
        exact had
      obtain ⟨u, hu⟩ := hu
      rw [← hu] at hh
      simpa [← mul_assoc] using K.mul_mem_left (↑u⁻¹ : S) hh
    exact Submodule.mem_sup.mpr ⟨j, hj, a * d,
      Ideal.mem_span_singleton_mul.mpr ⟨d, hd, rfl⟩, rfl⟩
  have hback : K.under R ≤ J.under R :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      ((Ideal.span_singleton_le_iff_mem _).mpr
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R) ha)) hcontain
  exact hJK.not_ge ((IsLocalization.under_le_under_iff M S).mp hback)
private theorem length_localization_le_length_cut {R S : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R) {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit (algebraMap R S a)) :
    Module.length S (S ⧸ I.map (algebraMap R S)) ≤ Module.length R (R ⧸ (I ⊔ Ideal.span {a})) := by
  let F : Set.Ici (I.map (algebraMap R S)) → Set.Ici (I ⊔ Ideal.span {a}) := fun J =>
    ⟨J.1.under R ⊔ Ideal.span {a}, sup_le_sup_right (Ideal.map_le_iff_le_comap.mp J.2) _⟩
  have hF : StrictMono F := fun _ _ h => contract_sup_span_strictMono M ha hu h
  rw [← WithBot.coe_le_coe, Module.length_quotient, Module.length_quotient,
    Order.coheight_eq_krullDim_Ici, Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_le_of_strictMono F hF
theorem length_atPrime_le_length_principalCut {R : Type*}
    [CommRing R] [IsNoetherianRing R] {P Q I : Ideal R} [P.IsPrime] [Q.IsPrime]
    (hPQ : P ≤ Q) {a : R} (haQ : a ∈ Q) (haP : a ∉ P) :
    let A := Localization.AtPrime P
    let B := Localization.AtPrime Q
    Module.length A (A ⧸ I.map (algebraMap R A)) ≤
      Module.length B (B ⧸ (I ⊔ Ideal.span {a}).map (algebraMap R B)) := by
  let A := Localization.AtPrime P
  let B := Localization.AtPrime Q
  have hsub : Q.primeCompl ≤ P.primeCompl := fun _ h => fun hp => h (hPQ hp)
  change Module.length A (A ⧸ I.map (algebraMap R A)) ≤
    Module.length B (B ⧸ (I ⊔ Ideal.span {a}).map (algebraMap R B))
  let : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe B A _ _ hsub
  let : IsScalarTower R B A := IsLocalization.localization_isScalarTower_of_submonoid_le B A _ _ hsub
  let : IsLocalization (P.primeCompl.map (algebraMap R B)) A :=
    IsLocalization.isLocalization_of_submonoid_le B A _ _ hsub
  have ha : algebraMap R B a ∈ IsLocalRing.maximalIdeal B := by
    change a ∈ (IsLocalRing.maximalIdeal B).under R
    rwa [IsLocalization.AtPrime.under_maximalIdeal B Q]
  have hu : IsUnit (algebraMap B A (algebraMap R B a)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact IsLocalization.map_units A (⟨a, haP⟩ : P.primeCompl)
  have he := length_localization_le_length_cut (P.primeCompl.map (algebraMap R B))
    (I.map (algebraMap R B)) ha hu
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R B A] at he
  rwa [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
end
end K1_13_5_4_2_3
end
section
set_option autoImplicit false
namespace K1_13_7_6_2_2
open LinearMap
section Euler
variable {R : Type*} [CommRing R]
variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]
def CutFinite (t : R) (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  Module.length R (ker (lsmul R M t)) < ⊤ ∧
    Module.length R (M ⧸ range (lsmul R M t)) < ⊤
noncomputable def cutEuler (t : R) (M : Type*) [AddCommGroup M] [Module R M] : ℤ :=
  ((Module.length R (M ⧸ range (lsmul R M t))).toNat : ℤ) -
    (Module.length R (ker (lsmul R M t))).toNat
theorem length_kernel_add_range (v : M →ₗ[R] N) :
    Module.length R M = Module.length R (ker v) + Module.length R (range v) := by
  refine Module.length_eq_add_of_exact (ker v).subtype v.rangeRestrict
    (Submodule.subtype_injective _) v.surjective_rangeRestrict ?_
  rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
theorem length_range_add_cokernel (v : M →ₗ[R] N) :
    Module.length R N = Module.length R (range v) + Module.length R (N ⧸ range v) :=
  Module.length_eq_add_of_exact (range v).subtype (range v).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
theorem cut_add (t : R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM : CutFinite t M) (hP : CutFinite t P) :
    CutFinite t N ∧ cutEuler t N = cutEuler t M + cutEuler t P := by
  let a := lsmul R M t
  let b := lsmul R N t
  let c := lsmul R P t
  have hab : g.comp b = c.comp g := by ext x; simp [b, c]
  have hbc : f.comp a = b.comp f := by ext x; simp [a, b]
  let fK : ker a →ₗ[R] ker b := (f.comp (ker a).subtype).codRestrict _ (by
    intro x
    change t • f x.val = 0
    rw [← map_smul]
    exact (congrArg f x.property).trans (map_zero f))
  let gK : ker b →ₗ[R] ker c := (g.comp (ker b).subtype).codRestrict _ (by
    intro x
    change t • g x.val = 0
    rw [← map_smul]
    exact (congrArg g x.property).trans (map_zero g))
  let fC := Submodule.mapQ (range a) (range b) f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, (DFunLike.congr_fun hbc x).symm⟩)
  let gC := Submodule.mapQ (range b) (range c) g (by
    rintro _ ⟨x, rfl⟩
    exact ⟨g x, (DFunLike.congr_fun hab x).symm⟩)
  let δ := SnakeLemma.δ' a b c f g hfg f g hfg hbc hab
    (ker c).subtype (LinearMap.exact_subtype_ker_map c) (range a).mkQ
    (LinearMap.exact_map_mkQ_range a) hg hf
  have hfK : Function.Injective fK := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
  have hgC : Function.Surjective gC := by
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨y, rfl⟩ := hg x
    exact ⟨(range b).mkQ y, rfl⟩
  have hk : Function.Exact fK gK := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (hfg x.val).mp (congrArg Subtype.val hx)
      have hay : a y = 0 := hf (by
        simpa [hy, x.property] using DFunLike.congr_fun hbc y)
      exact ⟨⟨y, hay⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext (hfg.apply_apply_eq_zero y.val)
  have hkδ : Function.Exact gK δ :=
    SnakeLemma.exact_δ'_right a b c f g hfg f g hfg hbc hab
      (ker b).subtype (LinearMap.exact_subtype_ker_map b)
      (ker c).subtype (LinearMap.exact_subtype_ker_map c)
      (range a).mkQ (LinearMap.exact_map_mkQ_range a) hg hf gK rfl
      (Submodule.subtype_injective _)
  have hδc : Function.Exact δ fC :=
    SnakeLemma.exact_δ'_left a b c f g hfg f g hfg hbc hab
      (ker c).subtype (LinearMap.exact_subtype_ker_map c)
      (range a).mkQ (LinearMap.exact_map_mkQ_range a)
      (range b).mkQ (LinearMap.exact_map_mkQ_range b) hg hf fC rfl
      (Submodule.mkQ_surjective _)
  have hc : Function.Exact fC gC := by
    apply (hfg.exact_mapQ_iff _ _).2
    rw [show range g = ⊤ from LinearMap.range_eq_top.mpr hg, top_inf_eq]
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hg x
    exact ⟨b y, ⟨y, rfl⟩, DFunLike.congr_fun hab y⟩
  change Module.length R (ker a) < ⊤ ∧ Module.length R (M ⧸ range a) < ⊤ at hM
  change Module.length R (ker c) < ⊤ ∧ Module.length R (P ⧸ range c) < ⊤ at hP
  have l1 := length_kernel_add_range gK
  rw [hk.linearMap_ker_eq, ← (LinearEquiv.ofInjective fK hfK).length_eq] at l1
  have l2 := length_kernel_add_range δ
  rw [hkδ.linearMap_ker_eq] at l2
  have l3 := length_kernel_add_range fC
  rw [hδc.linearMap_ker_eq] at l3
  have l4 := length_kernel_add_range gC
  rw [hc.linearMap_ker_eq, LinearMap.range_eq_top.mpr hgC, Module.length_top] at l4
  have h2 := ENat.add_lt_top.mp (l2 ▸ hP.1)
  have h3 := ENat.add_lt_top.mp (l3 ▸ hM.2)
  refine ⟨⟨l1.symm ▸ ENat.add_lt_top.mpr ⟨hM.1, h2.1⟩,
      l4.symm ▸ ENat.add_lt_top.mpr ⟨h3.2, hP.2⟩⟩, ?_⟩
  have n1 := congrArg ENat.toNat l1
  have n2 := congrArg ENat.toNat l2
  have n3 := congrArg ENat.toNat l3
  have n4 := congrArg ENat.toNat l4
  rw [ENat.toNat_add hM.1.ne h2.1.ne] at n1
  rw [ENat.toNat_add h2.1.ne h2.2.ne] at n2
  rw [ENat.toNat_add h3.1.ne h3.2.ne] at n3
  rw [ENat.toNat_add h3.2.ne hP.2.ne] at n4
  unfold cutEuler
  change ((Module.length R (N ⧸ range b)).toNat : ℤ) - (Module.length R (ker b)).toNat =
    ((Module.length R (M ⧸ range a)).toNat : ℤ) - (Module.length R (ker a)).toNat +
      (((Module.length R (P ⧸ range c)).toNat : ℤ) - (Module.length R (ker c)).toNat)
  omega
theorem cut_congr (t : R) (e : M ≃ₗ[R] N) :
    (CutFinite t M ↔ CutFinite t N) ∧ cutEuler t M = cutEuler t N := by
  let a := lsmul R M t
  let b := lsmul R N t
  have hker : (ker a).map e.toLinearMap = ker b := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    constructor
    · rintro ⟨z, hz, ezy⟩
      have hx : a x = 0 := e.injective ezy ▸ hz
      show t • e x = 0
      rw [← map_smul, show t • x = 0 from hx, map_zero]
    · intro hx
      exact ⟨x, e.injective (by simpa [a, b] using hx), rfl⟩
  have hrange : (range a).map e.toLinearMap = range b := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp [a, b]⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := e.surjective x
      exact ⟨a z, ⟨z, rfl⟩, by simp [a, b]⟩
  have lk := (e.ofSubmodules (ker a) (ker b) hker).length_eq
  have lc := (Submodule.Quotient.equiv (range a) (range b) e hrange).length_eq
  unfold CutFinite cutEuler
  rw [lk, lc]
  exact ⟨Iff.rfl, rfl⟩
theorem cut_of_finite_length (t : R) (h : Module.length R M < ⊤) :
    CutFinite t M ∧ cutEuler t M = 0 := by
  let a := lsmul R M t
  have lk := length_kernel_add_range a
  have lc := length_range_add_cokernel a
  have hk := ENat.add_lt_top.mp (lk ▸ h)
  have hc := ENat.add_lt_top.mp (lc ▸ h)
  refine ⟨⟨hk.1, hc.2⟩, ?_⟩
  have h₁ := congrArg ENat.toNat lk
  have h₂ := congrArg ENat.toNat lc
  rw [ENat.toNat_add hk.1.ne hk.2.ne] at h₁
  rw [ENat.toNat_add hc.1.ne hc.2.ne] at h₂
  unfold cutEuler
  change ((Module.length R (M ⧸ range a)).toNat : ℤ) - (Module.length R (ker a)).toNat = 0
  omega
end Euler
end K1_13_7_6_2_2
end
section
namespace K1_13_7_4_2_2
noncomputable section
open MvPolynomial
abbrev Vars (K : Type*) [CommRing K] (n : ℕ) := idealOfVars (Fin n) K
abbrev Jets (K : Type*) [CommRing K] (n t : ℕ) :=
  MvPolynomial (Fin n) K ⧸ Vars K n ^ t
abbrev jet (K : Type*) [CommRing K] (n t : ℕ) :
    MvPolynomial (Fin n) K →+* Jets K n t := Ideal.Quotient.mk _
abbrev aug (K : Type*) [CommRing K] (n t : ℕ) : Ideal (Jets K n t) :=
  (Vars K n).map (jet K n t)
theorem aug_pow_self (K : Type*) [CommRing K] (n t : ℕ) :
    aug K n t ^ t = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
theorem aug_eq_span (K : Type*) [CommRing K] (n t : ℕ) :
    aug K n t = Ideal.span (Set.range fun i => jet K n t («X» i)) := by
  change (Ideal.span (Set.range «X»)).map (jet K n t) = _
  rw [Ideal.map_span, ← Set.range_comp]
  rfl
theorem X_mem_aug (K : Type*) [CommRing K] (n t : ℕ) (i : Fin n) :
    jet K n t («X» i) ∈ aug K n t :=
  Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
theorem ker_constantCoeff (K : Type*) [CommRing K] (n : ℕ) :
    RingHom.ker (constantCoeff : MvPolynomial (Fin n) K →+* K) = Vars K n := by
  ext p
  rw [RingHom.mem_ker, ← pow_one (Vars K n), mem_pow_idealOfVars_iff']
  change p.coeff 0 = 0 ↔ _
  constructor
  · intro h d hd
    obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd)
    exact h
  · intro h
    exact h 0 (by simp)
abbrev constant (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t) :
    Jets K n t →+* K :=
  Ideal.Quotient.lift _ constantCoeff <| by
    change Vars K n ^ t ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin n) K →+* K)
    rw [ker_constantCoeff]
    exact Ideal.pow_le_self ht.ne'
@[simp] theorem constant_jet (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t)
    (p : MvPolynomial (Fin n) K) : constant K n t ht (jet K n t p) = constantCoeff p := rfl
theorem ker_constant (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t) :
    RingHom.ker (constant K n t ht) = aug K n t := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, constant_jet, ← RingHom.mem_ker, ker_constantCoeff]
  change p ∈ Vars K n ↔ p ∈ (aug K n t).comap (jet K n t)
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  change p ∈ Vars K n ↔ p ∈ Vars K n ⊔ RingHom.ker (jet K n t)
  rw [Ideal.mk_ker, sup_eq_left.mpr (Ideal.pow_le_self ht.ne')]
@[simp] theorem constant_algebraMap (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t)
    (c : K) : constant K n t ht (algebraMap K (Jets K n t) c) = c := by
  change constant K n t ht (jet K n t (C c)) = c
  simp
theorem constant_surjective (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t) :
    Function.Surjective (constant K n t ht) := fun c =>
  ⟨algebraMap K (Jets K n t) c, constant_algebraMap K n t ht c⟩
end
end K1_13_7_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_1
open Ideal
private theorem mul_mem_square_iff {R : Type*} [CommRing R] (I : Ideal R) (a x : R)
    (hreg : ∀ y, a * y ∈ I → y ∈ I) :
    a * x ∈ I ⊔ span {a ^ 2} ↔ x ∈ I ⊔ span {a} := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hv
    have he : a * (x - a * r) = u := by
      calc
        a * (x - a * r) = a * x - a ^ 2 * r := by ring
        _ = u := by rw [← huv, add_sub_cancel_right]
    exact Submodule.mem_sup.mpr
      ⟨x - a * r, hreg _ (he ▸ hu), a * r, mem_span_singleton.mpr ⟨r, rfl⟩,
        sub_add_cancel _ _⟩
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hv
    exact Submodule.mem_sup.mpr
      ⟨a * u, I.mul_mem_left _ hu, a ^ 2 * r, mem_span_singleton.mpr ⟨r, rfl⟩,
        by rw [mul_add, pow_two, mul_assoc]⟩
theorem square_length {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    (I : Ideal R) (a : R) (hreg : ∀ y, a * y ∈ I → y ∈ I)
    [Module.Finite k (R ⧸ (I ⊔ span {a}))] :
    Module.Finite k (R ⧸ (I ⊔ span {a ^ 2})) ∧
      Module.finrank k (R ⧸ (I ⊔ span {a ^ 2})) =
        2 * Module.finrank k (R ⧸ (I ⊔ span {a})) := by
  let J : Ideal R := I ⊔ span {a}
  let J₂ : Ideal R := I ⊔ span {a ^ 2}
  change Module.Finite k (R ⧸ J₂) ∧ Module.finrank k (R ⧸ J₂) = 2 * Module.finrank k (R ⧸ J)
  have hle : J₂ ≤ J := sup_le_sup_left
    (span_singleton_le_span_singleton.mpr (dvd_pow_self a (by decide))) I
  let π : (R ⧸ J₂) →ₗ[k] (R ⧸ J) := (Ideal.Quotient.factorₐ k hle).toLinearMap
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hle
  let m : R →ₗ[k] (R ⧸ J₂) :=
    (Ideal.Quotient.mkₐ k J₂).toLinearMap.comp (LinearMap.mulLeft k a)
  let Jk : Submodule k R := J.restrictScalars k
  have hm (x : R) : m x = 0 ↔ x ∈ J := by
    change Ideal.Quotient.mk J₂ (a * x) = 0 ↔ x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact mul_mem_square_iff I a x hreg
  let ι : (R ⧸ J) →ₗ[k] (R ⧸ J₂) :=
    Jk.liftQ m (fun x hx => LinearMap.mem_ker.mpr ((hm x).mpr hx))
  have hι (x : R) : ι (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J₂ (a * x) := rfl
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hm x).mp (LinearMap.mem_ker.mp hz))
  have hexact : Function.Exact ι π := by
    rw [LinearMap.exact_iff]
    ext z
    constructor
    · intro hz
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hx : x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hz)
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp hv
      refine ⟨Ideal.Quotient.mk J r, ?_⟩
      rw [hι, ← huv, map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ J₂ from le_sup_left) hu),
        zero_add]
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [hι]
      apply LinearMap.mem_ker.mpr
      change Ideal.Quotient.mk J (a * x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show span {a} ≤ J from le_sup_right) (mem_span_singleton.mpr ⟨x, rfl⟩))
  have hfin : Module.Finite k (R ⧸ J₂) := Module.Finite.of_exact hexact hπ
  refine ⟨hfin, ?_⟩
  have hlen := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, LinearMap.exact_iff.mp hexact,
    LinearMap.finrank_range_of_inj hinj] at hlen
  simpa only [two_mul] using hlen.symm
end K1_13_6_1_4_3_3_1
end
section
namespace K1_13_7_3
noncomputable section
open MvPolynomial
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
private def project (φ : L →ₗ[F] F) (P : MvPolynomial (Fin 3) L) :
    MvPolynomial (Fin 3) F :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange φ (map_zero φ) P.coeff)
private theorem coeff_project (φ : L →ₗ[F] F) (P : MvPolynomial (Fin 3) L)
    (m : Fin 3 →₀ ℕ) : (project φ P).coeff m = φ (P.coeff m) :=
  Finsupp.mapRange_apply (hf := map_zero φ)
private theorem project_mul (φ : L →ₗ[F] F) (P : MvPolynomial (Fin 3) F)
    (V : MvPolynomial (Fin 3) L) :
    project φ (MvPolynomial.map (algebraMap F L) P * V) = P * project φ V := by
  ext m
  simp only [coeff_project, coeff_mul, coeff_map, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]
private theorem project_total_le (φ : L →ₗ[F] F) (V : MvPolynomial (Fin 3) L) :
    (project φ V).totalDegree ≤ V.totalDegree := by
  refine Finset.sup_le fun m hm => le_totalDegree ?_
  rw [MvPolynomial.mem_support_iff, coeff_project] at hm
  exact MvPolynomial.mem_support_iff.mpr fun h => hm (by rw [h, map_zero])
theorem relPrime_map_field (P Q : MvPolynomial (Fin 3) F)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hrel : IsRelPrime P Q) :
    IsRelPrime (MvPolynomial.map (algebraMap F L) P)
      (MvPolynomial.map (algebraMap F L) Q) := by
  let i := algebraMap F L
  have hi : Function.Injective i := i.injective
  have hmap : Function.Injective (MvPolynomial.map (σ := Fin 3) i) := MvPolynomial.map_injective _ hi
  rintro D ⟨U, hU⟩ ⟨V, hV⟩
  by_contra hD
  have hv : V ≠ 0 := by
    intro hz
    exact hQ (hmap (by rw [hV, hz, mul_zero, map_zero]))
  have hd : D ≠ 0 := by
    intro hz
    exact hP (hmap (by rw [hU, hz, zero_mul, map_zero]))
  have hdeg : 0 < D.totalDegree := by
    by_contra! h
    have hc : D = C (D.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    have hn : D.coeff 0 ≠ 0 := by
      intro hz
      exact hd (by rw [hc, hz, map_zero])
    exact hD (hc ▸ (isUnit_iff_ne_zero.mpr hn).map C)
  obtain ⟨m, hm⟩ := support_nonempty.mpr hv
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F (MvPolynomial.mem_support_iff.mp hm)
  have hpv : project φ V ≠ 0 := fun h => hφ (by
    simpa [coeff_project] using congrArg (fun G : MvPolynomial (Fin 3) F => G.coeff m) h)
  have hsyzygy : P * project φ V = Q * project φ U := by
    rw [← project_mul, ← project_mul]
    change project φ (MvPolynomial.map i P * V) = project φ (MvPolynomial.map i Q * U)
    rw [hU, hV, mul_assoc, mul_assoc, mul_comm U V]
  have hdiv : Q ∣ project φ V :=
    hrel.symm.dvd_of_dvd_mul_left ⟨project φ U, hsyzygy⟩
  have hle := (totalDegree_le_of_dvd_of_isDomain hdiv hpv).trans (project_total_le φ V)
  have heq : Q.totalDegree = D.totalDegree + V.totalDegree := by
    change (Finset.sup Q.support _) = _
    rw [← support_map_of_injective Q hi]
    change (MvPolynomial.map i Q).totalDegree = _
    rw [hV, totalDegree_mul_of_isDomain hd hv]
  omega
end
end K1_13_7_3
end
section
namespace K1_13_6_1_4_3_2
noncomputable section
open scoped BigOperators
open LinearMap Submodule
section Length
variable {R : Type*} [CommRing R]
private theorem length_step (S K : Type*) [CommRing S] [CommRing K]
    [Algebra R S] [Algebra K S] [Module.Flat R S]
    (I Q : Ideal R) (x : R)
    (hQ : (⊥ : Submodule R (R ⧸ I)).colon {I.mkQ x} = Q) :
    Module.length K (S ⧸ I.map (algebraMap R S)) =
      Module.length K (S ⧸ Q.map (algebraMap R S)) +
        Module.length K (S ⧸ (I ⊔ Ideal.span {x}).map (algebraMap R S)) := by
  let N := I ⊔ Ideal.span {x}
  let f₀ := toSpanSingleton R (R ⧸ I) (I.mkQ x)
  have hf₀ : ker f₀ = Q := by
    rw [← hQ]
    ext a
    simp [f₀, mem_colon_singleton]
  let f : (R ⧸ Q) →ₗ[R] (R ⧸ I) := Q.liftQ f₀ hf₀.ge
  let hIN : I ≤ N := le_sup_left
  let g : (R ⧸ I) →ₗ[R] (R ⧸ N) := I.mapQ N LinearMap.id (by simpa using hIN)
  have hf : Function.Injective f :=
    ker_eq_bot.mp (Q.ker_liftQ_eq_bot f₀ hf₀.ge hf₀.le)
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨z, rfl⟩ := N.mkQ_surjective z
    exact ⟨I.mkQ z, rfl⟩
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    have hrange : range f = Submodule.map I.mkQ (Ideal.span {x}) := by
      dsimp only [f, f₀]
      rw [range_liftQ, LinearMap.range_toSpanSingleton,
        Ideal.span, Submodule.map_span, Set.image_singleton]
    dsimp only [g]
    rw [ker_mapQ, comap_id, hrange]
    change Submodule.map I.mkQ ((I : Submodule R R) ⊔ Ideal.span {x}) = _
    rw [Submodule.map_sup, mkQ_map_self, bot_sup_eq]
  let e (L : Ideal R) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S L).toLinearEquiv.restrictScalars K
  rw [(e I).length_eq, (e Q).length_eq, (e N).length_eq]
  exact Module.length_eq_add_of_exact ((f.baseChange S).restrictScalars K)
    ((g.baseChange S).restrictScalars K)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)
    (LinearMap.baseChange_surjective S hg) (Module.Flat.lTensor_exact S hfg)
def localWeight (I P : Ideal R) : ℕ∞ :=
  haveI := Classical.dec P.IsPrime
  if hP : P.IsPrime then
    letI := hP
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))
  else 0
theorem localWeight_of_prime (I P : Ideal R) [hp : P.IsPrime] :
    localWeight I P =
      Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  exact dite_eq_left hp
private theorem localWeight_step {J I Q P : Ideal R} {x : R}
    (hJI : J ≤ I) (hP : J.IsMinimalPrime P) (hQ : Q.IsPrime)
    (hcolon : (⊥ : Submodule R (R ⧸ I)).colon {I.mkQ x} = Q) :
    localWeight I P = (if P = Q then 1 else 0) + localWeight (I ⊔ Ideal.span {x}) P := by
  classical
  let hp := hP.isPrime
  let L := Localization.AtPrime P
  have hIQ : I ≤ Q := by
    intro y hy
    rw [← hcolon, mem_colon_singleton, Submodule.mem_bot]
    change y • Ideal.Quotient.mk I x = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hy,
      zero_mul]
  have hlen := length_step L L I Q x hcolon
  rw [localWeight_of_prime, localWeight_of_prime, hlen]
  congr 1
  by_cases h : P = Q
  · rw [← h, ite_eq_left rfl, IsLocalization.AtPrime.map_eq_maximalIdeal P L]
    apply Module.length_eq_one_iff.mpr
    exact isSimpleModule_iff_quot_maximal.mpr
      ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
  · have hn : ¬ Q ≤ P := fun hQP => h (hP.eq_of_le ⟨hQ, hJI.trans hIQ⟩ hQP).symm
    rw [ite_eq_right h, IsLocalization.AtPrime.map_eq_top_of_not_le (S := L) hn]
    exact Module.length_eq_zero
theorem weighted_length_le (S K : Type*) [CommRing S] [CommRing K]
    [Algebra R S] [Algebra K S] [Module.Flat R S] [IsNoetherianRing R]
    (J : Ideal R) (surfaces : Finset (Ideal R))
    (hmin : ∀ P ∈ surfaces, J.IsMinimalPrime P) :
    (∑ P ∈ surfaces, localWeight J P *
      Module.length K (S ⧸ P.map (algebraMap R S))) ≤
      Module.length K (S ⧸ J.map (algebraMap R S)) := by
  classical
  let d (I : Ideal R) := Module.length K (S ⧸ I.map (algebraMap R S))
  suffices H : ∀ I : Ideal R, J ≤ I → (∑ P ∈ surfaces, localWeight I P * d P) ≤ d I by
    exact H J le_rfl
  intro I
  induction I using WellFoundedGT.induction with
  | ind I ih =>
    intro hJI
    by_cases hI : I = ⊤
    · subst I
      have hw (P : Ideal R) (hP : P ∈ surfaces) : localWeight (⊤ : Ideal R) P = 0 := by
        let hp := (hmin P hP).isPrime
        rw [localWeight_of_prime, Ideal.map_top]
        exact Module.length_eq_zero
      simp [Finset.sum_congr rfl fun P hP => show localWeight (⊤ : Ideal R) P * d P = 0 by
        rw [hw P hP, zero_mul]]
    · have : Nontrivial (R ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hI
      obtain ⟨Q, hQ⟩ := associatedPrimes.nonempty R (R ⧸ I)
      rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hQ
      obtain ⟨hQ, z, hcolon⟩ := hQ
      obtain ⟨x, rfl⟩ := I.mkQ_surjective z
      have hx : x ∉ I := by
        intro hx
        have hzero : I.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hx
        rw [hzero, Submodule.colon_singleton_zero] at hcolon
        exact hQ.ne_top hcolon
      let N := I ⊔ Ideal.span {x}
      have hxN : x ∈ N :=
        (show Ideal.span {x} ≤ N from le_sup_right) (Ideal.mem_span_singleton_self x)
      have hIN : I < N := lt_of_le_of_ne le_sup_left (fun he => hx (he.symm ▸ hxN))
      have hnext := ih N hIN (hJI.trans hIN.le)
      have hstep : d I = d Q + d N := length_step S K I Q x hcolon.symm
      have hfirst :
          (∑ P ∈ surfaces, (if P = Q then (1 : ℕ∞) else 0) * d P) ≤ d Q := by
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq']
        split <;> simp
      rw [hstep]
      calc
        _ = (∑ P ∈ surfaces, (if P = Q then (1 : ℕ∞) else 0) * d P) +
              ∑ P ∈ surfaces, localWeight N P * d P := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro P hP
          rw [localWeight_step hJI (hmin P hP) hQ hcolon.symm, add_mul]
        _ ≤ d Q + d N := add_le_add hfirst hnext
end Length
end
end K1_13_6_1_4_3_2
end
section
namespace K1_13_7_2_1_2
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Polynomial
private theorem monic_dvd_derivative_mul_of_dvd_pow {A : Type*} [CommRing A] [IsReduced A]
    {F g : (Polynomial A)} (hF : F.Monic) {n : ℕ} (h : F ∣ g ^ n) :
    F ∣ F.derivative * g := by
  classical
  apply (modByMonic_eq_zero_iff_dvd hF).mp
  ext i
  rw [coeff_zero]
  apply (nilpotent_iff_mem_prime.mpr ?_).eq_zero
  intro P hP
  let : P.IsPrime := hP
  let L := FractionRing (A ⧸ P)
  let ρ : A →+* L := (algebraMap (A ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hFL : (F.map ρ).Monic := hF.map ρ
  have hd : F.map ρ ∣ (g.map ρ) ^ n := by
    simpa only [map_pow, coe_mapRingHom] using map_dvd (Polynomial.mapRingHom ρ) h
  have hr : radical (F.map ρ) ∣ g.map ρ :=
    (exists_dvd_pow_iff_radical_dvd hFL.ne_zero).mp ⟨n, hd⟩
  have hL : F.map ρ ∣ (F.map ρ).derivative * g.map ρ := by
    calc
      F.map ρ = EuclideanDomain.divRadical (F.map ρ) * radical (F.map ρ) :=
        EuclideanDomain.divRadical_mul_radical.symm
      _ ∣ (F.map ρ).derivative * g.map ρ := mul_dvd_mul (divRadical_dvd_derivative _) hr
  have hm : ((F.derivative * g) %ₘ F).map ρ = 0 := by
    rw [map_modByMonic ρ hF, Polynomial.map_mul, ← derivative_map]
    exact (modByMonic_eq_zero_iff_dvd hFL).mpr hL
  have hc := congrArg (fun p : (Polynomial L) => p.coeff i) hm
  rw [coeff_map, coeff_zero] at hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (IsFractionRing.injective (A ⧸ P) L (by simpa [ρ] using hc))
attribute [local instance] Polynomial.algebra
theorem clear_monic_cut {A : Type*} [CommRing A] (F g : (Polynomial A)) {q : A}
    (hq : (Ideal.span ({q} : Set A)).IsRadical) {n : ℕ}
    (hn : g ^ n ∈ Ideal.span {F, Polynomial.C q}) :
    ∃ k : ℕ, Polynomial.C F.leadingCoeff ^ k * (F.derivative * g) ∈
      Ideal.span {F, Polynomial.C q} := by
  let I : Ideal A := Ideal.span {q}
  let J : Ideal (Polynomial A) := Ideal.span {F, Polynomial.C q}
  let B := A ⧸ I
  let a : B := Ideal.Quotient.mk I F.leadingCoeff
  let D := Localization.Away a
  let π : (Polynomial A) →+* (Polynomial B) := Polynomial.mapRingHom (Ideal.Quotient.mk I)
  let j : (Polynomial B) →+* (Polynomial D) := algebraMap (Polynomial B) (Polynomial D)
  let φ : A →+* D := (algebraMap B D).comp (Ideal.Quotient.mk I)
  let : IsLocalization ((Submonoid.powers a).map (Polynomial.C : B →+* (Polynomial B))) (Polynomial D) :=
    Polynomial.isLocalization (Submonoid.powers a) D
  have : IsReduced D := by
    have hB : (⊥ : Ideal B).radical = ⊥ :=
      nilradical_eq_bot_iff.mpr ((Ideal.isRadical_iff_quotient_reduced I).mp hq)
    have hD := IsLocalization.map_radical (Submonoid.powers a) D (⊥ : Ideal B)
    rw [hB, Ideal.map_bot] at hD
    exact nilradical_eq_bot_iff.mp hD.symm
  have hπ : Function.Surjective π :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = Ideal.span {Polynomial.C q} := by
    change RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk I)) = _
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
    simp [I, Ideal.map_span]
  have hπq : π (Polynomial.C q) = 0 := by
    change (Polynomial.C q).map (Ideal.Quotient.mk I) = 0
    rw [Polynomial.map_C, Ideal.Quotient.mk_singleton_self, Polynomial.C_0]
  have hJπ : J.map π = Ideal.span {π F} := by
    change (Ideal.span {F, Polynomial.C q}).map π = _
    rw [Ideal.span_insert, Ideal.map_sup, Ideal.map_span, Ideal.map_span,
      Set.image_singleton, Set.image_singleton, hπq, Ideal.span_singleton_zero, sup_bot_eq]
  have hj (x : (Polynomial A)) : j (π x) = x.map φ := by
    change (x.map (Ideal.Quotient.mk I)).map (algebraMap B D) = _
    rw [Polynomial.map_map]
  have hu : IsUnit (φ F.leadingCoeff) :=
    IsLocalization.Away.algebraMap_isUnit a
  have hlead : (F.map φ).leadingCoeff = φ F.leadingCoeff := by
    rcases subsingleton_or_nontrivial D with hD | hD
    · exact Subsingleton.elim _ _
    · exact leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero
  have hinv : φ F.leadingCoeff * (↑(hu.unit⁻¹) : D) = 1 := by
    calc
      _ = (↑hu.unit : D) * (↑(hu.unit⁻¹) : D) :=
        congrArg (fun c : D => c * (↑(hu.unit⁻¹) : D)) hu.unit_spec.symm
      _ = 1 := Units.mul_inv _
  let G : (Polynomial D) := F.map φ * Polynomial.C (↑(hu.unit⁻¹) : D)
  have hG : G.Monic := by
    apply monic_mul_C_of_leadingCoeff_mul_eq_one
    exact hlead.symm ▸ hinv
  have hscale : G * Polynomial.C (φ F.leadingCoeff) = F.map φ := by
    dsimp only [G]
    rw [mul_assoc, ← map_mul, mul_comm (↑(hu.unit⁻¹) : D), hinv, map_one, mul_one]
  have hnπ : π F ∣ (π g) ^ n := by
    have h := Ideal.mem_map_of_mem π (show g ^ n ∈ J from hn)
    rwa [hJπ, Ideal.mem_span_singleton, map_pow] at h
  have hnD : F.map φ ∣ (g.map φ) ^ n := by
    have h := map_dvd j hnπ
    rwa [map_pow, hj, hj] at h
  have hd := monic_dvd_derivative_mul_of_dvd_pow hG
    ((show G ∣ F.map φ from ⟨_, hscale.symm⟩).trans hnD)
  have hderiv : G.derivative * Polynomial.C (φ F.leadingCoeff) =
      (F.map φ).derivative := by
    simpa only [derivative_mul, derivative_C, mul_zero, add_zero]
      using congrArg derivative hscale
  have hdD : F.map φ ∣ (F.derivative * g).map φ := by
    obtain ⟨d, hd⟩ := hd
    refine ⟨d, ?_⟩
    rw [Polynomial.map_mul, ← derivative_map, ← hderiv, mul_right_comm, hd, mul_right_comm, hscale]
  have hmem : j (π (F.derivative * g)) ∈ (Ideal.span {π F}).map j := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, hj, hj]
    exact hdD
  obtain ⟨m, hm, hmJ⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((Submonoid.powers a).map (Polynomial.C : B →+* (Polynomial B))) (Polynomial D) _ _).mp hmem
  obtain ⟨b, hb, rfl⟩ := hm
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  have hkerle : RingHom.ker π ≤ J := by
    rw [hker, Ideal.span_singleton_le_iff_mem]
    apply Ideal.subset_span
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hcomap : (J.map π).comap π = J := by
    rw [Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerle]
  rw [← show J = Ideal.span {F, Polynomial.C q} from rfl, ← hcomap, Ideal.mem_comap, hJπ]
  simpa only [map_mul, map_pow, π, coe_mapRingHom, Polynomial.map_C, a] using hmJ
end
end K1_13_7_2_1_2
end
section
namespace K1_13_6_1_4_2_1_1_2
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem linear_cancel {R β : Type*} [CommRing R] (s : Finset β)
    (w : β → R) (b : β) (hb : b ∈ s) (hu : IsUnit (w b)) (p : MvPolynomial β R)
    (hp : p * (∑ j ∈ s, C (w j) * «X» j) = 0) : p = 0 := by
  classical
  let e := (renameEquiv R (Equiv.optionSubtypeNe b).symm).trans
    (optionEquivLeft R {j // j ≠ b})
  have hc (r : R) : e (C r) = Polynomial.C (C r) := by
    simp [e, renameEquiv_apply, optionEquivLeft_C]
  have hx (j : β) : (e («X» j)).coeff 1 = if j = b then 1 else 0 := by
    by_cases hj : j = b
    · subst j
      simp [e, renameEquiv_apply, optionEquivLeft_X_none]
    · simp [e, renameEquiv_apply, Equiv.optionSubtypeNe_symm_of_ne hj,
        optionEquivLeft_X_some, hj]
  have hcoef : (e (∑ j ∈ s, C (w j) * «X» j)).coeff 1 = C (w b) := by
    simp only [map_sum, map_mul, Polynomial.finsetSum_coeff, hc, Polynomial.coeff_C_mul, hx]
    rw [Finset.sum_eq_single_of_mem b hb]
    · simp
    · intro j _ hj
      simp [hj]
  have hregular : e (∑ j ∈ s, C (w j) * «X» j) ∈
      (Polynomial (MvPolynomial {j // j ≠ b} R))⁰ :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
      (hcoef ▸ (hu.map (C (σ := {j // j ≠ b}))).mem_nonZeroDivisors)
  apply e.injective
  rw [map_zero, ← mul_right_mem_nonZeroDivisors_eq_zero_iff hregular, ← map_mul, hp, map_zero]
private theorem cancel_over_unit {R α β : Type*} [CommRing R] (l : MvPolynomial α R)
    (s : Finset β) (w : β → R) (b : β) (hb : b ∈ s) (hu : IsUnit (w b))
    (p : MvPolynomial β (MvPolynomial α R))
    (hp : p * (∑ j ∈ s, C (C (w j)) * «X» j) ∈ Ideal.span {C l}) :
    p ∈ Ideal.span {C l} := by
  let I : Ideal (MvPolynomial α R) := Ideal.span {l}
  let q := Ideal.Quotient.mk I
  have hk : RingHom.ker (MvPolynomial.map (σ := β) q) = Ideal.span {C l} := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
  have hmul := RingHom.mem_ker.mp (hk.symm ▸ hp)
  rw [map_mul, map_sum] at hmul
  simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X] at hmul
  rw [← hk, RingHom.mem_ker]
  exact linear_cancel s (fun j => q (C (w j))) b hb ((hu.map C).map q) _ hmul
theorem cancel_chart {R α β : Type*} [CommRing R] (l : MvPolynomial α R)
    (s : Finset β) (w : β → R) (b : β) (hb : b ∈ s) (a : R)
    (p : MvPolynomial β (MvPolynomial α R))
    (hp : p * (∑ j ∈ s, C (C (w j)) * «X» j) ∈ Ideal.span {C l}) :
    ∃ n : ℕ, (C (C (a * w b))) ^ n * p ∈ Ideal.span {C l} := by
  let z := a * w b
  let T := Localization.Away z
  let q := algebraMap R T
  let B := MvPolynomial β (MvPolynomial α T)
  let M := ((Submonoid.powers z).map (C (σ := α))).map (C (σ := β))
  let g := algebraMap (MvPolynomial β (MvPolynomial α R)) B
  have hloc : IsLocalization M B := MvPolynomial.isLocalization _ _
  have hu : IsUnit (q (w b)) := by
    have hz : IsUnit (q z) := IsLocalization.map_units T ⟨z, Submonoid.mem_powers _⟩
    change IsUnit (q (a * w b)) at hz
    rw [map_mul] at hz
    exact isUnit_of_mul_isUnit_right hz
  have hmap : (Ideal.span {C l}).map g = Ideal.span {C (MvPolynomial.map q l)} := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {MvPolynomial.map (MvPolynomial.map q) (C l)} = _
    rw [MvPolynomial.map_C]
  have hmem := Ideal.mem_map_of_mem g hp
  rw [hmap, map_mul] at hmem
  change g p * MvPolynomial.map (MvPolynomial.map q) (∑ j ∈ s, C (C (w j)) * «X» j) ∈ _ at hmem
  simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X] at hmem
  have h := cancel_over_unit (MvPolynomial.map q l) s (q ∘ w) b hb hu (g p) hmem
  rw [← hmap] at h
  obtain ⟨d, hd, hdp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M B
    (Ideal.span {C l}) p).mp h
  obtain ⟨e, he, rfl⟩ := Submonoid.mem_map.mp hd
  obtain ⟨f, hf, rfl⟩ := Submonoid.mem_map.mp he
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hf
  exact ⟨n, by simpa only [map_pow] using hdp⟩
theorem cancel_localization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (I : Ideal A) (z r : A)
    (h : ∀ p : A, p * r ∈ I → ∃ n : ℕ, z ^ n * p ∈ I)
    (q : B) (hq : q * algebraMap A B r ∈ I.map (algebraMap A B)) :
    ∃ n : ℕ, (algebraMap A B z) ^ n * q ∈ I.map (algebraMap A B) := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj M q
  have hp : algebraMap A B (p * r) ∈ I.map (algebraMap A B) := by
    rw [map_mul, ← hs]
    have hmul : algebraMap A B s * (q * algebraMap A B r) ∈ I.map (algebraMap A B) :=
      Ideal.mul_mem_left _ _ hq
    convert hmul using 1
    ac_rfl
  obtain ⟨d, hd, hdp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M B I _).mp hp
  rw [← mul_assoc] at hdp
  obtain ⟨n, hn⟩ := h (d * p) hdp
  refine ⟨n, ?_⟩
  have he := Ideal.mem_map_of_mem (algebraMap A B) hn
  rw [map_mul, map_pow, map_mul, ← hs] at he
  have hu := (IsLocalization.map_units B ⟨d, hd⟩).mul (IsLocalization.map_units B s)
  have he' : (algebraMap A B d * algebraMap A B s) * ((algebraMap A B z) ^ n * q) ∈
      I.map (algebraMap A B) := by
    convert he using 1
    ac_rfl
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp he'
end
end K1_13_6_1_4_2_1_1_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3_3
noncomputable section
open MvPolynomial Filter
open scoped BigOperators
variable {k σ τ F E : Type} [Field k] [Finite σ] [Finite τ]
variable [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E]
variable {P : Ideal (MvPolynomial σ k)} {Q : Ideal (MvPolynomial τ k)}
local notation "A" => MvPolynomial τ k ⧸ Q
local notation "B" => MvPolynomial σ k ⧸ P
theorem lower_bound (g : A →ₐ[k] B) (i : A →ₐ[k] F) (j : B →ₐ[k] E)
    (hi : Function.Injective i) (hcomm : ∀ a, j (g a) = algebraMap F E (i a))
    (hg : ∀ t, g (Ideal.Quotient.mk Q (MvPolynomial.X t)) ∈ quotientDegreeLE P 1)
    {ι : Type} [Fintype ι] (e : Module.Basis ι F E)
    (u : ι → B) (hu : ∀ l, j (u l) = e l) :
    ∃ C : ℕ, ∀ n : ℕ, Fintype.card ι * affineHilbertFunction Q n ≤
      affineHilbertFunction P (n + C) := by
  classical
  choose d hd using fun l => exists_mem_quotientDegreeLE P (u l)
  obtain ⟨C, hC⟩ := Finite.exists_le d
  refine ⟨C, fun n => ?_⟩
  let T : (ι → quotientDegreeLE Q n) →ₗ[k] B :=
    ∑ l, (LinearMap.mulRight k (u l)).comp
      (g.toLinearMap.comp ((quotientDegreeLE Q n).subtype.comp (LinearMap.proj l)))
  have hT (x : ι → quotientDegreeLE Q n) : T x = ∑ l, g (x l) * u l := by
    simp [T]
  let S := T.codRestrict (quotientDegreeLE P (n + C)) fun x => by
    rw [hT]
    refine Submodule.sum_mem _ fun l _ => mul_mem_quotientDegreeLE ?_ ?_
    · simpa only [one_mul] using map_mem_quotientDegreeLE g hg (x l).property
    · exact quotientDegreeLE_mono P (hC l) (hd l)
  have hcoords (x : ι → quotientDegreeLE Q n) :
      j (T x) = e.equivFun.symm (fun l => i (x l)) := by
    simp only [hT, map_sum, map_mul, hcomm, hu, Module.Basis.equivFun_symm_apply, Algebra.smul_def]
  have hinj : Function.Injective S := by
    intro x y h
    have h' : T x = T y := congrArg Subtype.val h
    have h'' := e.equivFun.symm.injective ((hcoords x).symm.trans ((congrArg j h').trans (hcoords y)))
    exact funext fun l => Subtype.ext (hi (congrFun h'' l))
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
variable [IsScalarTower k F E]
omit [Finite σ] in
theorem upper_bound (g : A →ₐ[k] B) (i : A →ₐ[k] F) (j : B →ₐ[k] E)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hcomm : ∀ a, j (g a) = algebraMap F E (i a))
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : Module.Basis ι F E)
    (v : κ → B)
    (hgen : ∀ n (x : B), x ∈ quotientDegreeLE P n → ∃ a : κ → A,
      (∀ l, a l ∈ quotientDegreeLE Q n) ∧ ∑ l, g (a l) * v l = x)
    {d : F} (hd : d ≠ 0) (b : κ → ι → A)
    (hb : ∀ l r, i (b l r) = d * e.equivFun (j (v l)) r) :
    ∃ C : ℕ, ∀ n : ℕ, affineHilbertFunction P n ≤
      Fintype.card ι * affineHilbertFunction Q (n + C) := by
  classical
  choose levels hlevels using fun s : κ × ι => exists_mem_quotientDegreeLE Q (b s.1 s.2)
  obtain ⟨C, hC⟩ := Finite.exists_le levels
  refine ⟨C, fun n => ?_⟩
  let W := (quotientDegreeLE Q (n + C)).map i.toLinearMap
  let T (r : ι) : B →ₗ[k] F :=
    (LinearMap.mulLeft k d).comp (((LinearMap.proj r).comp
      e.equivFun.toLinearMap).restrictScalars k |>.comp j.toLinearMap)
  have hT (r : ι) (x : B) : T r x = d * e.equivFun (j x) r := rfl
  have hmem (r : ι) (x : quotientDegreeLE P n) : T r x ∈ W := by
    obtain ⟨a, ha, hax⟩ := hgen n x x.property
    refine Submodule.mem_map.mpr ⟨∑ l, a l * b l r, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun l _ =>
        mul_mem_quotientDegreeLE (ha l) (quotientDegreeLE_mono Q (hC (l, r)) (hlevels (l, r)))
    · change i (∑ l, a l * b l r) = T r x
      have hm (l : κ) : j (g (a l) * v l) = (i (a l)) • j (v l) := by
        rw [map_mul, hcomm, Algebra.smul_def]
      rw [hT, ← hax, map_sum, map_sum, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, hb, hm, map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  let S : quotientDegreeLE P n →ₗ[k] (ι → W) :=
    LinearMap.pi fun r => ((T r).domRestrict _).codRestrict W (hmem r)
  have hinj : Function.Injective S := by
    intro x y h
    apply Subtype.ext
    apply hj
    apply e.equivFun.injective
    funext r
    apply mul_left_cancel₀ hd
    exact congrArg (fun f : ι → W => (f r : F)) h
  have hrw : Module.finrank k W = affineHilbertFunction Q (n + C) :=
    (Submodule.equivMapOfInjective i.toLinearMap hi (quotientDegreeLE Q (n + C))).finrank_eq.symm
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hrw] at h
theorem degree_of_bounds {d C₁ C₂ : ℕ} (hd : d ≠ 0)
    (hdeg : (affineHilbertPolynomial P).natDegree = (affineHilbertPolynomial Q).natDegree)
    (hl : ∀ n, d * affineHilbertFunction Q n ≤ affineHilbertFunction P (n + C₁))
    (hu : ∀ n, affineHilbertFunction P n ≤ d * affineHilbertFunction Q (n + C₂)) :
    affineDegree P = (d : ℚ) * affineDegree Q := by
  open Polynomial in
  let HS := affineHilbertPolynomial P
  let HT := Polynomial.C (d : ℚ) * affineHilbertPolynomial Q
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hdeg' : HS.natDegree = HT.natDegree := by
    rw [show HT.natDegree = (affineHilbertPolynomial Q).natDegree from natDegree_C_mul hd']
    exact hdeg
  have hshift (c : ℕ) : Tendsto (fun n : ℕ => n + c) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n c) tendsto_id
  have hS : ∀ᶠ n : ℕ in atTop, HS.eval (n : ℚ) = affineHilbertFunction P n :=
    eventually_eval_affineHilbertPolynomial _
  have hT : ∀ᶠ n : ℕ in atTop, HT.eval (n : ℚ) = (d * affineHilbertFunction Q n : ℕ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial Q] with n hn
    simp [HT, hn]
  have hlo : ∀ᶠ n : ℕ in atTop, HT.eval (n : ℚ) ≤ (taylor (C₁ : ℚ) HS).eval (n : ℚ) := by
    filter_upwards [hT, (hshift C₁).eventually hS] with n hn hn'
    rw [taylor_eval, ← Nat.cast_add, hn, hn']
    exact_mod_cast hl n
  have hup : ∀ᶠ n : ℕ in atTop, HS.eval (n : ℚ) ≤ (taylor (C₂ : ℚ) HT).eval (n : ℚ) := by
    filter_upwards [hS, (hshift C₂).eventually hT] with n hn hn'
    rw [taylor_eval, ← Nat.cast_add, hn, hn']
    exact_mod_cast hu n
  have hTpos : ∀ᶠ n : ℕ in atTop, 0 ≤ HT.eval (n : ℚ) :=
    hT.mono fun n h => h.symm ▸ Nat.cast_nonneg (α := ℚ) (d * affineHilbertFunction Q n)
  have lc₁ := (natDegree_le_of_eventually_eval_natCast_le hTpos hlo).2
    (hdeg'.symm.trans (natDegree_taylor _ _).symm)
  have lc₂ := (natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg P) hup).2
    (hdeg'.trans (natDegree_taylor _ _).symm)
  rw [leadingCoeff_taylor] at lc₁ lc₂
  have he := lc₂.antisymm lc₁
  change (HS.natDegree.factorial : ℚ) * HS.leadingCoeff =
    (d : ℚ) * ((((affineHilbertPolynomial Q).natDegree.factorial : ℕ) : ℚ) *
      (affineHilbertPolynomial Q).leadingCoeff)
  rw [show HS.natDegree = (affineHilbertPolynomial Q).natDegree from hdeg, he,
    show HT.leadingCoeff = _ from leadingCoeff_C_mul_of_isUnit hd'.isUnit _]
  ring
end
end K1_13_6_3_5_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_1_1
noncomputable section
open scoped TensorProduct
private theorem quotient_reduced_of_fiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (q : Ideal R) [q.IsPrime]
    (h : IsReduced (S ⊗[R] q.ResidueField)) :
    IsReduced (S ⧸ q.map (algebraMap R S)) := by
  let f : (R ⧸ q) →ₐ[R] q.ResidueField := IsScalarTower.toAlgHom R _ _
  have hf : Function.Injective f := Ideal.injective_algebraMap_quotient_residueField q
  let e := Algebra.TensorProduct.map (AlgHom.id R S) f
  have he : Function.Injective e :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S) f.toLinearMap hf
  have : IsReduced (S ⊗[R] (R ⧸ q)) := isReduced_of_injective e he
  let baseChange := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S q
  exact isReduced_of_injective baseChange baseChange.injective
variable {k E R S : Type*} [Field k] [Field E] [CommRing R] [CommRing S]
  [Algebra k E] [Algebra k R] [Algebra k S] [Algebra R S] [Algebra E S]
  [IsScalarTower k R S] [IsScalarTower k E S] [Algebra.IsPushout k R E S]
  [IsPurelyInseparable k E]
include k E in
private theorem algebraMap_power (x : S) :
    ∃ n > 0, ∃ y : R, algebraMap R S y = x ^ n := by
  let e := Algebra.IsPushout.equiv k R E S
  obtain ⟨n, hn, y, hy⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct (e.symm x)
  refine ⟨n, hn, y, ?_⟩
  simpa [Algebra.TensorProduct.algebraMap_apply, Algebra.IsPushout.equiv_tmul, e] using
    congrArg e hy
include k E in
private theorem localization_at_contraction (P : Ideal S) [P.IsPrime]
    (q : Ideal R) [q.IsPrime] (hq : q = P.comap (algebraMap R S)) :
    IsLocalization (Algebra.algebraMapSubmonoid S q.primeCompl) (Localization.AtPrime P) := by
  let M := Algebra.algebraMapSubmonoid S q.primeCompl
  have hle : M ≤ P.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    apply Ideal.mem_primeCompl_iff.mpr
    intro hp
    apply Ideal.mem_primeCompl_iff.mp hx
    rw [hq]
    exact hp
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := Localization.AtPrime P) M
    P.primeCompl hle ?_).mpr inferInstance
  intro x hx
  obtain ⟨n, hn, y, hy⟩ := algebraMap_power (k := k) (E := E) (R := R) x
  refine ⟨x ^ n, ⟨y, ?_, hy⟩, dvd_pow_self x hn.ne'⟩
  change y ∉ q
  rw [hq, Ideal.mem_comap, hy]
  exact P.primeCompl.pow_mem hx _
include k E in
private def localFiberEquiv (P : Ideal S) [P.IsPrime]
    (q : Ideal R) [q.IsPrime] (hq : q = P.comap (algebraMap R S)) :
    let L := Localization.AtPrime P
    S ⊗[R] q.ResidueField ≃+* L ⧸ (q.map (algebraMap R S)).map (algebraMap S L) := by
  let L := Localization.AtPrime P
  let M := Algebra.algebraMapSubmonoid S q.primeCompl
  let B := Localization M
  letI : IsLocalization M L := localization_at_contraction (k := k) (E := E) P q hq
  let e := IsLocalization.algEquiv M B L
  letI : Algebra S (q.Fiber S) := Algebra.TensorProduct.rightAlgebra
  refine (Algebra.TensorProduct.comm R S q.ResidueField).toRingEquiv.trans ?_
  refine (Ideal.Fiber.algEquivAux₁ (S := S) q).toRingEquiv.trans ?_
  refine Ideal.quotientEquiv _ _ e.toRingEquiv ?_
  have hcomp : e.toRingEquiv.toRingHom.comp (algebraMap S B) = algebraMap S L :=
    RingHom.ext e.commutes
  exact ((Ideal.map_map (algebraMap S B) e.toRingEquiv.toRingHom).trans
    (congrArg (q.map (algebraMap R S)).map hcomp)).symm
include k E in
theorem descent_of_local_equality (P : Ideal S) [P.IsPrime]
    (h : let L := Localization.AtPrime P
      ((P.comap (algebraMap R S)).map (algebraMap R S)).map (algebraMap S L) =
        IsLocalRing.maximalIdeal L) :
    (P.comap (algebraMap R S)).map (algebraMap R S) = P := by
  let q := P.comap (algebraMap R S)
  have : q.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime P
  let e : S ⊗[R] q.ResidueField ≃+* IsLocalRing.ResidueField L :=
    (localFiberEquiv (k := k) (E := E) P q rfl).trans (Ideal.quotEquivOfEq h)
  have hred : IsReduced (S ⊗[R] q.ResidueField) :=
    isReduced_of_injective e e.injective
  have hpush : Algebra.IsPushout k R E S := inferInstance
  have : Module.Flat R S := Module.Flat.isBaseChange k R E S hpush.out
  let J := q.map (algebraMap R S)
  have hrad : J.IsRadical := (Ideal.isRadical_iff_quotient_reduced J).mpr
    (quotient_reduced_of_fiber q hred)
  refine le_antisymm Ideal.map_comap_le ?_
  intro x hx
  obtain ⟨n, hn, y, hy⟩ := algebraMap_power (k := k) (E := E) (R := R) x
  have hyq : y ∈ q := by
    change algebraMap R S y ∈ P
    rw [hy]
    exact P.pow_mem_of_mem hx n hn
  exact hrad ⟨n, hy ▸ Ideal.mem_map_of_mem (algebraMap R S) hyq⟩
end
end K1_13_6_3_1_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_1
open scoped Polynomial
open MvPolynomial
private theorem infinite_good_slopes {k A : Type} [Field k] [Infinite k]
    [CommRing A] [Algebra k A] (y v : A)
    (hvar : ¬ IsAlgebraic k y ∨ ¬ IsAlgebraic k v) :
    {t : k | ¬ IsAlgebraic k (y + algebraMap k A t * v)}.Infinite := by
  apply Set.infinite_of_finite_compl
  apply Set.Subsingleton.finite
  intro t ht u hu
  change ¬ ¬ IsAlgebraic k (y + algebraMap k A t * v) at ht
  change ¬ ¬ IsAlgebraic k (y + algebraMap k A u * v) at hu
  by_contra htu
  have ht' := isAlgebraic_iff_isIntegral.mp (not_not.mp ht)
  have hu' := isAlgebraic_iff_isIntegral.mp (not_not.mp hu)
  have hdiff : IsIntegral k (algebraMap k A (t - u) * v) := by
    convert ht'.sub hu' using 1
    rw [map_sub]
    ring
  have hv : IsIntegral k v := by
    have h := (isIntegral_algebraMap (R := k) (A := A) (x := (t - u)⁻¹)).mul hdiff
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr htu), map_one, one_mul] at h
    exact h
  have hy : IsIntegral k y := by
    have h := ht'.sub ((isIntegral_algebraMap (R := k) (A := A) (x := t)).mul hv)
    rwa [add_sub_cancel_right] at h
  exact hvar.elim (fun h => h hy.isAlgebraic) (fun h => h hv.isAlgebraic)
theorem parameter_injective_of_varying {k A : Type} [Field k] [Infinite k]
    [CommRing A] [Algebra k A] (y v : A)
    (hvar : ¬ IsAlgebraic k y ∨ ¬ IsAlgebraic k v) :
    Function.Injective (MvPolynomial.eval₂Hom (σ := Fin 2)
      (Polynomial.C.comp (algebraMap k A))
      ![Polynomial.X, Polynomial.C y + Polynomial.X * Polynomial.C v]) := by
  let f : MvPolynomial (Fin 2) k →+* (Polynomial A) :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k A))
      ![Polynomial.X, Polynomial.C y + Polynomial.X * Polynomial.C v]
  apply (injective_iff_map_eq_zero f).mpr
  intro P hP
  let good : Set k := {t | ¬ IsAlgebraic k (y + algebraMap k A t * v)}
  let box : Fin 2 → Set k := ![good, Set.univ]
  have hbox (i : Fin 2) : (box i).Infinite := by
    fin_cases i
    · exact infinite_good_slopes y v hvar
    · exact Set.infinite_univ
  apply MvPolynomial.funext_set box hbox
  intro a ha
  have ht : a 0 ∈ good := ha 0 (Set.mem_univ _)
  let intercept := y + algebraMap k A (a 0) * v
  let fixSlope : MvPolynomial (Fin 2) k →+* (Polynomial k) :=
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C (a 0), Polynomial.X]
  have hfix : (Polynomial.aeval intercept).toRingHom.comp fixSlope =
      (Polynomial.evalRingHom (algebraMap k A (a 0))).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [fixSlope, f]
    · intro i
      fin_cases i
      · simp [fixSlope, f, intercept]
      · simp [fixSlope, f, intercept]
        exact mul_comm _ _
  have hfixP : fixSlope P = 0 := by
    apply (transcendental_iff_injective.mp ht)
    change ((Polynomial.aeval intercept).toRingHom.comp fixSlope) P = _
    rw [hfix]
    simp [hP]
  have heval : (Polynomial.evalRingHom (a 1)).comp fixSlope = MvPolynomial.eval a := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [fixSlope]
    · intro i
      fin_cases i <;> simp [fixSlope]
  rw [← heval]
  simp [hfixP]
theorem affine_dimension {k A : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) ∧ Algebra.trdeg k A = (n : Cardinal) := by
  obtain ⟨n, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin n) k
  let : Algebra B A := g.toRingHom.toAlgebra
  let : IsScalarTower k B A := IsScalarTower.of_algHom g
  have : Module.Finite B A := hg_fin
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg_inj
  have hdim : ringKrullDim B = (n : WithBot ℕ∞) := by
    simp [B, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  refine ⟨n, ?_, ?_⟩
  · apply le_antisymm
    · rw [← hdim]
      apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B A))
      intro a b hab
      exact Ideal.IsIntegral.under_lt_under (R := B) (show a.asIdeal < b.asIdeal from hab)
    · obtain ⟨l, hlen⟩ := Order.le_krullDim_iff.mp hdim.ge
      have := l.head.isPrime
      have hle : (⊥ : Ideal A).under B ≤ l.head.asIdeal := by
        change Ideal.comap (algebraMap B A) ⊥ ≤ l.head.asIdeal
        rw [← RingHom.ker_eq_comap_bot,
          (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
        exact bot_le
      obtain ⟨P, _, hP, hPhead⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
        (⊥ : Ideal A) hle
      let : P.IsPrime := hP
      let : P.LiesOver l.head.asIdeal := ⟨hPhead.symm⟩
      obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
      exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hlen⟩
  · have h := trdeg_add_eq k B (A := A)
    rw [trdeg_eq_zero (R := B) (A := A), add_zero] at h
    simpa [B, MvPolynomial.trdeg_of_isDomain] using h.symm
theorem parameter_field_trdeg (k : Type) [Field k] :
    Algebra.trdeg k (FractionRing (MvPolynomial (Fin 2) k)) = 2 := by
  let P := MvPolynomial (Fin 2) k
  let F := FractionRing P
  have : Algebra.IsAlgebraic P F := IsLocalization.isAlgebraic _ (nonZeroDivisors P)
  have : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective P F).mpr
    (IsFractionRing.injective P F)
  rw [← trdeg_add_eq k P (A := F), trdeg_eq_zero (R := P) (A := F), add_zero]
  simp [P]
theorem affine_slice_dimension {k E A B : Type}
    [Field k] [Field E] [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra k E] [Algebra k A] [Algebra k B] [Algebra E B] [IsScalarTower k E B]
    [Algebra.FiniteType k A] [Algebra.FiniteType E B]
    (f : (Polynomial A) →ₐ[k] B) (hf : Function.Injective f)
    (hAlg : let : Algebra (Polynomial A) B := f.toRingHom.toAlgebra; Algebra.IsAlgebraic (Polynomial A) B)
    (hE : Algebra.trdeg k E = 2) (d : ℕ)
    (hdim : ringKrullDim A = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim B = (d : WithBot ℕ∞) := by
  let : Algebra (Polynomial A) B := f.toRingHom.toAlgebra
  let : IsScalarTower k (Polynomial A) B := IsScalarTower.of_algHom f
  have : FaithfulSMul (Polynomial A) B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  have : Algebra.IsAlgebraic (Polynomial A) B := hAlg
  obtain ⟨n, hdimA, htrdegA⟩ := affine_dimension (k := k) (A := A)
  obtain ⟨m, hdimB, htrdegB⟩ := affine_dimension (k := E) (A := B)
  have hn : n = d + 1 := by exact_mod_cast hdimA.symm.trans hdim
  have hSlope := trdeg_add_eq k A (A := (Polynomial A))
  rw [htrdegA, Polynomial.trdeg_of_isDomain] at hSlope
  have hSlice := trdeg_add_eq k (Polynomial A) (A := B)
  rw [trdeg_eq_zero (R := (Polynomial A)) (A := B), add_zero, ← hSlope] at hSlice
  have h := trdeg_add_eq k E (A := B)
  rw [hE, htrdegB, ← hSlice] at h
  have hm : (2 + m : ℕ) = n + 1 := by exact_mod_cast h
  rw [hdimB, show m = d by omega]
end K1_14_2_2_7_4_1
end
section
namespace K1_14_2_2_5_1
noncomputable section
open Polynomial
variable {M E : Type*} [Field M] [Field E] [Algebra M E]
def genericLine (x y : E) : MvPolynomial (Fin 3) M →+* MvPolynomial (Fin 2) E :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap M E))
    ![MvPolynomial.X 0, MvPolynomial.X 1,
      MvPolynomial.C x + MvPolynomial.X 0 * MvPolynomial.C y]
private theorem algebraic_of_specialization (x y : E) (P : MvPolynomial (Fin 3) M)
    (hP : genericLine x y P = 0) (b : Fin 3 → M) (hb : MvPolynomial.eval b P ≠ 0) :
    IsAlgebraic M (x + algebraMap M E (b 0) * y) := by
  let f : MvPolynomial (Fin 3) M →+* (Polynomial M) :=
    MvPolynomial.eval₂Hom C ![C (b 0), C (b 1), «X»]
  let v : E := x + algebraMap M E (b 0) * y
  have he : (evalRingHom (b 2)).comp f = MvPolynomial.eval b := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f]
    · intro i
      fin_cases i <;> simp [f]
  have hf : f P ≠ 0 := by
    intro hz
    apply hb
    rw [← he, RingHom.comp_apply, hz, map_zero]
  let s : MvPolynomial (Fin 2) E →+* E :=
    MvPolynomial.eval ![algebraMap M E (b 0), algebraMap M E (b 1)]
  have hs : (aeval v).toRingHom.comp f = s.comp (genericLine x y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f, s, genericLine]
    · intro i
      fin_cases i <;> simp [f, s, genericLine, v]
  refine ⟨f P, hf, ?_⟩
  change ((aeval v).toRingHom.comp f) P = 0
  rw [hs, RingHom.comp_apply, hP, map_zero]
theorem genericLine_injective [Infinite M] (x y : E)
    (ht : ¬ (IsAlgebraic M x ∧ IsAlgebraic M y)) :
    Function.Injective (genericLine (M := M) x y) := by
  classical
  apply (injective_iff_map_eq_zero (genericLine (M := M) x y)).mpr
  intro P hP
  by_contra hp
  have hex (Q : MvPolynomial (Fin 3) M) (hQ : Q ≠ 0) :
      ∃ b : Fin 3 → M, MvPolynomial.eval b Q ≠ 0 := by
    by_contra! h
    apply hQ
    exact MvPolynomial.funext (fun b => by rw [h b, map_zero])
  obtain ⟨b, hb⟩ := hex P hp
  have hlin : (MvPolynomial.X 0 - MvPolynomial.C (b 0) : MvPolynomial (Fin 3) M) ≠ 0 :=
    fun h => by
      have he := congrArg (MvPolynomial.eval ![b 0 + 1, (0 : M), 0]) h
      simp at he
  obtain ⟨d, hd⟩ := hex (P * (MvPolynomial.X 0 - MvPolynomial.C (b 0))) (mul_ne_zero hp hlin)
  have hd' : MvPolynomial.eval d P * (d 0 - b 0) ≠ 0 := by simpa using hd
  have hdb := right_ne_zero_of_mul hd'
  have hb_alg := algebraic_of_specialization x y P hP b hb
  have hd_alg := algebraic_of_specialization x y P hP d (left_ne_zero_of_mul hd')
  have hdiff : IsAlgebraic M (algebraMap M E (d 0 - b 0) * y) := by
    have h := hd_alg.sub hb_alg
    convert h using 1
    rw [map_sub]
    ring
  have hy : IsAlgebraic M y := by
    have h := (isAlgebraic_algebraMap (A := E) ((d 0 - b 0)⁻¹)).mul hdiff
    have hn : algebraMap M E (d 0 - b 0) ≠ 0 :=
      (map_ne_zero_iff (algebraMap M E) (algebraMap M E).injective).mpr hdb
    rw [map_inv₀, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] at h
    exact h
  have hx : IsAlgebraic M x := by
    simpa using hb_alg.sub ((isAlgebraic_algebraMap (A := E) (b 0)).mul hy)
  exact ht ⟨hx, hy⟩
end
end K1_14_2_2_5_1
end
section
namespace K1_13_7_5_1
open Polynomial Algebra TensorProduct
noncomputable section
variable {A : Type*} [CommRing A]
abbrev LeadingChart (F : (Polynomial A)) := Localization.Away (AdjoinRoot.of F F.leadingCoeff)
theorem leadingChart_flat [IsDomain A] (F : (Polynomial A)) (hF : F.leadingCoeff ≠ 0) :
    Module.Flat A (LeadingChart F) := by
  let a := F.leadingCoeff
  let R := Localization.Away a
  let : IsDomain R := Localization.Away.isDomain hF
  let p := F.map (algebraMap A R)
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := R) a
  let g := C (↑u⁻¹ : R) * p
  have hg : g.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    change (↑u⁻¹ : R) * (F.map (algebraMap A R)).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ (hu ▸ Units.ne_zero u),
      ← hu, Units.inv_mul]
  let q := F.map (Algebra.TensorProduct.includeRight : A →ₐ[A] R ⊗[A] A).toRingHom
  let e := Algebra.TensorProduct.rid A R R
  have hq : q.map e = p := by
    rw [show q = F.map (Algebra.TensorProduct.includeRight : A →ₐ[A] R ⊗[A] A).toRingHom from rfl,
      Polynomial.map_map]
    congr 1
    apply RingHom.ext
    intro x
    change e (1 ⊗ₜ[A] x) = algebraMap A R x
    simp [e, Algebra.smul_def]
  have hassoc : Associated (q.map e) g := by
    rw [hq]
    exact associated_unit_mul_right _ _ (IsUnit.map Polynomial.C (u⁻¹).isUnit)
  let e₀ : R ⊗[A] AdjoinRoot F ≃ₐ[A] LeadingChart F := by
    let : Algebra (AdjoinRoot F) (R ⊗[A] AdjoinRoot F) := Algebra.TensorProduct.rightAlgebra
    exact (IsLocalization.Away.tensorRightEquiv (R := A) (A := R) (r := a)
      (AdjoinRoot F)).restrictScalars A
  let e₁ : R ⊗[A] AdjoinRoot F ≃ₐ[R] AdjoinRoot q := AdjoinRoot.tensorAlgEquiv F q rfl
  let e₂ : AdjoinRoot q ≃ₐ[R] AdjoinRoot g := AdjoinRoot.mapAlgEquiv e q g hassoc
  let : Module.Free R (AdjoinRoot g) := hg.free_adjoinRoot
  let : Module.Flat R (AdjoinRoot g) := Module.Flat.of_free
  let : Module.Flat A (AdjoinRoot g) := Module.Flat.trans A R (AdjoinRoot g)
  exact Module.Flat.of_linearEquiv (e₀.symm.trans ((e₁.trans e₂).restrictScalars A)).toLinearEquiv
end
end K1_13_7_5_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 750000
namespace K1_14_3R_3_1_3_1
open scoped BigOperators nonZeroDivisors
open Module
abbrev FrobeniusRing (A : Type) [CommRing A] (p n : ℕ) [ExpChar A p] :=
  (iterateFrobenius A p n).range
def FrobeniusLattices (A : Type) [CommRing A] : Prop :=
  ∀ (p n : ℕ) [ExpChar A p] (w : Finset A),
    ∃ T : Submodule (FrobeniusRing A p n) A, T.FG ∧ (w : Set A) ⊆ T ∧
      ∀ (s : FrobeniusRing A p n) (a : A), s ≠ 0 → s • a ∈ T → a ∈ T
theorem finite_normalization (A K L : Type) [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hA : FrobeniusLattices A) : Module.Finite A (integralClosure A L) := by
  classical
  let E := separableClosure K L
  let B := integralClosure A L
  let C := integralClosure A E
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite A C := IsIntegralClosure.finite A K E C
  have : IsTorsionFree A E := .trans_faithfulSMul A K E
  have : Module.Free A C := IsIntegralClosure.module_free A K E C
  let p := ringExpChar L
  have : ExpChar L p := ringExpChar.expChar L
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : ExpChar A p := (algebraMap A L).expChar hAL p
  have : ExpChar E p := (algebraMap E L).expChar (algebraMap E L).injective p
  let n := IsPurelyInseparable.exponent E L
  let S := FrobeniusRing A p n
  let σ : A →+* S := (iterateFrobenius A p n).rangeRestrict
  let e : A ≃+* S := RingEquiv.ofBijective σ
    ⟨fun _ _ h => iterateFrobenius_inj A p n (congrArg Subtype.val h),
      (iterateFrobenius A p n).rangeRestrict_surjective⟩
  have : RingHomInvPair (e : A →+* S) (e.symm : S →+* A) := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair (e.symm : S →+* A) (e : A →+* S) := RingHomInvPair.of_ringEquiv e.symm
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv A e
  let φ : L →+* E := IsPurelyInseparable.iterateFrobenius E L p (n := n) le_rfl
  have hφ (b : L) : algebraMap E L (φ b) = b ^ p ^ n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius E p le_rfl b
  have hmem (b : B) : φ b.val ∈ integralClosure A E := by
    change IsIntegral A (φ b.val)
    apply (IntermediateField.coe_isIntegral_iff (R := A)).mp
    change IsIntegral A (algebraMap E L (φ b.val))
    rw [hφ]
    exact (show IsIntegral A b.val from b.property).pow _
  let g : B →+* C :=
    (φ.comp (integralClosure A L).val.toRingHom).codRestrict (integralClosure A E).toSubring hmem
  let f : B →ₛₗ[(e : A →+* S)] C :=
    { g with
      map_smul' a b := by
        apply Subtype.ext
        apply (algebraMap E L).injective
        change algebraMap E L (φ (a • b.val)) =
          algebraMap E L ((a ^ p ^ n) • φ b.val)
        simp only [Algebra.smul_def]
        rw [hφ, mul_pow, map_mul, ← IsScalarTower.algebraMap_apply A E L, map_pow, hφ] }
  have hf : Function.Injective f := by
    intro b b' hb
    apply Subtype.ext
    apply iterateFrobenius_inj L p n
    change b.val ^ p ^ n = b'.val ^ p ^ n
    rw [← hφ, ← hφ]
    exact congrArg (fun c : C => algebraMap E L c.val) hb
  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let J := Module.Free.ChooseBasisIndex A C
  let v : Basis J A C := Module.Free.chooseBasis A C
  let w (i : ι) : B := ⟨b i, hb i⟩
  let r : B →ₛₗ[(e : A →+* S)] (J → A) :=
    (v.equivFun.toLinearMap.restrictScalars S).comp f
  have hr : Function.Injective r := v.equivFun.injective.comp hf
  let coeffs := (Finset.univ : Finset (ι × J)).image (fun ij => r (w ij.1) ij.2)
  obtain ⟨T, hT, hcoeffs, hsat⟩ := hA p n coeffs
  have hw (i : ι) (j : J) : r (w i) j ∈ T :=
    hcoeffs (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  have hr_mem (z : B) (j : J) : r z j ∈ T := by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite A⁰ (b.repr z.val)
    choose a ha using hd
    have hdenom : (d : A) • z = ∑ i, a i • w i := by
      apply Subtype.ext
      change (d : A) • z.val = (integralClosure A L).val (∑ i, a i • w i)
      rw [map_sum]
      calc
        _ = ∑ i, (b.repr ((d : A) • z.val) i) • b i := (b.sum_repr _).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          have hrepr : b.repr ((d : A) • z.val) i = algebraMap A K (a i) := by
            rw [← IsScalarTower.algebraMap_smul K (d : A) z.val,
              LinearEquiv.map_smul, Finsupp.smul_apply]
            exact (IsScalarTower.algebraMap_smul K (d : A) _).trans (ha i).symm
          rw [hrepr]
          exact IsScalarTower.algebraMap_smul K (a i) (b i)
    have hd0 : (e : A →+* S) d ≠ 0 :=
      e.map_ne_zero_iff.mpr (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
    apply hsat ((e : A →+* S) d) _ hd0
    have h := congrFun (congrArg r hdenom) j
    simp only [map_smulₛₗ, map_sum, Pi.smul_apply, Finset.sum_apply] at h
    rw [h]
    exact Submodule.sum_mem T (fun i _ => T.smul_mem _ (hw i j))
  have : Module.Finite S T := Module.Finite.of_fg hT
  let q : B →ₛₗ[(e : A →+* S)] (J → T) :=
    { toFun := fun z j => ⟨r z j, hr_mem z j⟩
      map_add' := fun a b => by
        ext j
        exact congrFun (map_add r a b) j
      map_smul' := fun a b => by
        ext j
        exact congrFun (map_smulₛₗ r a b) j }
  apply Module.Finite.of_injective q
  intro a b hab
  exact hr (funext fun j => congrArg (fun u : J → T => (u j : A)) hab)
end K1_14_3R_3_1_3_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 750000
namespace K1_14_3R_3_1_3_1
open Polynomial
open scoped Polynomial
theorem polynomial_frobenius_lattices (k : Type) [Field k] : FrobeniusLattices (Polynomial k) := by
  classical
  intro p n _ w
  have : ExpChar k p := Polynomial.C.expChar Polynomial.C_injective p
  let R := (iterateFrobenius k p n).fieldRange
  let S := FrobeniusRing (Polynomial k) p n
  let D := w.biUnion fun a => a.coeffs
  let K := IntermediateField.adjoin R (D : Set k)
  let f : K →+* k := K.subtype
  have hr (a : k) : IsIntegral R a := by
    apply IsIntegral.of_pow (expChar_pow_pos k p n)
    exact isIntegral_algebraMap (x := (iterateFrobenius k p n).rangeRestrictField a)
  let V : Subalgebra S (Polynomial k) :=
    { (mapRingHom f).range.toSubsemiring with
      algebraMap_mem' := fun s => by
        obtain ⟨a, ha⟩ := s.property
        let g : k →+* K := (algebraMap R K).comp (iterateFrobenius k p n).rangeRestrictField
        change ∃ b : (Polynomial K), b.map f = (s : (Polynomial k))
        refine ⟨(expand k (p ^ n) a).map g, ?_⟩
        rw [Polynomial.map_map]
        change (expand k (p ^ n) a).map (iterateFrobenius k p n) = (s : (Polynomial k))
        rw [map_iterateFrobenius_expand, ← iterateFrobenius_def, ha] }
  let U : Subalgebra S (Polynomial k) := Algebra.adjoin S (insert «X» (C '' (D : Set k)))
  have huX : «X» ∈ U := Algebra.subset_adjoin (Set.mem_insert _ _)
  have huC (a : k) (ha : a ∈ K) : C a ∈ U := by
    change a ∈ K.toSubalgebra at ha
    change a ∈ (IntermediateField.adjoin R (D : Set k)).toSubalgebra at ha
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun a _ => (hr a).isAlgebraic)] at ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)
    | algebraMap r =>
      obtain ⟨c, hc⟩ := r.property
      have hs : C (r : k) ∈ (iterateFrobenius (Polynomial k) p n).range := by
        refine ⟨C c, ?_⟩
        rw [iterateFrobenius_def, ← map_pow]
        exact congrArg C hc
      exact U.algebraMap_mem ⟨_, hs⟩
    | add a b _ _ ha hb => simpa only [map_add] using U.add_mem ha hb
    | mul a b _ _ ha hb => simpa only [map_mul] using U.mul_mem ha hb
  have hVU : V = U := by
    apply le_antisymm
    · intro a ha
      obtain ⟨b, rfl⟩ : ∃ b : (Polynomial K), b.map f = a := ha
      induction b using Polynomial.induction_on' with
      | add a b ha hb => simpa only [Polynomial.map_add] using U.add_mem ha hb
      | monomial i c =>
        rw [Polynomial.map_monomial, ← C_mul_X_pow_eq_monomial]
        exact U.mul_mem (huC c c.property) (U.pow_mem huX i)
    · apply Algebra.adjoin_le
      rintro _ (rfl | ⟨c, hc, rfl⟩)
      · exact ⟨«X», Polynomial.map_X f⟩
      · exact ⟨C ⟨c, IntermediateField.subset_adjoin R _ hc⟩, Polynomial.map_C f⟩
  refine ⟨V.toSubmodule, ?_, ?_, ?_⟩
  · rw [hVU]
    apply fg_adjoin_of_finite ((D.finite_toSet.image C).insert «X»)
    intro a _
    apply IsIntegral.of_pow (expChar_pow_pos (Polynomial k) p n)
    exact isIntegral_algebraMap (x := (iterateFrobenius (Polynomial k) p n).rangeRestrict a)
  · intro a ha
    change a ∈ Polynomial.lifts f
    apply (Polynomial.lifts_iff_coeffs_subset_range a).mpr
    intro c hc
    have hD : c ∈ D := Finset.mem_biUnion.mpr ⟨a, ha, hc⟩
    exact ⟨⟨c, IntermediateField.subset_adjoin R _ hD⟩, rfl⟩
  · intro s a hs0 hs
    change (s : (Polynomial k)) * a ∈ V at hs
    obtain ⟨s', hs'⟩ : ∃ s' : (Polynomial K), s'.map f = (s : (Polynomial k)) := V.algebraMap_mem s
    obtain ⟨b, hb⟩ : ∃ b : (Polynomial K), b.map f = (s : (Polynomial k)) * a := hs
    have hd : s'.map f ∣ b.map f := ⟨a, by rw [hb, hs']⟩
    obtain ⟨a', ha'⟩ := (Polynomial.map_dvd_map' f).mp hd
    refine ⟨a', ?_⟩
    change a'.map f = a
    apply mul_left_cancel₀ (show (s : (Polynomial k)) ≠ 0 from fun h => hs0 (Subtype.ext h))
    rw [← hs', ← Polynomial.map_mul, ← ha', hb, hs']
end K1_14_3R_3_1_3_1
end
section
namespace K1_13_6_1_3_2
noncomputable section
open IsLocalRing
private theorem dim_le_two {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {f q : A} (hf : f ∈ maximalIdeal A) (hq : q ∈ maximalIdeal A)
    (hlen : Order.coheight (Ideal.span ({f, q} : Set A)) ≠ ⊤) :
    ringKrullDim A ≤ 2 := by
  let J : Ideal A := Ideal.span {f, q}
  have hJ : J ≤ maximalIdeal A :=
    Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨hf, Set.singleton_subset_iff.mpr hq⟩)
  have hfin : IsFiniteLength A (A ⧸ J) :=
    Module.length_ne_top_iff.mp (by simpa only [Module.length_quotient] using hlen)
  have : IsArtinianRing (A ⧸ J) :=
    isArtinian_of_tower A (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  have hmin : J.IsMinimalPrime (maximalIdeal A) := by
    refine ⟨⟨inferInstance, hJ⟩, ?_⟩
    intro p hp hp'
    have := hp.1
    exact Ideal.IsPrime.le_of_pow_le (hn.trans hp.2)
  have hcard : ({f, q} : Set A).ncard ≤ 2 := by
    classical
    simpa using (Set.ncard_insert_le f ({q} : Set A))
  have hh := (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hmin).trans
    (show (({f, q} : Set A).ncard : ℕ∞) ≤ 2 by exact_mod_cast hcard)
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr hh
private theorem span_with {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {x : V} (hx : x ≠ 0) (hdim : Module.finrank k V ≤ 2) :
    ∃ y : V, Submodule.span k ({x, y} : Set V) = ⊤ := by
  let U := Submodule.span k ({x} : Set V)
  have hU : Module.finrank k U = 1 := finrank_span_singleton hx
  have hd := U.finrank_quotient_add_finrank
  rw [hU] at hd
  obtain ⟨y', hy'⟩ := finrank_le_one_iff.mp (show Module.finrank k (V ⧸ U) ≤ 1 by omega)
  obtain ⟨y, rfl⟩ := U.mkQ_surjective y'
  refine ⟨y, eq_top_iff.mpr fun z _ => ?_⟩
  obtain ⟨c, hc⟩ := hy' (U.mkQ z)
  have hz : z - c • y ∈ U := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hc, sub_self]
  have hy : c • y ∈ Submodule.span k ({x, y} : Set V) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact (Submodule.sub_mem_iff_left _ hy).mp
    ((Submodule.span_mono (by simp : ({x} : Set V) ⊆ {x, y})) hz)
private theorem maximalIdeal_span_pair {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {f : A} (hf : f ∈ maximalIdeal A) (hf2 : f ∉ maximalIdeal A ^ 2)
    (hdim : ringKrullDim A ≤ 2) :
    ∃ t : A, maximalIdeal A = Ideal.span {f, t} := by
  let m := maximalIdeal A
  let f' : m := ⟨f, hf⟩
  have hf' : m.toCotangent f' ≠ 0 := by
    rwa [ne_eq, Ideal.toCotangent_eq_zero]
  have hd := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp ‹_›
  have hd' : Module.finrank (ResidueField A) (CotangentSpace A) ≤ 2 := by
    exact_mod_cast hd ▸ hdim
  obtain ⟨y, hy⟩ := span_with hf' hd'
  obtain ⟨t, rfl⟩ := m.toCotangent_surjective y
  have hs : Submodule.span A ({f', t} : Set m) = ⊤ :=
    CotangentSpace.span_image_eq_top_iff.mp (by simpa only [Set.image_insert_eq, Set.image_singleton] using hy)
  have hm := congrArg (Submodule.map m.subtype) hs
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    Set.image_insert_eq, Set.image_singleton] at hm
  exact ⟨t, hm.symm⟩
theorem local_order {A : Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [UniqueFactorizationMonoid A] {f q : A} {v : ℕ}
    (hf : f ∈ maximalIdeal A) (hq : q ∈ maximalIdeal A)
    (hf2 : f ∉ maximalIdeal A ^ 2) (hqf : q ∉ Ideal.span {f})
    (hlen : Order.coheight (Ideal.span ({f, q} : Set A)) = (v : ℕ∞)) :
    ∃ t u : A, maximalIdeal A = Ideal.span {f, t} ∧ IsUnit u ∧
      q - u * t ^ v ∈ Ideal.span {f} := by
  let I : Ideal A := Ideal.span {f}
  let B := A ⧸ I
  let π : A →+* B := Ideal.Quotient.mk I
  have hf0 : f ≠ 0 := by
    intro e
    exact hf2 (e.symm ▸ (maximalIdeal A ^ 2).zero_mem)
  have hirr : Irreducible f := by
    refine ⟨hf, fun a b e => ?_⟩
    by_contra! h
    apply hf2
    rw [e, pow_two]
    exact Ideal.mul_mem_mul h.1 h.2
  have : I.IsPrime := (Ideal.span_singleton_prime hf0).mpr (irreducible_iff_prime.mp hirr)
  have hdim := dim_le_two hf hq (hlen.trans_ne (by simp))
  obtain ⟨t, ht⟩ := maximalIdeal_span_pair hf hf2 hdim
  have : IsLocalRing B := .of_surjective' π Ideal.Quotient.mk_surjective
  have : IsLocalHom π := .of_surjective π Ideal.Quotient.mk_surjective
  have hmax : maximalIdeal B = Ideal.span {π t} := by
    rw [← map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective, ht,
      Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    have hf' : π f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    simp [hf']
  have hq0 : π q ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hqf
  have hqB : π q ∈ maximalIdeal B := map_nonunit π q hq
  have hB : ¬ IsField B := by
    rw [isField_iff_maximalIdeal_eq]
    exact fun H => hq0 (Ideal.mem_bot.mp (H ▸ hqB))
  have hprincipal : (maximalIdeal B).IsPrincipal := ⟨⟨π t, hmax⟩⟩
  have : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hB).out 5 1).mp hprincipal
  have hti := (IsDiscreteValuationRing.irreducible_iff_uniformizer (π t)).mpr hmax
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hti
  have hI : I ≤ Ideal.span ({f, q} : Set A) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.subset_span (Set.mem_insert _ _)))
  have hcomap : (Ideal.span ({π q} : Set B)).comap π = Ideal.span ({f, q} : Set A) := by
    have h := Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective
      (Ideal.span ({f, q} : Set A))
    rwa [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      show π f = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f),
      Ideal.span_pair_comm (x := (0 : B)), Ideal.span_pair_zero,
      ← RingHom.ker_eq_comap_bot, show RingHom.ker π = I from Ideal.mk_ker, sup_of_le_left hI] at h
  have hn : Order.coheight (Ideal.span ({π q} : Set B)) = (n : ℕ∞) := by
    rw [hw, Ideal.span_singleton_mul_left_unit w.isUnit, ← Ideal.span_singleton_pow, ← hmax]
    exact IsDiscreteValuationRing.coheight_pow_maximalIdeal B n
  have hvn : v = n := by
    have h := Ideal.coheight_comap_of_surjective π Ideal.Quotient.mk_surjective
      (Ideal.span ({π q} : Set B))
    rw [hcomap, hlen, hn] at h
    exact_mod_cast h
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (w : B)
  have hu' : π u = (w : B) := hu
  refine ⟨t, u, ht, isUnit_of_map_unit π u (hu'.symm ▸ w.isUnit), ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (q - u * t ^ v) = 0
  rw [map_sub, map_mul, map_pow, hu', hvn, ← hw, sub_self]
end
end K1_13_6_1_3_2
end
section
namespace K1_13_7_4_2_2
noncomputable section
open IsLocalRing KaehlerDifferential MvPolynomial
open scoped TensorProduct
variable {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
private theorem firstOrder [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (ResidueField R)] {n : ℕ}
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R)) :
    ∃ (f : R →ₐ[k] Jets (ResidueField R) n 2),
      (∀ r, constant (ResidueField R) n 2 (by decide) (f r) = residue R r) ∧
      ∀ i, ∃ x ∈ maximalIdeal R, f x = jet (ResidueField R) n 2 («X» i) := by
  let K := ResidueField R
  let S := Jets K n 2
  let J := aug K n 2
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k)
    (P := R) (A := K) residue_surjective).mp inferInstance
  have hk : RingHom.ker (algebraMap R K) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  let e : (RingHom.ker (algebraMap R K)).Cotangent ≃ₗ[R] CotangentSpace R :=
    Ideal.Cotangent.equivOfEq _ _ hk
  let τ : Ω[R⁄k] →ₗ[R] K ⊗[R] Ω[R⁄k] := TensorProduct.mk R K _ 1
  let D₀ : Derivation k R (CotangentSpace R) :=
    (e.toLinearMap.comp (l.comp τ)).compDer (D k R)
  let v (i : Fin n) : J := ⟨jet K n 2 («X» i), X_mem_aug K n 2 i⟩
  let L : CotangentSpace R →ₗ[K] J := b.constr K v
  let δ : Derivation k R J := (L.restrictScalars R).compDer D₀
  let f := liftOfDerivationToSquareZero J (aug_pow_self K n 2) δ
  refine ⟨f, ?_, ?_⟩
  · intro r
    rw [liftOfDerivationToSquareZero_apply, map_add]
    have hδ : (δ r : S) ∈ RingHom.ker (constant K n 2 (by decide)) := by
      rw [ker_constant]
      exact (δ r).2
    rw [RingHom.mem_ker.mp hδ, zero_add]
    exact constant_algebraMap K n 2 (by decide) (residue R r)
  · intro i
    obtain ⟨x, hx⟩ := (maximalIdeal R).toCotangent_surjective (b i)
    let x' : RingHom.ker (algebraMap R K) := ⟨x, by
      rw [ResidueField.algebraMap_eq, ker_residue]
      exact x.2⟩
    have hD : D₀ (x : R) = b i := by
      change e (l (1 ⊗ₜ[R] D k R (x : R))) = b i
      rw [← kerCotangentToTensor_toCotangent k R K x']
      have h := DFunLike.congr_fun hl ((RingHom.ker (algebraMap R K)).toCotangent x')
      change l (kerCotangentToTensor k R K _) = _ at h
      rw [h, LinearMap.id_apply]
      dsimp only [e]
      rw [Ideal.Cotangent.equivOfEq_toCotangent]
      exact hx
    refine ⟨x, x.2, ?_⟩
    rw [liftOfDerivationToSquareZero_apply]
    change (L (D₀ (x : R)) : S) + algebraMap K S (residue R x) = _
    dsimp only [L]
    rw [hD, Module.Basis.constr_basis, (residue_eq_zero_iff _).mpr x.2, map_zero, add_zero]
private theorem le_of_le_sup_sq {S : Type*} [CommRing S] (J I : Ideal S) (t : ℕ)
    (hJ : J ^ t = ⊥) (h : J ≤ I ⊔ J ^ 2) : J ≤ I := by
  have step (s : ℕ) : J ^ (s + 1) ≤ I ⊔ J ^ (s + 1 + 1) := by
    calc
      J ^ (s + 1) = J * J ^ s := pow_succ' _ _
      _ ≤ (I ⊔ J ^ 2) * J ^ s := Ideal.mul_mono_left h
      _ ≤ I ⊔ J ^ (s + 1 + 1) := by
        rw [Ideal.sup_mul, ← pow_add, show 2 + s = s + 1 + 1 by omega]
        exact sup_le_sup (Ideal.mul_le_left) le_rfl
  have all (s : ℕ) : J ≤ I ⊔ J ^ s := by
    induction s with
    | zero => simp
    | succ s ih =>
      cases s with
      | zero => simpa only [Nat.zero_add, pow_one] using (le_sup_right : J ≤ I ⊔ J)
      | succ s => exact ih.trans (sup_le le_sup_left (step s))
  simpa [hJ] using all t
omit [IsLocalRing R] in
private theorem surj_of_augmentation {S K : Type*} [CommRing S] [CommRing K]
    (f : R →+* S) (a : S →+* K) (I : Ideal R) (J : Ideal S) (t : ℕ)
    (hJ : J ^ t = ⊥) (hmap : I.map f = J)
    (ha : RingHom.ker a = J) (hs : Function.Surjective (a.comp f)) :
    Function.Surjective f := by
  let : Algebra R S := f.toAlgebra
  let A : Submodule R S := LinearMap.range (Algebra.linearMap R S)
  have htop : A ⊔ I • (⊤ : Submodule R S) = ⊤ := by
    rw [Ideal.smul_top_eq_map, show algebraMap R S = f from rfl, hmap]
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨x, hx⟩ := hs (a y)
    refine Submodule.mem_sup.mpr ⟨f x, ⟨x, rfl⟩, y - f x, ?_, by ring⟩
    rw [Submodule.restrictScalars_mem, ← ha, RingHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr hx.symm
  have hs' (s : ℕ) : A ⊔ I ^ s • (⊤ : Submodule R S) = ⊤ := by
    induction s with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
    | succ s ih =>
      calc
        A ⊔ I ^ (s + 1) • (⊤ : Submodule R S)
            = A ⊔ I • (I ^ s • (⊤ : Submodule R S)) := by rw [pow_succ', mul_smul]
        _ = A ⊔ I • (A ⊔ I ^ s • (⊤ : Submodule R S)) := by
          rw [Submodule.smul_sup, ← sup_assoc, sup_eq_left.mpr (Submodule.smul_le_right : I • A ≤ A)]
        _ = ⊤ := by rw [ih, htop]
  have hzero : I ^ t • (⊤ : Submodule R S) = ⊥ := by
    rw [Ideal.smul_top_eq_map, show algebraMap R S = f from rfl, Ideal.map_pow, hmap, hJ]
    rfl
  have hA := hs' t
  rw [hzero, sup_bot_eq] at hA
  exact LinearMap.range_eq_top.mp hA
theorem exists_jet_surjection [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (ResidueField R)] {n t : ℕ} (ht : 2 ≤ t)
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R)) :
    ∃ f : (R ⧸ maximalIdeal R ^ t) →+* Jets (ResidueField R) n t,
      Function.Surjective f := by
  let K := ResidueField R
  let S := Jets K n t
  let J := aug K n t
  let a : S →+* K := constant K n t (by omega)
  let π : S →ₐ[k] Jets K n 2 :=
    Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right ht)
  have hπ : RingHom.ker π = J ^ 2 := by
    change RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right ht :
      Vars K n ^ t ≤ Vars K n ^ 2)) = J ^ 2
    rw [Ideal.Quotient.factor_ker, Ideal.map_pow]
  have hnil : IsNilpotent (RingHom.ker π) := by
    rw [hπ]
    refine ⟨t, ?_⟩
    change (J ^ 2) ^ t = (⊥ : Ideal S)
    rw [← pow_mul, mul_comm 2 t, pow_mul, show J ^ t = ⊥ from aug_pow_self K n t]
    exact Ideal.bot_pow (by decide)
  have hs : Function.Surjective π :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right ht)
  obtain ⟨f₂, hconst, hx⟩ := firstOrder (k := k) b
  let f := Algebra.FormallySmooth.liftOfSurjective f₂ π hs hnil
  have hf (r : R) : π (f r) = f₂ r :=
    Algebra.FormallySmooth.liftOfSurjective_apply f₂ π hs hnil r
  have hconst' (r : R) : a (f r) = residue R r := by
    have ha (y : S) : a y = constant K n 2 (by decide) (π y) := by
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    rw [ha, hf, hconst]
  have hker : RingHom.ker a = J := ker_constant K n t _
  have hm : (maximalIdeal R).map f.toRingHom ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    rw [Ideal.mem_comap, ← hker, RingHom.mem_ker]
    change a (f r) = 0
    rw [hconst']
    exact (residue_eq_zero_iff _).mpr hr
  have hmap : (maximalIdeal R).map f.toRingHom = J := by
    refine le_antisymm hm (le_of_le_sup_sq J _ t (aug_pow_self K n t) ?_)
    refine ((aug_eq_span K n t).le).trans (Ideal.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, hx₁, hx₂⟩ := hx i
    refine Submodule.mem_sup.mpr ⟨f x, Ideal.mem_map_of_mem _ hx₁, jet K n t («X» i) - f x, ?_,
      by ring⟩
    change _ ∈ J ^ 2
    rw [← hπ, RingHom.mem_ker, map_sub, sub_eq_zero, hf, hx₂]
    rfl
  have hsurj := surj_of_augmentation f.toRingHom a _ J t (aug_pow_self K n t)
    hmap hker (fun c => by
      obtain ⟨r, hr⟩ := residue_surjective (R := R) c
      exact ⟨r, (hconst' r).trans hr⟩)
  have hkill : maximalIdeal R ^ t ≤ RingHom.ker f.toRingHom := by
    rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, hmap]
    exact aug_pow_self K n t
  exact ⟨Ideal.Quotient.lift _ f.toRingHom hkill,
    hsurj.of_comp (g := Ideal.Quotient.mk _)⟩
end
end K1_13_7_4_2_2
end
section
namespace K1_13_7_4_2_2
noncomputable section
open MvPolynomial IsLocalRing
open scoped BigOperators
private abbrev Mono (n t : ℕ) := Σ j : Fin t, Sym (Fin n) j.val
private def exponent {n t : ℕ} (a : Mono n t) : Fin n →₀ ℕ := a.2.val.toFinsupp
private theorem exponent_degree {n t : ℕ} (a : Mono n t) :
    (exponent a).degree = a.1.val := by
  change (a.2.val.toFinsupp).sum (fun _ j => j) = a.1.val
  exact (Multiset.toFinsupp_sum_eq _).trans a.2.property
private theorem exponent_injective (n t : ℕ) : Function.Injective (@exponent n t) := by
  rintro ⟨d, a⟩ ⟨e, b⟩ h
  have hde : d = e := Fin.ext ((exponent_degree ⟨d, a⟩).symm.trans
    ((congrArg Finsupp.degree h).trans (exponent_degree ⟨e, b⟩)))
  subst e
  exact congrArg (Sigma.mk d) (Subtype.ext (Multiset.toFinsupp.injective h))
private theorem card_mono (n t : ℕ) (ht : 0 < t) :
    Fintype.card (Mono n t) = (t + n - 1).choose n := by
  classical
  rw [Fintype.card_sigma]
  simp only [Sym.card_sym_eq_multichoose, Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  rw [Nat.sum_range_multichoose]
  congr 1
  omega
private theorem length_over_field (K : Type*) [Field K] (n t : ℕ) (ht : 0 < t) :
    ((t + n - 1).choose n : ℕ∞) ≤ Module.length K (Jets K n t) := by
  classical
  let coeff (a : Mono n t) : Jets K n t →ₗ[K] K :=
    ((Vars K n ^ t).restrictScalars K).liftQ (lcoeff K (exponent a)) (by
      intro p hp
      exact (mem_pow_idealOfVars_iff' t p).mp hp _ (by
        rw [exponent_degree]
        exact a.1.isLt))
  let f : Jets K n t →ₗ[K] (Mono n t → K) := LinearMap.pi coeff
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨jet K n t (∑ a, monomial (exponent a) (c a)), ?_⟩
    funext a
    change (∑ b, monomial (exponent b) (c b)).coeff (exponent a) = c a
    rw [coeff_sum, Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      simp [coeff_monomial, (exponent_injective n t).ne hba]
    · simp
  have h := Module.length_le_of_surjective f hsurj
  rw [Module.length_pi_of_fintype] at h
  simpa [card_mono n t ht] using h
theorem length_jets (K : Type*) [Field K] (n t : ℕ) (ht : 0 < t) :
    ((t + n - 1).choose n : ℕ∞) ≤ Module.length (Jets K n t) (Jets K n t) := by
  let S := Jets K n t
  let J := aug K n t
  let f := constant K n t ht
  have hf : Function.Surjective f := constant_surjective K n t ht
  have hker : RingHom.ker f = J := ker_constant K n t ht
  have hmax : J.IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective f hf
  have hnil : nilradical S = J := by
    let : J.IsPrime := hmax.isPrime
    refine le_antisymm (nilradical_le_prime J) (fun x hx => ?_)
    apply mem_nilradical.mpr
    refine ⟨t, ?_⟩
    exact Ideal.mem_bot.mp ((show J ^ t = ⊥ from aug_pow_self K n t) ▸ Ideal.pow_mem_pow hx t)
  let : (nilradical S).IsMaximal := hnil.symm ▸ hmax
  let : IsLocalRing S := IsLocalRing.of_isMaximal_nilradical S
  have hm : maximalIdeal S = J := (IsLocalRing.eq_maximalIdeal hmax).symm
  let : IsLocalHom (algebraMap K S) := ⟨fun x hx => by
    apply isUnit_iff_ne_zero.mpr
    rintro rfl
    simp at hx⟩
  have hres : Function.Surjective (algebraMap K (ResidueField S)) := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    refine ⟨f x, ?_⟩
    change residue S (algebraMap K S (f x)) = residue S x
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, hm, ← hker,
      RingHom.mem_ker, map_sub, constant_algebraMap, sub_self]
  have hlen : Module.length (ResidueField K) (ResidueField S) = 1 := by
    rw [← Module.length_eq_of_surjective (M := ResidueField S) (residue_surjective (R := K)),
      Module.length_eq_of_surjective hres, Module.length_eq_one]
  have h := length_over_field K n t ht
  rwa [IsLocalRing.length_restrictScalars K S S, hlen, mul_one] at h
end
end K1_13_7_4_2_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F row : Type*} [Field F] [Fintype row]
theorem degreeLT_natDegree_le {q : ℕ} (Q : Polynomial.degreeLT F (q+1)) :
    (Q : (Polynomial F)).natDegree ≤ q := by
  by_cases hQ : (Q : (Polynomial F)) = 0
  · simp [hQ]
  · have h := (Polynomial.natDegree_lt_iff_degree_lt hQ).mpr
      (Polynomial.mem_degreeLT.mp Q.property)
    omega
def multipleCoefficients (g : (Polynomial F)) (q t : ℕ) :
    Polynomial.degreeLT F (q+1) →ₗ[F] (Fin (t+1) → F) where
  toFun Q j := (g * (Q : (Polynomial F))).coeff j.val
  map_add' Q R := by ext j; simp [mul_add]
  map_smul' c Q := by ext j; simp [mul_smul_comm]
theorem coefficients_injective_bounded (t : ℕ) (P Q : (Polynomial F))
    (hP : P.natDegree ≤ t) (hQ : Q.natDegree ≤ t)
    (hcoeff : ∀ j : Fin (t+1), P.coeff j.val = Q.coeff j.val) : P = Q := by
  ext j
  by_cases hj : j < t+1
  · exact hcoeff ⟨j,hj⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
theorem multipleCoefficients_injective (g : (Polynomial F)) (a q t : ℕ)
    (hg : g ≠ 0) (hga : g.natDegree ≤ a) (hsize : a+q ≤ t) :
    Function.Injective (multipleCoefficients g q t) := by
  intro Q R hQR
  apply Subtype.ext
  apply mul_left_cancel₀ hg
  apply coefficients_injective_bounded t
  · exact Polynomial.natDegree_mul_le.trans (by have := degreeLT_natDegree_le Q; omega)
  · exact Polynomial.natDegree_mul_le.trans (by have := degreeLT_natDegree_le R; omega)
  · exact fun j => congrFun hQR j
theorem normal_kernel_factorization (a q t : ℕ) (M : Matrix row (Fin (t+1)) F)
    (g : (Polynomial F)) (hg : g ≠ 0) (hga : g.natDegree ≤ a)
    (hsize : a+q ≤ t)
    (hnull : Module.finrank F (LinearMap.ker M.mulVecLin) = q+1)
    (hshift : ∀ Q : Polynomial.degreeLT F (q+1),
      M.mulVec (multipleCoefficients g q t Q) = 0)
    (E : (Polynomial F)) (hE : E.natDegree ≤ t)
    (hker : M.mulVec (fun j : Fin (t+1) => E.coeff j.val) = 0) :
    ∃ Q : (Polynomial F), Q.natDegree ≤ q ∧ E = g*Q := by
  let f := multipleCoefficients g q t
  have hinj := multipleCoefficients_injective g a q t hg hga hsize
  have hdim : Module.finrank F (LinearMap.range f) = q+1 := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact ((Polynomial.degreeLTEquiv F (q+1)).finrank_eq).trans
      (by simp [Module.finrank_fintype_fun_eq_card])
  have hsub : LinearMap.range f ≤ LinearMap.ker M.mulVecLin := by
    rintro _ ⟨Q,rfl⟩
    exact hshift Q
  have heq : LinearMap.range f = LinearMap.ker M.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hsub (hdim.trans hnull.symm)
  have hmem : (fun j : Fin (t+1) => E.coeff j.val) ∈ LinearMap.range f := by
    rw [heq]
    exact hker
  obtain ⟨Q,hQ⟩ := hmem
  refine ⟨Q,degreeLT_natDegree_le Q,?_⟩
  symm
  apply coefficients_injective_bounded t
  · exact Polynomial.natDegree_mul_le.trans (by have := degreeLT_natDegree_le Q; omega)
  · exact hE
  · exact fun j => congrFun hQ j
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
def assemble {R : Type*} [Semiring R] {d : ℕ} (v : Fin (d+1) → R) : (Polynomial R) :=
  ∑ j, Polynomial.monomial j.val (v j)
theorem assemble_coeff {R : Type*} [Semiring R] {d : ℕ}
    (v : Fin (d+1) → R) (j : Fin (d+1)) : (assemble v).coeff j.val=v j := by
  classical
  simp only [assemble, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [show b.val ≠ j.val from fun h => hbj (Fin.ext h)]
  · simp
theorem assemble_natDegree_le {R : Type*} [Semiring R] {d : ℕ}
    (v : Fin (d+1) → R) : (assemble v).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le (v j)).trans (by omega)
theorem map_assemble {R S : Type*} [Semiring R] [Semiring S] {d : ℕ}
    (φ : R →+* S) (v : Fin (d+1) → R) :
    (assemble v).map φ=assemble (fun j => φ (v j)) := by
  simp [assemble, Polynomial.map_sum]
theorem specialize_eq_assemble {F : Type*} [Field F] {d : ℕ}
    (v : Fin (d+1) → (Polynomial F)) (γ : F) :
    specialize v γ=assemble (fun j => (v j).eval γ) := by
  simp only [specialize,assemble,Polynomial.C_mul_X_pow_eq_monomial]
theorem assemble_map_eval {F : Type*} [Field F] {d : ℕ}
    (v : Fin (d+1) → (Polynomial F)) (γ : F) :
    (assemble v).map (Polynomial.evalRingHom γ)=specialize v γ := by
  rw [map_assemble,specialize_eq_assemble]
  rfl
theorem assemble_ne_zero {R : Type*} [Semiring R] {d : ℕ}
    (v : Fin (d+1) → R) (hv : v ≠ 0) : assemble v ≠ 0 := by
  intro hz
  apply hv
  funext j
  have h := congrArg (fun f : (Polynomial R) => f.coeff j.val) hz
  simpa only [assemble_coeff,coeff_zero,Pi.zero_apply] using h
theorem nodePolynomial_generic_eval {F K : Type*} [Field F] [Field K] {d : ℕ}
    (φ : (Polynomial F) →+* K) (v : Fin (d+1) → (Polynomial F)) (x : F) :
    φ (nodePolynomial v x) = (assemble (fun j => φ (v j))).eval (φ (C x)) := by
  simp only [nodePolynomial,map_sum,map_mul,assemble,Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  have hp : φ (C (x^j.val))=(φ (C x))^j.val := by rw [← map_pow,← Polynomial.C_pow]
  rw [hp,mul_comm]
variable {R S row col : Type*} [CommRing R] [CommRing S] [Fintype col]
theorem family_kernel_map (φ : R →+* S) (M : Matrix row col R)
    (P : (Polynomial R)) (indices : col → ℕ)
    (hker : M.mulVec (fun j => P.coeff (indices j))=0) :
    (M.map φ).mulVec (fun j => (P.map φ).coeff (indices j))=0 := by
  funext i
  have hi := congrArg φ (congrFun hker i)
  simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,map_zero,
    Polynomial.coeff_map,Matrix.map_apply,Pi.zero_apply] using hi
theorem family_kernel_of_map (φ : R →+* S) (hφ : Function.Injective φ)
    (M : Matrix row col R) (P : (Polynomial R)) (indices : col → ℕ)
    (hker : (M.map φ).mulVec (fun j => (P.map φ).coeff (indices j))=0) :
    M.mulVec (fun j => P.coeff (indices j))=0 := by
  funext i
  apply hφ
  have hi := congrFun hker i
  simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,map_zero,
    Polynomial.coeff_map,Matrix.map_apply,Pi.zero_apply] using hi
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K]
def recurrenceEval (s : ℕ → K) (j : ℕ) : (Polynomial K) →ₗ[K] K where
  toFun f := f.sum (fun i c => c*s (i+j))
  map_add' f g := Polynomial.sum_add_index f g _ (fun _ => by simp)
    (fun _ _ _ => by ring)
  map_smul' c f := by
    rw [Polynomial.sum_smul_index _ _ _ (fun _ => by simp)]
    simp only [RingHom.id_apply, smul_eq_mul, Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
theorem recurrenceEval_monomial (s : ℕ → K) (j i : ℕ) (c : K) :
    recurrenceEval s j (monomial i c) = c*s (i+j) := by
  change (monomial i c : (Polynomial K)).sum (fun n a => a*s (n+j)) = _
  exact Polynomial.sum_monomial_index c (fun n a => a*s (n+j)) (zero_mul _)
theorem recurrenceEval_shift (s : ℕ → K) (j l : ℕ) (f : (Polynomial K)) :
    recurrenceEval s j (f*«X»^l) = recurrenceEval s (j+l) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [add_mul, map_add, hf, hg]
  | monomial i c =>
    rw [X_pow_eq_monomial, Polynomial.monomial_mul_monomial,
      mul_one, recurrenceEval_monomial, recurrenceEval_monomial]
    congr 2
    omega
def InRecurrenceKernel (s : Fin 2 → ℕ → K) (m t : ℕ) (f : (Polynomial K)) : Prop :=
  f.natDegree ≤ t ∧ ∀ b j, j < m-t → recurrenceEval (s b) j f = 0
theorem generator_in_small_kernel (s : Fin 2 → ℕ → K) (m a q : ℕ)
    (hL : a+q < m) (g : (Polynomial K)) (hga : g.natDegree ≤ a)
    (hshift : ∀ l ≤ q, InRecurrenceKernel s m (a+q) (g*«X»^l)) :
    InRecurrenceKernel s m a g := by
  refine ⟨hga,?_⟩
  intro b j hj
  let l := min j q
  let i := j-l
  have hl : l ≤ q := min_le_right _ _
  have hlj : l ≤ j := min_le_left _ _
  have hi : i < m-(a+q) := by dsimp [i,l]; omega
  have hij : i+l=j := by dsimp [i]; omega
  have h := (hshift l hl).2 b i hi
  rw [recurrenceEval_shift, hij] at h
  exact h
theorem small_kernel_shifts (s : Fin 2 → ℕ → K) (m a q : ℕ)
    (hsize : a+q ≤ m) (f : (Polynomial K)) (hf : InRecurrenceKernel s m a f)
    (l : ℕ) (hl : l ≤ q) : InRecurrenceKernel s m (a+q) (f*«X»^l) := by
  refine ⟨?_,?_⟩
  · have hdegree := hf.1
    exact Polynomial.natDegree_mul_le.trans (by simp only [natDegree_X_pow]; omega)
  · intro b j hj
    rw [recurrenceEval_shift]
    exact hf.2 b (j+l) (by omega)
theorem principal_small_kernel_line (s : Fin 2 → ℕ → K) (m a q : ℕ)
    (hsize : a+q ≤ m) (g : (Polynomial K)) (hg : g ≠ 0)
    (hprincipal : ∀ f : (Polynomial K), InRecurrenceKernel s m (a+q) f ↔
      ∃ Q : (Polynomial K), Q.natDegree ≤ q ∧ f=g*Q)
    (f : (Polynomial K)) (hf : InRecurrenceKernel s m a f) :
    ∃ c : K, f=c • g := by
  have hfirst := small_kernel_shifts s m a q hsize f hf 0 (by omega)
  simp only [pow_zero, mul_one] at hfirst
  obtain ⟨Q,hQ,hfQ⟩ := (hprincipal f).mp hfirst
  have hlast := small_kernel_shifts s m a q hsize f hf q (by omega)
  obtain ⟨R,hR,hfR⟩ := (hprincipal (f*«X»^q)).mp hlast
  have hQR : Q*«X»^q=R := by
    apply mul_left_cancel₀ hg
    rw [← mul_assoc, ← hfQ, hfR]
  by_cases hQ0 : Q=0
  · exact ⟨0,by simp [hfQ,hQ0]⟩
  have hQdegree : Q.natDegree=0 := by
    have hdeg := Polynomial.natDegree_mul hQ0 (pow_ne_zero q X_ne_zero)
    rw [hQR, natDegree_X_pow] at hdeg
    omega
  have hQC : Q=C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQdegree
  refine ⟨Q.coeff 0,?_⟩
  rw [hfQ,hQC]
  simp only [Polynomial.smul_eq_C_mul, coeff_C_zero]
  ring
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {R row : Type*} [CommRing R]
def multiplicationMatrix (H : (Polynomial R)) (a d : ℕ) :
    Matrix (Fin (a+1)) (Fin (d+1)) R :=
  fun l j => (H*«X»^j.val).coeff l.val
def restrictByFamily (a d : ℕ) (M : Matrix row (Fin (a+1)) R) (H : (Polynomial R)) :
    Matrix row (Fin (d+1)) R := M*multiplicationMatrix H a d
theorem multiplicationMatrix_mulVec (H : (Polynomial R)) (a d : ℕ) (c : Fin (d+1) → R) :
    (multiplicationMatrix H a d).mulVec c =
      (fun l : Fin (a+1) => (H*assemble c).coeff l.val) := by
  funext l
  simp only [multiplicationMatrix,Matrix.mulVec,dotProduct,assemble]
  rw [Finset.mul_sum,Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  have heq : H*(C (c j)*«X»^j.val) = c j • (H*«X»^j.val) := by
    rw [Polynomial.smul_eq_C_mul]
    ring
  rw [heq,Polynomial.coeff_smul,smul_eq_mul,mul_comm]
theorem restrictByFamily_mulVec (a d : ℕ) (M : Matrix row (Fin (a+1)) R) (H : (Polynomial R))
    (c : Fin (d+1) → R) :
    (restrictByFamily a d M H).mulVec c =
      M.mulVec (fun l : Fin (a+1) => (H*assemble c).coeff l.val) := by
  rw [restrictByFamily,← Matrix.mulVec_mulVec,multiplicationMatrix_mulVec]
theorem restrictByFamily_map {S : Type*} [CommRing S]
    (a d : ℕ) (φ : R →+* S) (M : Matrix row (Fin (a+1)) R) (H : (Polynomial R)) :
    (restrictByFamily a d M H).map φ =
      restrictByFamily a d (M.map φ) (H.map φ) := by
  ext i j
  simp only [restrictByFamily,Matrix.mul_apply,Matrix.map_apply,map_sum,map_mul,
    multiplicationMatrix,Polynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro l _
  have heq : φ ((H*«X»^j.val).coeff l.val) = (H.map φ*«X»^j.val).coeff l.val := by
    rw [← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  rw [heq]
theorem assemble_coefficients {K : Type*} [Field K] (d : ℕ) (P : (Polynomial K))
    (hP : P.natDegree ≤ d) : assemble (fun j : Fin (d+1) => P.coeff j.val)=P := by
  apply coefficients_injective_bounded d
  · exact assemble_natDegree_le _
  · exact hP
  · intro j
    exact assemble_coeff _ j
theorem restricted_natDegree_le {F : Type*} [Field F] (a d : ℕ)
    (M : Matrix row (Fin (a+1)) (Polynomial F)) (H : (Polynomial F)) (cost : row → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ cost i) (i : row) (j : Fin (d+1)) :
    (restrictByFamily a d M (H.map (Polynomial.C : F →+* (Polynomial F))) i j).natDegree ≤ cost i := by
  simp only [restrictByFamily,Matrix.mul_apply,multiplicationMatrix]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l _
  have hcoeff : ((H.map (Polynomial.C : F →+* (Polynomial F)))*(Polynomial.X : (Polynomial (Polynomial F)))^j.val).coeff l.val =
      (Polynomial.C : F →+* (Polynomial F)) ((H*(Polynomial.X : (Polynomial F))^j.val).coeff l.val) := by
    have heq : (H*(Polynomial.X : (Polynomial F))^j.val).map (Polynomial.C : F →+* (Polynomial F)) =
        H.map (Polynomial.C : F →+* (Polynomial F))*(Polynomial.X : (Polynomial (Polynomial F)))^j.val := by
      rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
    have hc := congrArg (fun P : (Polynomial (Polynomial F)) => P.coeff l.val) heq
    simpa only [Polynomial.coeff_map] using hc.symm
  change (M i l*((H.map (Polynomial.C : F →+* (Polynomial F)))*(Polynomial.X : (Polynomial (Polynomial F)))^j.val).coeff l.val).natDegree ≤ _
  rw [hcoeff,mul_comm]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hM i l)
variable {K : Type*} [Field K]
theorem restricted_kernel_line (a h d : ℕ) (hah : h+d=a)
    (M : Matrix row (Fin (a+1)) K) (H f : (Polynomial K))
    (hH : H ≠ 0) (hHd : H.natDegree ≤ h) (hfd : f.natDegree ≤ d)
    (hkernel : LinearMap.ker M.mulVecLin =
      K ∙ (fun j : Fin (a+1) => (H*f).coeff j.val)) :
    LinearMap.ker (restrictByFamily a d M H).mulVecLin =
      K ∙ (fun j : Fin (d+1) => f.coeff j.val) := by
  have hHf : (H*f).natDegree ≤ a := Polynomial.natDegree_mul_le.trans (by omega)
  apply le_antisymm
  · intro c hc
    have hc' : (restrictByFamily a d M H).mulVec c=0 := hc
    rw [restrictByFamily_mulVec] at hc'
    have hmem : (fun j : Fin (a+1) => (H*assemble c).coeff j.val) ∈
        K ∙ (fun j : Fin (a+1) => (H*f).coeff j.val) := by
      rw [← hkernel]
      exact hc'
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hmem
    have heq : H*assemble c=b • (H*f) := by
      apply coefficients_injective_bounded a
      · exact Polynomial.natDegree_mul_le.trans (by have := assemble_natDegree_le c; omega)
      · exact (Polynomial.natDegree_smul_le _ _).trans hHf
      · intro j
        have hh := congrFun hb j
        simpa only [Polynomial.coeff_smul,Pi.smul_apply,smul_eq_mul] using hh.symm
    have hcancel : assemble c=b • f := by
      apply mul_left_cancel₀ hH
      simpa only [mul_smul_comm] using heq
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b,?_⟩
    funext j
    have hh := congrArg (fun P : (Polynomial K) => P.coeff j.val) hcancel
    simpa only [assemble_coeff,Polynomial.coeff_smul,Pi.smul_apply,smul_eq_mul] using hh.symm
  · apply Submodule.span_le.mpr
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    subst c
    change (restrictByFamily a d M H).mulVec _=0
    rw [restrictByFamily_mulVec,assemble_coefficients d f hfd]
    have hmem : (fun j : Fin (a+1) => (H*f).coeff j.val) ∈
        K ∙ (fun j : Fin (a+1) => (H*f).coeff j.val) := Submodule.mem_span_singleton_self _
    rw [← hkernel] at hmem
    exact hmem
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {K : Type*} [Field K]
def recurrenceMatrix (s : Fin 2 → ℕ → K) (m t : ℕ) :
    Matrix (Fin 2 × Fin (m-t)) (Fin (t+1)) K :=
  fun i j => s i.1 (i.2.val+j.val)
theorem recurrenceEval_eq_sum (s : ℕ → K) (j t : ℕ) (f : (Polynomial K))
    (hf : f.natDegree ≤ t) :
    recurrenceEval s j f = ∑ i : Fin (t+1), f.coeff i.val*s (i.val+j) := by
  change f.sum (fun i c => c*s (i+j)) = _
  rw [Fin.sum_univ_eq_sum_range (fun i => f.coeff i*s (i+j)) (t+1)]
  apply Polynomial.sum_eq_of_subset _ (fun _ => by simp)
  intro i hi
  apply Finset.mem_range.mpr
  have := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
  omega
theorem recurrence_kernel_iff_matrix (s : Fin 2 → ℕ → K) (m t : ℕ) (f : (Polynomial K)) :
    InRecurrenceKernel s m t f ↔ f.natDegree ≤ t ∧
      (recurrenceMatrix s m t).mulVec (fun i => f.coeff i.val) = 0 := by
  constructor
  · rintro ⟨hf,hrec⟩
    refine ⟨hf,?_⟩
    funext i
    have hh := hrec i.1 i.2.val i.2.isLt
    rw [recurrenceEval_eq_sum _ _ t f hf] at hh
    simpa only [recurrenceMatrix, Matrix.mulVec, dotProduct, Nat.add_comm,
      mul_comm, Pi.zero_apply] using hh
  · rintro ⟨hf,hker⟩
    refine ⟨hf,?_⟩
    intro b j hj
    rw [recurrenceEval_eq_sum _ _ t f hf]
    have hh := congrFun hker (b,⟨j,hj⟩)
    simpa only [recurrenceMatrix, Matrix.mulVec, dotProduct, Nat.add_comm,
      mul_comm, Pi.zero_apply] using hh
structure PrincipalAt (s : Fin 2 → ℕ → K) (m a q : ℕ) where
  generator : (Polynomial K)
  nonzero : generator ≠ 0
  degree_bound : generator.natDegree ≤ a
  kernel_eq : ∀ f : (Polynomial K), InRecurrenceKernel s m (a+q) f ↔
    ∃ Q : (Polynomial K), Q.natDegree ≤ q ∧ f=generator*Q
theorem PrincipalAt.generator_small {s : Fin 2 → ℕ → K} {m a q : ℕ}
    (P : PrincipalAt s m a q) (hL : a+q < m) :
    InRecurrenceKernel s m a P.generator := by
  apply generator_in_small_kernel s m a q hL P.generator P.degree_bound
  intro l hl
  apply (P.kernel_eq _).mpr
  exact ⟨«X»^l,by simpa using hl,rfl⟩
theorem PrincipalAt.small_kernel_line {s : Fin 2 → ℕ → K} {m a q : ℕ}
    (P : PrincipalAt s m a q) (hL : a+q < m) :
    LinearMap.ker (recurrenceMatrix s m a).mulVecLin =
      K ∙ (fun i : Fin (a+1) => P.generator.coeff i.val) := by
  have hgen := (recurrence_kernel_iff_matrix s m a P.generator).mp (P.generator_small hL)
  apply le_antisymm
  · intro c hc
    let f := (Polynomial.degreeLTEquiv K (a+1)).symm c
    have hfdeg : (f : (Polynomial K)).natDegree ≤ a := degreeLT_natDegree_le f
    have hfcoeff : ∀ i : Fin (a+1), (f : (Polynomial K)).coeff i.val=c i := by
      intro i
      exact congrFun ((Polynomial.degreeLTEquiv K (a+1)).apply_symm_apply c) i
    have hrec : InRecurrenceKernel s m a (f : (Polynomial K)) := by
      apply (recurrence_kernel_iff_matrix s m a _).mpr
      refine ⟨hfdeg,?_⟩
      have hc' : (recurrenceMatrix s m a).mulVec c=0 := hc
      simpa only [hfcoeff] using hc'
    obtain ⟨b,hb⟩ := principal_small_kernel_line s m a q (by omega)
      P.generator P.nonzero P.kernel_eq f hrec
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b,?_⟩
    funext i
    have hbi := congrArg (fun f : (Polynomial K) => f.coeff i.val) hb
    simpa only [hfcoeff, Polynomial.coeff_smul, Pi.smul_apply, smul_eq_mul] using hbi.symm
  · apply Submodule.span_le.mpr
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    exact hc ▸ hgen.2
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {K : Type*} [Field K]
theorem small_kernel_multiples (s : Fin 2 → ℕ → K) (m a q : ℕ)
    (hsize : a+q ≤ m) (f Q : (Polynomial K)) (hf : InRecurrenceKernel s m a f)
    (hQ : Q.natDegree ≤ q) : InRecurrenceKernel s m (a+q) (f*Q) := by
  refine ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hf.1 hQ),?_⟩
  intro b i hi
  have hterm (j : Fin (q+1)) :
      recurrenceEval (s b) i (f*Polynomial.monomial j.val (Q.coeff j.val))=0 := by
    have hpoly : f*Polynomial.monomial j.val (Q.coeff j.val) =
        Q.coeff j.val • (f*«X»^j.val) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.smul_eq_C_mul]
      ring
    rw [hpoly,map_smul]
    have hz := (small_kernel_shifts s m a q hsize f hf j.val (by omega)).2 b i hi
    rw [hz,smul_zero]
  calc
    _ = ∑ j : Fin (q+1), recurrenceEval (s b) i
        (f*Polynomial.monomial j.val (Q.coeff j.val)) := by
      conv_lhs => rw [← assemble_coefficients q Q hQ,assemble,Finset.mul_sum,map_sum]
    _ = 0 := Finset.sum_eq_zero (fun j _ => hterm j)
theorem PrincipalAt.big_nullity {s : Fin 2 → ℕ → K} {m a q : ℕ}
    (P : PrincipalAt s m a q) :
    Module.finrank K (LinearMap.ker (recurrenceMatrix s m (a+q)).mulVecLin)=q+1 := by
  let M := recurrenceMatrix s m (a+q)
  let f := multipleCoefficients P.generator q (a+q)
  have hinj := multipleCoefficients_injective P.generator a q (a+q)
    P.nonzero P.degree_bound (by omega)
  have heq : LinearMap.range f=LinearMap.ker M.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨Q,rfl⟩
      have hrec := (P.kernel_eq _).mpr ⟨Q,degreeLT_natDegree_le Q,rfl⟩
      exact ((recurrence_kernel_iff_matrix s m (a+q) _).mp hrec).2
    · intro c hc
      let E := assemble c
      have hE : InRecurrenceKernel s m (a+q) E := by
        apply (recurrence_kernel_iff_matrix s m (a+q) E).mpr
        refine ⟨assemble_natDegree_le _,?_⟩
        have hc' : M.mulVec c=0 := hc
        simpa only [E,assemble_coeff] using hc'
      obtain ⟨Q,hQ,hEQ⟩ := (P.kernel_eq E).mp hE
      refine ⟨⟨Q,Polynomial.mem_degreeLT.mpr
        (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<q+1 by omega)))⟩,?_⟩
      funext j
      change (P.generator*Q).coeff j.val=c j
      rw [← hEQ]
      exact assemble_coeff c j
  rw [← heq,LinearMap.finrank_range_of_inj hinj]
  exact ((Polynomial.degreeLTEquiv K (q+1)).finrank_eq).trans (by simp)
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
def parameterSyndromes (p : ℕ) (x u v : ι → F) (b : Fin 2) (j : ℕ) : (Polynomial F) :=
  if b=0 then C (syndrome x u j)+«X»*C (syndrome x v j)
  else C (syndrome x u j ^ p)+«X»^p*C (syndrome x v j ^ p)
theorem recurrenceMatrix_parameter (φ : (Polynomial F) →+* K) (p : ℕ) (x u v : ι → F)
    (m t : ℕ) : recurrenceMatrix (fun b j => φ (parameterSyndromes p x u v b j)) m t =
      (stacked p x u v (m-t) t).map φ := by
  rfl
theorem family_multiples_annihilate (p : ℕ) (x u v : ι → F) (m a q : ℕ)
    (hsize : a+q ≤ m) (P : (Polynomial (Polynomial F))) (hP : P.natDegree ≤ a)
    (hker : (stacked p x u v (m-a) a).mulVec
      (fun j : Fin (a+1) => P.coeff j.val)=0)
    (γ : F) (Q : Polynomial.degreeLT F (q+1)) :
    ((stacked p x u v (m-(a+q)) (a+q)).map (Polynomial.evalRingHom γ)).mulVec
      (multipleCoefficients (P.map (Polynomial.evalRingHom γ)) q (a+q) Q)=0 := by
  let s := fun b j => (parameterSyndromes p x u v b j).eval γ
  have hsmall : InRecurrenceKernel s m a (P.map (Polynomial.evalRingHom γ)) := by
    apply (recurrence_kernel_iff_matrix s m a _).mpr
    refine ⟨Polynomial.natDegree_map_le.trans hP,?_⟩
    change ((stacked p x u v (m-a) a).map (Polynomial.evalRingHom γ)).mulVec
      (fun i : Fin (a+1) => (P.map (Polynomial.evalRingHom γ)).coeff i.val)=0
    exact family_kernel_map (Polynomial.evalRingHom γ) _ P (fun j : Fin (a+1) => j.val) hker
  have hbig := small_kernel_multiples s m a q hsize _ Q hsmall (degreeLT_natDegree_le Q)
  have hbigM := ((recurrence_kernel_iff_matrix s m (a+q) _).mp hbig).2
  change ((stacked p x u v (m-(a+q)) (a+q)).map (Polynomial.evalRingHom γ)).mulVec
    (fun i : Fin (a+q+1) => ((P.map (Polynomial.evalRingHom γ))*(Q:(Polynomial F))).coeff i.val)=0 at hbigM
  exact hbigM
end
end FrobeniusLocator.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
theorem two_block_rank_exception_count (p : ℕ) [ExpChar F p]
    (x u v : ι → F) (L t r : ℕ)
    (hr : GenericLayer.genericRank (stacked p x u v L t)=t+1-r)
    (hfirst : GenericLayer.genericRank (hankel x u v L t)=L)
    (Γ : Finset F) (hΓ : ∀ γ∈Γ,
      ((stacked p x u v L t).map (evalRingHom γ)).rank ≠ t+1-r) :
    Γ.card ≤ L+p*(t+1-r-L) := by
  obtain ⟨B,hledger,hdeg⟩ :=
    GenericLayer.exists_frobenius_basis p x u v L t r hr hfirst
  apply (Polynomial.card_le_degree_of_subset_roots ?_).trans hdeg
  intro γ hγ
  apply (Polynomial.mem_roots B.minor_ne).mpr
  by_contra hn
  exact hΓ γ hγ (NormalFiber.rank_specializes _
    (IsFractionRing.injective (Polynomial F) (GenericLayer.GenericField F)) _ _ B γ hn)
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_6_2
open Polynomial Matrix Finset
open FrobeniusLocator
open scoped BigOperators
private def unitColumns {R row col : Type*} [Zero R] [One R] [DecidableEq row]
    (rows : col → row) : Matrix row col R :=
  fun i j => (Pi.single (rows j) 1 : row → R) i
private theorem transpose_mul_unitColumns {R row col pick : Type*}
    [CommRing R] [Fintype row] [DecidableEq row]
    (W : Matrix row col R) (rows : pick → row) :
    W.transpose * unitColumns rows = (W.submatrix rows id).transpose := by
  ext i j
  change W.transpose.mulVec (Pi.single (rows j) 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl
variable {E : Type*} [Field E] {r s : ℕ}
private theorem augmentation_det_ne_zero
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) E)
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) E)
    (hWC : W.transpose * C = 0)
    (hC : ∀ a, C.mulVec a = 0 → a = 0)
    (rows : Fin s → (Fin r ⊕ Fin s)) (hminor : (W.submatrix rows id).det ≠ 0) :
    (Matrix.fromCols C (unitColumns rows)).det ≠ 0 := by
  let A := Matrix.fromCols C (unitColumns rows)
  have hker : ∀ v, A.mulVec v = 0 → v = 0 := by
    intro v hv
    have hz := congrArg W.transpose.mulVec hv
    change W.transpose.mulVec ((Matrix.fromCols C (unitColumns rows)).mulVec v) =
      W.transpose.mulVec 0 at hz
    rw [Matrix.mulVec_zero, Matrix.fromCols_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hWC, Matrix.zero_mulVec,
      zero_add, transpose_mul_unitColumns] at hz
    have hs : v ∘ Sum.inr = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero (by simpa only [Matrix.det_transpose] using hminor) hz
    change (Matrix.fromCols C (unitColumns rows)).mulVec v = 0 at hv
    rw [Matrix.fromCols_mulVec, hs, Matrix.mulVec_zero, add_zero] at hv
    have hr := hC _ hv
    funext i
    cases i with
    | inl i => exact congrFun hr i
    | inr i => exact congrFun hs i
  have hinj : Function.Injective A.mulVec := by
    intro u v huv
    exact sub_eq_zero.mp (hker (u - v) (by rw [Matrix.mulVec_sub, huv, sub_self]))
  exact ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero
private theorem augmented_minor_cross
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) E)
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) E)
    (hWC : W.transpose * C = 0)
    (hC : ∀ a, C.mulVec a = 0 → a = 0)
    (rows : Fin s → (Fin r ⊕ Fin s)) (hminor : (W.submatrix rows id).det ≠ 0) :
    (Matrix.fromCols C (unitColumns rows)).det ≠ 0 ∧
    ∀ pick : Fin s → (Fin r ⊕ Fin s),
      (Matrix.fromCols C (unitColumns pick)).det * (W.submatrix rows id).det =
        (Matrix.fromCols C (unitColumns rows)).det * (W.submatrix pick id).det := by
  let A := Matrix.fromCols C (unitColumns rows)
  have hA := augmentation_det_ne_zero C W hWC hC rows hminor
  refine ⟨hA, ?_⟩
  intro pick
  let B := Matrix.fromCols C (unitColumns pick)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  let T := A⁻¹ * B
  let J : Matrix (Fin r ⊕ Fin s) (Fin r) E := Matrix.fromRows 1 0
  have hAJ : A * J = C := by
    simp only [A, J, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hfirst : T.submatrix id Sum.inl = J := by
    change A⁻¹ * C = J
    rw [← hAJ, Matrix.nonsing_inv_mul_cancel_left A J hunit]
  let D := T.submatrix Sum.inr Sum.inr
  have hT : T = Matrix.fromBlocks 1 (T.submatrix Sum.inl Sum.inr) 0 D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrFun (congrFun hfirst (Sum.inl i)) j
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => exact congrFun (congrFun hfirst (Sum.inr i)) j
      | inr j => rfl
  have hAT : A * T = B := Matrix.mul_nonsing_inv_cancel_left A B hunit
  have hWaug (I : Fin s → (Fin r ⊕ Fin s)) :
      W.transpose * Matrix.fromCols C (unitColumns I) =
        Matrix.fromCols 0 (W.submatrix I id).transpose := by
    rw [Matrix.mul_fromCols, hWC, transpose_mul_unitColumns]
  have hbottom : (W.submatrix rows id).transpose * D = (W.submatrix pick id).transpose := by
    have hh : (W.transpose * A) * T = W.transpose * B := by rw [Matrix.mul_assoc, hAT]
    change (W.transpose * Matrix.fromCols C (unitColumns rows)) * T =
      W.transpose * Matrix.fromCols C (unitColumns pick) at hh
    rw [hWaug, hWaug, hT, Matrix.fromCols_mul_fromBlocks, Matrix.zero_mul,
      Matrix.mul_zero, zero_add, Matrix.zero_mul, zero_add] at hh
    exact congrArg (fun M : Matrix (Fin s) (Fin r ⊕ Fin s) E => M.submatrix id Sum.inr) hh
  have hdetD : (W.submatrix rows id).det * D.det = (W.submatrix pick id).det := by
    simpa only [Matrix.det_mul, Matrix.det_transpose] using congrArg Matrix.det hbottom
  have hdetT : T.det = D.det := by
    rw [hT, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have hdetB : B.det = A.det * D.det := by
    rw [← hAT, Matrix.det_mul, hdetT]
  change B.det * (W.submatrix rows id).det = A.det * (W.submatrix pick id).det
  rw [hdetB, ← hdetD]
  ring
variable {F : Type*} [Field F]
private theorem augmented_det_degree
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) (Polynomial F))
    (d : (Fin r ⊕ Fin s) → ℕ) (hpositive : ∀ i, 1 ≤ d i)
    (hdegree : ∀ i j, (C i j).natDegree ≤ d i)
    (rows : Fin s → (Fin r ⊕ Fin s)) :
    (Matrix.fromCols C (unitColumns rows)).det.natDegree ≤ (∑ i, d i) - s := by
  classical
  let A := Matrix.fromCols C (unitColumns rows : Matrix _ _ (Polynomial F))
  change A.det.natDegree ≤ _
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hsign : (Equiv.Perm.sign σ • ∏ j, A (σ j) j).natDegree =
      (∏ j, A (σ j) j).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
  rw [hsign]
  let saving : (Fin r ⊕ Fin s) → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  have hpoint (j : Fin r ⊕ Fin s) : (A (σ j) j).natDegree + saving j ≤ d (σ j) := by
    cases j with
    | inl j => simpa [A, saving] using hdegree (σ (Sum.inl j)) j
    | inr j =>
      change ((Pi.single (rows j) 1 : Fin r ⊕ Fin s → (Polynomial F))
        (σ (Sum.inr j))).natDegree + 1 ≤
        d (σ (Sum.inr j))
      simp only [Pi.single_apply]
      split_ifs <;> simpa only [Polynomial.natDegree_one, Polynomial.natDegree_zero, zero_add]
        using hpositive (σ (Sum.inr j))
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  have hsaving : (∑ j, saving j) = s := by simp [saving, Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib, hsaving, Equiv.sum_comp σ d] at hsum
  have hprod := Polynomial.natDegree_prod_le Finset.univ (fun j => A (σ j) j)
  omega
private theorem map_augmentation (φ : (Polynomial F) →+* E)
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) (Polynomial F)) (rows : Fin s → (Fin r ⊕ Fin s)) :
    φ (Matrix.fromCols C (unitColumns rows)).det =
      (Matrix.fromCols (C.map φ) (unitColumns rows)).det := by
  rw [φ.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  cases j with
  | inl j => rfl
  | inr j =>
    change φ ((Pi.single (rows j) 1 : Fin r ⊕ Fin s → (Polynomial F)) i) =
      (Pi.single (rows j) 1 : Fin r ⊕ Fin s → E) i
    simp only [Pi.single_apply]
    split_ifs <;> simp
theorem primitive_minor_degree (φ : (Polynomial F) →+* E) (hφ : Function.Injective φ)
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) (Polynomial F))
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) (Polynomial F))
    (hWC : (W.map φ).transpose * (C.map φ) = 0)
    (hC : ∀ a, (C.map φ).mulVec a = 0 → a = 0)
    (hprim : PrimitiveVector.IsPrimitive
      (fun I : Fin s → (Fin r ⊕ Fin s) => (W.submatrix I id).det))
    (d : (Fin r ⊕ Fin s) → ℕ) (hpositive : ∀ i, 1 ≤ d i)
    (hdegree : ∀ i j, (C i j).natDegree ≤ d i)
    (rows : Fin s → (Fin r ⊕ Fin s)) :
    (W.submatrix rows id).det.natDegree ≤ (∑ i, d i) - s := by
  classical
  let P (I : Fin s → (Fin r ⊕ Fin s)) := (W.submatrix I id).det
  let A (I : Fin s → (Fin r ⊕ Fin s)) := (Matrix.fromCols C (unitColumns I)).det
  change (P rows).natDegree ≤ _
  by_cases hP : P rows = 0
  · simp [hP]
  have hmap (I : Fin s → (Fin r ⊕ Fin s)) : φ (P I) = ((W.map φ).submatrix I id).det :=
    φ.map_det (W.submatrix I id)
  have hW : ((W.map φ).submatrix rows id).det ≠ 0 := by
    rw [← hmap]
    exact fun hz => hP (hφ (hz.trans (map_zero φ).symm))
  obtain ⟨hAfield, hcrossField⟩ := augmented_minor_cross (C.map φ) (W.map φ) hWC hC rows hW
  have hA : A rows ≠ 0 := by
    intro hz
    apply hAfield
    rw [← map_augmentation φ C rows]
    exact (congrArg φ hz).trans (map_zero φ)
  have hcross (I : Fin s → (Fin r ⊕ Fin s)) : A I * P rows = A rows * P I := by
    apply hφ
    simpa only [map_mul, hmap, A, map_augmentation] using hcrossField I
  obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout P).mp hprim
  let q := ∑ I, a I * A I
  have hfactor : A rows = q * P rows := by
    calc
      A rows = (∑ I, a I * P I) * A rows := by rw [ha, one_mul]
      _ = q * P rows := by
        dsimp only [q]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro I _
        rw [mul_assoc, mul_comm (P I), ← hcross I, ← mul_assoc]
  have hq : q ≠ 0 := by
    intro hz
    exact hA (by rw [hfactor, hz, zero_mul])
  have hbound := augmented_det_degree C d hpositive hdegree rows
  change (A rows).natDegree ≤ _ at hbound
  rw [hfactor, Polynomial.natDegree_mul hq hP] at hbound
  omega
end K1_6_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]
theorem exists_primitive_kernel_vector (φ : (Polynomial F) →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col (Polynomial F)) (r : ℕ) (B : NormalFiber.RowBasis φ M r)
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i)
    (E : col → K) (hE0 : E ≠ 0) (hE : (M.map φ).mulVec E = 0) :
    ∃ v : col → (Polynomial F), PrimitiveVector.IsPrimitive v ∧ M.mulVec v = 0 ∧
      (∀ j, (v j).natDegree ≤ ∑ i, d (B.rows i)) ∧
      (∀ γ, ∃ j, (v j).eval γ ≠ 0) := by
  classical
  have hcofactor : ∃ j, GenericCofactor.vector B j ≠ 0 := by
    by_contra h
    push_neg at h
    have hspan := GenericCofactor.generic_spans B hφ E hE
    have hz : ∀ j, (fun c => φ (GenericCofactor.vector B j c)) = 0 := by
      intro j
      funext c
      rw [h j]
      exact map_zero φ
    rw [show (∑ j, (E j / φ (NormalFiber.pivot B).det) •
      (fun c => φ (GenericCofactor.vector B j c))) = 0 by simp only [hz,smul_zero,
        Finset.sum_const_zero]] at hspan
    exact hE0 hspan
  obtain ⟨j,hj⟩ := hcofactor
  obtain ⟨g,v,hg,hgv,hprim⟩ := PrimitiveVector.exists_normalization
    (GenericCofactor.vector B j) hj
  refine ⟨v,hprim,?_,?_,PrimitiveVector.exists_eval_ne_zero v hprim⟩
  · exact PrimitiveVector.normalization_preserves_kernel M _ v g hg hgv
      (GenericCofactor.annihilates B hφ j)
  · intro c
    exact (PrimitiveVector.normalization_natDegree_le _ v g hg hgv c).trans
      (GenericCofactor.vector_natDegree_le B d hdeg j c)
end
end FrobeniusLocator.Principal
end

end Merged6967_Fast006
