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
import ProximityPrize.SubmissionLower.BC
set_option Elab.async false
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
theorem ayC {q:ℕ} (Q:z3F F (q+1)) :
   (Q:F[X]).natDegree≤q:= by
 by_cases hQ: (Q:F[X])=0
 · simp [hQ]
 · have h:=(Polynomial.natDegree_lt_iff_degree_lt hQ).mpr
     (Polynomial.mem_degreeLT.mp Q.property)
   omega
def aOU (g:F[X]) (q t:ℕ) :
    z3F F (q+1) →ₗ[F] (Fin (t+1)→F) where
  toFun Q j:=(g*(Q:F[X])).coeff j.val
  map_add' Q R:= by ext j; simp [mul_add]
  map_smul' c Q:= by ext j; simp [zGx]
theorem bcF (t:ℕ) (P Q:F[X])
   (hP:P.natDegree≤t) (hQ:Q.natDegree≤t)
   (hcoeff : ∀ j:Fin (t+1),P.coeff j.val= Q.coeff j.val) :P= Q:= by
 ext j
 by_cases hj:j<t+1
 · exact hcoeff ⟨j,hj⟩
 · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
     Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
theorem b9A (g:F[X]) (a q t:ℕ)
   (hg:g≠0) (hga :g.natDegree≤a) (hsize :a+q≤t) :
   zq4 (aOU g q t) := by
 intro Q R hQR
 apply zkt
 apply zyS hg
 apply bcF t
 · exact Polynomial.natDegree_mul_le.trans (by have :=ayC Q; omega)
 · exact Polynomial.natDegree_mul_le.trans (by have :=ayC R; omega)
 · exact fun j=>zTC hQR j
theorem c1F (a q t:ℕ) (M:z30 row (Fin (t+1)) F)
   (g:F[X]) (hg:g≠0) (hga :g.natDegree≤a)
   (hsize :a+q≤t)
   (hnull:zsE F (z83 M.mulVecLin)=q+1)
   (hshift : ∀ Q:z3F F (q+1),
     M.mulVec (aOU g q t Q)=0)
   (E :F[X]) (hE :E.natDegree≤t)
   (hker :M.mulVec (fun j:Fin (t+1)=>E.coeff j.val)=0) :
   ∃ Q:F[X],Q.natDegree≤q∧E=g*Q:= by
 let f :=aOU g q t
 have hinj:=b9A g a q t hg hga hsize
 have hdim:zsE F (zWl f)=q+1 := by
   rw [z0K hinj]
   exact ((zAj F (q+1)).finrank_eq).trans
     (by simp [Module.finrank_fintype_fun_eq_card])
 have hsub:zWl f≤z83 M.mulVecLin:= by
   rintro _ ⟨Q,rfl⟩
   exact hshift Q
 have heq :zWl f=z83 M.mulVecLin :=
   Submodule.eq_of_le_of_finrank_eq hsub (hdim.trans hnull.symm)
 have hmem: (fun j:Fin (t+1)=>E.coeff j.val)∈zWl f := by
   rw [heq]
   exact hker
 obtain ⟨Q,hQ⟩:=hmem
 refine ⟨Q,ayC Q,?_⟩
 symm
 apply bcF t
 · exact Polynomial.natDegree_mul_le.trans (by have :=ayC Q; omega)
 · exact hE
 · exact fun j=>zTC hQ j
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
def assemble {R:Type*} [z0Y R] {d:ℕ} (v :Fin (d+1)→R) :R[X] :=
 ∑ j,zdM j.val (v j)
theorem ahe {R:Type*} [z0Y R] {d:ℕ}
   (v :Fin (d+1)→R) (j:Fin (d+1)) : (assemble v).coeff j.val=v j:= by
 classical
 simp only [assemble,zaW,zQm]
 rw [Finset.sum_eq_single j]
 · simp
 · intro b _ hbj
   simp [show b.val≠j.val from fun h=>hbj (Fin.ext h)]
 · simp
theorem aCg {R:Type*} [z0Y R] {d:ℕ}
  (v :Fin (d+1)→R) : (assemble v).natDegree≤d:= by
 apply zMZ
 intro j _
 exact (Polynomial.natDegree_monomial_le (v j)).trans (by omega)
theorem cZi {R S:Type*} [z0Y R] [z0Y S] {d:ℕ}
  (φ:R →+* S) (v :Fin (d+1)→R) :
  (assemble v).map φ=assemble (fun j=>φ (v j)) := by
 simp [assemble,Polynomial.map_sum]
theorem bwQ {F:Type*} [zrb F] {d:ℕ}
  (v :Fin (d+1)→F[X]) (γ:F) :
  specialize v γ=assemble (fun j=>(v j).eval γ) := by
 simp only [specialize,assemble,zoT]
theorem bUg {F:Type*} [zrb F] {d:ℕ}
  (v :Fin (d+1)→F[X]) (γ:F) :
  (assemble v).map (zhy γ)=specialize v γ:= by
 rw [cZi,bwQ]
 rfl
theorem dtp {R:Type*} [z0Y R] {d:ℕ}
  (v :Fin (d+1)→R) (hv :v≠0) :assemble v≠0:= by
 intro hz
 apply hv
 funext j
 have h:=zPw (fun f :R[X]=>f.coeff j.val) hz
 simpa only [ahe,coeff_zero,zbd] using h
theorem eEZ {F K:Type*} [zrb F] [zrb K] {d:ℕ}
  (φ:F[X] →+* K) (v :Fin (d+1)→F[X]) (x :F) :
  φ (avE v x)=(assemble (fun j=>φ (v j))).eval (φ (C x)) := by
 simp only [avE,zdo,zok,assemble,Polynomial.eval_finsetSum,
  Polynomial.eval_monomial]
 apply zUo rfl
 intro j _
 have hp:φ (C (x^j.val))=(φ (C x))^j.val := by rw [← map_pow,← Polynomial.C_pow]
 rw [hp,zDE]
variable {R S row col:Type*} [za6 R] [za6 S] [z85 col]
theorem d6i (φ:R →+* S) (M:z30 row col R)
  (P:R[X]) (indices :col→ℕ)
  (hker :M.mulVec (fun j=>P.coeff (indices j))=0) :
  (M.map φ).mulVec (fun j=>(P.map φ).coeff (indices j))=0:= by
 funext i
 have hi:=zPw φ (zTC hker i)
 simpa only [zeQ,zKe,zdo,zok,zhd,
  z0b,zAg,zbd] using hi
theorem d6j (φ:R →+* S) (hφ:zq4 φ)
  (M:z30 row col R) (P:R[X]) (indices :col→ℕ)
  (hker : (M.map φ).mulVec (fun j=>(P.map φ).coeff (indices j))=0) :
  M.mulVec (fun j=>P.coeff (indices j))=0:= by
 funext i
 apply hφ
 have hi:=zTC hker i
 simpa only [zeQ,zKe,zdo,zok,zhd,
  z0b,zAg,zbd] using hi
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
def az1 (s :ℕ→K) (j:ℕ) :K[X] →ₗ[K] K where
  toFun f :=f.sum (fun i c=>c*s (i+j))
  map_add' f g:=Polynomial.sum_add_index f g _ (fun _=> by simp)
    (fun _ _ _=> by ring)
  map_smul' c f := by
    rw [Polynomial.sum_smul_index _ _ _ (fun _=> by simp)]
    simp only [RingHom.id_apply,zs5,Polynomial.sum,zxw]
    apply zUo rfl
    intro i _
    ring
theorem c7D (s :ℕ→K) (j i:ℕ) (c:K) :
  az1 s j (zdM i c)=c*s (i+j) := by
 change (zdM i c:K[X]).sum (fun n a=>a*s (n+j))= _
 exact Polynomial.sum_monomial_index c (fun n a=>a*s (n+j)) (zero_mul _)
theorem bLb (s :ℕ→K) (j l:ℕ) (f :K[X]) :
   az1 s j (f*X^l)=az1 s (j+l) f := by
 induction f using Polynomial.induction_on' with
 | add f g hf hg=>simp only [add_mul,map_add,hf,hg]
 | monomial i c =>
   rw [X_pow_eq_monomial,Polynomial.monomial_mul_monomial,
    zqe,c7D,c7D]
   congr 2
   omega
def akK (s :Fin 2→ℕ→K) (m t:ℕ) (f :K[X]) :Prop :=
 f.natDegree≤t ∧ ∀ b j,j< m-t→az1 (s b) j f=0
theorem efp (s :Fin 2→ℕ→K) (m a q:ℕ)
  (hL:a+q< m) (g:K[X]) (hga :g.natDegree≤a)
  (hshift : ∀ l≤q,akK s m (a+q) (g*X^l)) :
  akK s m a g:= by
 refine ⟨hga,?_⟩
 intro b j hj
 let l:=min j q
 let i:=j-l
 have hl:l≤q:=min_le_right _ _
 have hlj:l≤j:=min_le_left _ _
 have hi:i< m-(a+q) := by dsimp [i,l]; omega
 have hij:i+l=j:= by dsimp [i]; omega
 have h:=(hshift l hl).2 b i hi
 rw [bLb,hij] at h
 exact h
theorem cp7 (s :Fin 2→ℕ→K) (m a q:ℕ)
   (hsize :a+q≤ m) (f :K[X]) (hf :akK s m a f)
   (l:ℕ) (hl:l≤q) :akK s m (a+q) (f*X^l) := by
 refine ⟨?_,?_⟩
 · have hdegree :=hf.1
   exact Polynomial.natDegree_mul_le.trans (by simp only [natDegree_X_pow]; omega)
 · intro b j hj
   rw [bLb]
   exact hf.2 b (j+l) (by omega)
theorem eOD (s :Fin 2→ℕ→K) (m a q:ℕ)
   (hsize :a+q≤ m) (g:K[X]) (hg:g≠0)
   (hprincipal : ∀ f :K[X],akK s m (a+q) f ↔
     ∃ Q:K[X],Q.natDegree≤q∧f=g*Q)
   (f :K[X]) (hf :akK s m a f) :
   ∃ c:K,f=c•g:= by
 have hfirst:=cp7 s m a q hsize f hf 0 (by omega)
 simp only [pow_zero,zqe] at hfirst
 obtain ⟨Q,hQ,hfQ⟩:=(hprincipal f).mp hfirst
 have hlast :=cp7 s m a q hsize f hf q (by omega)
 obtain ⟨R,hR,hfR⟩:=(hprincipal (f*X^q)).mp hlast
 have hQR:Q*X^q=R:= by
   apply zyS hg
   rw [← ztg,← hfQ,hfR]
 by_cases hQ0:Q=0
 · exact ⟨0,by simp [hfQ,hQ0]⟩
 have hQdegree :Q.natDegree=0:= by
   have hdeg:=zNh hQ0 (pow_ne_zero q X_ne_zero)
   rw [hQR,natDegree_X_pow] at hdeg
   omega
 have hQC:Q=C (Q.coeff 0) :=zr7 hQdegree
 refine ⟨Q.coeff 0,?_⟩
 rw [hfQ,hQC]
 simp only [zQI,coeff_C_zero]
 ring
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
def bsQ (H :R[X]) (a d:ℕ) :
    z30 (Fin (a+1)) (Fin (d+1)) R :=
  fun l j=>(H*X^j.val).coeff l.val
def az6 (a d:ℕ) (M:z30 row (Fin (a+1)) R) (H :R[X]) :
    z30 row (Fin (d+1)) R:=M*bsQ H a d
theorem eEl (H :R[X]) (a d:ℕ) (c:Fin (d+1)→R) :
   (bsQ H a d).mulVec c =
     (fun l:Fin (a+1)=>(H*assemble c).coeff l.val) := by
 funext l
 simp only [bsQ,zeQ,zKe,assemble]
 rw [zxw,zaW]
 apply zUo rfl
 intro j _
 rw [← zoT]
 have heq :H*(C (c j)*X^j.val)=c j•(H*X^j.val) := by
   rw [zQI]
   ring
 rw [heq,zmM,zs5,zDE]
theorem cfn (a d:ℕ) (M:z30 row (Fin (a+1)) R) (H :R[X])
   (c:Fin (d+1)→R) :
   (az6 a d M H).mulVec c =
     M.mulVec (fun l:Fin (a+1)=>(H*assemble c).coeff l.val) := by
 rw [az6,← zbx,eEl]
theorem fXe {S:Type*} [za6 S]
   (a d:ℕ) (φ:R →+* S) (M:z30 row (Fin (a+1)) R) (H :R[X]) :
   (az6 a d M H).map φ =
     az6 a d (M.map φ) (H.map φ) := by
 ext i j
 simp only [az6,Matrix.mul_apply,zAg,zdo,zok,
   bsQ,z0b]
 apply zUo rfl
 intro l _
 have heq :φ ((H*X^j.val).coeff l.val)=(H.map φ*X^j.val).coeff l.val := by
   rw [← z0b,zNl,z5m,Polynomial.map_X]
 rw [heq]
theorem bUf {K:Type*} [zrb K] (d:ℕ) (P:K[X])
   (hP:P.natDegree≤d) :assemble (fun j:Fin (d+1)=>P.coeff j.val)=P:= by
 apply bcF d
 · exact aCg _
 · exact hP
 · intro j
   exact ahe _ j
theorem fXg {F:Type*} [zrb F] (a d:ℕ)
    (M:z30 row (Fin (a+1)) F[X]) (H :F[X]) (cost:row→ℕ)
    (hM : ∀ i j,(M i j).natDegree≤ cost i) (i:row) (j:Fin (d+1)) :
    (az6 a d M (H.map (z1z:F →+* F[X])) i j).natDegree≤ cost i:= by
  simp only [az6,Matrix.mul_apply,bsQ]
  apply zMZ
  intro l _
  have hcoeff : ((H.map (z1z:F →+* F[X]))*(z7y:F[X][X])^j.val).coeff l.val =
      (z1z:F →+* F[X]) ((H*(z7y:F[X])^j.val).coeff l.val) := by
    have heq : (H*(z7y:F[X])^j.val).map (z1z:F →+* F[X]) =
        H.map (z1z:F →+* F[X])*(z7y:F[X][X])^j.val := by
      rw [zNl,z5m,Polynomial.map_X]
    have hc:=zPw (fun P:F[X][X]=>P.coeff l.val) heq
    simpa only [z0b] using hc.symm
  change (M i l*((H.map (z1z:F →+* F[X]))*(z7y:F[X][X])^j.val).coeff l.val).natDegree≤_
  rw [hcoeff,zDE]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hM i l)
variable {K:Type*} [zrb K]
theorem fXf (a h d:ℕ) (hah:h+d=a)
    (M:z30 row (Fin (a+1)) K) (H f :K[X])
    (hH :H≠0) (hHd:H.natDegree≤h) (hfd:f.natDegree≤d)
    (hkernel:z83 M.mulVecLin =
      K ∙ (fun j:Fin (a+1)=>(H*f).coeff j.val)) :
    z83 (az6 a d M H).mulVecLin =
      K ∙ (fun j:Fin (d+1)=>f.coeff j.val) := by
  have hHf : (H*f).natDegree≤a :=Polynomial.natDegree_mul_le.trans (by omega)
  apply zWs
  · intro c hc
    have hc' : (az6 a d M H).mulVec c=0:=hc
    rw [cfn] at hc'
    have hmem: (fun j:Fin (a+1)=>(H*assemble c).coeff j.val) ∈
        K ∙ (fun j:Fin (a+1)=>(H*f).coeff j.val) := by
      rw [← hkernel]
      exact hc'
    obtain ⟨b,hb⟩:=Submodule.mem_span_singleton.mp hmem
    have heq :H*assemble c=b•(H*f) := by
      apply bcF a
      · exact Polynomial.natDegree_mul_le.trans (by have :=aCg c; omega)
      · exact (Polynomial.natDegree_smul_le _ _).trans hHf
      · intro j
        have hh:=zTC hb j
        simpa only [zmM,zD4,zs5] using hh.symm
    have hcancel:assemble c=b•f := by
      apply zyS hH
      simpa only [zGx] using heq
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b,?_⟩
    funext j
    have hh:=zPw (fun P:K[X]=>P.coeff j.val) hcancel
    simpa only [ahe,zmM,zD4,zs5] using hh.symm
  · apply Submodule.span_le.mpr
    intro c hc
    rw [zpV] at hc
    subst c
    change (az6 a d M H).mulVec _=0
    rw [cfn,bUf d f hfd]
    have hmem: (fun j:Fin (a+1)=>(H*f).coeff j.val) ∈
        K ∙ (fun j:Fin (a+1)=>(H*f).coeff j.val) :=Submodule.mem_span_singleton_self _
    rw [← hkernel] at hmem
    exact hmem
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
def akc (s :Fin 2→ℕ→K) (m t:ℕ) :
    z30 (Fin 2×Fin (m-t)) (Fin (t+1)) K :=
  fun i j=>s i.1 (i.2.val+j.val)
theorem bLa (s :ℕ→K) (j t:ℕ) (f :K[X])
  (hf :f.natDegree≤t) :
  az1 s j f = ∑ i:Fin (t+1),f.coeff i.val*s (i.val+j) := by
 change f.sum (fun i c=>c*s (i+j))= _
 rw [Fin.sum_univ_eq_sum_range (fun i=>f.coeff i*s (i+j)) (t+1)]
 apply Polynomial.sum_eq_of_subset _ (fun _=> by simp)
 intro i hi
 apply Finset.mem_range.mpr
 have :=Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
 omega
theorem aPN (s :Fin 2→ℕ→K) (m t:ℕ) (f :K[X]) :
   akK s m t f↔f.natDegree≤t ∧
    (akc s m t).mulVec (fun i=>f.coeff i.val)=0:= by
 constructor
 · rintro ⟨hf,hrec⟩
   refine ⟨hf,?_⟩
   funext i
   have hh:=hrec i.1 i.2.val i.2.isLt
   rw [bLa _ _ t f hf] at hh
   simpa only [akc,zeQ,zKe,zg2,
    zDE,zbd] using hh
 · rintro ⟨hf,hker⟩
   refine ⟨hf,?_⟩
   intro b j hj
   rw [bLa _ _ t f hf]
   have hh:=zTC hker (b,⟨j,hj⟩)
   simpa only [akc,zeQ,zKe,zg2,
    zDE,zbd] using hh
structure atR (s :Fin 2→ℕ→K) (m a q:ℕ) where
 generator :K[X]
 nonzero :generator≠0
 aNb:generator.natDegree≤a
 aOk : ∀ f :K[X],akK s m (a+q) f ↔
  ∃ Q:K[X],Q.natDegree≤q∧f=generator*Q
theorem atR.efq {s :Fin 2→ℕ→K} {m a q:ℕ}
  (P:atR s m a q) (hL:a+q< m) :
  akK s m a P.generator := by
 apply efp s m a q hL P.generator P.aNb
 intro l hl
 apply (P.aOk _).mpr
 exact ⟨X^l,by simpa using hl,rfl⟩
theorem atR.gs0 {s :Fin 2→ℕ→K} {m a q:ℕ}
   (P:atR s m a q) (hL:a+q< m) :
   z83 (akc s m a).mulVecLin =
     K ∙ (fun i:Fin (a+1)=>P.generator.coeff i.val) := by
 have hgen:=(aPN s m a P.generator).mp (P.efq hL)
 apply zWs
 · intro c hc
   let f :=(zAj K (a+1)).symm c
   have hfdeg: (f :K[X]).natDegree≤a :=ayC f
   have hfcoeff : ∀ i:Fin (a+1),(f :K[X]).coeff i.val=c i:= by
     intro i
     exact zTC ((zAj K (a+1)).apply_symm_apply c) i
   have hrec:akK s m a (f :K[X]) := by
     apply (aPN s m a _).mpr
     refine ⟨hfdeg,?_⟩
     have hc' : (akc s m a).mulVec c=0:=hc
     simpa only [hfcoeff] using hc'
   obtain ⟨b,hb⟩:=eOD s m a q (by omega)
     P.generator P.nonzero P.aOk f hrec
   apply Submodule.mem_span_singleton.mpr
   refine ⟨b,?_⟩
   funext i
   have hbi:=zPw (fun f :K[X]=>f.coeff i.val) hb
   simpa only [hfcoeff,zmM,zD4,zs5] using hbi.symm
 · apply Submodule.span_le.mpr
   intro c hc
   rw [zpV] at hc
   exact hc ▸ hgen.2
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
theorem deM (s :Fin 2→ℕ→K) (m a q:ℕ)
    (hsize :a+q≤ m) (f Q:K[X]) (hf :akK s m a f)
    (hQ:Q.natDegree≤q) :akK s m (a+q) (f*Q) := by
  refine ⟨Polynomial.natDegree_mul_le.trans (z9f hf.1 hQ),?_⟩
  intro b i hi
  have hterm (j:Fin (q+1)) :
      az1 (s b) i (f*zdM j.val (Q.coeff j.val))=0:= by
    have hpoly :f*zdM j.val (Q.coeff j.val) =
        Q.coeff j.val•(f*X^j.val) := by
      rw [← zoT,zQI]
      ring
    rw [hpoly,map_smul]
    have hz :=(cp7 s m a q hsize f hf j.val (by omega)).2 b i hi
    rw [hz,smul_zero]
  calc
    _ = ∑ j:Fin (q+1),az1 (s b) i
        (f*zdM j.val (Q.coeff j.val)) := by
      conv_lhs=>rw [← bUf q Q hQ,assemble,zxw,zdo]
    _=0:=Finset.sum_eq_zero (fun j _=>hterm j)
theorem atR.dyW {s :Fin 2→ℕ→K} {m a q:ℕ}
    (P:atR s m a q) :
    zsE K (z83 (akc s m (a+q)).mulVecLin)=q+1 := by
  let M:=akc s m (a+q)
  let f :=aOU P.generator q (a+q)
  have hinj:=b9A P.generator a q (a+q)
    P.nonzero P.aNb (by omega)
  have heq :zWl f=z83 M.mulVecLin:= by
    apply zWs
    · rintro _ ⟨Q,rfl⟩
      have hrec:=(P.aOk _).mpr ⟨Q,ayC Q,rfl⟩
      exact ((aPN s m (a+q) _).mp hrec).2
    · intro c hc
      let E :=assemble c
      have hE :akK s m (a+q) E := by
        apply (aPN s m (a+q) E).mpr
        refine ⟨aCg _,?_⟩
        have hc' : M.mulVec c=0:=hc
        simpa only [E,ahe] using hc'
      obtain ⟨Q,hQ,hEQ⟩:=(P.aOk E).mp hE
      refine ⟨⟨Q,Polynomial.mem_degreeLT.mpr
        (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<q+1 by omega)))⟩,?_⟩
      funext j
      change (P.generator*Q).coeff j.val=c j
      rw [← hEQ]
      exact ahe c j
  rw [← heq,z0K hinj]
  exact ((zAj K (q+1)).finrank_eq).trans (by simp)
variable {F ι:Type} [zrb F] [z85 ι] [zRw ι]
def P8 (p:ℕ) (x u v :ι→F) (b:Fin 2) (j:ℕ) :F[X] :=
 if b=0 then C (oX x u j)+X*C (oX x v j)
 else C (oX x u j^p)+X^p*C (oX x v j^p)
theorem buO (φ:F[X] →+* K) (p:ℕ) (x u v :ι→F)
  (m t:ℕ) :akc (fun b j=>φ (P8 p x u v b j)) m t =
    (AI p x u v (m-t) t).map φ:= by
 rfl
theorem d6k (p:ℕ) (x u v :ι→F) (m a q:ℕ)
   (hsize :a+q≤ m) (P:F[X][X]) (hP:P.natDegree≤a)
   (hker : (AI p x u v (m-a) a).mulVec
     (fun j:Fin (a+1)=>P.coeff j.val)=0)
   (γ:F) (Q:z3F F (q+1)) :
   ((AI p x u v (m-(a+q)) (a+q)).map (zhy γ)).mulVec
     (aOU (P.map (zhy γ)) q (a+q) Q)=0:= by
 let s := fun b j=>(P8 p x u v b j).eval γ
 have hsmall:akK s m a (P.map (zhy γ)) := by
   apply (aPN s m a _).mpr
   refine ⟨Polynomial.natDegree_map_le.trans hP,?_⟩
   change ((AI p x u v (m-a) a).map (zhy γ)).mulVec
     (fun i:Fin (a+1)=>(P.map (zhy γ)).coeff i.val)=0
   exact d6i (zhy γ) _ P (fun j:Fin (a+1)=>j.val) hker
 have hbig:=deM s m a q hsize _ Q hsmall (ayC Q)
 have hbigM:=((aPN s m (a+q) _).mp hbig).2
 change ((AI p x u v (m-(a+q)) (a+q)).map (zhy γ)).mulVec
   (fun i:Fin (a+q+1)=>((P.map (zhy γ))*(Q:F[X])).coeff i.val)=0 at hbigM
 exact hbigM
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
theorem diw (p:ℕ) [ExpChar F p]
  (x u v :ι→F) (L t r :ℕ)
  (hr :Bx.adJ (AI p x u v L t)=t+1-r)
  (hfirst:Bx.adJ (QO x u v L t)=L)
  (Γ:zJe F) (hΓ : ∀ γ∈Γ,
    ((AI p x u v L t).map (zhy γ)).rank≠t+1-r) :
  Γ.card≤L+p*(t+1-r-L) := by
 obtain ⟨B,hledger,hdeg⟩ :=
  Bx.d4e p x u v L t r hr hfirst
 apply (Polynomial.card_le_degree_of_subset_roots ?_).trans hdeg
 intro γ hγ
 apply (Polynomial.mem_roots B.minor_ne).mpr
 by_contra hn
 exact hΓ γ hγ (zQ.buH _
  (IsFractionRing.injective F[X] (Bx.lN F)) _ _ B γ hn)
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace bz5
open Polynomial Matrix Finset
open gR
open scoped BigOperators
private def Tr {R row col:Type*} [Zero R] [One R] [zRw row]
  (rows :col→ row) :z30 row col R :=
 fun i j=>(znV (rows j) 1 :row→R) i
private theorem bx1 {R row col pick :Type*}
  [za6 R] [z85 row] [zRw row]
  (W:z30 row col R) (rows :pick→ row) :
  W.transpose*Tr rows=(W.submatrix rows id).transpose := by
 ext i j
 change W.transpose.mulVec (znV (rows j) 1) i= _
 rw [Matrix.mulVec_single_one]
 rfl
variable {E :Type*} [zrb E] {r s :ℕ}
private theorem duY
   (C:z30 (Fin r ⊕ Fin s) (Fin r) E)
   (W:z30 (Fin r ⊕ Fin s) (Fin s) E)
   (hWC:W.transpose*C=0)
   (hC : ∀ a,C.mulVec a=0→a=0)
   (rows :Fin s→(Fin r ⊕ Fin s)) (hminor : (W.submatrix rows id).det≠0) :
   (zE7 C (Tr rows)).det≠0:= by
 let A:=zE7 C (Tr rows)
 have hker : ∀ v,A.mulVec v=0→v=0:= by
   intro v hv
   have hz :=zPw W.transpose.mulVec hv
   change W.transpose.mulVec ((zE7 C (Tr rows)).mulVec v) =
     W.transpose.mulVec 0 at hz
   rw [zvf,zIR,Matrix.mulVec_add,
     zbx,zbx,hWC,Matrix.zero_mulVec,
     zOP,bx1] at hz
   have hs :v ∘ znU=0 :=
     Matrix.eq_zero_of_mulVec_eq_zero (by simpa only [zgP] using hminor) hz
   change (zE7 C (Tr rows)).mulVec v=0 at hv
   rw [zIR,hs,zvf,add_zero] at hv
   have hr :=hC _ hv
   funext i
   cases i with
   | inl i=>exact congrFun hr i
   | inr i=>exact congrFun hs i
 have hinj:zq4 A.mulVec:= by
   intro u v huv
   exact sub_eq_zero.mp (hker (u - v) (by rw [Matrix.mulVec_sub,huv,sub_self]))
 exact ((Matrix.isUnit_iff_isUnit_det A).mp
   (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero
private theorem du2
    (C:z30 (Fin r ⊕ Fin s) (Fin r) E)
    (W:z30 (Fin r ⊕ Fin s) (Fin s) E)
    (hWC:W.transpose*C=0)
    (hC : ∀ a,C.mulVec a=0→a=0)
    (rows :Fin s→(Fin r ⊕ Fin s)) (hminor : (W.submatrix rows id).det≠0) :
    (zE7 C (Tr rows)).det≠0 ∧
    ∀ pick :Fin s→(Fin r ⊕ Fin s),
      (zE7 C (Tr pick)).det*(W.submatrix rows id).det =
        (zE7 C (Tr rows)).det*(W.submatrix pick id).det:= by
  let A:=zE7 C (Tr rows)
  have hA:=duY C W hWC hC rows hminor
  refine ⟨hA,?_⟩
  intro pick
  let B:=zE7 C (Tr pick)
  have hunit :IsUnit A.det:=isUnit_iff_ne_zero.mpr hA
  let T:=A⁻¹*B
  let J:z30 (Fin r ⊕ Fin s) (Fin r) E :=Matrix.fromRows 1 0
  have hAJ:A*J=C:= by
    simp only [A,J,Matrix.fromCols_mul_fromRows,Matrix.mul_one,Matrix.mul_zero,add_zero]
  have hfirst:T.submatrix id Sum.inl=J:= by
    change A⁻¹*C=J
    rw [← hAJ,Matrix.nonsing_inv_mul_cancel_left A J hunit]
  let D:=T.submatrix znU znU
  have hT:T=Matrix.fromBlocks 1 (T.submatrix Sum.inl znU) 0 D:= by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j=>exact congrFun (congrFun hfirst (Sum.inl i)) j
      | inr j=>rfl
    | inr i =>
      cases j with
      | inl j=>exact congrFun (congrFun hfirst (Sum.inr i)) j
      | inr j=>rfl
  have hAT:A*T=B:=Matrix.mul_nonsing_inv_cancel_left A B hunit
  have hWaug (I:Fin s→(Fin r ⊕ Fin s)) :
      W.transpose*zE7 C (Tr I) =
        zE7 0 (W.submatrix I id).transpose := by
    rw [Matrix.mul_fromCols,hWC,bx1]
  have hbottom: (W.submatrix rows id).transpose*D =(W.submatrix pick id).transpose := by
    have hh: (W.transpose*A)*T=W.transpose*B:= by rw [Matrix.mul_assoc,hAT]
    change (W.transpose*zE7 C (Tr rows))*T =
      W.transpose*zE7 C (Tr pick) at hh
    rw [hWaug,hWaug,hT,Matrix.fromCols_mul_fromBlocks,Matrix.zero_mul,
      Matrix.mul_zero,zOP,Matrix.zero_mul,zOP] at hh
    exact zPw (fun M:z30 (Fin s) (Fin r ⊕ Fin s) E=>M.submatrix id znU) hh
  have hdetD: (W.submatrix rows id).det*D.det=(W.submatrix pick id).det:= by
    simpa only [Matrix.det_mul,zgP] using zPw Matrix.det hbottom
  have hdetT:T.det=D.det:= by
    rw [hT,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,zkF]
  have hdetB:B.det=A.det*D.det:= by
    rw [← hAT,Matrix.det_mul,hdetT]
  change B.det*(W.submatrix rows id).det=A.det*(W.submatrix pick id).det
  rw [hdetB,← hdetD]
  ring
variable {F:Type*} [zrb F]
private theorem du1
    (C:z30 (Fin r ⊕ Fin s) (Fin r) F[X])
    (d: (Fin r ⊕ Fin s)→ℕ) (hpositive : ∀ i,1≤d i)
    (hdegree : ∀ i j,(C i j).natDegree≤d i)
    (rows :Fin s→(Fin r ⊕ Fin s)) :
    (zE7 C (Tr rows)).det.natDegree≤(∑ i,d i) - s := by
  classical
  let A:=zE7 C (Tr rows :z30 _ _ F[X])
  change A.det.natDegree≤_
  rw [Matrix.det_apply]
  apply zMZ
  intro σ _
  have hsign: (Equiv.Perm.sign σ • ∏ j,A (σ j) j).natDegree =
      (∏ j,A (σ j) j).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h,one_smul]
    · rw [h,Units.neg_smul,one_smul,Polynomial.natDegree_neg]
  rw [hsign]
  let saving: (Fin r ⊕ Fin s)→ℕ:=Sum.elim (fun _=>0) (fun _=>1)
  have hpoint (j:Fin r ⊕ Fin s) : (A (σ j) j).natDegree+saving j≤d (σ j) := by
    cases j with
    | inl j=>simpa [A,saving] using hdegree (σ (Sum.inl j)) j
    | inr j =>
      change ((znV (rows j) 1 :Fin r ⊕ Fin s→F[X])
        (σ (znU j))).natDegree+1 ≤
        d (σ (znU j))
      simp only [zOw]
      split_ifs <;> simpa only [Polynomial.natDegree_one,Polynomial.natDegree_zero,zOP]
        using hpositive (σ (znU j))
  have hsum:=Finset.sum_le_sum (fun j (_:j∈zdB)=>hpoint j)
  have hsaving: (∑ j,saving j)=s := by simp [saving,Fintype.sum_sum_type]
  rw [zfW,hsaving,Equiv.sum_comp σ d] at hsum
  have hprod:=Polynomial.natDegree_prod_le zdB (fun j=>A (σ j) j)
  omega
private theorem cZj (φ:F[X] →+* E)
   (C:z30 (Fin r ⊕ Fin s) (Fin r) F[X]) (rows :Fin s→(Fin r ⊕ Fin s)) :
   φ (zE7 C (Tr rows)).det =
     (zE7 (C.map φ) (Tr rows)).det:= by
 rw [φ.map_det,RingHom.mapMatrix_apply]
 congr 1
 ext i j
 cases j with
 | inl j=>rfl
 | inr j =>
   change φ ((znV (rows j) 1 :Fin r ⊕ Fin s→F[X]) i) =
     (znV (rows j) 1 :Fin r ⊕ Fin s→E) i
   simp only [zOw]
   split_ifs <;> simp
theorem eOj (φ:F[X] →+* E) (hφ:zq4 φ)
    (C:z30 (Fin r ⊕ Fin s) (Fin r) F[X])
    (W:z30 (Fin r ⊕ Fin s) (Fin s) F[X])
    (hWC: (W.map φ).transpose*(C.map φ)=0)
    (hC : ∀ a,(C.map φ).mulVec a=0→a=0)
    (hprim:M4.IsPrimitive
      (fun I:Fin s→(Fin r ⊕ Fin s)=>(W.submatrix I id).det))
    (d: (Fin r ⊕ Fin s)→ℕ) (hpositive : ∀ i,1≤d i)
    (hdegree : ∀ i j,(C i j).natDegree≤d i)
    (rows :Fin s→(Fin r ⊕ Fin s)) :
    (W.submatrix rows id).det.natDegree≤(∑ i,d i) - s := by
  classical
  let P (I:Fin s→(Fin r ⊕ Fin s)) :=(W.submatrix I id).det
  let A (I:Fin s→(Fin r ⊕ Fin s)) :=(zE7 C (Tr I)).det
  change (P rows).natDegree≤_
  by_cases hP:P rows=0
  · simp [hP]
  have hmap (I:Fin s→(Fin r ⊕ Fin s)) :φ (P I)=((W.map φ).submatrix I id).det :=
    φ.map_det (W.submatrix I id)
  have hW: ((W.map φ).submatrix rows id).det≠0:= by
    rw [← hmap]
    exact fun hz=>hP (hφ (hz.trans (zhd φ).symm))
  obtain ⟨hAfield,hcrossField⟩:=du2 (C.map φ) (W.map φ) hWC hC rows hW
  have hA:A rows≠0:= by
    intro hz
    apply hAfield
    rw [← cZj φ C rows]
    exact (zPw φ hz).trans (zhd φ)
  have hcross (I:Fin s→(Fin r ⊕ Fin s)) :A I*P rows=A rows*P I:= by
    apply hφ
    simpa only [zok,hmap,A,cZj] using hcrossField I
  obtain ⟨a,ha⟩:=(M4.a6R P).mp hprim
  let q := ∑ I,a I*A I
  have hfactor :A rows=q*P rows := by
    calc
      A rows=(∑ I,a I*P I)*A rows := by rw [ha,zkF]
      _=q*P rows := by
        dsimp only [q]
        rw [Finset.sum_mul,Finset.sum_mul]
        apply zUo rfl
        intro I _
        rw [ztg,zDE (P I),← hcross I,← ztg]
  have hq:q≠0:= by
    intro hz
    exact hA (by rw [hfactor,hz,zero_mul])
  have hbound:=du1 C d hpositive hdegree rows
  change (A rows).natDegree≤_ at hbound
  rw [hfactor,zNh hq hP] at hbound
  omega
end bz5
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K row col:Type*} [zrb F] [zrb K] [z85 col] [zRw col]
theorem d4C (φ:F[X] →+* K) (hφ:zq4 φ)
    (M:z30 row col F[X]) (r :ℕ) (B:zQ.RowBasis φ M r)
    (d:row→ℕ) (hdeg : ∀ i j,(M i j).natDegree≤d i)
    (E :col→K) (hE0:E≠0) (hE : (M.map φ).mulVec E=0) :
    ∃ v :col→F[X],M4.IsPrimitive v∧M.mulVec v=0 ∧
      (∀ j,(v j).natDegree ≤ ∑ i,d (B.rows i)) ∧
      (∀ γ,∃ j,(v j).eval γ≠0) := by
  classical
  have hcofactor : ∃ j,asZ.vector B j≠0:= by
    by_contra h
    push_neg at h
    have hspan:=asZ.ef9 B hφ E hE
    have hz : ∀ j,(fun c=>φ (asZ.vector B j c))=0:= by
      intro j
      funext c
      rw [h j]
      exact zhd φ
    rw [show (∑ j,(E j/φ (zQ.pivot B).det) •
      (fun c=>φ (asZ.vector B j c)))=0 by simp only [hz,smul_zero,
        Finset.sum_const_zero]] at hspan
    exact hE0 hspan
  obtain ⟨j,hj⟩:=hcofactor
  obtain ⟨g,v,hg,hgv,hprim⟩:=M4.b2i
    (asZ.vector B j) hj
  refine ⟨v,hprim,?_,?_,M4.cNz v hprim⟩
  · exact M4.c1J M _ v g hg hgv
      (asZ.bA5 B hφ j)
  · intro c
    exact (M4.c1I _ v g hg hgv c).trans
      (asZ.bPI B d hdeg j c)
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
theorem bWs {F:Type*} [zrb F] {b c j r :ℕ}
    (hb:0<b) (hc:0<c) {g:z3y (Fin 2) F}
    (hg0:g≠0) (hprime : (zye {g}).IsPrime)
    (hg:g∈zVE (Fin 2) F 1 j r)
    {q:z3y (Fin 2) F} (hq:q∈zVE (Fin 2) F 1 b c)
    (hproper :q∉zye {g}) (S:zJe (Fin 2→F))
    (hS : ∀ x∈S,zIe x g=0∧zIe x q=0) :
    S.card≤ cappedDegreeMixedVolume j r b c:= by
  classical
  let E :=cappedDegreeExponents (Fin 2) 1 b c
  let φ:=monomialMap F E
  let P:=(zye {g}).comap φ
  have hq' : q∈restrictSupport F E := by simpa only [zVE,E] using hq
  let cut:=monomialLift q hq'
  let T:=S.image (monomialPoint E)
  have hφ:Function.Surjective φ:=monomialMap_cappedDegreeExponents_surjective hb hc
  have hE :=single_mem_cappedDegreeExponents (σ:=Fin 2) (i:=1) hb hc
  have hcut_map :φ cut=q:=monomialMap_monomialLift q hq'
  have :P.IsPrime :=hprime.comap φ.toRingHom
  have hdim: (affineHilbertPolynomial P).natDegree=1 := by
    have h:=natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      φ hφ hg0 hprime.ne_top
    rw [Nat.card_eq_fintype_card,Fintype.card_fin] at h
    change (affineHilbertPolynomial P).natDegree+1=2 at h
    omega
  have hcut:cut∉P:= by
    change φ cut∉zye {g}
    rw [hcut_map]
    exact hproper
  have hT : ∀ z∈T,z∈zeroLocus F P∧zIe z cut=0:= by
    intro z hz
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    constructor
    · rw [monomialPoint_mem_zeroLocus_comap_iff hE]
      simpa [zeroLocus_span] using (hS x hx).1
    · rw [aeval_monomialPoint]
      change zIe x (φ cut)=0
      rw [hcut_map]
      exact (hS x hx).2
  have h:=ncard_inter_cut_le_of_retained_le (P:=P) (1 :z3y E F) hcut
    (totalDegree_monomialLift_le_one q hq') T
    (fun z hz=>⟨(hT z hz).1,by simp⟩) (c:=1) zero_le_one (by
      intro Q hQ
      have hm:=(Ideal.mem_retainedMinimalPrimes.mp hQ).1
      have hz :=principalCut_natDegree_affineHilbertPolynomial_add_one hcut hm
      rw [hdim] at hz
      obtain ⟨hf,hbound⟩:=finite_zeroLocus_and_ncard_le_affineDegree (K:=F) Q (by omega)
      rw [zqe]
      have hcard:=Set.ncard_le_ncard (s :=(T:Set (E→F))∩zeroLocus F Q)
        Set.inter_subset_right hf
      exact le_trans (by exact_mod_cast hcard) hbound)
  have hset : (T:Set (E→F)) ∩ {z | zIe z cut=0} = T :=
    Set.inter_eq_left.mpr (fun z hz=>(hT z hz).2)
  rw [hset,Set.ncard_coe_finset,Nat.cast_one,zkF,zqe] at h
  change ((S.image (monomialPoint E)).card:ℚ)≤affineDegree P at h
  rw [ze7 _ (monomialPoint_injective hE)] at h
  exact_mod_cast h.trans (affineDegree_comap_cappedDegree_span_singleton_le hb hc hg0 hg)
end
end ana
end
section
namespace bzO
open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R:Type u} [za6 R] [IsNoetherianRing R] [znQ R]
private theorem buW {M:Type u} [AddCommGroup M] [Module R M] [zAa R M]
    (a :R) (J:znc R) (hJ:J≤ zrY R)
    (h : ∀ P∈zMd R M,a∈P → ¬ J≤P) :
    ∃ b∈J,ziO M (a+b) := by
  classical
  let A := {P∈zMd R M | a∈P}
  have hA:A.Finite :=(zrB R M).subset fun _ hP=>hP.1
  have hav : ¬ ((J:Set R) ⊆ ⋃ P∈A,(P:Set R)) := by
    intro hall
    obtain ⟨P,hP,hJP⟩ :=
      (J.subset_union_prime_finite hA (f :=id) ⊥ ⊥
        (fun P hP _ _=>(show zOA P M from hP.1).isPrime)).mp hall
    exact h P hP.1 hP.2 hJP
  obtain ⟨b,hb,hbA⟩:=Set.not_subset.mp hav
  let bad (P:znc R) := {n:ℕ | a+b^(n+1)∈P}
  have hbad (P:znc R) (hP:P∈zMd R M) : (bad P).Finite := by
    have hp:P.IsPrime :=(show zOA P M from hP).isPrime
    have hlt (i j:ℕ) (hi:i∈bad P) (hj:j∈bad P) (hij:i<j) :False := by
      have hpos :0<j - i:=Nat.sub_pos_of_lt hij
      have he :j+1=(i+1)+(j - i) := by omega
      have hd:b^(i+1)*(1 - b^(j - i))∈P:= by
        rw [mul_sub,zqe,← pow_add,← he]
        simpa only [add_sub_add_left_eq_sub] using P.sub_mem hi hj
      have hu:IsUnit (1 - b^(j - i)) :=
        isUnit_one_sub_self_of_mem_nonunits _ ((zrY R).pow_mem_of_mem (hJ hb) _ hpos)
      have hbP:b∈P:=hp.mem_of_pow_mem _
        ((hp.mem_or_mem hd).resolve_right fun hm=>hp.ne_top (P.eq_top_of_isUnit_mem hm hu))
      have haP:a∈P:= by
        simpa only [zY6] using
          P.sub_mem hi (P.pow_mem_of_mem hbP (i+1) (Nat.succ_pos i))
      exact hbA (Set.mem_iUnion₂.mpr ⟨P,⟨hP,haP⟩,hbP⟩)
    apply Set.Subsingleton.finite
    intro i hi j hj
    exact (lt_trichotomy i j).elim (fun h=>(hlt i j hi hj h).elim)
      (fun h=>h.elim id (fun h=>(hlt j i hj hi h).elim))
  obtain ⟨n,hn⟩:=((zrB R M).biUnion hbad).exists_notMem
  refine ⟨b^(n+1),J.pow_mem_of_mem hb _ (by omega),?_⟩
  by_contra hreg
  have hh:a+b^(n+1) ∈ ⋃ P∈zMd R M,(P:Set R) := by
    rwa [zC8 R M]
  obtain ⟨P,hP,hhP⟩:=Set.mem_iUnion₂.mp hh
  exact hn (Set.mem_iUnion₂.mpr ⟨P,hP,hhP⟩)
private abbrev aLV (R:Type u) [za6 R] [znQ R] :=
 zbv R (R ⧸ zrY R)
omit [IsNoetherianRing R] [znQ R] in
private theorem aHM (N M:ModuleCat.{u} R) {a :R}
  (ha :ziO M a) {n:ℕ} (h : ∀ i<n+1,zOt (Ext N M i)) :
  ∀ i<n,zOt (Ext N (zbv R (QuotSMulTop a M)) i) := by
 intro i hi
 have h₀:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
 have h₁:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i+1) (by omega))
 exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
  (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i+1) rfl)
  (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
private theorem byD (rs :List R) (M:ModuleCat.{u} R) [zAa R M]
    (hm : ∀ a∈rs,a∈zrY R)
    (hI:zrY R≤(zGX rs ⊔ zM1 R M).radical)
    (hext : ∀ i< rs.length,zOt (Ext (aLV R) M i)) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil=>exact IsWeaklyRegular.nil R M
  | cons a rs ih =>
    have hHom:zOt (aLV R →ₗ[R] M) :=
      (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp
        (hext 0 (by simp))
    obtain ⟨r,hr,hreg⟩:=IsSMulRegular.subsingleton_linearMap_iff.mp hHom
    have hAnn:zM1 R (aLV R)=zrY R :=
      zsb
    have hrm:r∈zrY R:=hAnn ▸ hr
    let J:=zGX rs
    have hJm:J≤ zrY R:=Ideal.span_le.mpr
      (fun z hz=>hm z (zrw _ hz))
    obtain ⟨b,hb,hab⟩:=buW (M:=M) a J hJm (by
      intro P hP haP hJP
      have hassoc:zOA P M:=hP
      have hle :zGX (a :: rs) ⊔ zM1 R M≤P:= by
        rw [z2L]
        exact zbX (zbX ((zvl P).mpr haP) hJP)
          (by simpa only [Submodule.annihilator_top] using hassoc.annihilator_le)
      have hrP:=hassoc.isPrime.radical_le_iff.mpr hle (hI hrm)
      have hru:r ∈ ⋃ P∈zMd R M,(P:Set R) :=
        Set.mem_iUnion₂.mpr ⟨P,hP,hrP⟩
      rw [zC8 R M] at hru
      exact hru hreg)
    let M' := zbv R (QuotSMulTop (a+b) M)
    have habann:a+b∈zM1 R M' := QuotSMulTop.mem_annihilator M (a+b)
    have hann:zM1 R M≤zM1 R M' :=
      (Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _)
    have hle :zGX (a :: rs) ⊔ zM1 R M ≤
        J ⊔ zM1 R M' := by
      rw [z2L]
      refine zbX (zbX ((zvl _).mpr ?_) zPQ)
        (hann.trans ztJ)
      have hsum:a+b∈J ⊔ zM1 R M' := zs0 habann
      have hb' : b∈J ⊔ zM1 R M' := zKg hb
      simpa only [zY6] using (J ⊔ zM1 R M').sub_mem hsum hb'
    have htail:=ih M' (fun z hz=>hm z (zrw _ hz))
      (hI.trans (zks hle)) (aHM _ M hab hext)
    have hcons :IsWeaklyRegular M ((a+b) :: rs) :=IsWeaklyRegular.cons hab htail
    have happ:IsWeaklyRegular M (rs ++ [a+b]) :=
      zq3 hcons
        (show List.Perm ([a+b] ++ rs) (rs ++ [a+b]) from ztt) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Ideal.add_mem _ (hm a List.mem_cons_self) (hJm hb)
        · exact hm z (zrw _ hz))
    obtain ⟨hrs,hlast⟩:=(isWeaklyRegular_append_iff M rs [a+b]).mp happ
    let T:zpI R M:=J • ⊤
    have hlast' : ziO (M ⧸ T) (a+b) :=(isWeaklyRegular_singleton_iff _ _).mp hlast
    have ha :ziO (M ⧸ T) a := by
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hlast' ⊢
      intro x hx
      apply hlast'
      have hbT:b•x∈T:= by
        apply (Submodule.smul_mono_left ((zvl J).mpr hb) :
          zye {b} • (⊤ : zpI R M)≤T)
        rw [Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mem_pointwise_smul x b ⊤ trivial
      rw [add_smul]
      exact T.add_mem hx hbT
    have hnew :IsWeaklyRegular M (rs ++ [a]) :=
      (isWeaklyRegular_append_iff M rs [a]).mpr
        ⟨hrs,(isWeaklyRegular_singleton_iff _ _).mpr ha⟩
    have hp:List.Perm (a :: rs) (rs ++ [a]) :=
      show List.Perm ([a] ++ rs) (rs ++ [a]) from ztt
    exact zq3 hnew hp.symm
      (fun z hz=>hm z (hp.mem_iff.mpr hz))
theorem bPS (ref rs :List R) (hlen:ref.length=rs.length)
  (hmem : ∀ a∈ref,a∈zrY R) (href :IsRegular R ref)
  (hrad: (zGX rs).radical=zrY R) :
  IsWeaklyRegular R rs := by
 let N :=aLV R
 have hAnn:zM1 R N=zrY R:=zsb
 have hSupp:Module.support R N⊆PrimeSpectrum.zeroLocus (zrY R) := by
  rw [Module.support_eq_zeroLocus,hAnn]
 have hlt:zrY R•(⊤ : zpI R R) < ⊤ := by
  change zrY R•(⊤ : znc R) < ⊤
  rw [Ideal.smul_eq_mul,Ideal.mul_top]
  exact (zHl R).ne_top.lt_top
 have hext:=ModuleCat.subsingleton_ext_of_exists_isRegular _ N hSupp
  (zbv R R) hlt ref hmem href
 exact byD rs (zbv R R)
  (fun a ha=>hrad ▸ (zGX rs).le_radical (Ideal.subset_span ha))
  (hrad ▸ zks zPQ) (fun i hi=>hext i (hlen ▸ hi))
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
theorem dPh (v :σ→ℕ) :zq4 (a2U v) := by
 intro e f h
 have :=zPw Finsupp.some h
 simpa [a2U] using this
def RK (v :σ→ℕ) :z3y σ F →+* zM2 (z3y σ F) :=
 (zpj F σ).toRingHom.comp (zXo F (a2U v))
theorem bYE (v :σ→ℕ) :zq4 (RK (F:=F) v) :=
 (zpj F σ).injective.comp
   (AddMonoidAlgebra.mapDomain_injective (dPh v))
theorem dPi (v :σ→ℕ) (e :σ →₀ ℕ) (a :F) :
  RK v (monomial e a)=zdM (e.weight v) (monomial e a) := by
 change (zpj F σ) (zTd (a2U v) (monomial e a))=_
 change (zpj F σ) (zTd (a2U v) (AddMonoidAlgebra.single e a))=_
 rw [AddMonoidAlgebra.mapDomain_single]
 change (zpj F σ) (monomial ((a2U v) e) a)=_
 rw [optionEquivLeft_monomial]
 simp [a2U]
theorem bDk (v :σ→ℕ) (P:z3y σ F) (n:ℕ) (e :σ →₀ ℕ) :
   ((RK v P).coeff n).coeff e=if e.weight v=n then P.coeff e else 0:= by
 classical
 induction P using MvPolynomial.induction_on' with
 | monomial f a =>
   rw [dPi]
   by_cases hfe :f=e
   · subst f
     split_ifs <;> simp_all [zQm]
   · by_cases hw:f.weight v=n <;> by_cases he :e.weight v=n <;> simp [zQm,MvPolynomial.coeff_monomial,hfe,Ne.symm hfe,hw,he]
 | add P Q hP hQ =>
   simp only [zrl,Polynomial.coeff_add,MvPolynomial.coeff_add,hP,hQ]
   split_ifs <;> simp
theorem bnR (v :σ→ℕ) (m:ℕ) (P:z3y σ F) :
   z7y^m∣RK v P↔P∈zlK v m:= by
 rw [Polynomial.X_pow_dvd_iff,mem_restrictWeightedOrder]
 constructor
 · intro h e he
   by_contra hh
   have hc:=zPw (fun Q:z3y σ F=>Q.coeff e) (h (e.weight v) (by omega))
   rw [bDk,z3d rfl] at hc
   exact (mem_support_iff.mp he) hc
 · intro h n hn
   ext e
   rw [bDk]
   by_cases he :e.weight v=n
   · rw [z3d he]
     by_contra hc
     have :=h e (mem_support_iff.mpr hc)
     omega
   · simp [he]
theorem dPq (v :σ→ℕ) (L:z3y σ F)
  (horder :L∈zlK v 1) (e :σ →₀ ℕ)
  (he :e.weight v=1) (hc:L.coeff e≠0) :
  (RK v L).natTrailingDegree=1 := by
 have hLn:L≠0:= by intro hz; exact hc (by rw [hz]; rfl)
 have hLn' : RK v L≠0:= fun hz=>hLn (bYE v (hz.trans (zhd _).symm))
 have hlow:=zKd hLn'
  (Polynomial.X_pow_dvd_iff.mp ((bnR v 1 L).mpr horder))
 have hc' : (RK v L).coeff 1≠0:= by
  intro hz
  have hh:=zPw (fun P:z3y σ F=>P.coeff e) hz
  rw [bDk,z3d he] at hh
  exact hc hh
 have hup:=zxD hc'
 omega
theorem bnS (v :σ→ℕ) (m:ℕ)
  (L H :z3y σ F)
  (hL: (RK v L).natTrailingDegree=1) (hLn:L≠0)
  (hH :H≠0) (hHlow : ∀ e∈H.support,e.weight v<m-1) :
  L*H∉zlK v m:= by
 intro hh
 have hLn' : RK v L≠0:= fun hz=>hLn (bYE v (hz.trans (zhd _).symm))
 have hHn' : RK v H≠0:= fun hz=>hH (bYE v (hz.trans (zhd _).symm))
 have hmul :RK v (L*H)≠0:= by rw [zok]; exact mul_ne_zero hLn' hHn'
 have hhigh:=zKd hmul
  (Polynomial.X_pow_dvd_iff.mp ((bnR v m (L*H)).mpr hh))
 rw [zok,Polynomial.natTrailingDegree_mul hLn' hHn',hL] at hhigh
 obtain ⟨e,he⟩:=support_nonempty.mpr hH
 have hc: (RK v H).coeff (e.weight v)≠0:= by
  intro hz
  have hz' := zPw (fun Q:z3y σ F=>Q.coeff e) hz
  rw [bDk,z3d rfl] at hz'
  exact (mem_support_iff.mp he) hz'
 have hmin:=zxD hc
 have :=hHlow e he
 omega
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
theorem bxT (d:ℕ) (Q:zQp E (d+1)) (P:E[X]) :
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
def cfy (d:ℕ) (P:E[X]) :
    z3y (zNO (zxV d)) E →+* E[X] :=
  (zfh (d:=d+1) P).toRingHom.comp (HC d).symm.toRingHom
theorem fXP (d:ℕ) (Q:zQp E (d+1)) (P:E[X]) :
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
theorem c8V (d:ℕ) (Q:zQp E (d+1)) (hQ:Q≠0) (P:E[X])
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
def filtered (v :ι→σ→ℕ) (d:ι→ℕ) :zpI F (z3y σ F) :=
 ⨅ i,zAp (v i) (d i)
@[simp] theorem Wb (v :ι→σ→ℕ) (d:ι→ℕ) (P:z3y σ F) :
   P∈filtered v d ↔ ∀ i,P.weightedTotalDegree (v i)≤d i:= by
  simp only [filtered,Submodule.mem_iInf,mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
theorem c0Z (v :ι→σ→ℕ) (d e :ι→ℕ)
   (L H :z3y σ F) (hL:L≠0)
   (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i) :
   L*H∈filtered v d↔H∈filtered v (fun i=>d i-e i) := by
 by_cases hH :H=0
 · simp [hH]
 · simp only [Wb]
   constructor
   · intro h i
     have hi:=h i
     rw [zmN _ _ _ hL hH,hdeg i] at hi
     omega
   · intro h i
     have hi:=h i
     rw [zmN _ _ _ hL hH,hdeg i]
     have :=hed i
     omega
def aNQ (v :ι→σ→ℕ) (d e :ι→ℕ) (L:z3y σ F)
    (hL:L≠0) (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i)
    (hed : ∀ i,e i≤d i) :
    filtered (F:=F) v (fun i=>d i-e i) →ₗ[F] filtered (F:=F) v d where
  toFun H :=⟨L*H.val,(c0Z v d e L H.val hL hdeg hed).mpr H.property⟩
  map_add' H J:= by apply zkt; exact mul_add L H.val J.val
  map_smul' a H := by apply zkt; exact zGx a L H.val
theorem a3Z (v :ι→σ→ℕ) (d e :ι→ℕ)
  (L:z3y σ F) (hL:L≠0)
  (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i) :
  zq4 (aNQ v d e L hL hdeg hed) := by
 intro H J heq
 apply zkt
 exact zyS hL (zPw Subtype.val heq)
theorem a5K (v :ι→σ→ℕ) (d e :ι→ℕ)
   (L:z3y σ F) (hL:L≠0)
   (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i)
   (Q:filtered (F:=F) v d) :
   Q∈zWl (aNQ v d e L hL hdeg hed)↔L∣Q.val := by
 constructor
 · rintro ⟨H,hH⟩
   exact ⟨H.val,zPw Subtype.val hH.symm⟩
 · rintro ⟨H,hH⟩
   have hm:H∈filtered v (fun i=>d i-e i) :=
     (c0Z v d e L H hL hdeg hed).mp (hH ▸ Q.property)
   exact ⟨⟨H,hm⟩,zkt hH.symm⟩
end
end wT
end
section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open Finset MvPolynomial
def vO (w:ℕ) :Fin 4→Fin 5→ℕ :=
 ![![1,w,w,0,0],![0,1,1,0,0],![0,1,0,1,0],![0,0,1,0,1]]
def A6 (D B s t:ℕ) :Fin 4→ℕ := ![D,B,s,t]
def tuples (D w B s t:ℕ) :zJe (Σ _:ℕ,Σ _:ℕ,ℕ×ℕ×ℕ) :=
  (range (B+1)).sigma fun i=>(range (B+1-i)).sigma fun j =>
    (range (D+1-w*(i+j))) ×ˢ ((range (s+1-i)) ×ˢ (range (t+1-j)))
def b2r (x i j a b:ℕ) :Fin 5 →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm ![x,i,j,a,b]
def bx9 (c:Σ _:ℕ,Σ _:ℕ,ℕ×ℕ×ℕ) :Fin 5 →₀ ℕ :=
 b2r c.2.2.1 c.1 c.2.1 c.2.2.2.1 c.2.2.2.2
@[simp] theorem d5d (x i j a b:ℕ) (q:Fin 5) :
   b2r x i j a b q = ![x,i,j,a,b] q:= by
  simp [b2r]
theorem gEE :zq4 bx9:= by
 intro c d h
 have h0:=zPw (fun e :Fin 5 →₀ ℕ=>e 0) h
 have h1 :=zPw (fun e :Fin 5 →₀ ℕ=>e 1) h
 have h2 :=zPw (fun e :Fin 5 →₀ ℕ=>e 2) h
 have h3:=zPw (fun e :Fin 5 →₀ ℕ=>e 3) h
 have h4 :=zPw (fun e :Fin 5 →₀ ℕ=>e 4) h
 simp only [bx9,d5d,Matrix.cons_val_zero,Matrix.cons_val_succ,
  Matrix.head_cons] at h0 h1 h2 h3 h4
 rcases c with ⟨i,j,x,a,b⟩
 rcases d with ⟨i',j',x',a',b'⟩
 dsimp at h0 h1 h2 h3 h4
 subst i'; subst j'; subst x'; subst a'; subst b'
 rfl
@[simp] theorem cun (D w B s t:ℕ) : (tuples D w B s t).card=V D w B s t:= by
  simp [tuples,V,card_sigma,Nat.mul_assoc]
def aE1 (D w B s t:ℕ) :zJe (Fin 5 →₀ ℕ) :=
 (tuples D w B s t).image bx9
theorem gs8 (D w B s t:ℕ) :
  (aE1 D w B s t).card=V D w B s t:= by
 rw [aE1,ze7 _ gEE,cun]
theorem aQ8 (e :Fin 5 →₀ ℕ) (a b c d f :ℕ) :
  e.weight ![a,b,c,d,f]=e 0*a+e 1*b+e 2*c+e 3*d+e 4*f := by
 simp [zDM,z9d,zCS,zs5]
 omega
theorem bfz (D w B s t:ℕ) (e :Fin 5 →₀ ℕ) :
   e∈aE1 D w B s t ↔
   e 0+w*(e 1+e 2)≤D ∧e 1+e 2≤B∧e 1+e 3≤s∧e 2+e 4≤t:= by
 constructor
 · rintro he
   obtain ⟨⟨i,j,x,a,b⟩,hc,rfl⟩:=mem_image.mp he
   simp only [tuples,mem_sigma,mem_range,mem_product] at hc
   simp [bx9]
   omega
 · rintro ⟨hX,hY,hS,hT⟩
   apply mem_image.mpr
   refine ⟨⟨e 1,e 2,e 0,e 3,e 4⟩,?_,?_⟩
   · simp only [tuples,mem_sigma,mem_range,mem_product]
     omega
   · ext q
     fin_cases q <;> simp [bx9]
theorem bhw {F:Type*} [zrb F] (D w B s t:ℕ) :
   filtered (F:=F) (vO w) (A6 D B s t)=
     restrictSupport F (↑(aE1 D w B s t) :Set (Fin 5 →₀ ℕ)) := by
 ext P
 rw [Wb]
 simp only [zUj,Finset.mem_coe]
 constructor
 · intro h e he
   apply (bfz D w B s t e).mpr
   have hh q:=(z6P (vO w q) he).trans (h q)
   have h0:=hh 0
   have h1 :=hh 1
   have h2 :=hh 2
   have h3:=hh 3
   simp [vO,A6,aQ8] at h0 h1 h2 h3
   constructor
   · nlinarith
   · exact ⟨h1,h2,h3⟩
 · intro h q
   apply zf9
   change ∀ e∈P.support,_
   intro e he
   have hh:=(bfz D w B s t e).mp (h he)
   fin_cases q <;> simp [vO,A6,aQ8] <;> nlinarith
instance gRP {F:Type*} [zrb F] (D w B s t:ℕ) :
  zAa F (filtered (F:=F) (vO w) (A6 D B s t)) := by
 rw [bhw]
 exact restrictSupport_finite (Finset.finite_toSet _)
theorem awB {F:Type*} [zrb F] (D w B s t:ℕ) :
   zsE F (filtered (F:=F) (vO w) (A6 D B s t))=
     V D w B s t:= by
 rw [bhw,finrank_restrictSupport_finset,gs8]
end
end wT
end
section
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open Finset MvPolynomial
variable {F σ:Type*} [zrb F]
theorem aTD (v :σ→ℕ) (B d e aa bb:ℕ)
   (Q:zM2 (z3y σ F)) (a b:z3y σ F)
   (hcoeff : ∀ j≤B,Q.coeff j≠0→(Q.coeff j).weightedTotalDegree v+j*e≤d)
   (ha :a.weightedTotalDegree v≤aa) (hb:b.weightedTotalDegree v≤bb)
   (hbalance :aa≤e+bb) :
   (aCC B Q a b).weightedTotalDegree v≤d+B*bb:= by
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
 unfold aCC
 apply Submodule.sum_mem
 intro j hj
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
 by_cases hc:Q.coeff j=0
 · simp [hc,zXg]
 have hjB:j≤B:= by have :=mem_range.mp hj; omega
 have hco:=hcoeff j hjB hc
 have hpa :=(zvm v a j).trans (zBI j ha)
 have hpb:=(zvm v b (B-j)).trans (zBI (B-j) hb)
 have hm:=(zku v (Q.coeff j*a^j) (b^(B-j))).trans
   (z9f ((zku v _ _).trans (z3b hpa _)) hpb)
 have hjadd:j+(B-j)=B:=Nat.add_sub_of_le hjB
 have hbal:=zBI j hbalance
 nlinarith
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
def a3p:Fin 5 ≃ Fin 5 :=
 Equiv.ofBijective ![1,2,0,3,4] (by decide)
def xx :z3y (Fin 5) F ≃ₐ[F] zM2 (z3y (Fin 4) F) :=
 (zGY F a3p).trans (z8s F 4)
def Qb:Fin 4→ℕ := ![0,1,0,0]
def ME :Fin 4→ℕ := ![0,1,1,0]
def MD:Fin 4→ℕ := ![0,0,0,1]
theorem cce (Q:z3y (Fin 5) F) (j:ℕ)
  (f :Fin 4 →₀ ℕ) (hf :f∈((xx Q).coeff j).support) :
  ∃ e∈Q.support,e 0=f 0∧e 1=f 1∧e 2=j∧e 3=f 2∧e 4=f 3:= by
 have hc:=mem_support_iff.mp hf
 change ((z8s F 4 (rename a3p Q)).coeff j).coeff f≠0 at hc
 rw [finSuccEquiv_coeff_coeff] at hc
 obtain ⟨e,he,hcoeff⟩:=coeff_rename_ne_zero a3p Q (f.cons j) hc
 refine ⟨e,mem_support_iff.mpr hcoeff,?_⟩
 have hh (i:Fin 5) :=zPw (fun z :Fin 5 →₀ ℕ=>z (a3p i)) he
 have h0:=hh 0
 have h1 :=hh 1
 have h2 :=hh 2
 have h3:=hh 3
 have h4 :=hh 4
 simp only [Finsupp.mapDomain_apply_of_injective a3p.injective] at h0 h1 h2 h3 h4
 simp [a3p] at h0 h1 h2 h3 h4
 exact ⟨h0,h1,h2,h3,h4⟩
theorem dl0 {σ:Type*} (v :σ→ℕ) (P:z3y σ F)
  (c d:ℕ) (hP:P≠0) (h : ∀ e∈P.support,e.weight v+c≤d) :
  P.weightedTotalDegree v+c≤d:= by
 obtain ⟨e,he⟩:=support_nonempty.mpr hP
 have hcd:c≤d:= by have :=h e he; omega
 have hdeg:P.weightedTotalDegree v≤d-c:= by
  apply zf9
  intro e he
  have :=h e he
  omega
 omega
theorem bgg (D w B s t:ℕ)
   (Q:z3y (Fin 5) F)
   (hQ:Q∈filtered (vO w) (A6 D B s t)) :
   (∀ j≤B,(xx Q).coeff j≠0 →
     ((xx Q).coeff j).weightedTotalDegree Qb+j≤B) ∧
   (∀ j≤B,(xx Q).coeff j≠0 →
     ((xx Q).coeff j).weightedTotalDegree ME≤s) ∧
   (∀ j≤B,(xx Q).coeff j≠0 →
     ((xx Q).coeff j).weightedTotalDegree MD+j≤t) := by
 have hmono (j:ℕ) (f :Fin 4 →₀ ℕ) (hf :f∈((xx Q).coeff j).support) :
     f 1+j≤B∧f 1+f 2≤s∧j+f 3≤t:= by
   obtain ⟨e,he,he0,he1,he2,he3,he4⟩:=cce Q j f hf
   rw [bhw,zUj] at hQ
   have hh:=(bfz D w B s t e).mp (hQ he)
   omega
 constructor
 · intro j hj hc
   apply dl0 Qb _ j B hc
   intro f hf
   have hh:=hmono j f hf
   simpa [Qb,zDM,z9d,zCS,zs5] using hh.1
 constructor
 · intro j hj hc
   apply zf9
   intro f hf
   have hh:=hmono j f hf
   simpa [ME,zDM,z9d,zCS,zs5] using hh.2.1
 · intro j hj hc
   apply dl0 MD _ j t hc
   intro f hf
   have hh:=hmono j f hf
   simpa [MD,zDM,z9d,zCS,zs5,zg2] using hh.2.2
theorem c4O (D w B s t:ℕ) (Q:z3y (Fin 5) F)
  (hQ:Q∈filtered (vO w) (A6 D B s t)) :
  (xx Q).natDegree≤B:= by
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro j hj
 by_contra hc
 obtain ⟨f,hf⟩:=support_nonempty.mpr hc
 obtain ⟨e,he,he0,he1,he2,he3,he4⟩:=cce Q j f hf
 rw [bhw,zUj] at hQ
 have hh:=(bfz D w B s t e).mp (hQ he)
 omega
theorem aI3 (i:Fin 5) :
    xx (F:=F) (X i)=
      ![z1z (X 0),z1z (X 1),z7y,
        z1z (X 2),z1z (X 3)] i:= by
  fin_cases i <;> simp [xx,a3p,finSuccEquiv_apply,zyk] <;> rfl
def D9 (P:zM2 F) (s t:F) :Fin 4→zM2 F :=
 ![z7y,P,z1z s,z1z t]
theorem ccf (P Q:zM2 F) (s t:F) (G:z3y (Fin 5) F) :
  zmH (zIe (D9 P s t)).toRingHom Q (xx G)=
    zIe ![z7y,P,Q,z1z s,z1z t] G:= by
 have heq : (Polynomial.eval₂RingHom (zIe (D9 P s t)).toRingHom Q).comp
    (xx (F:=F)).toRingHom=(zIe ![z7y,P,Q,z1z s,z1z t]).toRingHom:= by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [xx,finSuccEquiv_apply]
  · intro i
    change zmH (zIe (D9 P s t)).toRingHom Q (xx (X i))=_
    rw [aI3]
    fin_cases i <;> simp [D9]
 exact RingHom.congr_fun heq G
end
end wT
end
section
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial Finset
variable {F:Type*} [zrb F]
def oH :Fin 5→ℕ := ![1,1,1,0,0]
abbrev WH (F:Type*) [zrb F] (d s t:ℕ) :=
 filtered (F:=F) (vO 1) (A6 d d s t)
theorem dm3 (d s t:ℕ) :J (d+1) s t=V d 1 d s t:= by
 unfold J V
 apply zUo rfl
 intro i hi
 apply zUo rfl
 intro j hj
 simp only [zkF,Nat.sub_sub]
theorem aIi (d s t:ℕ) :
  zsE F (WH F d s t)=J (d+1) s t:= by
 rw [dm3]
 exact awB d 1 d s t
theorem brn (d s t:ℕ) (H :WH F d s t) :
  ∀ e∈H.val.support,e.weight oH<d+1 := by
 intro e he
 have hh:=(z6P (vO 1 0) he).trans
  ((Wb _ _ _).mp H.property 0)
 simpa [vO,A6,oH] using Nat.lt_succ_of_le hh
theorem bx6 (d s t dS dT:ℕ) (L:z3y (Fin 5) F)
  (hS:L.weightedTotalDegree (vO 1 2)≤dS)
  (hT:L.weightedTotalDegree (vO 1 3)≤dT)
  (H :WH F d s t) :
  za1 oH (d+2) (L*H.val)∈WH F (d+1) (s+dS) (t+dT) := by
 simp only [WH]
 rw [bhw,zUj]
 intro e he
 have hc:e.weight oH<d+2 := by
  have he' := mem_support_iff.mp he
  rw [zjG] at he'
  by_contra hh
  exact he' (if_neg hh)
 have heL:e∈(L*H.val).support := by
  apply mem_support_iff.mpr
  have :=mem_support_iff.mp he
  simpa only [zjG,z3d hc] using this
 have hHs :=(Wb _ _ _).mp H.property 2
 have hHt:=(Wb _ _ _).mp H.property 3
 have hs :=(z6P (vO 1 2) heL).trans
  ((zku _ _ _).trans (z9f hS hHs))
 have ht:=(z6P (vO 1 3) heL).trans
  ((zku _ _ _).trans (z9f hT hHt))
 apply (bfz (d+1) 1 (d+1) (s+dS) (t+dT) e).mpr
 simp [vO,A6,oH,aQ8] at hc hs ht ⊢
 omega
end
end wT
end
section
set_option maxHeartbeats 1000000
namespace wT
noncomputable section
open MvPolynomial
variable {F:Type*} [zrb F]
def bhe (x a b c d:F) :Fin 5→z3y (Fin 5) F :=
 ![X 0+C x,X 1+C a+X 3*C b,X 2+C c+X 4*C d,X 3,X 4]
def Ko (x a b c d:F) :z3y (Fin 5) F →ₐ[F] z3y (Fin 5) F :=
 zIe (bhe x a b c d)
theorem gqk (v :Fin 5→ℕ) (hv1 :v 1=v 3) (hv2 :v 2=v 4)
    (x a b c d:F) (P:z3y (Fin 5) F) :
    (Ko x a b c d P).weightedTotalDegree v≤P.weightedTotalDegree v := by
  apply zZ0 v v
  intro i
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  fin_cases i
  · change X 0+C x∈zAp v (v 0)
    exact zcy _ (zCH v _ _ zs1)
      (zzE v _ _)
  · change X 1+C a+X 3*C b∈zAp v (v 1)
    apply zcy _
      (zcy _ (zCH v _ _ zs1)
        (zzE v _ _))
    have hm:=zD1
      (zCH (R:=F) v (v 3) 3 zs1)
      (zzE (R:=F) v 0 b)
    simpa [hv1] using hm
  · change X 2+C c+X 4*C d∈zAp v (v 2)
    apply zcy _
      (zcy _ (zCH v _ _ zs1)
        (zzE v _ _))
    have hm:=zD1
      (zCH (R:=F) v (v 4) 4 zs1)
      (zzE (R:=F) v 0 d)
    simpa [hv2] using hm
  · change X 3∈zAp v (v 3)
    exact zCH v _ _ zs1
  · change X 4∈zAp v (v 4)
    exact zCH v _ _ zs1
theorem aCL (x a b c d:F) (P:z3y (Fin 5) F) :
  (Ko x a b c d P).weightedTotalDegree (vO 1 2)≤
    P.weightedTotalDegree (vO 1 2) ∧
  (Ko x a b c d P).weightedTotalDegree (vO 1 3)≤
    P.weightedTotalDegree (vO 1 3) := by
 constructor <;> apply gqk <;> decide
theorem gEA (d s t:ℕ) (P:z3y (Fin 5) F)
  (hS:P.weightedTotalDegree (vO 1 2)≤s)
  (hT:P.weightedTotalDegree (vO 1 3)≤t) :
  za1 oH (d+1) P∈WH F d s t:= by
 simp only [WH]
 rw [bhw,zUj]
 intro e he
 have hc:e.weight oH<d+1 := by
  have hh:=mem_support_iff.mp he
  rw [zjG] at hh
  by_contra hn
  exact hh (if_neg hn)
 have heP:e∈P.support := by
  apply mem_support_iff.mpr
  have :=mem_support_iff.mp he
  simpa only [zjG,z3d hc] using this
 have hs :=(z6P (vO 1 2) heP).trans hS
 have ht:=(z6P (vO 1 3) heP).trans hT
 apply (bfz d 1 d s t e).mpr
 simp [vO,oH,aQ8] at hc hs ht ⊢
 omega
def a8H (D w B s t d:ℕ) (x a b c e :F) :
    filtered (F:=F) (vO w) (A6 D B s t) →ₗ[F] WH F d s t where
  toFun Q:=⟨za1 oH (d+1) (Ko x a b c e Q.val),by
    apply gEA
    · exact (aCL x a b c e Q.val).1.trans
        ((Wb _ _ _).mp Q.property 2)
    · exact (aCL x a b c e Q.val).2.trans
        ((Wb _ _ _).mp Q.property 3)⟩
  map_add' Q R:= by apply zkt; simp
  map_smul' a Q:= by apply zkt; simp
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
theorem dPm {σ:Type*} (v :σ→ℕ) (m:ℕ)
  (P L H :z3y σ F) (g:σ→F[X]) (z :F[X])
  (hcontact :P-L*H∈zlK v m)
  (hg : ∀ i,z^(v i)∣g i)
  (hL:eval₂Hom z1z g L=0) :
  z^m∣eval₂Hom z1z g P:= by
 have hd:=pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder z1z hcontact hg
 simpa only [map_sub,zok,hL,zero_mul,sub_zero] using hd
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
def aju (P Q:zM2 F) (s t:F) :Fin 5→zM2 F :=
 ![z7y,P,Q,z1z s,z1z t]
def aCK (x a b c d s t:F) (P Q:zM2 F) :Fin 5→zM2 F :=
  ![z7y-Polynomial.C x,P-Polynomial.C (a+s*b),
    Q-Polynomial.C (c+t*d),z1z s,z1z t]
theorem boM (x a b c d s t:F) (P Q:zM2 F)
   (G:z3y (Fin 5) F) :
   zIe (aCK x a b c d s t P Q) (Ko x a b c d G)=
     zIe (aju P Q s t) G:= by
 rw [Ko,aeval_eq_bind₁,aeval_bind₁]
 have hf : (fun i=>zIe (aCK x a b c d s t P Q) (bhe x a b c d i))=aju P Q s t:= by
   funext i
   fin_cases i <;> simp [bhe,aCK,aju] <;> ring
 rw [hf]
theorem bDi (x a b c d s t:F) (P Q:zM2 F)
  (hP:P.eval x=a+s*b) (hQ:Q.eval x=c+t*d) :
  ∀ i,(z7y-Polynomial.C x)^oH i∣
    aCK x a b c d s t P Q i:= by
 have hp: (z7y-Polynomial.C x)∣P-Polynomial.C (a+s*b) := by
  apply Polynomial.dvd_iff_isRoot.mpr
  simp [hP]
 have hq: (z7y-Polynomial.C x)∣Q-Polynomial.C (c+t*d) := by
  apply Polynomial.dvd_iff_isRoot.mpr
  simp [hQ]
 simp only [Polynomial.C_add,Polynomial.C_mul] at hp hq
 intro i
 fin_cases i <;> simp [oH,aCK,hp,hq]
theorem bDX (m:ℕ) (x a b c d s t:F)
   (P Q:zM2 F) (G L H :z3y (Fin 5) F)
   (hP:P.eval x=a+s*b) (hQ:Q.eval x=c+t*d)
   (hL:zIe (aju P Q s t) L=0)
   (hcontact :Ko x a b c d G-Ko x a b c d L*H∈
     zlK oH m) :
   (z7y-Polynomial.C x)^m∣zIe (aju P Q s t) G:= by
 have hh:=dPm oH m
   (Ko x a b c d G) (Ko x a b c d L) H
   (aCK x a b c d s t P Q) (z7y-Polynomial.C x)
   hcontact (bDi x a b c d s t P Q hP hQ)
   (by
     change zIe (aCK x a b c d s t P Q) (Ko x a b c d L)=0
     rw [boM]
     exact hL)
 change (z7y-Polynomial.C x)^m∣zIe (aCK x a b c d s t P Q) (Ko x a b c d G) at hh
 rwa [boM] at hh
theorem bc5 (w D:ℕ) (G:z3y (Fin 5) F)
  (hG:G.weightedTotalDegree (vO w 0)≤D)
  (P Q:zM2 F) (hP:P.natDegree≤w) (hQ:Q.natDegree≤w) (s t:F) :
  (zIe (aju P Q s t) G).natDegree≤D:= by
 apply (natDegree_aeval_le_weightedTotalDegree_of_le (vO w 0)
  (aju P Q s t) G ?_).trans hG
 intro i
 fin_cases i <;> simp [aju,vO] <;> assumption
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
def aP3 (B:ℕ) (G:z3y (Fin 5) F)
    (a b:z3y (Fin 4) F) :z3y (Fin 4) F :=
  aCC B (xx G) a b
theorem bNc (D w B s t:ℕ) (G L:z3y (Fin 5) F)
  (hG:G∈filtered (vO w) (A6 D B s t))
  (hnot : ¬ L∣G) (a b:z3y (Fin 4) F) (hb:b≠0)
  (hlinear :xx L=z1z b*z7y-Polynomial.C a)
  (hprimitive : (z1z b*z7y-Polynomial.C a).IsPrimitive) :
  aP3 B G a b≠0:= by
 have hnd : ¬ (z1z b*z7y-Polynomial.C a)∣xx G:= by
  rintro ⟨H,hH⟩
  apply hnot
  refine ⟨xx.symm H,?_⟩
  apply xx.injective
  rw [zok,hlinear,zIH]
  exact hH
 letI:GCDMonoid (z3y (Fin 4) F) :=UniqueFactorizationMonoid.toGCDMonoid _
 exact dLG (K:=FractionRing (z3y (Fin 4) F)) B
  (xx G) (c4O D w B s t G hG) a b hb hprimitive hnd
theorem bNb (D w B s t:ℕ) (G L:z3y (Fin 5) F)
   (hG:G∈filtered (vO w) (A6 D B s t))
   (a b:z3y (Fin 4) F)
   (hlinear :xx L=z1z b*z7y-Polynomial.C a)
   (P Q:zM2 F) (s0 t0:F)
   (hL:zIe (aju P Q s0 t0) L=0)
   (hzero :zIe (aju P Q s0 t0) G=0) :
   zIe (D9 P s0 t0) (aP3 B G a b)=0:= by
 let φ:z3y (Fin 4) F →+* zM2 F:=(zIe (D9 P s0 t0)).toRingHom
 have hroot :Polynomial.eval Q ((xx G).map φ)=0:= by
   rw [Polynomial.eval_map,ccf]
   exact hzero
 have hrel :φ b*Q=φ a := by
   have hh:=ccf P Q s0 t0 L
   rw [hlinear] at hh
   have hz :zmH φ Q (z1z b*z7y-Polynomial.C a)=0 :=
     hh.trans hL
   apply sub_eq_zero.mp
   simpa only [Polynomial.eval₂_sub,zxy,zJU,Polynomial.eval₂_X] using hz
 have hd: ((xx G).map φ).natDegree≤B :=
   Polynomial.natDegree_map_le.trans (c4O D w B s t G hG)
 have hh:=dLI B ((xx G).map φ) hd (φ a) (φ b) Q hrel hroot
 rw [← cZm] at hh
 exact hh
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
  | h l ih =>
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
private theorem cXs {R:Type*} [za6 R] (A B:znc R) (x :R)
    (h : ∀ r,r*x∈B↔r∈A) :
    zKQ R (R ⧸ B) =
      zKQ R (R ⧸ A)+Module.length R (R ⧸ (B ⊔ zye {x} : znc R)) := by
  let f :=a5U A B x (fun r hr=>(h r).mpr hr)
  let q:=Submodule.factor (show (B:zpI R R)≤B ⊔ zye {x} from zPQ)
  have hfi:zq4 f := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro u hu
    obtain ⟨u,rfl⟩:=zld u
    change f (zVv A u)=0 at hu
    rw [show f (zVv A u)=zVv B (u*x) from
      aV1 _ _ _ _ _,z1Q] at hu
    change zVv A u=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((h u).mp hu)
  have hqf :Function.Exact f q:= by
    apply LinearMap.exact_iff.mpr
    ext u
    obtain ⟨u,rfl⟩:=zld u
    change zVv (B ⊔ zye {x}) u=0 ↔
      zVv B u∈zWl f
    rw [z1Q]
    constructor
    · rintro hu
      obtain ⟨a,ha,b,hb,rfl⟩:=Submodule.mem_sup.mp hu
      obtain ⟨c,rfl⟩:=Ideal.mem_span_singleton.mp hb
      refine ⟨zVv A c,?_⟩
      simp [f,aV1,zrl,Ideal.Quotient.eq_zero_iff_mem.mpr ha,zDE]
    · rintro ⟨z,hz⟩
      obtain ⟨z,rfl⟩:=zld z
      have hz' := Ideal.Quotient.eq.mp
        (hz.symm.trans (aV1 A B x (fun r hr=>(h r).mpr hr) z))
      have hs :=(B ⊔ zye {x}).add_mem (zKg hz')
        (zs0 (Ideal.mem_span_singleton.mpr ⟨z,zDE _ _⟩))
      rwa [sub_add_cancel] at hs
  exact Module.length_eq_add_of_exact f q hfi (Submodule.factor_surjective _) hqf
private theorem c47 {R:Type*} [za6 R]
    {m X Y:znc R} (h:m=X ⊔ Y) (k :ℕ) :
    m^(k+1)=X*m^k ⊔ Y^(k+1) := by
  have hX:X≤ m:=h ▸ zPQ
  have hY:Y≤ m:=h ▸ ztJ
  induction k with
  | zero=>simpa using h
  | succ k ih =>
      apply zWs
      · calc
          m^(k+1+1)=X*m^(k+1) ⊔ Y*m^(k+1) := by
            rw [zdG]
            exact (zPw (fun I=>I*m^(k+1)) h).trans (Ideal.sup_mul _ _ _)
          _=X*m^(k+1) ⊔ (Y*(X*m^k) ⊔ Y^(k+1+1)) := by
            congr 1
            conv_lhs=>rw [ih]
            rw [Ideal.mul_sup,← zdG]
          _≤_:= by
            rw [← sup_assoc]
            apply sup_le_sup_right
            apply zbX zs1
            rw [← ztg,zDE Y X,ztg,zdG]
            exact zIS zs1 (zIS hY zs1)
      · apply zbX
        · calc
            X*m^(k+1)≤ m*m^(k+1) :=zIS hX zs1
            _=m^(k+1+1) :=(zdG _ _).symm
        · exact pow_le_pow_left' hY _
private theorem eQB {R:Type*} [za6 R] [znQ R]
    [IsDomain R] {x y :R} (hx :x≠0) (hprime : (zye {x} : znc R).IsPrime)
    (hy :y∉(zye {x} : znc R))
    (hmax :zrY R=(zye {x} : znc R) ⊔ zye {y}) (k :ℕ) :
    zKQ R (R ⧸ (zrY R)^k)=(triangle k :ℕ∞) := by
  let m:=zrY R
  let X:znc R:=zye {x}
  let Y:znc R:=zye {y}
  have hxm:x∈m:= by
    change x∈zrY R
    rw [hmax]
    exact zKg (z5J x)
  have hym:y∈m:= by
    change y∈zrY R
    rw [hmax]
    exact zs0 (z5J y)
  have hyY (i:ℕ) :y ^i∈Y^i:=z2s (z5J y) i
  have hpow (i:ℕ) :X ⊔ m^i=X ⊔ Y^i:= by
    cases i with
    | zero=>simp
    | succ i =>
        rw [c47 hmax,← sup_assoc,
          sup_eq_left.mpr (Ideal.mul_le_left:X*m^i≤X)]
  have hcolonX (i:ℕ) (r :R) :r*x∈m^(i+1)↔r∈m^i:= by
    constructor
    · intro h
      rw [c47 hmax] at h
      obtain ⟨a,ha,b,hb,hab⟩:=Submodule.mem_sup.mp h
      obtain ⟨c,hc,rfl⟩:=Ideal.mem_span_singleton_mul.mp ha
      rw [zNi] at hb
      obtain ⟨d,rfl⟩:=Ideal.mem_span_singleton.mp hb
      have hbX:y ^(i+1)*d∈X:= by
        rw [show y ^(i+1)*d=r*x - x*c by rw [← hab]; ring]
        apply X.sub_mem <;> exact Ideal.mem_span_singleton.mpr (by
          first | exact ⟨r,zDE _ _⟩ | exact ⟨c,rfl⟩)
      have hdX:d∈X:=(hprime.mem_or_mem hbX).resolve_left
        (fun hp=>hy (hprime.mem_of_pow_mem _ hp))
      obtain ⟨e,rfl⟩:=Ideal.mem_span_singleton.mp hdX
      have hr :r=c+y ^(i+1)*e := by
        apply zyS hx
        calc
          x*r=r*x :=zDE _ _
          _=x*c+y ^(i+1)*(x*e) :=hab.symm
          _=x*(c+y ^(i+1)*e) := by ring
      rw [hr]
      exact (m^i).add_mem hc ((m^i).mul_mem_right _
        (Ideal.pow_le_pow_right (Nat.le_succ i) (z2s hym _)))
    · intro hr
      rw [pow_succ]
      exact zgK hr hxm
  have hcolonY (i:ℕ) (r :R) :
      r*y∈X ⊔ Y^(i+1)↔r∈X ⊔ Y^i:= by
    constructor
    · intro h
      obtain ⟨a,ha,b,hb,hab⟩:=Submodule.mem_sup.mp h
      rw [zNi] at hb
      obtain ⟨c,rfl⟩:=Ideal.mem_span_singleton.mp hb
      have hh: (r - y ^i*c)*y∈X:= by
        have he :a=r*y - y ^(i+1)*c:=eq_sub_of_add_eq hab
        convert ha using 1
        rw [he,pow_succ]
        ring
      exact (Submodule.mem_sup.mpr
        ⟨r - y ^i*c,(hprime.mem_or_mem hh).resolve_right hy,y ^i*c,
          (Y^i).mul_mem_right _ (hyY i),sub_add_cancel _ _⟩)
    · intro h
      obtain ⟨a,ha,b,hb,rfl⟩:=Submodule.mem_sup.mp h
      rw [add_mul]
      have hbY:b*y∈Y^(i+1) := by
        rw [pow_succ]
        exact zgK hb (z5J y)
      exact (X ⊔ Y^(i+1)).add_mem (zKg (X.mul_mem_right _ ha))
        (zs0 hbY)
  have hm_one :zKQ R (R ⧸ m)=1 := by
    rw [Module.length_quotient]
    have hc:IsCoatom (m:zpI R R) :=Ideal.isMaximal_def.mp (zHl R)
    apply zWs
    · apply (Order.coheight_le_coe_iff (n:=1)).mpr
      intro z hz
      rw [hc.2 z hz]
      simp
    · simpa using (Order.coheight_add_one_le hc.lt_top)
  have hYLength (i:ℕ) :zKQ R (R ⧸ (X ⊔ Y^i:znc R))=(i:ℕ∞) := by
    induction i with
    | zero=>simp
    | succ i ih =>
        have he : (X ⊔ Y^(i+1)) ⊔ Y=m:= by
          rw [sup_assoc,sup_eq_right.mpr (Ideal.pow_le_pow_right (show 1≤ i+1 by omega)
            |>.trans_eq (pow_one Y)),← hmax]
        rw [cXs _ _ y (hcolonY i),ih,he,hm_one,Nat.cast_succ]
  induction k with
  | zero=>simp [triangle]
  | succ k ih =>
      change zKQ R (R ⧸ m^(k+1))= _
      rw [cXs _ _ x (hcolonX k),ih,sup_comm,hpow,hYLength,triangle]
      simp only [Nat.cast_add,Nat.cast_succ]
theorem ce2 {R:Type*} [za6 R] [IsDomain R]
    [UniqueFactorizationMonoid R] [IsRegularLocalRing R] (hd:ringKrullDim R=2) (i:ℕ) :
    zKQ R (R ⧸ (zrY R)^i)=(triangle i:ℕ∞) := by
  classical
  let m:=zrY R
  have hdim:m.spanFinrank=2 := by
    have h:=(IsRegularLocalRing.spanFinrank_maximalIdeal (R:=R)).trans hd
    exact_mod_cast h
  have hfg: (m:zpI R R).FG:=zLU _
  obtain ⟨s,hs,hspan⟩:=Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  rw [hdim] at hs
  obtain ⟨x,y,_,rfl⟩:=Finset.card_eq_two.mp hs
  have hmax :m=(zye {x} : znc R) ⊔ zye {y} := by
    rw [← Ideal.span_insert]
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hspan.symm
  have not_principal (z :R) :m≠zye {z} := by
    intro he
    have ht:=Submodule.spanFinrank_span_le_ncard_of_finite (R:=R) (Set.finite_singleton z)
    change (zye {z}).spanFinrank≤_ at ht
    rw [← he,hdim,Set.ncard_singleton] at ht
    omega
  have hx :x∈m:=hmax ▸ zKg (z5J x)
  have hy' : y∉(zye {x} : znc R) := fun hy =>
    not_principal x (hmax.trans (sup_eq_left.mpr (zvl _ |>.mpr hy)))
  have hx' : x∉m^2 := by
    intro h
    apply not_principal y
    apply zWs _ (hmax ▸ ztJ)
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I:=m) (zLU _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · rw [zs5,← pow_two]
      calc
        m=(zye {x} : znc R) ⊔ zye {y} := hmax
        _≤_:=zbX
          ((zvl _).mpr (zs0 h)) zPQ
  have hp:Prime x :=irreducible_iff_prime.mp
    ⟨(z0F _).mp hx,fun a b hab=> by
      by_contra! hn
      apply hx'
      simpa [← hab,pow_two] using zgK
        ((z0F _).mpr hn.1) ((z0F _).mpr hn.2)⟩
  exact eQB hp.ne_zero ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hy' hmax i
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
theorem eEr :
 262144+131072*(7*262144^3+1)^2<(2130706433:ℕ)^6:= by norm_num
end yP.aLT
end
section
namespace yP
open Finset Module
theorem d3Z
   {K V I:Type*} [zrb K] [z85 K] [AddCommGroup V] [Module K V]
   [z85 V] [FiniteDimensional K V]
   (s :zJe I) (p:I→zpI K V)
   (hp : ∀ i∈s,p i ≠ ⊤) (hs :s.card≤zhP K) :
   ∃ v :V,∀ i∈s,v∉p i:= by
 classical
 by_cases he :s = ∅
 · subst s
   exact ⟨0,by simp⟩
 obtain ⟨i₀,hi₀⟩:=Finset.nonempty_iff_ne_empty.mpr he
 let q:=zhP K
 let d:=zsE K V
 let N :=q^(d - 1)
 have hq:1<q:=Fintype.one_lt_card
 have hd:0<d:=lt_of_le_of_lt (zD0 _) (zYs (hp i₀ hi₀))
 have hN :0<N :=pow_pos (by omega :0<q) _
 have hfull:q*N=zhP V:= by
   rw [zbA (K:=K)]
   exact (zDE _ _).trans (Nat.pow_pred_mul hd)
 let A:I→zJe V:= fun i=>Finset.univ.filter fun x=>x∈p i
 have hz : ∀ i,(0:V)∈A i:= by intro i; simp [A]
 have hA : ∀ i∈s,(A i).card≤N := by
   intro i hi
   change (Finset.univ.filter fun x :V=>x∈p i).card≤N
   rw [← Fintype.card_subtype (fun x :V=>x∈p i)]
   rw [zbA (K:=K)]
   change q^zsE K (p i)≤q^(d - 1)
   have hr :=zYs (hp i hi)
   gcongr
   omega
 let U:=s.biUnion fun i=>(A i).erase 0
 have hU:U.card≤q*(N - 1) := by
   apply (Finset.card_biUnion_le_card_mul s (fun i=>(A i).erase 0) (N - 1) ?_).trans
   · exact Nat.mul_le_mul_right _ hs
   · intro i hi
     have hzero :=z0k (hz i)
     have hbound:=hA i hi
     omega
 have hcomp: (Finset.univ.erase (0:V)).card+1=zhP V:= by
   simpa using (z0k (zTc (0:V)))
 have hstrict :U.card<(Finset.univ.erase (0:V)).card:= by
   have hprod:q*(N - 1)=q*N - q:= by
     rw [Nat.mul_sub_left_distrib,Nat.mul_one]
   rw [hprod,hfull] at hU
   have hV:q≤zhP V:= by
     rw [← hfull]
     nlinarith
   omega
 obtain ⟨v,hv,hvU⟩:=Finset.exists_mem_notMem_of_card_lt_card hstrict
 refine ⟨v,?_⟩
 intro i hi hvp
 apply hvU
 exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_erase.mpr
   ⟨(Finset.mem_erase.mp hv).1,by simpa [A] using hvp⟩⟩
theorem d4O
   {K I R:Type*} [zrb K] [z85 K] [z85 R]
   (s :zJe I) (v :I→R→K)
   (hv : ∀ i∈s,v i≠0) (hs :s.card≤zhP K) :
   ∃ lambda :R→K,∀ i∈s,(∑ j,lambda j*v i j)≠0:= by
 classical
 let f :I→((R→K) →ₗ[K] K) := fun i =>
   { toFun:= fun lambda => ∑ j,lambda j*v i j
     map_add' := by intro a b; simp [add_mul,zfW]
     map_smul' := by intro a b; simp [zxw,ztg] }
 have hp : ∀ i∈s,z83 (f i) ≠ ⊤ := by
   intro i hi htop
   obtain ⟨j,hj⟩ : ∃ j,v i j≠0:= by
     by_contra hn
     push_neg at hn
     exact hv i hi (funext hn)
   have heval :f i (znV j 1)=v i j:= by simp [f,zOw]
   have hz : (znV j 1 :R→K)∈z83 (f i) := by rw [htop]; trivial
   change f i (znV j 1)=0 at hz
   exact hj (heval.symm.trans hz)
 obtain ⟨lambda,hlambda⟩:=d3Z s
   (fun i=>z83 (f i)) hp hs
 exact ⟨lambda,by simpa [f] using hlambda⟩
end yP
end
section
namespace yP.a92
noncomputable section
open scoped BigOperators
variable {K I R:Type*} [zrb K] [z85 K] [z85 R]
def project (lambda :R→K) (f :I→R→K) :I→K :=
 fun i ↦ ∑ r,lambda r*f i r
omit [zrb K] [z85 K] [z85 R] in
private theorem cNy {f g:I→R→K} (hne :f≠g) :
  ∃ i,f i≠g i:= by
 by_contra h
 push Not at h
 exact hne (funext h)
theorem d4E (P:zJe (I→R→K))
   (hroom:P.card^2≤zhP K) :
   ∃ lambda :R→K,Set.InjOn (project (I:=I) lambda) (P:Set (I→R→K)) := by
 classical
 let pairs :=(P.product P).filter fun fg ↦ fg.1≠fg.2
 let coordinate :pairs→ I:= fun fg ↦
   Classical.choose (cNy (Finset.mem_filter.mp fg.property).2)
 let residual:pairs→R→K:= fun fg ↦ fg.val.1 (coordinate fg) - fg.val.2 (coordinate fg)
 have hresidual : ∀ fg:pairs,residual fg≠0:= by
   intro fg
   exact sub_ne_zero.mpr (Classical.choose_spec
     (cNy (Finset.mem_filter.mp fg.property).2))
 have hpairs : (zdB :zJe pairs).card≤zhP K:= by
   rw [Finset.card_univ,Fintype.card_coe]
   calc
     pairs.card≤(P.product P).card:=Finset.card_filter_le _ _
     _=P.card^2 := by simp [pow_two]
     _≤zhP K:=hroom
 obtain ⟨lambda,hlambda⟩:=yP.d4O
   (zdB :zJe pairs) residual (fun fg _ ↦ hresidual fg) hpairs
 refine ⟨lambda,?_⟩
 intro f hf g hg heq
 by_contra hne
 let fg:pairs :=⟨(f,g),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hf,hg⟩,hne⟩⟩
 apply hlambda fg (zTc _)
 have he :=zTC heq (coordinate fg)
 change (∑ r,lambda r*f (coordinate fg) r) =
   ∑ r,lambda r*g (coordinate fg) r at he
 change (∑ r,lambda r*(f (coordinate fg) r - g (coordinate fg) r))=0
 simpa only [mul_sub,Finset.sum_sub_distrib] using sub_eq_zero.mpr he
omit [z85 K] in
theorem ePd (C:zpI K (I→K)) (lambda :R→K)
  (f :I→R→K) (hf : ∀ r,(fun i ↦ f i r)∈C) :project lambda f∈C:= by
 classical
 have hm: (∑ r,lambda r•(fun i ↦ f i r))∈C :=
  C.sum_mem (fun r _ ↦ C.smul_mem (lambda r) (hf r))
 have heq :project lambda f = ∑ r,lambda r•(fun i ↦ f i r) := by
  ext i
  simp [project]
 rw [heq]
 exact hm
open Classical in
def aaC [z85 I] {A:Type*} (f w:I→A) :ℕ :=
 (Finset.univ.filter fun i ↦ f i=w i).card
omit [zrb K] [z85 K] [z85 R] in
theorem cA4 [z85 I] {A B:Type*}
  (f w:I→A) (g z :I→B) (h : ∀ i,f i=w i→ g i=z i) :
  aaC f w≤aaC g z := by
 classical
 apply Finset.card_le_card
 intro i hi
 exact Finset.mem_filter.mpr ⟨zTc _,h i (Finset.mem_filter.mp hi).2⟩
omit [z85 K] in
theorem dsO [z85 I] (lambda :R→K) (f w:I→R→K) :
  aaC f w≤aaC (project lambda f) (project lambda w) := by
 classical
 apply cA4
 intro i he
 simp only [project,he]
theorem cSg [z85 I]
   (C:zpI K (I→K)) (A B:ℕ)
   (hroom: (B+1)^2≤zhP K)
   (hscalar : ∀ w:I→K,∀ P:zJe (I→K),
     (∀ f∈P,f∈C∧A≤aaC f w)→P.card≤B)
   (w:I→R→K) (P:zJe (I→R→K))
   (hP : ∀ f∈P,(∀ r,(fun i ↦ f i r)∈C)∧A≤aaC f w) :
   P.card≤B:= by
 classical
 by_contra hlarge
 have hsize :B+1≤P.card:= by omega
 obtain ⟨Q,hQP,hQcard⟩:=zo4 hsize
 obtain ⟨lambda,hinj⟩:=d4E Q (by simpa only [hQcard] using hroom)
 have hprojected : ∀ f∈Q.image (project lambda),
     f∈C∧A≤aaC f (project lambda w) := by
   intro f hf
   obtain ⟨g,hg,rfl⟩:=Finset.mem_image.mp hf
   obtain ⟨hcode,hagree⟩:=hP g (hQP hg)
   exact ⟨ePd C lambda g hcode,
     hagree.trans (dsO lambda g w)⟩
 have hbound:=hscalar (project lambda w) (Q.image (project lambda)) hprojected
 rw [Finset.card_image_of_injOn hinj,hQcard] at hbound
 omega
end
end yP.a92
end
section
namespace yP.bQq
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
theorem map_resultant_eq_zero_of_common_root
  {R S:Type*} [za6 R] [za6 S]
  (phi:R →+* S) (f g:R[X]) (m n:ℕ)
  (hf :f.natDegree≤ m) (hg:g.natDegree≤n) (hsize :m≠0∨n≠0)
  (z :S) (hfroot :f.eval₂ phi z=0) (hgroot :g.eval₂ phi z=0) :
  phi (f.resultant g m n)=0:= by
 obtain ⟨p,q,_hp,_hq,hbezout⟩ :=
  Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hsize
 have he :=zPw (fun t:R[X] ↦ t.eval₂ phi z) hbezout
 simpa only [eval₂_add,zxy,zJU,hfroot,hgroot,zero_mul,zOP] using he.symm
theorem c1j {E :Type*} [zrb E] [CharP E 2130706433]
  (r :ℕ) (_hr :r≤2) (i:ℕ) (hri:r< i) (hi:i<131073) :
  (i.choose r :E)≠0:= by
 have h:=natCast_choose_ne_zero_of_ringChar (D:=131072) (s :=r)
  (Or.inr (by rw [ringChar.eq E 2130706433]; norm_num)) (i - r)
  (by omega) (by omega)
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
theorem grg (d:ℕ) (Q:zQp E (d+1)) (P:E[X])
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
    (hQ:Q≠0) (P:E[X]) (hroot :zho Q P=0)
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
open Classical in
def aul (nodes :I ↪ F) :zJe F:=Finset.univ.image nodes
omit [zrb F] in
theorem dyE (nodes :I ↪ F) : (aul nodes).card=zhP I:= by
 classical
 unfold aul
 rw [ze7 _ nodes.injective,Finset.card_univ]
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
theorem d4F (C D:ModuleCode I K K) (delta :ℝ)
    (U:Fin 2→ I→R→K) (hU : ∀ j r,(fun i ↦ U j i r)∈D)
    (S:zJe K) (hs : (S.card:ℕ∞)≤ENat.card K)
    (hbad : ∀ gamma∈S,IsMCA (z7S K) (C^⋈R) gamma U delta) :
    ∃ V:Fin 2→ I→K,(∀ j,V j∈D) ∧
      ∀ gamma∈S,IsMCA (z7S K) C gamma V delta := by
  classical
  choose! T hT using hbad
  obtain ⟨lambda,hlambda⟩:=Code.exists_rowFunctional_forall_notMem C U S T hs
    (fun gamma hg ↦ (hT gamma hg).2.2)
  let V:Fin 2→ I→K:= fun j i ↦ ∑ r,lambda r•U j i r
  refine ⟨V,?_,?_⟩
  · intro j
    have heq :V j = ∑ r,lambda r•(fun i ↦ U j i r) := by
      ext i
      simp [V]
    rw [heq]
    exact D.sum_mem (fun r _ ↦ D.smul_mem (lambda r) (hU j r))
  · intro gamma hg
    refine ⟨T gamma,(hT gamma hg).1,?_,hlambda gamma hg⟩
    have hcomb:=Code.projectedWord_rowCombination_mem C _ (T gamma) lambda (hT gamma hg).2.1
    have hfun: (fun i ↦ ∑ r,lambda r•(∑ j,(z7S K gamma j)•U j i) r) =
        fun i ↦ ∑ j,(z7S K gamma j)•V j i:= by
      funext i
      simp only [V,Finset.sum_apply,zD4,Finset.smul_sum]
      rw [Finset.sum_comm]
      exact zUo rfl fun j _ ↦ zUo rfl fun r _ ↦ smul_comm _ _ _
    rwa [hfun] at hcomb
theorem c8F (C D:ModuleCode I K K) (delta :ℝ) (B:ℕ)
   (hroom:B+1≤zhP K)
   (hscalar : ∀ V:Fin 2→ I→K,(∀ j,V j∈D) → ∀ S:zJe K,
     (∀ gamma∈S,IsMCA (z7S K) C gamma V delta)→S.card≤B)
   (U:Fin 2→ I→R→K) (hU : ∀ j r,(fun i ↦ U j i r)∈D)
   (S:zJe K) (hbad : ∀ gamma∈S,IsMCA (z7S K) (C^⋈R) gamma U delta) :
   S.card≤B:= by
 classical
 by_contra hlarge
 have hsize :B+1≤S.card:= by omega
 obtain ⟨Q,hQS,hQcard⟩:=zo4 hsize
 have hroom' : (Q.card:ℕ∞)≤ENat.card K:= by
   rw [hQcard,ENat.card_eq_coe_fintype_card]
   exact_mod_cast hroom
 obtain ⟨V,hV,hbadV⟩:=d4F C D delta U hU Q hroom'
   (fun gamma hg ↦ hbad gamma (hQS hg))
 have hcount:=hscalar V hV Q hbadV
 rw [hQcard] at hcount
 omega
end
end yP.FM
end
