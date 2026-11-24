import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import ProximityPrize.SubmissionLower.AE
set_option Elab.async false
open _root_ renaming Algebra.algebraMap→lJ,Finset→lV,Finset.sum_add_distrib→pC,FractionRing→ oj,Function.Injective→ oK,Ideal→c9,Ideal.span→nX,Ideal.subset_span→ oZ,MvPolynomial→aU,MvPolynomial.C→n5,MvPolynomial.X→mD,MvPolynomial.affineHilbertPolynomial→ ox,MvPolynomial.coeff_mul_X'→ oY,MvPolynomial.eval→lz,MvPolynomial.eval_X→ oy,MvPolynomial.map→ oz,MvPolynomial.pderiv→ ov,MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one→pz,Polynomial→ oD,Polynomial.derivative→cy,WithBot→ oq,aR.Shape→lI,map_mul→nq,ringKrullDim→nI
set_option autoImplicit true
section
namespace dN
noncomputable section
open Polynomial K1 aR
open scoped BigOperators
abbrev lN :=oj ao[X]
abbrev GeoField:=AlgebraicClosure lN
abbrev GeoJets :=aU (Fin 4) GeoField
def j8:ao[X] →+* GeoField :=
 (lJ lN GeoField).comp (lJ ao[X] lN)
def bC (P:af 4) :GeoJets :=oz j8 P
def An (S:ao[X]) :GeoJets →+* GeoField :=
 lz (fun i=>j8 (jet S i))
def Ch (S:ao[X]) :c9 GeoJets :=RingHom.ker (An S)
def kC (f Q:af 4) :c9 GeoJets :=
 nX {bC f,bC Q}
def AX (aI:c9 GeoJets) (E :af 4) :c9 GeoJets :=
 aI ⊔ nX {bC E}
def oA (J aI:c9 GeoJets) (hp:aI.IsPrime) :ℕ∞ :=
 letI:=hp
 let L:=Localization.AtPrime aI
 Module.length L (L ⧸ J.map (lJ GeoJets L))
def separant (g:af 4) :af 4 :=ov 3 g
def lX (P:af 4) :af 4 :=
 ∑ m∈P.support,MvPolynomial.monomial m (cy (P.coeff m))
def pK (P:af 4) :af 4 :=
  lX P +
  ∑ i:Fin 3,n5 (C ((i.val+1 :ℕ) :ao)) *
    mD i.succ*ov i.castSucc P
def u6 (g P:af 4) :af 4 :=
 separant g*pK P - pK g*separant P
def aqZ (g:af 4) (a :ℕ) (P:af 4) :af 4 :=
 separant g*u6 g P-(a :af 4)*u6 g (separant g)*P
def su (g:af 4) :ℕ→af 4
 | 0=>MvPolynomial.X 0
 | n+1=>aqZ g (2*n) (su g n)
def vU (g:af 4) :af 4 :=su g bf
def ZV (g:af 4) :af 4 :=su g (bf+1)
def Invariant (g:af 4) (aI:c9 GeoJets) :Prop :=
 ∀ P:af 4,bC P∈aI→bC (u6 g P)∈aI
def YR (f :af 4) (aI:c9 GeoJets) (r :ℕ) :Prop :=
  r<(shape f).t∧(∀ j≤ r,bC ((separant^[j]) f)∈aI) ∧
    bC (separant ((separant^[r]) f))∉aI
def agC (Γ:lV K) (s :K→K[X]) (d:ℕ) :Prop := by
  classical
  exact ∀ x a :K,(∃ γ∈Γ,(s γ).eval x≠a) →
    (Γ.filter fun γ=>(s γ).eval x=a).card≤d
structure DA (Γ:lV K) where
 n:ℕ
 dO:Fin n→lV K
 subset : ∀ i,dO i⊆Γ
 degree :Fin n→ℕ
def DA.union {Γ:lV K} (C:DA Γ) :lV K:= by
 classical exact Finset.univ.biUnion C.dO
def DA.total {Γ:lV K} (C:DA Γ) :ℕ := ∑ i,C.degree i
def DA.qv {Γ:lV K} (C:DA Γ) (s :K→K[X]) :Prop :=
 ∀ i,agC (C.dO i) s (C.degree i)
def aB7 (Γ:lV K) (s :K→K[X]) (d:ℕ) :Prop := by
  classical
  exact ∀ x a :K,(∃ γ∈Γ,(s γ).eval x≠a) →
    let H :=Γ.filter fun γ=>(s γ).eval x=a
    ∃ C:DA H,H⊆C.union∧C.qv s∧(∀ i,0<C.degree i)∧C.total≤d
def DA.uG {Γ:lV K} (C:DA Γ) (s :K→K[X]) :Prop :=
 ∀ i,aB7 (C.dO i) s (C.degree i)
abbrev H6:Shape :=⟨4013,1650,550⟩
end
end dN
end
section
namespace dN
noncomputable section
open Polynomial aR
open scoped BigOperators
@[simp] private theorem ajn (P:af 4) (m:Fin 4 →₀ ℕ) :
    (lX P).coeff m=cy (P.coeff m) := by
  classical
  rw [lX,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial,Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,map_zero]
private theorem aTO (p:ao[X]) :
  lX (n5 p)=n5 (cy p) := by
 classical
 apply MvPolynomial.ext
 intro m
 rw [ajn]
 by_cases hm:0=m <;> simp [MvPolynomial.coeff_C,hm]
private theorem aCH (P Q:af 4) :
  lX (P+Q)=lX P+lX Q:= by
 ext m
 simp
private theorem bnr (P:af 4) (j:Fin 4) :
  lX (P*mD j)=lX P*mD j:= by
 classical
 ext m
 rw [ajn,oY ,oY]
 split_ifs <;> simp
private theorem aNu (P:af 4) (a :Fin 4→ao[X]) :
    cy (lz a P)=lz a (lX P) +
      ∑ i,cy (a i)*lz a (ov i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [aTO]
  | add P Q hP hQ =>
    simp only [map_add,aCH,hP,hQ,mul_add,pC]
    ring
  | mul_X P j ih =>
    rw [nq,oy ,derivative_mul,ih,bnr,
      nq,oy]
    simp only [MvPolynomial.pderiv_mul,map_add,nq,oy ,
      mul_add,pC]
    have left: (∑ i,cy (a i) *
          (lz a (ov i P)*a j)) =
        (∑ i,cy (a i)*lz a (ov i P))*a j:= by
      simp only [Finset.sum_mul,mul_assoc]
    have right: (∑ i,cy (a i) *
          (lz a P*lz a (ov i (mD j)))) =
        cy (a j)*lz a P:= by
      simp [MvPolynomial.pderiv_X,Pi.single_apply,mul_ite]
    rw [left,right]
    ring
private theorem aNh (S:ao[X]) (k :ℕ) :
  cy (hasseDeriv k S)=C ((k+1 :ℕ) :ao)*hasseDeriv (k+1) S:= by
 have h:=LinearMap.congr_fun (hasseDeriv_comp (R:=ao) 1 k) S
 simpa [hasseDeriv_one',Nat.choose_one_right,nsmul_eq_mul,C_eq_natCast,Nat.add_comm,add_mul] using h
private theorem bdn (P:af 4) (S:ao[X]) :
   cy (cK P S)=cK (pK P) S +
     cy (jet S (3:Fin 4))*cK (separant P) S:= by
 unfold cK pK separant
 rw [aNu,Fin.sum_univ_castSucc,map_add,map_sum]
 rw [← add_assoc]
 congr 2
 refine Finset.sum_congr rfl fun i _ => ?_
 simp only [jet,aNh,nq,MvPolynomial.eval_C,oy ,
   Fin.val_castSucc,Fin.val_succ]
theorem aNw (g P:af 4) (S:ao[X]) (hg:cK g S=0) :
   cK (u6 g P) S=cK (separant g) S*cy (cK P S) := by
 have hz :cK (pK g) S +
     cy (jet S (3:Fin 4))*cK (separant g) S=0:= by
   rw [← bdn,hg,map_zero]
 unfold u6
 rw [bdn]
 change (lz (jet S)) (_-_)= _
 rw [map_sub,nq,nq]
 change cK (separant g) S*cK (pK P) S -
     cK (pK g) S*cK (separant P) S= _
 linear_combination -cK (separant P) S*hz
private theorem anS (a :ℕ) (U V:ao[X]) :
   U*(U*cy (U^a*V))-(a :ao[X])*(U*cy U)*(U^a*V) =
     U^(a+2)*cy V:= by
 cases a with
 | zero=>simp [pow_two,mul_assoc]
 | succ a =>
   rw [derivative_mul,derivative_pow,Nat.succ_sub_one,
     pow_add U (a+1) 2,pow_succ' U a]
   simp only [C_eq_natCast]
   push_cast
   ring
theorem arh (g:af 4) (S:ao[X]) (hg:cK g S=0) (n:ℕ) :
    cK (su g n) S =
      cK (separant g) S^(2*n)*((cy (R:=ao))^[n]) S:= by
  induction n with
  | zero =>
    simp [su,cK,jet]
  | succ n ih =>
    let e :=lz (jet S:Fin 4→ao[X])
    change e (aqZ g (2*n) (su g n))= _
    unfold aqZ
    rw [map_sub,nq,nq,nq,map_natCast]
    change cK (separant g) S*cK (u6 g (su g n)) S -
      (↑(2*n) :ao[X])*cK (u6 g (separant g)) S *
        cK (su g n) S= _
    rw [aNw _ _ _ hg,aNw _ _ _ hg,ih,
      anS,
      show 2*(n+1)=2*n+2 by omega,Function.iterate_succ_apply']
end
end dN
end
section
namespace lB
noncomputable section
open Polynomial aR dN
abbrev AK:=Fin bf
abbrev KE :=Fin 4→GeoField
def bF (p:lI) :Prop :=p.j≤p.b∧3*p.t≤p.j
def yy (g:GeoJets) (p:lI) :Prop :=
 g.totalDegree≤p.b∧g.weightedTotalDegree Fin.val≤p.j∧g.degreeOf 3≤p.t
structure TaylorChart where
 denom:GeoJets
 numerator :AK→GeoJets
 initial : ∀ i:Fin 4,
  numerator (i.castLE (by decide :4≤bf))=mD i*denom
def TaylorChart.dM (C:TaylorChart) (h:lI) :Prop :=
 yy C.denom h ∧ ∀ i,yy (C.numerator i) h
def TaylorChart.aay (C:TaylorChart) (S:ao[X]) :Prop :=
  An S C.denom≠0 ∧
    ∀ i,An S (C.numerator i) =
      An S C.denom*j8 (hasseDeriv i.val S)
abbrev agy :=GeoField×(AK→GeoField)
def TaylorChart.pullback (C:TaylorChart) (a :agy) :GeoJets :=
 n5 a.1*C.denom + ∑ i,n5 (a.2 i)*C.numerator i
def aKn (f g u v :GeoJets) (y :KE) :Prop :=
 RingHom.ker (lz y)∈(nX ({f,g,u,v} : Set GeoJets)).minimalPrimes
def cAp (f g:GeoJets) (C:TaylorChart) (d:ℕ) :Prop :=
  ∀ a b:agy,∀ points :lV KE,
    (∀ y∈points,aKn f g (C.pullback a) (C.pullback b) y ∧
      lz y C.denom≠0)→points.card≤d
end
end lB
end
section
namespace BO
noncomputable section
open Polynomial K1 aR dN
open scoped BigOperators
abbrev m6 (f :af 4) :Shape :=(shape f).iU
def Uy (g P:af 4) (a :ℕ) :af 4 :=
 (u6 g)^[a] P
def asR (f :af 4) (aI:c9 GeoJets) (r w:ℕ) :Prop :=
  let g:=(separant^[r]) f
  ¬ f∣g∧aO (shape g) (m6 f)∧0<w ∧
    ∃ hZ: (kC f g).IsMinimalPrime aI,
      oA (kC f g) aI hZ.isPrime=(w:ℕ∞)
structure aYz (f :af 4) (C:c9 GeoJets) :Prop where
 prime :C.IsPrime
 dim:nI (GeoJets ⧸ C)=1
 contains :bC f∈C
abbrev uL (a :lI) :=Fin 4→Fin (a.b+1)
abbrev dV (a :lI) :=oj (aU (uL a) GeoField)
abbrev adi (a :lI) :=aU (Fin 4) (dV a)
def Bz (a :lI) :lV (uL a) :=
  Finset.univ.filter fun m =>
    (∑ i,(m i).val)≤a.b ∧
      (∑ i,i.val*(m i).val)≤a.j∧(m 3).val≤a.t
def adK (a :lI) :adi a :=
  ∑ m∈Bz a,
    n5 (lJ (aU (uL a) GeoField)
      (dV a) (mD m)) *
      ∏ i:Fin 4,mD i^(m i).val
def pN (C:c9 GeoJets) (a :lI) :ℕ :=
  let J:=C.map (oz (lJ GeoField (dV a))) ⊔
    nX {adK a}
  Module.finrank (dV a) (adi a ⧸ J)
end
end BO
end
section
namespace lB
noncomputable section
open Polynomial MvPolynomial aR dN
open RingTheory.Sequence
open scoped Pointwise
theorem SZ:oK j8 :=
 (lJ lN GeoField).injective.comp (IsFractionRing.injective ao[X] lN)
theorem aFf :oK bC :=
 MvPolynomial.map_injective _ SZ
private theorem aOO {R:Type*} [CommRing R] (f x :R) :
  x∈f•(⊤ : Submodule R R)↔f∣x := by
 simp only [Submodule.mem_smul_pointwise_iff_exists,Submodule.mem_top,true_and,smul_eq_mul]
 exact exists_congr fun _=>eq_comm
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem amo (f g:af 4) (hf :Irreducible f) (hg : ¬ f∣g) :
   IsRelPrime (bC f) (bC g) := by
 have hp:Prime f :=UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
 have hreg:IsWeaklyRegular (af 4) [f,g] := by
   rw [isWeaklyRegular_cons_iff,isWeaklyRegular_singleton_iff]
   refine ⟨mul_right_injective₀ hp.ne_zero,?_⟩
   apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
   intro x hx
   exact (aOO f x).mpr
     ((hp.dvd_mul.mp ((aOO f (g*x)).mp hx)).resolve_left hg)
 let _:Algebra ao[X] GeoField:=j8.toAlgebra
 let _:Module.IsTorsionFree ao[X] GeoField :=
   Module.isTorsionFree_iff_algebraMap_injective.mpr SZ
 have hflat :Module.Flat (af 4) GeoJets :=
   Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv ao[X] (af 4) GeoField GeoJets).symm.toLinearEquiv
 have h:=hreg.of_flat (S:=GeoJets)
 change IsWeaklyRegular GeoJets [bC f,bC g] at h
 rw [isWeaklyRegular_cons_iff,isWeaklyRegular_singleton_iff] at h
 rintro a ⟨b,hb⟩ ⟨c,hc⟩
 have hzero :bC f≠0:= fun hz=>hp.ne_zero (aFf (hz.trans (map_zero _).symm))
 have hprod:bC g*b=bC f*c:= by rw [hc,hb]; ring
 have hdiv :bC f∣b:=(aOO _ _).mp
   (mem_of_isSMulRegular_quotient_of_smul_mem h.2
     ((aOO _ _).mpr ⟨c,hprod⟩))
 obtain ⟨q,hq⟩:=hdiv
 have hb0:b≠0:=right_ne_zero_of_mul (hb ▸ hzero)
 have hu:a*q=1 :=mul_left_cancel₀ hb0 (by
   calc
     b*(a*q)=(a*b)*q:= by ring
     _=b:= by rw [← hb,← hq]
     _=b*1 :=(mul_one _).symm)
 exact ⟨⟨a,q,hu,by rw [mul_comm,hu]⟩,rfl⟩
end
end lB
end
section
namespace GJ
noncomputable section
open aR dN BO lB
open scoped BigOperators
def vE (a :lI) :Prop :=bF a∧0<a.t
abbrev aav (a h:lI) :=uL a ⊕ uL h
abbrev VM (a h:lI) :=
 oj (aU (aav a h) GeoField)
def Uq {σ:Type*} (a :lI) (ι:uL a→σ) :
    aU (Fin 4) (oj (aU σ GeoField)) :=
  ∑ m∈Bz a,
    n5 (lJ (aU σ GeoField)
      (oj (aU σ GeoField)) (mD (ι m))) *
      ∏ i:Fin 4,mD i^(m i).val
def Ux (aI:c9 GeoJets) (a h:lI) :ℕ :=
  let F:=VM a h
  let I:=aI.map (oz (lJ GeoField F)) ⊔
    nX {Uq a (Sum.inl:uL a→aav a h),
      Uq h (Sum.inr :uL h→aav a h)}
  Module.finrank F (aU (Fin 4) F ⧸ I)
abbrev Ib (F G:GeoJets) :c9 GeoJets :=nX {F,G}
end
end GJ
end
section
namespace GJ
noncomputable section
open MvPolynomial aR dN BO lB
private theorem b68 {k R:Type*} [Field k]
   [CommRing R] [IsDomain R] {d:ℕ} [Algebra (aU (Fin d) k) R]
   [FaithfulSMul (aU (Fin d) k) R] [Module.Finite (aU (Fin d) k) R] :
   nI R=(d:oq ℕ∞) := by
 let B:=aU (Fin d) k
 have hB:nI B=(d:oq ℕ∞) := by
   rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field]
   simp
 rw [← hB]
 apply le_antisymm
 · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (lJ B R))
   intro x y hxy
   exact Ideal.IsIntegral.under_lt_under (show x.asIdeal<y.asIdeal from hxy)
 · obtain ⟨b,hb,hd⟩:=Ideal.exists_isPrime_le_height (n:=d) hB.ge
   obtain ⟨z,hz⟩ :=
     Algebra.IsIntegral.comap_surjective B R (⟨b,hb⟩:PrimeSpectrum B)
   have hz' : z.asIdeal.under B=b:=congrArg PrimeSpectrum.asIdeal hz
   have hle :=Ideal.height_under_le_height (R:=B) z.asIdeal
   rw [hz'] at hle
   calc
     nI B=(d:oq ℕ∞) :=hB
     _≤(z.asIdeal.height:oq ℕ∞) :=WithBot.coe_le_coe.mpr (hd.trans hle)
     _≤ nI R:=Ideal.height_le_ringKrullDim_of_isPrime
private theorem b67 {k R:Type*} [Field k] [CommRing R] [IsDomain R]
  {d:ℕ} (g:aU (Fin d) k →+* R) (hg:oK g)
  (hgfin:g.Finite) :nI R=(d:oq ℕ∞) := by
 let algebra :=g.toAlgebra
 let:=algebra
 let faithful:FaithfulSMul (aU (Fin d) k) R :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
 let finite :Module.Finite (aU (Fin d) k) R:=hgfin
 exact @b68 k R _ _ _ d algebra faithful finite
private theorem b0H {k σ:Type*} [Field k] [Finite σ]
   (I:c9 (aU σ k)) [I.IsPrime] :
   nI (aU σ k ⧸ I) =
     ((ox I).natDegree :oq ℕ∞) := by
 obtain ⟨d,g,hg,hgfin⟩:=exists_finite_inj_algHom_of_fg k (aU σ k ⧸ I)
 have hH :=natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hgfin hg
 rw [Nat.card_fin] at hH
 rw [hH]
 exact b67 g.toRingHom hg hgfin
theorem bf6 {F G:GeoJets} (hF:F≠0) (hproper :IsRelPrime F G)
   {aI:c9 GeoJets} (hZ: (Ib F G).IsMinimalPrime aI) :
   nI (GeoJets ⧸ aI)=2 := by
 let:=hZ.isPrime
 have hFZ:nX {F} ≤ aI :=
   le_trans (Ideal.span_mono (by simp)) hZ.le
 obtain ⟨D,hD,hDZ⟩:=Ideal.exists_minimalPrimes_le hFZ
 let:=hD.isPrime
 have hD0:D ≠ ⊥ := fun e =>
   hF (Ideal.mem_bot.mp (e ▸ hD.le (oZ (by simp))))
 have hDh:D.height = 1 :=
   le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ D hD)
     (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hD0))
 obtain ⟨a,ha,hap⟩:=Ideal.IsPrime.exists_mem_prime_of_ne_bot hD.isPrime hD0
 have heq :=Ideal.eq_span_singleton_of_height_eq_one hDh ha hap
 have hGD:G∉D:= by
   intro hG
   have hFa :a∣F:=Ideal.mem_span_singleton.mp (heq ▸ hD.le (oZ (by simp)))
   have hGa :a∣G:=Ideal.mem_span_singleton.mp (heq ▸ hG)
   exact hap.not_isUnit (hproper hFa hGa)
 have hpair :Ib F G≤D ⊔ nX {G} := by
   rw [Ib,Ideal.span_insert]
   exact sup_le (hD.le.trans le_sup_left) le_sup_right
 have hcut: (D ⊔ nX {G}).IsMinimalPrime aI :=
   ⟨⟨hZ.isPrime,sup_le hDZ ((Ideal.span_mono (by simp)).trans hZ.le)⟩,
     fun J hJ hJZ=>hZ.2 ⟨hJ.1,hpair.trans hJ.2⟩ hJZ⟩
 have hDdeg:=natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hF hD
 have hZdeg:=pz hGD hcut
 rw [Nat.card_fin] at hDdeg
 have hdeg: (ox aI).natDegree=2 := by omega
 simp [b0H aI,hdeg]
theorem bZi {f P:af 4} {aI C:c9 GeoJets}
  (hZ:aI.IsPrime) (hdim:nI (GeoJets ⧸ aI)=2)
  (hf :bC f∈aI) (hP:bC P∉aI)
  (hC: (AX aI P).IsMinimalPrime C) :aYz f C:= by
 let:=hZ
 let:=hC.isPrime
 have hZdeg: (ox aI).natDegree=2 := by
  have hd:=(b0H aI).symm.trans hdim
  exact_mod_cast hd
 have hCdeg:=pz hP hC
 have hd: (ox C).natDegree=1 := by omega
 have hle :aI≤C:=(show aI≤AX aI P from le_sup_left).trans hC.le
 exact ⟨hC.isPrime,by simp [b0H C,hd],hle hf⟩
end
end GJ
end
section
namespace cu
noncomputable section
open K1 Polynomial
open scoped BigOperators
abbrev L:=AlgebraicClosure K
abbrev FX:=oj L[X]
abbrev aZ:=aU (Fin 2) FX
abbrev Equation :=oD aZ
def j9 (g:K[X]) :L[X] :=g.map (lJ K L)
def kr (g:K[X]) :FX:=lJ L[X] FX (j9 g)
def jz :K →+* FX :=
 (lJ L[X] FX).comp ((Polynomial.C:L →+* L[X]).comp (lJ K L))
def qD (z :K) :aZ →+* FX :=
 lz ![jz z,(jz z)^p]
def yq (f :Equation) (z :K) (S:K[X]) :FX :=
 f.eval₂ (qD z) (kr S)
abbrev Jet:=oD Equation
structure Shape where
 m:ℕ
 B:ℕ
 J:ℕ
 U:ℕ
 deriving DecidableEq
structure fO where
 Ly :ℕ
 yBound:ℕ
 seedBound:ℕ
 multiplicity :ℕ
 jetBound:ℕ
 vBound:ℕ
 subbankSeeds :ℕ
def kA (w:ℤ) :fO :=
 if w≤3554 then ⟨3554,5,144,836,1164,247,19371⟩
 else if w≤8249 then ⟨8249,4,98,358,500,105,6798⟩
 else if w≤23999 then ⟨23999,4,47,358,500,105,4860⟩
 else ⟨32680,4,36,358,500,105,3913⟩
def vm (f :Equation) (b:ℕ) :Prop :=
 ∀ i,(f.coeff i).totalDegree≤b
def triangle (U:ℕ) :ℕ:=(U + 1)*(U + 2)/2
def slots (U spent:ℕ) :ℕ :=
 if spent≤U then triangle (U - spent) else 0
abbrev vP:=Shape→ℕ→Submodule FX Jet
def ku (s :Shape) (g:ℕ→ℕ→ℕ) :ℕ :=
 ∑ q∈Finset.range (s.B+1),∑ j∈Finset.range (min q s.J+1),g q j
def rD (P:Jet) (z :K) (S:K[X]) :FX :=
 P.eval₂ (eval₂RingHom (qD z) (kr S)) (kr S.derivative)
def Vy (i:Fin 2) :aZ →+* oD aZ :=
  MvPolynomial.eval₂Hom (C.comp n5)
    (fun j=>C (mD j:aZ)+if j=i then Polynomial.X (R:=aZ) else 0)
def A5 (i:Fin 2) (r :ℕ) (P:Jet) :Jet :=
 P.sum fun j g=>monomial j (g.sum fun k c=>monomial k ((Vy i c).coeff r))
end
end cu
end
section
namespace cu
noncomputable section
open K1 Polynomial
theorem trim (P:L[X]) (h:ℕ) (hh:h≤P.natDegree) :
  ∃ H :L[X],H.Monic∧H.natDegree=h∧H∣P:= by
 classical
 have hc:0<(P.roots.powersetCard h).card:= by
  rw [Multiset.card_powersetCard,IsAlgClosed.card_roots_eq_natDegree]
  exact Nat.choose_pos hh
 obtain ⟨s,hs⟩:=Multiset.card_pos_iff_exists_mem.mp hc
 obtain ⟨hle,hsize⟩:=Multiset.mem_powersetCard.mp hs
 exact ⟨_,monic_multisetProd_X_sub_C s,(natDegree_multiset_prod_X_sub_C_eq_card s).trans hsize,
  (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)).trans P.prod_multiset_X_sub_C_dvd⟩
theorem dio (P:K[X]) :
  j9 (P.map twist)=(j9 P).map (frobenius L p) := by
 simp only [j9,Polynomial.map_map,twist,RingHom.frobenius_comm]
end
end cu
end
