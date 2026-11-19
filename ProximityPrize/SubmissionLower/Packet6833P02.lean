import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.GradedMulAction
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Int.Associated
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Real.Embedding
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Submonoid.Inverses
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.GameAdd
import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.NormalClosure
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.ZMod
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.GroupTheory.CosetCover
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import ProximityPrize.SubmissionLower.Packet6833P01
set_option autoImplicit false
set_option linter.all false
set_option maxErrors 100000

section
set_option linter.all false
section Compact_PackedLegacy
section PackedLegacy_C3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN107
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN120 RCN102 RCN106 RCN192 RCN197 RCN236 RCN307 RCN225 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A→RCN264.RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀a:A,Transcendental Omega
 (RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀a:A,
 letI:=RCN120.flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega (component a).1))
variable (hgen:∀a:A,
 letI:=RCN120.flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (RCN002.CoordinateField Omega (component a).1))=⊤)
end
end RCN107
end SubmissionLower
end ProximityPrize
end PackedLegacy_C3
section PackedLegacy_I6
namespace ProximityPrize
namespace SubmissionLower
namespace RCN073
open RCN324
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K R:Type} [Field K] [CommRing R] [IsDomain R]
 [Algebra K R] [IsDiscreteValuationRing R]
theorem DWM
   (D:Derivation K R R) (pi:R) (p:ℕ) [CharP R p]
   (_hp:1≤p) (f:R) (hf:pi^p∣f):pi^p∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul,CharP.cast_eq_zero R p,zero_mul,
   mul_zero,add_zero]
 exact ⟨D u,rfl⟩
theorem DBZ
   (D:Derivation K R R) (H DH:R) (c:ℕ→R) (N:ℕ→R)
   (hrec:∀j,N (j+1)=H*D (N j)-c j*N j*DH)
   (a:R) (j:ℕ) (hN:a∣N j) (hDN:a∣D (N j)):
   a∣N (j+1):=by
 obtain ⟨u,hu⟩:=hN
 obtain ⟨v,hv⟩:=hDN
 refine ⟨H*v-c j*u*DH,?_⟩
 rw [hrec j,hv,hu]
 ring
theorem GVI
   (D:Derivation K R R) (H DH:R) (c:ℕ→R) (N:ℕ→R)
   (hrec:∀j,N (j+1)=H*D (N j)-c j*N j*DH)
   (pi a:R) (htangent:D pi=pi*a)
   (hN0:pi∣N 0):∀j,pi∣N j:=by
 intro j
 induction j with
 | zero=>exact hN0
 | succ j ih=>
     apply DBZ D H DH c N hrec pi j ih
     simpa only [pow_one] using
       RCN324.tangent_preserves_divisibility D pi a 1 (by simp) htangent
         (N j) (by simpa only [pow_one] using ih)
theorem GNO
   (D:Derivation K R R) (H DH:R) (c:ℕ→R) (N:ℕ→R)
   (hrec:∀j,N (j+1)=H*D (N j)-c j*N j*DH)
   (pi:R) (p:ℕ) [CharP R p] (hp:1≤p)
   (hN0:pi^p∣N 0):∀j,pi^p∣N j:=by
 intro j
 induction j with
 | zero=>exact hN0
 | succ j ih=>
     apply DBZ D H DH c N hrec (pi^p) j ih
     exact DWM D pi p hp (N j) ih
theorem ELH
   (D:Derivation K R R) (pi:R) (hpi:Irreducible pi)
   (htrans:IsUnit (D pi)) (p k:ℕ) [CharP R p]
   (hp:p.Prime) (hkpos:1≤k) (hkp:k<p)
   (x:R) (u:Rˣ) (hx:x=(u:R)*pi^k):
   IsDiscreteValuationRing.addVal R (D x)=k-1:=by
 have h:=CUH D pi (u:R) k 1 p hp hkp
   hkpos hpi u.isUnit htrans
 rw [hx,mul_comm]
 simpa using h
theorem EGP
   (D:Derivation K R R) (H DH c x next pi:R)
   (hrec:next=H*D x-c*x*DH)
   (hH:IsUnit H) (hpi:Irreducible pi) (htrans:IsUnit (D pi))
   (p k:ℕ) [CharP R p] (hp:p.Prime) (hkpos:1≤k) (hkp:k<p)
   (u:Rˣ) (hx:x=(u:R)*pi^k):
   IsDiscreteValuationRing.addVal R next=k-1:=by
 let v:=IsDiscreteValuationRing.addVal R
 have hDx:v (D x)=k-1:=
   ELH D pi hpi htrans p k hp hkpos hkp x u hx
 have hxv:v x=k:=IsDiscreteValuationRing.addVal_def x u hpi k hx
 have hfirst:v (H*D x)=k-1:=by
   rw [IsDiscreteValuationRing.addVal_mul,
     IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hH,zero_add,hDx]
 have hsecond:k≤v (c*x*DH):=by
   rw [IsDiscreteValuationRing.addVal_mul,
     IsDiscreteValuationRing.addVal_mul,hxv]
   exact le_add_right (le_add_left (le_refl (k:ℕ∞)))
 have hlt:v (H*D x)<v (c*x*DH):=by
   rw [hfirst]
   exact (ENat.coe_lt_coe.mpr (Nat.pred_lt (Nat.ne_zero_of_lt hkpos))).trans_le hsecond
 rw [hrec,v.map_sub_eq_of_lt_left hlt,hfirst]
theorem DTN
   (D:Derivation K R R) (H DH:R) (c:ℕ→R) (N:ℕ→R)
   (p:ℕ) [CharP R p] (hp:p.Prime)
   (hrec:∀j,N (j+1)=H*D (N j)-c j*N j*DH)
   (hH:IsUnit H) (hN0ne:N 0≠0) (hN0nonunit:¬IsUnit (N 0)):
   let mu:=(IsDiscreteValuationRing.addVal R (N 0)).toNat
   1≤mu∧
     ((∃delay,1≤delay∧delay≤mu∧IsUnit (N delay))∨
       (∀delay,¬IsUnit (N delay))):=by
 classical
 let v:=IsDiscreteValuationRing.addVal R
 obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
 obtain ⟨mu,u,hN0⟩:=
   IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hN0ne hpi
 have hv0:v (N 0)=mu:=IsDiscreteValuationRing.addVal_def (N 0) u hpi mu hN0
 have hmuDef:(v (N 0)).toNat=mu:=by rw [hv0];simp
 have hmuPos:1≤mu:=by
   by_contra h
   have hz:mu=0:=Nat.eq_zero_of_not_pos h
   apply hN0nonunit
   apply IsDiscreteValuationRing.addVal_eq_zero_iff.mp
   change v (N 0)=0
   rw [hv0,hz]
   simp
 rw [hmuDef]
 refine ⟨hmuPos,?_⟩
 letI:Decidable (IsUnit (D pi)):=Classical.propDecidable _
 by_cases htrans:IsUnit (D pi)
 · by_cases hmup:mu<p
   · left
     refine ⟨mu,hmuPos,le_rfl,?_⟩
     have horders:∀j≤mu,v (N j)=mu-j:=by
       intro j hj
       induction j with
       | zero=>simpa using hv0
       | succ j ih=>
           have hjlt:j<mu:=by omega
           have hord:=ih hjlt.le
           have hNjNe:N j≠0:=by
             intro hz
             rw [hz,IsDiscreteValuationRing.addVal_zero] at hord
             exact ENat.top_ne_coe (mu-j) hord
           obtain ⟨k,uj,hNj⟩:=
             IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hNjNe hpi
           have hkv:v (N j)=k:=
             IsDiscreteValuationRing.addVal_def (N j) uj hpi k hNj
           have hk:k=mu-j:=by
             exact ENat.coe_inj.mp (hkv.symm.trans hord)
           have hkpos:1≤k:=by omega
           have hkp:k<p:=by omega
           have hstep:=EGP D H DH (c j) (N j)
             (N (j+1)) pi (hrec j) hH hpi htrans p k hp hkpos hkp uj hNj
           rw [hstep,hk]
           exact_mod_cast (show mu-j-1=mu-(j+1) by omega)
     exact IsDiscreteValuationRing.addVal_eq_zero_iff.mp (by
       simpa using horders mu le_rfl)
   · right
     have hpLe:p≤mu:=Nat.le_of_not_gt hmup
     have hpPos:1≤p:=hp.one_le
     have hpow:pi^p∣N 0:=by
       rw [hN0]
       refine ⟨(u:R)*pi^(mu-p),?_⟩
       have hpowEq:pi^mu=pi^p*pi^(mu-p):=by
         rw [←pow_add,Nat.add_sub_of_le hpLe]
       rw [hpowEq]
       ring
     have hall:=GNO D H DH c N hrec pi p hpPos hpow
     intro j hunit
     apply hpi.not_isUnit
     apply isUnit_of_dvd_one
     exact (dvd_pow_self pi (Nat.ne_of_gt hpPos)).trans
       ((hall j).trans (isUnit_iff_dvd_one.mp hunit))
 · right
   have hDmem:D pi∈IsLocalRing.maximalIdeal R:=
     (IsLocalRing.mem_maximalIdeal (D pi)).2 htrans
   obtain ⟨a,ha⟩:∃a,D pi=pi*a:=by
     have hmax:=(IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi
     rw [hmax,Ideal.mem_span_singleton'] at hDmem
     obtain ⟨a,ha⟩:=hDmem
     exact ⟨a,by simpa [mul_comm] using ha.symm⟩
   have hpiDvd:pi∣N 0:=by
     rw [hN0]
     refine ⟨(u:R)*pi^(mu-1),?_⟩
     have hpowEq:pi^mu=pi*pi^(mu-1):=by
       calc
         pi^mu=pi^(1+(mu-1)):=by
           rw [Nat.add_sub_of_le hmuPos]
         _=pi^1*pi^(mu-1):=pow_add pi 1 (mu-1)
         _=pi*pi^(mu-1):=by rw [pow_one]
     rw [hpowEq]
     ring
   have hall:=GVI D H DH c N hrec pi a ha hpiDvd
   intro j hunit
   exact hpi.not_isUnit (isUnit_of_dvd_one
     ((hall j).trans (isUnit_iff_dvd_one.mp hunit)))
end
end RCN073
end SubmissionLower
end ProximityPrize
end PackedLegacy_I6
section PackedLegacy_O2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN270
open IsLocalRing Ideal
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {A:Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
theorem CWS
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2):
   ∃g∈maximalIdeal A,maximalIdeal A=Ideal.span {f,g}:=by
 classical
 let m:=maximalIdeal A
 have hfg:m.FG:=m.fg_of_isNoetherianRing
 have hrank:m.spanFinrank=2:=by
   have hreg:=(isRegularLocalRing_iff A).mp (inferInstance:IsRegularLocalRing A)
   rw [hdim] at hreg
   exact_mod_cast hreg
 have hcard:m.generators.ncard=2:=by
   rw [Submodule.FG.generators_ncard hfg,hrank]
 obtain ⟨a,b,hab,hgen⟩:=Set.ncard_eq_two.mp hcard
 have hspan:Ideal.span {a,b}=m:=by
   simpa [hgen] using m.span_generators
 have ha:a∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hb:b∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hfm:f∈m:=by simpa [m] using hf
 have hfspan:f∈Ideal.span ({a,b}:Set A):=by rwa [hspan]
 obtain ⟨r,s,hrs⟩:=Ideal.mem_span_pair.mp hfspan
 have hunit:IsUnit r∨IsUnit s:=by
   letI:Decidable (IsUnit r):=Classical.propDecidable _
   letI:Decidable (IsUnit s):=Classical.propDecidable _
   by_cases hr:IsUnit r
   · exact Or.inl hr
   by_cases hs:IsUnit s
   · exact Or.inr hs
   · exfalso
     have hrm:r∈m:=(IsLocalRing.mem_maximalIdeal r).mpr hr
     have hsm:s∈m:=(IsLocalRing.mem_maximalIdeal s).mpr hs
     apply hf2
     rw [pow_two,←hrs]
     exact (m*m).add_mem (Ideal.mul_mem_mul hrm ha) (Ideal.mul_mem_mul hsm hb)
 rcases hunit with hr | hs
 · refine ⟨b,hb,le_antisymm ?_ ?_⟩
   · change m≤Ideal.span {f,b}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       obtain ⟨u,rfl⟩:=hr
       have hfmem:f∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have hbmem:b∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have heq:a=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*s*b:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           a=((↑(u⁻¹):A)*(↑u:A))*a:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*((↑u:A)*a+s*b)-
               (↑(u⁻¹):A)*s*b:=by ring
       rw [heq]
       exact (Ideal.span ({f,b}:Set A)).sub_mem
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hbmem)
     · rw [hx]
       exact Ideal.subset_span (by simp)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
 · refine ⟨a,ha,le_antisymm ?_ ?_⟩
   · change m≤Ideal.span {f,a}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       exact Ideal.subset_span (by simp)
     · rw [hx]
       obtain ⟨u,rfl⟩:=hs
       have hfmem:f∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have hamem:a∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have heq:b=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*r*a:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           b=((↑(u⁻¹):A)*(↑u:A))*b:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*(r*a+(↑u:A)*b)-
               (↑(u⁻¹):A)*r*a:=by ring
       rw [heq]
       exact (Ideal.span ({f,a}:Set A)).sub_mem
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hamem)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
theorem BRW
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2)
   (hdimQ:ringKrullDim (A ⧸ Ideal.span {f})=1):
   IsRegularLocalRing (A ⧸ Ideal.span {f}):=by
 obtain ⟨g,hg,hmg⟩:=CWS f hf hf2 hdim
 have hspanProper:Ideal.span ({f}:Set A)≠⊤:=by
   apply ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
   exact Ideal.span_le.2 (by simpa using hf)
 letI:Nontrivial (A ⧸ Ideal.span {f}):=
   Ideal.Quotient.nontrivial_iff.mpr hspanProper
 letI:IsLocalRing (A ⧸ Ideal.span {f}):=
   IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
     Ideal.Quotient.mk_surjective
 apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
 rw [hdimQ]
 have hmax:maximalIdeal (A ⧸ Ideal.span {f})=
     Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:=by
   rw [←IsLocalRing.map_maximalIdeal_of_surjective
     (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective,hmg,
     Ideal.map_span]
   simp [Set.image_insert_eq,Set.image_singleton]
 rw [hmax]
 have hle:(Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:
     Ideal (A ⧸ Ideal.span {f})).spanFinrank≤1:=by
   exact (Submodule.spanFinrank_span_le_ncard_of_finite
     (Set.finite_singleton _)).trans (by simp)
 exact_mod_cast hle
end RCN270
end SubmissionLower
end ProximityPrize
end PackedLegacy_O2
section PackedLegacy_FF
namespace ProximityPrize
namespace SubmissionLower
namespace RCN218
open RCN313 RCN077 RCN136 RCN055 RCN188 RCN270 RCN186 RCN230 IsLocalRing
variable {K:Type*} [Field K]
theorem DPR
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(RCN186.quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F≤p) (hheight:p.height=2)
   (hH:polyH K F∉p)
   (hdimFactor:ringKrullDim (FactorLocal F p hFp)=1):
   IsRegularLocalRing (FactorLocal F p hFp):=by
 letI:IsRegularLocalRing (Localization.AtPrime p):=
   RCN230.mvPolynomial_atPrime_isRegularLocalRing p
 let A:=Localization.AtPrime p
 let f:A:=algebraMap (Poly (K:=K)) A F
 have hdim:ringKrullDim A=2:=by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A,hheight]
   norm_num
 have hf:f∈maximalIdeal A:=by
   exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p F).mpr
     (hFp (Ideal.mem_span_singleton_self F))
 have hf2:f∉maximalIdeal A^2:=by
   intro hf2
   let D:Derivation K A A:=RCN188.localizationDerivation p.primeCompl
     (MvPolynomial.pderiv (2:Fin 4):Derivation K (Poly (K:=K)) _)
   have hDmem:D f∈maximalIdeal A:=RCN218.derivation_mem_maximal_of_mem_sq D f hf2
   have hD:D f=algebraMap (Poly (K:=K)) A (polyH K F):=by
     exact RCN188.localizationDerivation_algebraMap p.primeCompl _ F
   rw [hD] at hDmem
   exact hH ((IsLocalization.AtPrime.to_map_mem_maximal_iff A p (polyH K F)).mp hDmem)
 haveI hsource:IsRegularLocalRing
     (Localization.AtPrime p ⧸ Ideal.span {
       algebraMap (Poly (K:=K)) (Localization.AtPrime p) F}):=by
   change IsRegularLocalRing (A ⧸ Ideal.span {f})
   apply BRW f hf hf2 hdim
   calc
     ringKrullDim (A ⧸ Ideal.span {f})=
         ringKrullDim (FactorLocal F p hFp):=
       ringKrullDim_eq_of_ringEquiv (RCN218.factorAmbientQuotientEquiv F p hFp)
     _=1:=hdimFactor
 exact IsRegularLocalRing.of_ringEquiv (R:=
   Localization.AtPrime p ⧸ Ideal.span {
     algebraMap (Poly (K:=K)) (Localization.AtPrime p) F})
   (RCN218.factorAmbientQuotientEquiv F p hFp)
theorem CWC
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(RCN186.quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F≤p) (hheight:p.height=2)
   (hH:polyH K F∉p):
   IsDiscreteValuationRing (FactorLocal F p hFp):=by
 have hdim:ringKrullDim (FactorLocal F p hFp)=1:=by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height
     (RCN186.quotientPrime (factorIdeal F) p) (FactorLocal F p hFp)]
   exact_mod_cast RCN218.quotientPrime_height_eq_one F p hFp hheight hH
 letI:IsRegularLocalRing (FactorLocal F p hFp):=
   DPR F p hFp hheight hH hdim
 exact RCN324.isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one hdim
theorem DGH (F:Poly (K:=K)):RCN055.baseDerivation F F=0:=by
 rw [RCN055.baseDerivation_apply]
 unfold polyG polyH
 ring
theorem AOJ (F:Poly (K:=K)):
   ∀P∈factorIdeal F,RCN055.baseDerivation F P∈factorIdeal F:=by
 intro P hP
 rw [factorIdeal,Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨RCN055.baseDerivation F A,?_⟩
 rw [(RCN055.baseDerivation F).leibniz,DGH]
 simp
noncomputable def BGO (F:Poly (K:=K)):
   Derivation K (Poly (K:=K) ⧸ factorIdeal F) (Poly (K:=K) ⧸ factorIdeal F):=
 RCN077.quotientDerivation (RCN055.baseDerivation F) (factorIdeal F) (AOJ F)
noncomputable def AXE
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(RCN186.quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F≤p):
   Derivation K (FactorLocal F p hFp) (FactorLocal F p hFp):=
 RCN188.localizationDerivation (K:=K)
   (R:=Poly (K:=K) ⧸ factorIdeal F) (S:=FactorLocal F p hFp)
   (RCN186.quotientPrime (factorIdeal F) p).primeCompl (BGO F)
theorem DBS
   (F P:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(RCN186.quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F≤p):
   AXE F p hFp
       (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
         (Ideal.Quotient.mk (factorIdeal F) P))=
     algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
       (Ideal.Quotient.mk (factorIdeal F) (RCN055.baseDerivation F P)):=by
 rw [AXE,RCN188.localizationDerivation_algebraMap]
 have hq:=RCN077.quotientDerivation_mk
   (K:=K) (A:=Poly (K:=K)) (RCN055.baseDerivation F) (factorIdeal F)
     (AOJ F) P
 exact congrArg
   (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp))
   (by simpa only [BGO] using hq)
theorem EFV
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(RCN186.quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F≤p) (b:ℕ):
   RCN218.factorLocalImage F p hFp (numerator K F (b+1))=
     RCN218.factorLocalImage F p hFp (polyH K F)*
         AXE F p hFp
           (RCN218.factorLocalImage F p hFp (numerator K F b))-
       (2*b:FactorLocal F p hFp)*
         RCN218.factorLocalImage F p hFp (numerator K F b)*
         AXE F p hFp
           (RCN218.factorLocalImage F p hFp (polyH K F)):=by
 rw [RCN313.numerator_succ,RCN055.numeratorStep_eq]
 simp only [RCN218.factorLocalImage,map_sub,map_mul,map_natCast]
 rw [←DBS F (numerator K F b) p hFp,
   ←DBS F (polyH K F) p hFp]
 push_cast
 ring
end RCN218
end SubmissionLower
end ProximityPrize
end PackedLegacy_FF
section PackedLegacy_Q7
namespace ProximityPrize
namespace SubmissionLower
namespace RCN339
open RCN095 RCN237 RCN264 RCN326
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
 {G T1 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1:FlagDegree}
theorem BIB
   (B:FE (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RCN264.RegularComponent Omega G T1 H)
   (coefficient:ℕ) (hcoefficient:coefficient≤r.yz):
   coefficient*B.yzCost C≤B.weightedCost r C:=by
 unfold FE.weightedCost
 calc
   coefficient*B.yzCost C≤r.yz*B.yzCost C:=
     Nat.mul_le_mul_right (B.yzCost C) hcoefficient
   _≤r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C:=by
     omega
end
end RCN339
end SubmissionLower
end ProximityPrize
end PackedLegacy_Q7
section PackedLegacy_FE
namespace ProximityPrize
namespace SubmissionLower
namespace RCN217
open RCN077 RCN313 RCN347 RCN055
noncomputable section
variable {K:Type*} [CommRing K]
abbrev factorIdeal_p19 (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
theorem DGH (F:Poly4 K):RCN055.baseDerivation F F=0:=by
 rw [RCN055.baseDerivation_apply]
 unfold polyG polyH
 ring
theorem AOJ (F:Poly4 K):
   ∀P∈factorIdeal_p19 F,RCN055.baseDerivation F P∈factorIdeal_p19 F:=by
 intro P hP
 rw [Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨RCN055.baseDerivation F A,?_⟩
 rw [RCN347.leibniz_product,DGH]
 ring
def BGO (F:Poly4 K):
   Derivation K (Poly4 K ⧸ factorIdeal_p19 F) (Poly4 K ⧸ factorIdeal_p19 F):=
 RCN077.quotientDerivation (RCN055.baseDerivation F) (factorIdeal_p19 F)
   (AOJ F)
theorem DGI (F P:Poly4 K):
   BGO F (Ideal.Quotient.mk (factorIdeal_p19 F) P)=
     Ideal.Quotient.mk (factorIdeal_p19 F) (RCN055.baseDerivation F P):=
 RCN077.quotientDerivation_mk _ _ _ P
theorem factor_zero_p19 (F:Poly4 K):
   Ideal.Quotient.mk (factorIdeal_p19 F) F=0:=
 Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
theorem CTH (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal_p19 F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q*
       Ideal.Quotient.mk (factorIdeal_p19 F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul,factor_zero_p19]
 ring
theorem FEU (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal_p19 F) (polyG K (F*Q))=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q*
       Ideal.Quotient.mk (factorIdeal_p19 F) (polyG K F):=by
 unfold polyG
 simp only [MvPolynomial.pderiv_mul,map_neg,map_add,map_mul,factor_zero_p19]
 ring
theorem BSM (F Q P:Poly4 K):
   Ideal.Quotient.mk (factorIdeal_p19 F) (RCN055.baseDerivation (F*Q) P)=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q*
       BGO F (Ideal.Quotient.mk (factorIdeal_p19 F) P):=by
 rw [DGI,RCN055.baseDerivation_apply,RCN055.baseDerivation_apply]
 simp only [map_add,map_mul]
 rw [CTH,FEU]
 ring
theorem FEJ {A:Type*} [CommRing A] [Algebra K A]
   (D:Derivation K A A) (q h n nS:A) (b:ℕ)
   (hN:nS=q^(2*b)*n):
   q*h*(q*D nS)-(2*b:A)*nS*(q*D (q*h))=
     q^(2*(b+1))*(h*D n-(2*b:A)*n*D h):=by
 cases b with
 | zero=>
     simp only [hN,mul_zero,pow_zero,one_mul,Nat.cast_zero,
       zero_mul,sub_zero]
     ring
 | succ c=>
     rw [hN]
     simp only [RCN347.leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul,smul_eq_mul,
       Nat.cast_mul,Nat.cast_ofNat]
     have he:2*(c+1)=2*c+2:=by omega
     have hesub:2*c+2-1=2*c+1:=by omega
     have henext:2*(c+1+1)=2*c+4:=by omega
     rw [he,hesub,henext]
     have hp1:q^(2*c+1)=q^(2*c)*q:=by
       rw [pow_add,pow_one]
     have hp2:q^(2*c+2)=q^(2*c)*q^2:=by rw [pow_add]
     have hp4:q^(2*c+4)=q^(2*c)*q^4:=by rw [pow_add]
     rw [hp1,hp2,hp4]
     ring
theorem CPU (F Q:Poly4 K) (b:ℕ):
   Ideal.Quotient.mk (factorIdeal_p19 F) (numerator K (F*Q) b)=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q^(2*b)*
       Ideal.Quotient.mk (factorIdeal_p19 F) (numerator K F b):=by
 induction b with
 | zero=>simp
 | succ b ih=>
   change Ideal.Quotient.mk (factorIdeal_p19 F)
       (RCN313.numeratorStep K (F*Q) b (numerator K (F*Q) b))=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q^(2*(b+1))*
       Ideal.Quotient.mk (factorIdeal_p19 F)
         (RCN313.numeratorStep K F b (numerator K F b))
   rw [RCN055.numeratorStep_eq,RCN055.numeratorStep_eq]
   simp only [map_sub,map_mul,map_natCast]
   rw [CTH,
     BSM F Q (numerator K (F*Q) b),
     BSM F Q (polyH K (F*Q))]
   rw [←DGI F (numerator K F b),
     ←DGI F (polyH K F)]
   have hDH:=congrArg (BGO F) (CTH F Q)
   rw [hDH]
   simp only [Nat.cast_mul,Nat.cast_ofNat]
   apply FEJ (BGO F)
     (Ideal.Quotient.mk (factorIdeal_p19 F) Q)
     (Ideal.Quotient.mk (factorIdeal_p19 F) (polyH K F))
     (Ideal.Quotient.mk (factorIdeal_p19 F) (numerator K F b))
     (Ideal.Quotient.mk (factorIdeal_p19 F) (numerator K (F*Q) b))
     b
   exact ih
theorem BQR (F Q:Poly4 K) (b:ℕ):
   numerator K (F*Q) b-Q^(2*b)*numerator K F b∈
     Ideal.span ({F}:Set (Poly4 K)):=by
 rw [←Ideal.Quotient.mk_eq_mk_iff_sub_mem]
 simpa only [map_mul,map_pow] using CPU F Q b
theorem AKK (F Q:Poly4 K) (b:ℕ):
   F∣numerator K (F*Q) b-Q^(2*b)*numerator K F b:=by
 exact Ideal.mem_span_singleton.mp (BQR F Q b)
theorem AKR (F Q S:Poly4 K)
   (hS:S=F*Q) (b:ℕ):
   F∣numerator K S b-Q^(2*b)*numerator K F b:=by
 subst S
 exact AKK F Q b
end
end RCN217
end SubmissionLower
end ProximityPrize
end PackedLegacy_FE
section PackedLegacy_A5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN048
open scoped BigOperators
open RCN077 RCN313 RCN217
noncomputable section
variable {K:Type*} [Field K]
abbrev factorIdeal_p19 (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
theorem FPA (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal_p19 F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q*Ideal.Quotient.mk (factorIdeal_p19 F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul]
 have hz:Ideal.Quotient.mk (factorIdeal_p19 F) F=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
 rw [hz,zero_mul,add_zero]
 ring
theorem CPU (F Q:Poly4 K) (j:ℕ):
   Ideal.Quotient.mk (factorIdeal_p19 F) (numerator K (F*Q) j)=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q^(2*j)*
       Ideal.Quotient.mk (factorIdeal_p19 F) (numerator K F j):=by
 have h:=BQR F Q j
 rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,map_pow,sub_eq_zero] at h
 exact h
theorem EWU (F Q:Poly4 K) (w j:ℕ) (hj:j≤w)
   (c:ℕ→K) (x:K):
   Ideal.Quotient.mk (factorIdeal_p19 F) (RCN313.commonNumeratorTerm (F*Q) w c x j)=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal_p19 F) (RCN313.commonNumeratorTerm F w c x j):=by
 let ev:=Ideal.Quotient.mk (factorIdeal_p19 F)
 have he:2*j+2*(w-j)=2*w:=by omega
 unfold RCN313.commonNumeratorTerm
 simp only [map_mul,map_pow,MvPolynomial.map_C]
 rw [CPU,FPA,mul_pow]
 calc
   _=ev Q^(2*j+2*(w-j))*
       (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
         ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j):=by
     rw [pow_add]
     ring
   _=ev Q^(2*w)*
       (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
         ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j):=by rw [he]
   _=_:=by ring
theorem GAM (F Q:Poly4 K) (w:ℕ) (u0 u1:K):
   Ideal.Quotient.mk (factorIdeal_p19 F)
       (RCN313.affineSeedPolynomial u0 u1*polyH K (F*Q)^(2*w))=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal_p19 F)
         (RCN313.affineSeedPolynomial u0 u1*polyH K F^(2*w)):=by
 simp only [map_mul,map_pow]
 rw [FPA,mul_pow]
 ring
theorem DPP (F Q:Poly4 K) (w:ℕ)
   (c:ℕ→K) (x u0 u1:K):
   Ideal.Quotient.mk (factorIdeal_p19 F) (RCN313.agreementNumerator (F*Q) w c x u0 u1)=
     Ideal.Quotient.mk (factorIdeal_p19 F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal_p19 F) (RCN313.agreementNumerator F w c x u0 u1):=by
 let ev:=Ideal.Quotient.mk (factorIdeal_p19 F)
 have hsum:ev (RCN313.clearedTaylorNumerator (F*Q) w c x)=
     ev Q^(2*w)*ev (RCN313.clearedTaylorNumerator F w c x):=by
   unfold RCN313.clearedTaylorNumerator
   simp only [map_sum]
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro j hj
   exact EWU F Q w j (by have:=Finset.mem_range.mp hj;omega) c x
 unfold RCN313.agreementNumerator
 rw [map_sub,map_sub,hsum,GAM]
 ring
theorem DPC (F Q:Poly4 K) (w:ℕ)
   (c:ℕ→K) (x u0 u1:K):
   F∣RCN313.agreementNumerator (F*Q) w c x u0 u1-
     Q^(2*w)*RCN313.agreementNumerator F w c x u0 u1:=by
 rw [←Ideal.mem_span_singleton]
 rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,map_pow,
   DPP,sub_self]
end
end RCN048
end SubmissionLower
end ProximityPrize
end PackedLegacy_A5
section PackedLegacy_FH
namespace ProximityPrize
namespace SubmissionLower
namespace RCN220
open RCN136 RCN135 RCN138 RCN137 RCN082 RCN350 RCN313 RCN159 RCN217 RCN002 RCN048 RCN095 RCN275 RCN065
open RCN082 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω_p19 (K:Type) [Field K]:=GenericField K
theorem CLN
   {Γ:Finset K} {x:I→K} {p e:ℕ} [CharP (Ω_p19 K) p]
   {flag:FlagDegree} {w:ℕ} {support:RCN275.ResidualSupportParameters}
   (S:FH (RCN135.polynomialEmbedding K) Γ x p e flag w support)
   (hTail:S.G∣surfaceMap (RCN135.polynomialEmbedding K) (numerator K S.F (w+1))):
   ∃F0 Q:MvPolynomial (Fin 4) K,
     Irreducible F0∧0<F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
     S.F=F0*Q∧S.G∣surfaceMap (RCN135.polynomialEmbedding K) F0∧
     ¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) Q∧
     ¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) (polyH K F0)∧
     F0∣numerator K F0 (w+1):=by
 classical
 let P:=S.AUY
 letI:P.IsPrime:=S.DNW
 have hFne:S.F≠0:=by
   intro hzero
   apply S.BLO
   rw [hzero]
   simp [polyH]
 let φC:Polynomial K→+*RCN002.CoordinateField (Ω_p19 K) P:=
   (algebraMap (Ω_p19 K) (RCN002.CoordinateField (Ω_p19 K) P)).comp (RCN135.polynomialEmbedding K)
 let vC:Fin 3→RCN002.CoordinateField (Ω_p19 K) P:=
   fun i=>RCN065.componentPoint (RCN135.polynomialEmbedding K) P i.succ
 have hsurfaceZero:MvPolynomial.eval vC (surfaceMap φC S.F)=0:=by
   rw [RCN136.eval_surfaceMap]
   change MvPolynomial.eval₂Hom (RCN065.componentCoefficients (RCN135.polynomialEmbedding K) P)
     (RCN065.componentPoint (RCN135.polynomialEmbedding K) P) S.F=0
   rw [RCN065.component_evaluation]
   rw [RCN002.coordinateEvaluation_eq_aeval,RCN002.aeval_coordinate_eq_quotient,
     Ideal.Quotient.eq_zero_iff_mem.mpr S.CQP,map_zero]
 have hφC:Function.Injective φC:=
   (algebraMap (Ω_p19 K) (RCN002.CoordinateField (Ω_p19 K) P)).injective.comp
     (RCN135.polynomialEmbedding_injective K)
 obtain ⟨F0,hF0mem,hF0zero⟩:=RCN082.exists_active_factor_of_surface_zero
   φC hφC S.F hFne vC hsurfaceZero
 have hF0spec:=RCN082.activeFactors_spec S.F F0 hF0mem
 have hmapF0mem:surfaceMap (RCN135.polynomialEmbedding K) F0∈P:=by
   rw [←RCN002.coordinateEvaluation_ker (Ω_p19 K) P]
   rw [RCN136.eval_surfaceMap] at hF0zero
   change MvPolynomial.eval₂Hom (RCN065.componentCoefficients (RCN135.polynomialEmbedding K) P)
     (RCN065.componentPoint (RCN135.polynomialEmbedding K) P) F0=0 at hF0zero
   rw [RCN065.component_evaluation] at hF0zero
   exact hF0zero
 have hGdivF0:S.G∣surfaceMap (RCN135.polynomialEmbedding K) F0:=
   Ideal.mem_span_singleton.mp hmapF0mem
 obtain ⟨Q,hprod⟩:=hF0spec.2.1
 have hQnot:¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) Q:=by
   intro hGQ
   apply S.BLO
   rw [hprod,MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
   exact dvd_add (dvd_mul_of_dvd_right hGQ _) (dvd_mul_of_dvd_left hGdivF0 _)
 have hH0not:¬S.G∣surfaceMap (RCN135.polynomialEmbedding K) (polyH K F0):=by
   intro hGH
   apply S.BLO
   rw [hprod,MvPolynomial.pderiv_mul]
   simp only [polyH,map_add,map_mul]
   exact dvd_add (dvd_mul_of_dvd_left hGH _) (dvd_mul_of_dvd_left hGdivF0 _)
 have hscale:=AKK F0 Q (w+1)
 have hdiff:S.G∣surfaceMap (RCN135.polynomialEmbedding K)
     (numerator K (F0*Q) (w+1)-Q^(2*(w+1))*numerator K F0 (w+1)):=
   hGdivF0.trans (map_dvd (surfaceMap (RCN135.polynomialEmbedding K)) hscale)
 have htail':S.G∣surfaceMap (RCN135.polynomialEmbedding K) (numerator K (F0*Q) (w+1)):=by
   simpa only [hprod] using hTail
 have hmul:S.G∣surfaceMap (RCN135.polynomialEmbedding K)
     (Q^(2*(w+1))*numerator K F0 (w+1)):=by
   simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using dvd_sub htail' hdiff
 have hfactor:S.G∣surfaceMap (RCN135.polynomialEmbedding K) Q^(2*(w+1))∨
     S.G∣surfaceMap (RCN135.polynomialEmbedding K) (numerator K F0 (w+1)):=by
   have hmul':S.G∣surfaceMap (RCN135.polynomialEmbedding K) Q^(2*(w+1))*
       surfaceMap (RCN135.polynomialEmbedding K) (numerator K F0 (w+1)):=by
     rw [map_mul,map_pow] at hmul
     exact hmul
   exact S.MW.prime.dvd_or_dvd hmul'
 have hnum:S.G∣surfaceMap (RCN135.polynomialEmbedding K) (numerator K F0 (w+1)):=by
   rcases hfactor with hpow | hnum
   · exact False.elim (hQnot (Prime.dvd_of_dvd_pow S.MW.prime
       (by simpa only [map_pow] using hpow)))
   · exact hnum
 have hbase:F0∣numerator K F0 (w+1):=
   (RCN138.geometric_factor_dvd_iff K (Ω_p19 K) F0 (numerator K F0 (w+1))
     hF0spec.1 hF0spec.2.2 S.G S.MW
     (by simpa only [RCN138.canonical_geometricSurfaceMap] using hGdivF0)).mp
     (by simpa only [RCN138.canonical_geometricSurfaceMap] using hnum)
 exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGdivF0,hQnot,hH0not,hbase⟩
theorem DIL
   (φ:Polynomial K→+*Ω_p19 K) (F0 Q:MvPolynomial (Fin 4) K)
   (G:MvPolynomial (Fin 3) (Ω_p19 K))
   (hGdivF0:G∣surfaceMap φ F0)
   (w:ℕ) (c:ℕ→K) (x0 u0 u1:K)
   (hproper:¬G∣surfaceMap φ (RCN313.agreementNumerator (F0*Q) w c x0 u0 u1)):
   ¬F0∣RCN313.agreementNumerator F0 w c x0 u0 u1:=by
 intro hF0cut
 have hcut:G∣surfaceMap φ (RCN313.agreementNumerator F0 w c x0 u0 u1):=
   hGdivF0.trans (map_dvd (surfaceMap φ) hF0cut)
 have hscaled:G∣surfaceMap φ
     (Q^(2*w)*RCN313.agreementNumerator F0 w c x0 u0 u1):=by
   have h:=dvd_mul_of_dvd_right hcut (surfaceMap φ Q^(2*w))
   simpa only [map_mul,map_pow,mul_comm] using h
 have hdiff:G∣surfaceMap φ
     (RCN313.agreementNumerator (F0*Q) w c x0 u0 u1-
       Q^(2*w)*RCN313.agreementNumerator F0 w c x0 u0 u1):=
   hGdivF0.trans (map_dvd (surfaceMap φ)
     (DPC F0 Q w c x0 u0 u1))
 apply hproper
 simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using dvd_add hdiff hscaled
end
end RCN220
end SubmissionLower
end ProximityPrize
end PackedLegacy_FH
section PackedLegacy_FL
namespace ProximityPrize
namespace SubmissionLower
namespace RCN228
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN229 RCN319 RCN347 RCN311 RCN174
open RCN319 renaming specialization → BM
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 30000
variable {K L M:Type} [Field K] [Field L] [Field M]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
local instance:DecidableEq M:=Classical.decEq M
theorem CNR
   (coefficients:K→+*L) (F:Poly4 K) (v:Fin 4→L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p]
   (hw:1≤w) (hshort:w+1≤bound) (hchar:bound<p)
   (hcaps:F∈RCN174.globalCoefficientBox K bound w seedCap slopeCap)
   (hdiv:F∣numerator K F (w+1)):
   RCN319.specialization L (RCN139.globalPolynomial coefficients F v hF hreg w) (v 3)
     (MvPolynomial.map coefficients F)=0:=by
 apply RCN139.global_polynomiality_of_all_tails coefficients F v hF hreg
   p bound w seedCap slopeCap hw hshort hchar hcaps
 intro j hj _
 exact RCN311.all_tail_jets_zero_of_first_tail_dvd coefficients F v hF hreg w hdiv j hj
end
end RCN228
end SubmissionLower
end ProximityPrize
end PackedLegacy_FL
section PackedLegacy_E4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN258
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN229 RCN319 RCN347
open RCN319 renaming specialization → BM
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L M:Type*} [Field k] [Field L] [Field M]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq L:=Classical.decEq L
local instance:DecidableEq M:=Classical.decEq M
theorem mv_eval_mem_p19 (E:Subfield M) (c:k→+*M)
   (hc:∀a,c a∈E) (v:Fin 4→M) (hv:∀i,v i∈E) (Q:Poly4 k):
   MvPolynomial.eval₂Hom c v Q∈E:=by
 induction Q using MvPolynomial.induction_on with
 | C a=>simpa using hc a
 | add P Q hP hQ=>simpa only [map_add] using E.add_mem hP hQ
 | mul_X P i hP=>
     simpa only [map_mul,MvPolynomial.eval₂Hom_X'] using E.mul_mem hP (hv i)
theorem DFO (E:Subfield M) (c:L→+*M)
   (P:Polynomial L) (hP:∀j,c (P.coeff j)∈E) (x:M) (hx:x∈E):
   P.eval₂ c x∈E:=by
 rw [Polynomial.eval₂_eq_sum_range]
 exact E.sum_mem fun j _=>E.mul_mem (hP j) (E.pow_mem hx j)
theorem GAI (E:Subfield M) (P:Polynomial M)
   (hP:∀j,P.coeff j∈E) (x:M) (hx:x∈E) (j:ℕ):
   (Polynomial.taylor x P).coeff j∈E:=by
 rw [Polynomial.taylor_coeff]
 apply DFO E (RingHom.id M) (Polynomial.hasseDeriv j P) _ x hx
 intro n
 simp only [RingHom.id_apply,Polynomial.hasseDeriv_coeff]
 exact E.mul_mem (natCast_mem E _) (hP _)
theorem BUO
   (E:Subfield M) (c:k→+*M) (F:Poly4 k) (v:Fin 4→M)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hreg:MvPolynomial.eval₂Hom c v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (hv0:v 0∈E)
   (hnum:∀j,MvPolynomial.eval₂Hom c v (numerator k F j)∈E)
   (hH:MvPolynomial.eval₂Hom c v (polyH k F)∈E) (j:ℕ):
   (RCN139.globalPolynomial c F v hF hreg w).coeff j∈E:=by
 unfold RCN139.globalPolynomial
 apply GAI E _ _ _ (E.neg_mem hv0) j
 intro n
 simp only [RCN233.reconstructedPolynomial,RCN347.jetPolynomial_coeff]
 split_ifs with hn
 · rw [RCN047.jetCoefficient_eq_evaluated_numerator]
   exact E.div_mem (E.mul_mem (hnum n) (E.pow_mem (E.inv_mem hH) _))
     (natCast_mem E _)
 · exact E.zero_mem
theorem FQZ (c:k→+*L) (F Q:Poly4 k) (n:ℕ):
   MvPolynomial.map c (RCN313.numeratorStep k F n Q)=
     RCN313.numeratorStep L (MvPolynomial.map c F) n (MvPolynomial.map c Q):=by
 simp only [RCN313.numeratorStep,clearedStep,polyH,polyG,MvPolynomial.pderiv_map,
   map_sub,map_add,map_mul,map_pow,map_natCast,map_neg,MvPolynomial.map_X]
theorem FCD (c:k→+*L) (F:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numerator k F n)=numerator L (MvPolynomial.map c F) n:=by
 induction n with
 | zero=>simp
 | succ n ih=>rw [RCN313.numerator_succ,FQZ,ih,RCN313.numerator_succ]
theorem DGU
   (E:Subfield M) (c:k→+*L) (φ:L→+*M)
   (hc:∀a,φ (c a)∈E) (F:Poly4 k) (v:Fin 4→M)
   (hv:∀i,v i∈E)
   (hF:MvPolynomial.eval₂Hom φ v (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ v
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (w j:ℕ):
   (RCN139.globalPolynomial φ (MvPolynomial.map c F) v hF hreg w).coeff j∈E:=by
 apply BUO E φ (MvPolynomial.map c F)
   v hF hreg w (hv 0) _ _ j
 · intro n
   rw [←FCD c F n,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem_p19 E (φ.comp c) hc v hv (numerator k F n)
 · unfold polyH
   rw [MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem_p19 E (φ.comp c) hc v hv (MvPolynomial.pderiv (2:Fin 4) F)
theorem CTE
   (E:Subfield M) (c:k→+*L) (φ:L→+*M)
   (hc:∀a,φ (c a)∈E) (F:Poly4 k) (P:Polynomial L) (γ:L) (ξ:M)
   (hsolution:RCN319.specialization L P γ (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ (RCN231.polynomialPoint φ P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (hv:∀i,RCN231.polynomialPoint φ P γ ξ i∈E)
   (p w:ℕ) [CharP M p] (hw:w<p) (hP:P.natDegree≤w) (j:ℕ):
   φ (P.coeff j)∈E:=by
 have hmem:=DGU E c φ hc F
   (RCN231.polynomialPoint φ P γ ξ) hv
   (RCN231.polynomialPoint_relation φ (MvPolynomial.map c F) P γ ξ hsolution)
   hreg w j
 rw [RCN229.globalPolynomial_eq_map_of_solution φ (MvPolynomial.map c F) P γ ξ
   hsolution hreg p w hw hP,Polynomial.coeff_map] at hmem
 exact hmem
end
end RCN258
end SubmissionLower
end ProximityPrize
end PackedLegacy_E4
section PackedLegacy_J2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN083
open RCN077 RCN313 RCN269 RCN233 RCN139 RCN347 RCN047 RCN217 RCN048 RCN136 RCN258
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 15000
variable {K L Ω:Type} [Field K] [Field L] [Field Ω]
theorem ECX
   (c:K→+*L) (F:Poly4 K) (w:ℕ) (a:ℕ→K) (x u0 u1:K):
   MvPolynomial.map c (RCN313.agreementNumerator F w a x u0 u1)=
     RCN313.agreementNumerator (MvPolynomial.map c F) w (fun j=>c (a j))
       (c x) (c u0) (c u1):=by
 simp only [RCN313.agreementNumerator,RCN313.clearedTaylorNumerator,RCN313.commonNumeratorTerm,
   RCN313.affineSeedPolynomial,map_sub,map_sum,map_add,map_mul,map_pow,MvPolynomial.map_C,
   MvPolynomial.map_X,FCD,polyH,MvPolynomial.pderiv_map]
theorem EAT
   (c:K→+*L) (F Q:Poly4 K) (v:Fin 4→L)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hQ:MvPolynomial.eval₂Hom c v Q≠0)
   (hregF:MvPolynomial.eval₂Hom c v (polyH K F)≠0)
   (hprod:MvPolynomial.eval₂Hom c v (F*Q)=0)
   (hregprod:MvPolynomial.eval₂Hom c v (polyH K (F*Q))≠0)
   (w:ℕ):
   RCN139.globalPolynomial c (F*Q) v hprod hregprod w=
     RCN139.globalPolynomial c F v hF hregF w:=by
 let ev:=MvPolynomial.eval₂Hom c v
 change ev F=0 at hF
 change ev Q≠0 at hQ
 change ev (polyH K F)≠0 at hregF
 have hHscale:ev (polyH K (F*Q))=ev (polyH K F)*ev Q:=by
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul,hF,zero_mul,add_zero]
 have hNscale (j:ℕ):ev (numerator K (F*Q) j)=
     ev Q^(2*j)*ev (numerator K F j):=by
   obtain ⟨A,hA⟩:=AKK F Q j
   have h:=congrArg ev hA
   simp only [map_sub,map_mul,map_pow,hF,zero_mul] at h
   exact sub_eq_zero.mp h
 have hrecon:RCN233.reconstructedPolynomial c (F*Q) v hprod hregprod w=
     RCN233.reconstructedPolynomial c F v hF hregF w:=by
   ext j
   simp only [RCN233.reconstructedPolynomial,RCN347.jetPolynomial_coeff]
   by_cases hj:j<w+1
   · rw [if_pos hj,if_pos hj]
     rw [RCN047.jetCoefficient_eq_evaluated_numerator c (F*Q) v hprod hregprod,
       RCN047.jetCoefficient_eq_evaluated_numerator c F v hF hregF]
     change ev (numerator K (F*Q) j)*(ev (polyH K (F*Q)))⁻¹^(2*j)/
         (j.factorial:L)=
       ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j)/
         (j.factorial:L)
     rw [hNscale,hHscale,mul_inv,mul_pow]
     have hcancel:ev Q^(2*j)*(ev Q)⁻¹^(2*j)=1:=by
       rw [←mul_pow,mul_inv_cancel₀ hQ,one_pow]
     calc
       _=(ev Q^(2*j)*(ev Q)⁻¹^(2*j))*
           (ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j))/
             (j.factorial:L):=by ring
       _=_:=by rw [hcancel,one_mul]
   · rw [if_neg hj,if_neg hj]
 unfold RCN139.globalPolynomial
 rw [hrecon]
end
end RCN083
end SubmissionLower
end ProximityPrize
end PackedLegacy_J2
section PackedLegacy_EF
namespace ProximityPrize
namespace SubmissionLower
namespace RCN126
open RCN077 RCN231 RCN229 RCN139 RCN319 RCN258
open RCN319 renaming specialization → BM
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L:Type*} [Field k] [Field L] [Algebra k L]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq L:=Classical.decEq L
def freshPoint_p19 (P:Polynomial L) (γ:L):Fin 4→RatFunc L:=
 RCN231.polynomialPoint (algebraMap L (RatFunc L)) P γ RatFunc.X
def jetField_p19 (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k (Set.range (freshPoint_p19 P γ))
def APV (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k
   (insert RatFunc.X (insert (algebraMap L (RatFunc L) γ)
     (Set.range (fun j:ℕ=>algebraMap L (RatFunc L) (P.coeff j)))))
@[simp] theorem freshPoint_X (P:Polynomial L) (γ:L):
   freshPoint_p19 P γ 0=RatFunc.X:=rfl
@[simp] theorem freshPoint_Z (P:Polynomial L) (γ:L):
   freshPoint_p19 P γ 3=algebraMap L (RatFunc L) γ:=rfl
theorem EIM (P:Polynomial L) (γ:L) (Q:Poly4 L):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint_p19 P γ) Q=
     algebraMap (Polynomial L) (RatFunc L) (RCN319.specialization L P γ Q):=by
 rw [freshPoint_p19,RCN231.eval_polynomialPoint_eq_specialization]
 exact RatFunc.aeval_X_left_eq_algebraMap _
theorem FMU (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hreg:RCN319.specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint_p19 P γ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0:=by
 rw [EIM]
 exact RatFunc.algebraMap_ne_zero hreg
theorem DEV
   (E:IntermediateField k (RatFunc L))
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:RCN319.specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:RCN319.specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (hv:∀i,freshPoint_p19 P γ i∈E)
   (p w:ℕ) [CharP L p] (hw:w<p) (hP:P.natDegree≤w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈E:=by
 apply CTE E.toSubfield (algebraMap k L)
   (algebraMap L (RatFunc L)) _ F P γ RatFunc.X hsolution
   (FMU F P γ hreg) hv p w hw hP j
 intro a
 change algebraMap k (RatFunc L) a∈E
 exact E.algebraMap_mem a
theorem EPC
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:RCN319.specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:RCN319.specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w<p) (hP:P.natDegree≤w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈jetField_p19 (k:=k) P γ:=by
 apply DEV (jetField_p19 (k:=k) P γ)
   F P γ hsolution hreg _ p w hw hP j
 intro i
 exact IntermediateField.subset_adjoin k _ ⟨i,rfl⟩
theorem DYM (P:Polynomial L) (γ:L):
   jetField_p19 (k:=k) P γ≤APV (k:=k) P γ:=by
 let E:=APV (k:=k) P γ
 have hX:(RatFunc.X:RatFunc L)∈E:=
   IntermediateField.subset_adjoin k _ (Or.inl rfl)
 have hγ:algebraMap L (RatFunc L) γ∈E:=
   IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 have hc:∀j,algebraMap L (RatFunc L) (P.coeff j)∈E:=
   fun j=>IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
 apply IntermediateField.adjoin_le_iff.mpr
 rintro x ⟨i,rfl⟩
 fin_cases i
 · exact hX
 · exact DFO E.toSubfield (algebraMap L (RatFunc L)) P hc
     RatFunc.X hX
 · apply DFO E.toSubfield (algebraMap L (RatFunc L))
     P.derivative _ RatFunc.X hX
   intro j
   rw [Polynomial.coeff_derivative,map_mul]
   exact E.mul_mem (hc _) (by simpa using E.natCast_mem (j+1))
 · exact hγ
theorem DYE
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:RCN319.specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:RCN319.specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w<p) (hP:P.natDegree≤w):
   APV (k:=k) P γ≤jetField_p19 (k:=k) P γ:=by
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨0,rfl⟩
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨3,rfl⟩
 obtain ⟨j,rfl⟩:=hx
 exact EPC F P γ hsolution hreg p w hw hP j
theorem CXC
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:RCN319.specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:RCN319.specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w<p) (hP:P.natDegree≤w):
   jetField_p19 (k:=k) P γ=APV (k:=k) P γ:=
 le_antisymm (DYM P γ)
   (DYE F P γ hsolution hreg p w hw hP)
end
end RCN126
end SubmissionLower
end ProximityPrize
end PackedLegacy_EF
section PackedLegacy_A7
namespace ProximityPrize
namespace SubmissionLower
namespace RCN062
open RCN126
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
theorem EDH (P:Polynomial L) (γ:L):
   (RCN062.baseCoefficientField (k:=k) P γ).map (IsScalarTower.toAlgHom k L (RatFunc L))≤
     APV (k:=k) P γ:=by
 rw [IntermediateField.map_le_iff_le_comap]
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with h | hx
 · rw [h]
   change algebraMap L (RatFunc L) γ∈APV (k:=k) P γ
   exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 obtain ⟨j,hj⟩:=hx
 rw [←hj]
 change algebraMap L (RatFunc L) (P.coeff j)∈APV (k:=k) P γ
 exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
theorem DEY
   (P:Polynomial L) (γ:L)
   (hE:Algebra.trdeg k (APV (k:=k) P γ)≤2):
   Algebra.trdeg k (RCN062.baseCoefficientField (k:=k) P γ)≤1:=by
 apply RCN321.coefficient_trdeg_le_one_of_rational_extension
   (B:=RCN062.baseCoefficientField (k:=k) P γ)
   (E:=APV (k:=k) P γ)
   (EDH P γ) _ hE
 exact IntermediateField.subset_adjoin k _ (Or.inl rfl)
end
end RCN062
end SubmissionLower
end ProximityPrize
end PackedLegacy_A7
section PackedLegacy_GT
namespace ProximityPrize
namespace SubmissionLower
namespace RCN322
open RCN371 RCN011 RCN009 RCN013 RCN022 RCN021 RCN024 RCN129
open RCN371 renaming RationalPolynomials → KU
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L]
set_option maxHeartbeats 1000000
theorem CVW
   (v:Fin 3→L)
   (hgen:IntermediateField.adjoin K (Set.range v)=⊤)
   (F T:MvPolynomial (Fin 3) K)
   (hF:Irreducible F) (hproper:¬F∣T)
   (hFzero:MvPolynomial.aeval v F=0)
   (hTzero:MvPolynomial.aeval v T=0):Algebra.trdeg K L≤1:=by
 classical
 by_cases halg:∀i,IsAlgebraic K (v i)
 · have hA:=IntermediateField.isAlgebraic_adjoin
     (K:=K) (L:=L) (S:=Set.range v) (by
       rintro x ⟨i,rfl⟩
       exact isAlgebraic_iff_isIntegral.mp (halg i))
   rw [hgen] at hA
   letI:=hA
   letI:Algebra.IsAlgebraic K L:=(IntermediateField.topEquiv).isAlgebraic
   exact (trdeg_eq_zero (R:=K) (A:=L)).trans_le zero_le
 push Not at halg
 obtain ⟨i,hi⟩:=halg
 let e:Original K→ₐ[K] L:=MvPolynomial.aeval v
 let initial:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hi0:initial 0=i:=Equiv.swap_apply_left _ _
 have ht0:Transcendental K (e (MvPolynomial.X (initial 0))):=by
   simpa [e,hi0] using (show Transcendental K (v i) from hi)
 have hex:∃order:Fin 3 ≃ Fin 3,
     Transcendental K (e (MvPolynomial.X (order 0)))∧
     0<(planeMap K order F).natDegree:=by
   have hirr:=RCN021.rationalMap_irreducible_of_evaluation K L initial e F hF hFzero ht0
   rcases RCN013.positive_degree_of_irreducible (rationalMap K initial F) hirr with h0 | h1
   · refine ⟨initial,ht0,?_⟩
     change 0<(RCN011.bivariateEquiv (RatFunc K) (rationalMap K initial F)).natDegree
     rwa [RCN009.bivariateEquiv_natDegree]
   · exact ⟨RCN013.swapOtherOrder initial,by simpa only [RCN013.swapOtherOrder_zero] using ht0,
       by rwa [RCN013.swapped_outer_degree]⟩
 obtain ⟨order,ht,hpositive⟩:=hex
 let base:=RCN022.elementEmbedding K L (e (MvPolynomial.X (order 0))) ht
 letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 have hpair:IntermediateField.adjoin (RatFunc K)
     ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤:=by
   let S:=IntermediateField.adjoin (RatFunc K)
     ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)
   have hcoords:Set.range v ⊆ S.restrictScalars K:=by
     rintro x ⟨l,rfl⟩
     obtain ⟨j,rfl⟩:=order.surjective l
     have hj:j=0∨j=1∨j=2:=by omega
     rcases hj with rfl | rfl | rfl
     · have hm:=S.algebraMap_mem
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
       change RCN022.elementEmbedding K L _ ht _∈S at hm
       rw [RCN022.elementEmbedding_variable] at hm
       simpa [e] using hm
     · simpa [S,e] using IntermediateField.mem_adjoin_pair_right (RatFunc K)
         (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
     · simpa [S,e] using IntermediateField.mem_adjoin_pair_left (RatFunc K)
         (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
   have htop:S.restrictScalars K=⊤:=by
     apply top_unique
     rw [←hgen]
     exact IntermediateField.adjoin_le_iff.mpr hcoords
   exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
 have hroot (G:Original K) (hG:e G=0):
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (RatFunc K) L)
       (e (MvPolynomial.X (order 2))))
       (e (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
   rw [←RCN365.planeEval_eq_eval₂]
   change RCN021.planeEvaluation K L order e ht (planeMap K order G)=0
   rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
   exact hG
 have hirr:=RCN021.planeMap_irreducible_of_evaluation K L order e F hF hFzero ht
 have hproperPlane:¬planeMap K order F∣planeMap K order T:=by
   intro h
   exact hproper ((RCN021.planeMap_dvd_iff_of_evaluation K L order e F T hF hFzero ht).mp h)
 letI:FiniteDimensional (RatFunc K) L:=BAC
   (planeMap K order F) (planeMap K order T) hirr hpositive hproperPlane
   (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
   (hroot F hFzero) (hroot T hTzero) hpair
 exact RCN129.trdeg_le_one_of_functionField K L
end
end RCN322
end SubmissionLower
end ProximityPrize
end PackedLegacy_GT
section PackedLegacy_EG
namespace ProximityPrize
namespace SubmissionLower
namespace RCN127
open RCN077 RCN319 RCN136 RCN132 RCN126 RCN062 RCN322 RCN129 RCN022
open RCN319 renaming specialization → BM
open RCN132 renaming RationalPolynomials → KU
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
def freshJet_p19 (P:Polynomial L) (γ:L) (i:Fin 4):
   jetField_p19 (k:=k) P γ:=
 ⟨freshPoint_p19 P γ i,IntermediateField.subset_adjoin k _ ⟨i,rfl⟩⟩
@[simp] theorem freshJet_val (P:Polynomial L) (γ:L) (i:Fin 4):
   ((freshJet_p19 (k:=k) P γ i:jetField_p19 (k:=k) P γ):RatFunc L)=
     freshPoint_p19 P γ i:=rfl
def GXF (P:Polynomial L) (γ:L) (i:Fin 3):
   jetField_p19 (k:=k) P γ:=freshJet_p19 (k:=k) P γ i.succ
theorem ETJ (P:Polynomial L) (γ:L):
   Transcendental k (freshJet_p19 (k:=k) P γ 0):=by
 intro h
 have h':IsAlgebraic k (RatFunc.X:RatFunc L):=by
   exact IntermediateField.isAlgebraic_iff.mp h
 exact (RatFunc.transcendental_X.restrictScalars
   (algebraMap k L).injective) h'
set_option maxHeartbeats 1000000 in
theorem ABA
   (F T:Poly4 k) (P:Polynomial L) (γ:L)
   (hF:Irreducible F)
   (hpos:0<F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (hproper:¬F∣T)
   (hFsolution:RCN319.specialization L P γ
     (MvPolynomial.map (algebraMap k L) F)=0)
   (hTsolution:RCN319.specialization L P γ
     (MvPolynomial.map (algebraMap k L) T)=0)
   (hreg:RCN319.specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4)
       (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w<p) (hP:P.natDegree≤w):
   Algebra.trdeg k (RCN062.baseCoefficientField (k:=k) P γ)≤1:=by
 classical
 let E:=jetField_p19 (k:=k) P γ
 let full:Fin 4→E:=freshJet_p19 (k:=k) P γ
 let v:Fin 3→E:=GXF (k:=k) P γ
 let τ:E:=freshJet_p19 (k:=k) P γ 0
 have hτ:Transcendental k τ:=ETJ P γ
 let rawEquiv:=FractionRing.algEquiv (Polynomial k) (RatFunc k)
 let coeffEquiv:RCN132.RationalCoefficients k ≃ₐ[k] RatFunc k:=rawEquiv.restrictScalars k
 let baseRat:RatFunc k→ₐ[k] E:=RCN022.elementEmbedding k E τ hτ
 let base:RCN132.RationalCoefficients k→ₐ[k] E:=baseRat.comp coeffEquiv.toAlgHom
 letI:Algebra (RCN132.RationalCoefficients k) E:=base.toRingHom.toAlgebra
 letI:IsScalarTower k (RCN132.RationalCoefficients k) E:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 have hbaseX:base
     (algebraMap (Polynomial k) (RCN132.RationalCoefficients k) Polynomial.X)=τ:=by
   change baseRat (rawEquiv
     (algebraMap (Polynomial k) (RCN132.RationalCoefficients k) Polynomial.X))=τ
   rw [rawEquiv.commutes,RCN022.elementEmbedding_variable]
 have hfull:IntermediateField.adjoin k (Set.range full)=⊤:=by
   apply IntermediateField.map_injective E.val
   rw [IntermediateField.adjoin_map,←AlgHom.fieldRange_eq_map,
     IntermediateField.fieldRange_val]
   have himage:E.val '' Set.range full=Set.range (freshPoint_p19 P γ):=by
     ext x
     simp [full,freshJet_p19]
   rw [himage]
   rfl
 have hgen:IntermediateField.adjoin (RCN132.RationalCoefficients k) (Set.range v)=⊤:=by
   let S:=IntermediateField.adjoin (RCN132.RationalCoefficients k) (Set.range v)
   have hcoords:Set.range full ⊆ S.restrictScalars k:=by
     rintro x ⟨i,rfl⟩
     refine Fin.cases ?_ (fun j↦?_) i
     · have hm:=S.algebraMap_mem
         (algebraMap (Polynomial k) (RCN132.RationalCoefficients k) Polynomial.X)
       change base
         (algebraMap (Polynomial k) (RCN132.RationalCoefficients k) Polynomial.X)∈S at hm
       rw [hbaseX] at hm
       exact hm
     · exact IntermediateField.subset_adjoin (RCN132.RationalCoefficients k) _ ⟨j,rfl⟩
   have htop:S.restrictScalars k=⊤:=by
     apply top_unique
     rw [←hfull]
     exact IntermediateField.adjoin_le_iff.mpr hcoords
   exact (IntermediateField.restrictScalars_eq_top_iff (K:=k)).mp htop
 have hsurface:∀G:Poly4 k,
     MvPolynomial.eval₂Hom (algebraMap (RCN132.RationalCoefficients k) E) v
         (RCN132.rationalSurfaceMap k G)=
       MvPolynomial.eval₂Hom (algebraMap k E) full G:=by
   intro G
   have heq:(MvPolynomial.eval₂Hom
         (algebraMap (RCN132.RationalCoefficients k) E) v).comp (RCN132.rationalSurfaceMap k)=
       MvPolynomial.eval₂Hom (algebraMap k E) full:=by
     apply MvPolynomial.ringHom_ext
     · intro a
       simp only [RingHom.comp_apply,RCN132.rationalSurfaceMap,surfaceMap_C,
         MvPolynomial.eval₂Hom_C]
       change base
         (algebraMap (Polynomial k) (RCN132.RationalCoefficients k) (Polynomial.C a))=
           algebraMap k E a
       calc
         _=base (algebraMap k (RCN132.RationalCoefficients k) a):=by
           congr 1
         _=algebraMap k E a:=base.commutes a
     · intro i
       refine Fin.cases ?_ (fun j↦?_) i
       · simp only [RingHom.comp_apply,RCN132.rationalSurfaceMap,RCN136.surfaceMap_X_zero,
           MvPolynomial.eval₂Hom_C,
           MvPolynomial.eval₂Hom_X']
         change base
           (algebraMap (Polynomial k) (RCN132.RationalCoefficients k) Polynomial.X)=full 0
         exact hbaseX
       · simp only [RingHom.comp_apply,RCN132.rationalSurfaceMap,RCN136.surfaceMap_X_succ,
           MvPolynomial.eval₂Hom_X']
         rfl
   exact RingHom.congr_fun heq G
 have hcoeffcomp:E.val.toRingHom.comp
       (MvPolynomial.eval₂Hom (algebraMap k E) full)=
     (MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint_p19 P γ)).comp
       (MvPolynomial.map (algebraMap k L)):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       MvPolynomial.eval₂Hom_C,
       MvPolynomial.map_C]
     change algebraMap k (RatFunc L) a=
       algebraMap L (RatFunc L) (algebraMap k L a)
     exact IsScalarTower.algebraMap_apply k L (RatFunc L) a
   · intro i
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       MvPolynomial.eval₂Hom_X',
       MvPolynomial.map_X]
     change E.val (full i)=freshPoint_p19 P γ i
     rfl
 have hfullroot (G:Poly4 k)
     (hG:RCN319.specialization L P γ (MvPolynomial.map (algebraMap k L) G)=0):
     MvPolynomial.eval₂Hom (algebraMap k E) full G=0:=by
   apply E.val.injective
   change (E.val.toRingHom.comp
     (MvPolynomial.eval₂Hom (algebraMap k E) full)) G=E.val 0
   rw [hcoeffcomp,RingHom.comp_apply,EIM,hG,map_zero,map_zero]
 have hFroot:MvPolynomial.aeval v (RCN132.rationalSurfaceMap k F)=0:=by
   change MvPolynomial.eval₂Hom (algebraMap (RCN132.RationalCoefficients k) E) v
     (RCN132.rationalSurfaceMap k F)=0
   rw [hsurface]
   exact hfullroot F hFsolution
 have hTroot:MvPolynomial.aeval v (RCN132.rationalSurfaceMap k T)=0:=by
   change MvPolynomial.eval₂Hom (algebraMap (RCN132.RationalCoefficients k) E) v
     (RCN132.rationalSurfaceMap k T)=0
   rw [hsurface]
   exact hfullroot T hTsolution
 have hirr:Irreducible (RCN132.rationalSurfaceMap k F):=
   RCN132.rationalSurfaceMap_irreducible k F hF hpos
 have hproperRat:¬RCN132.rationalSurfaceMap k F∣RCN132.rationalSurfaceMap k T:=by
   intro h
   exact hproper ((RCN132.rationalSurfaceMap_dvd_iff k F T hF hpos).mp h)
 have hrelative:Algebra.trdeg (RCN132.RationalCoefficients k) E≤1:=
   CVW (RCN132.RationalCoefficients k) E v hgen
     (RCN132.rationalSurfaceMap k F) (RCN132.rationalSurfaceMap k T)
     hirr hproperRat hFroot hTroot
 have hbaseRat:Algebra.trdeg k (RatFunc k)≤1:=
   RCN129.trdeg_le_one_of_functionField k (RatFunc k)
 have hbase:Algebra.trdeg k (RCN132.RationalCoefficients k)≤1:=by
   rw [coeffEquiv.trdeg_eq]
   exact hbaseRat
 have hsum:Algebra.trdeg k (RCN132.RationalCoefficients k)+
     Algebra.trdeg (RCN132.RationalCoefficients k) E=Algebra.trdeg k E:=
   trdeg_add_eq k (RCN132.RationalCoefficients k)
 have hjet:Algebra.trdeg k E≤2:=by
   rw [←hsum]
   exact (add_le_add hbase hrelative).trans_eq (by norm_num)
 have hfield:=CXC F P γ hFsolution hreg p w hw hP
 change Algebra.trdeg k (jetField_p19 (k:=k) P γ)≤2 at hjet
 rw [hfield] at hjet
 exact DEY P γ hjet
end
end RCN127
end SubmissionLower
end ProximityPrize
end PackedLegacy_EG
section PackedLegacy_H9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN059
open scoped BigOperators
noncomputable section
variable {k F L Γ:Type*} [Field k] [Field F] [Field L]
 [LinearOrderedCommGroupWithZero Γ]
local instance:DecidableEq F:=Classical.decEq F
theorem FIG {w:ℕ}
   (v:Valuation L Γ) (x:L) (hx:v x=1)
   (b c:Fin (w+1)→L)
   (hclose:∀i,v (b i-c i)<1)
   (hc:v (∑ i,c i*x^(i:ℕ))=1):
   v (∑ i,b i*x^(i:ℕ))=1:=by
 have herr:v (∑ i,(b i-c i)*x^(i:ℕ))<1:=by
   apply v.map_sum_lt (by simp)
   intro i _
   simpa only [map_mul,map_pow,hx,one_pow,mul_one] using hclose i
 have hsplit:(∑ i,b i*x^(i:ℕ))=
     (∑ i,c i*x^(i:ℕ))+
     (∑ i,(b i-c i)*x^(i:ℕ)):=by
   rw [←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl
   intro i _
   ring
 rw [hsplit,v.map_add_eq_of_lt_left (by simpa only [hc] using herr),hc]
theorem BRT {w:ℕ}
   (v:Valuation L Γ) (φ:F→+*L) (κ:k→+*F)
   (x:L) (hx:v x=1)
   (hres:RCN059.ResidueApprox v φ κ)
   (hunit:RCN059.ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1)→F) (j:Fin (w+1)) (haj:a j≠0)
   (hmax:∀i,v (φ (a i))≤v (φ (a j))):
   v (∑ i,φ (a i)*x^(i:ℕ))=v (φ (a j)):=by
 have hφj:φ (a j)≠0:=by
   intro h
   apply haj
   apply φ.injective
   simpa using h
 have hvj:v (φ (a j))≠0:=(Valuation.ne_zero_iff v).mpr hφj
 have hnorm:∀i,v (φ (a i/a j))≤1:=by
   intro i
   rw [map_div₀,map_div₀]
   exact (div_le_one₀ (zero_lt_iff.mpr hvj)).mpr (hmax i)
 choose c hc using fun i=>hres (a i/a j) (hnorm i)
 have hcj:c j≠0:=by
   intro h
   have hbad:=hc j
   simpa [h,haj] using hbad
 have hsum:v (∑ i,φ (a i/a j)*x^(i:ℕ))=1:=by
   apply FIG v x hx
     (fun i=>φ (a i/a j)) (fun i=>φ (κ (c i)))
   · intro i
     simpa only [map_sub] using hc i
   · exact hunit c ⟨j,hcj⟩
 have hscale:(∑ i,φ (a i)*x^(i:ℕ))=
     φ (a j)*(∑ i,φ (a i/a j)*x^(i:ℕ)):=by
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro i _
   rw [map_div₀]
   field_simp
 rw [hscale,map_mul,hsum,mul_one]
theorem BMW {w:ℕ}
   (v:Valuation L Γ) (φ:F→+*L) (κ:k→+*F)
   (x:L) (hx:v x=1)
   (hres:RCN059.ResidueApprox v φ κ)
   (hunit:RCN059.ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1)→F) (i:Fin (w+1)):
   v (φ (a i))≤v (∑ j,φ (a j)*x^(j:ℕ)):=by
 classical
 by_cases hai:a i=0
 · simp [hai]
 have hφi:φ (a i)≠0:=by
   intro h
   apply hai
   apply φ.injective
   simpa using h
 have hvi:v (φ (a i))≠0:=(Valuation.ne_zero_iff v).mpr hφi
 obtain ⟨j,_,hmax⟩:=
   Finset.exists_max_image Finset.univ (fun j:Fin (w+1)=>v (φ (a j)))
     Finset.univ_nonempty
 have haj:a j≠0:=by
   intro h
   have hz:v (φ (a j))=0:=by simp [h]
   apply hvi
   apply le_antisymm
   · simpa only [hz] using hmax i (Finset.mem_univ i)
   · exact zero_le
 rw [BRT v φ κ x hx hres hunit a j haj
   (fun z=>hmax z (Finset.mem_univ z))]
 exact hmax i (Finset.mem_univ i)
theorem BAQ {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (φ:F→+*L) (κ:k→+*F)
   (x:L) (hx:v x=1)
   (hres:RCN059.ResidueApprox v φ κ)
   (hunit:RCN059.ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1)→F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i))≤
     RCN187.poleOrder v (∑ j,φ (a j)*x^(j:ℕ)):=by
 have hval:=BMW
   v φ κ x hx hres hunit a i
 by_cases hai:a i=0
 · simp only [hai,map_zero,RCN187.poleOrder,
     WithZero.log_zero,max_self]
   exact le_max_left _ _
 have hφi:φ (a i)≠0:=by
   intro h
   apply hai
   apply φ.injective
   simpa using h
 have hvi:v (φ (a i))≠0:=(Valuation.ne_zero_iff v).mpr hφi
 have hsum:v (∑ j,φ (a j)*x^(j:ℕ))≠0:=
   ne_of_gt ((zero_lt_iff.mpr hvi).trans_le hval)
 exact max_le_max_left 0 ((WithZero.log_le_log hvi hsum).mpr hval)
end
end RCN059
end SubmissionLower
end ProximityPrize
end PackedLegacy_H9
section PackedLegacy_I0
namespace ProximityPrize
namespace SubmissionLower
namespace RCN060
open scoped BigOperators
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k F Γ:Type*} [Field k] [Field F] [Algebra k F]
 [LinearOrderedCommGroupWithZero Γ]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq F:=Classical.decEq F
theorem EQL
   (v:Valuation F Γ) (κ:k→+*F)
   (hκ:∀c,v (κ c)≤1) (f:F) (hf:v f≤1) (p:k[X]):
   v (p.eval₂ κ f)≤1:=by
 rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
 apply v.map_sum_le
 intro i _
 rw [map_mul,map_pow]
 exact mul_le_one₀ (hκ _) zero_le (pow_le_one₀ zero_le hf)
theorem FLU
   {R:Type*} [CommRing R] [IsDomain R] (κ:R→+*F)
   (u:F) (hu:u≠0) (p:R[X]) (hp:p≠0)
   (hev:p.eval₂ κ u=0):
   ∃q:R[X],q.coeff 0≠0∧q.eval₂ κ u=0:=by
 classical
 induction hn:p.natDegree using Nat.strong_induction_on generalizing p with
 | h n ih=>
   by_cases hzero:p.coeff 0=0
   · obtain ⟨q,hpq⟩:=Polynomial.X_dvd_iff.mpr hzero
     have hq:q≠0:=by
       intro hz
       exact hp (by simp [hpq,hz])
     have hdeg:q.natDegree<n:=by
       rw [hpq,Polynomial.natDegree_X_mul hq] at hn
       omega
     have hqeval:q.eval₂ κ u=0:=by
       rw [hpq,Polynomial.eval₂_mul,Polynomial.eval₂_X] at hev
       exact (mul_eq_zero.mp hev).resolve_left hu
     exact ih q.natDegree hdeg q hq hqeval rfl
   · exact ⟨p,hzero,hev⟩
theorem BXA [IsAlgClosed k]
   (v:Valuation F Γ) (κ:k→+*F)
   (hκ:∀c,c≠0→v (κ c)=1)
   (f:F) (p:k[X]) (hp:p≠0) (hsmall:v (p.eval₂ κ f)<1):
   ∃c:k,v (f-κ c)<1:=by
 classical
 by_contra h
 push_neg at h
 have hge:1≤v (p.eval₂ κ f):=by
   rw [(IsAlgClosed.splits p).eq_prod_roots,Polynomial.eval₂_mul,
     Polynomial.eval₂_C,map_mul,hκ p.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hp),
     one_mul,Polynomial.eval₂_multiset_prod,map_multiset_prod]
   simp only [Multiset.map_map,Polynomial.eval₂_sub,Polynomial.eval₂_X,
     Polynomial.eval₂_C,Function.comp_def]
   exact Multiset.one_le_prod_map (fun c _=>h c)
 exact (not_lt_of_ge hge) hsmall
theorem DFX
   (v:Valuation F Γ) (κ:k→+*F)
   (hκ:∀c,v (κ c)≤1)
   (u f:F) (hu:v u<1) (hf:v f≤1)
   (q:Polynomial (Polynomial k))
   (hq:q.eval₂ (Polynomial.eval₂RingHom κ f) u=0):
   v ((q.coeff 0).eval₂ κ f)<1:=by
 have hcoeff:∀p:k[X],v ((Polynomial.eval₂RingHom κ f) p)≤1:=
   fun p=>EQL v κ hκ f hf p
 have htail:v (q.divX.eval₂ (Polynomial.eval₂RingHom κ f) u)≤1:=by
   rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
   apply v.map_sum_le
   intro i _
   rw [map_mul,map_pow]
   exact mul_le_one₀ (hcoeff _) zero_le (pow_le_one₀ zero_le hu.le)
 have hdecomp:=congrArg
   (fun p:Polynomial (Polynomial k)=>p.eval₂ (Polynomial.eval₂RingHom κ f) u)
   (Polynomial.X_mul_divX_add q)
 simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_X,
   Polynomial.eval₂_C,hq,Polynomial.coe_eval₂RingHom] at hdecomp
 have heq:(q.coeff 0).eval₂ κ f=
     -(u*q.divX.eval₂ (Polynomial.eval₂RingHom κ f) u):=by
   rw [eq_neg_iff_add_eq_zero]
   simpa only [add_comm] using hdecomp
 rw [heq,v.map_neg,map_mul]
 exact (mul_le_mul' le_rfl htail).trans_lt (by simpa using hu)
theorem CKA
   (htrdeg:Algebra.trdeg k F=1) (u f:F):
   ∃q:Polynomial (Polynomial k),q≠0∧
     q.eval₂ (Polynomial.eval₂RingHom (algebraMap k F) f) u=0:=by
 have hnot:¬AlgebraicIndependent k ![f,u]:=by
   intro hi
   have hc:=hi.lift_cardinalMk_le_trdeg
   rw [htrdeg] at hc
   norm_num at hc
 rw [algebraicIndependent_iff] at hnot
 push_neg at hnot
 obtain ⟨p,hpval,hp⟩:=hnot
 let e:=Polynomial.Bivariate.equivMvPolynomial k
 let q:Polynomial (Polynomial k):=e.symm p
 have hq:q≠0:=by
   intro hz
   apply hp
   have:=congrArg e hz
   simpa [q] using this
 have hmaps:
     (Polynomial.aevalAeval (R:=k) f u).comp e.symm.toAlgHom=
       MvPolynomial.aeval ![f,u]:=by
   ext i
   fin_cases i<;>simp [e,Polynomial.aevalAeval_C,
     Polynomial.aevalAeval_X,Polynomial.aevalAeval_Y]
 have hev:
     Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap k F) f) u=
       (Polynomial.aevalAeval (R:=k) f u).toRingHom:=by
   ext<;>simp [Polynomial.aevalAeval_C,Polynomial.aevalAeval_X,
     Polynomial.aevalAeval_Y]
 refine ⟨q,hq,?_⟩
 change (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap k F) f) u) q=0
 rw [hev]
 change ((Polynomial.aevalAeval (R:=k) f u).comp e.symm.toAlgHom) p=0
 rw [hmaps]
 exact hpval
theorem CWK [IsAlgClosed k]
   (v:Valuation F Γ) [v.IsTrivialOn k]
   (htrdeg:Algebra.trdeg k F=1)
   (u:F) (hu0:u≠0) (hu:v u<1)
   (f:F) (hf:v f≤1):
   ∃c:k,v (f-algebraMap k F c)<1:=by
 have hκ:∀c:k,v (algebraMap k F c)≤1:=by
   intro c
   by_cases hc:c=0
   · simp [hc]
   · exact (Valuation.IsTrivialOn.eq_one c hc).le
 obtain ⟨p,hp,hpval⟩:=CKA htrdeg u f
 obtain ⟨q,hq0,hqval⟩:=
   FLU (Polynomial.eval₂RingHom (algebraMap k F) f) u hu0 p hp hpval
 exact BXA v (algebraMap k F)
   (fun c hc=>Valuation.IsTrivialOn.eq_one c hc) f (q.coeff 0) hq0
   (DFX v (algebraMap k F) hκ u f hu hf q hqval)
variable {L:Type*} [Field L]
open ProximityPrize.SubmissionLower RCN059
theorem EEQ [IsAlgClosed k]
   (v:Valuation L Γ) (φ:F→+*L)
   (hconst:∀c:k,c≠0→v (φ (algebraMap k F c))=1)
   (htrdeg:Algebra.trdeg k F=1)
   (u:F) (hu0:u≠0) (hu:v (φ u)<1):
   RCN059.ResidueApprox v φ (algebraMap k F):=by
 let vF:Valuation F Γ:=v.comap φ
 letI:vF.IsTrivialOn k:=⟨hconst⟩
 intro f hf
 exact CWK vF htrdeg u hu0 hu f hf
theorem DKG [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) (φ:F→+*L)
   (hconst:∀c:k,c≠0→v (φ (algebraMap k F c))=1)
   (htrdeg:Algebra.trdeg k F=1)
   (x:L) (hx:v x=1)
   (hunit:RCN059.ConstantPolynomialUnit v φ (algebraMap k F) x w)
   (a:Fin (w+1)→F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i))≤
     RCN187.poleOrder v (∑ j,φ (a j)*x^(j:ℕ)):=by
 by_cases hi:v (φ (a i))≤1
 · have hz:RCN187.poleOrder v (φ (a i))=0:=by
     change max 0 (v (φ (a i))).log=0
     rw [←RCN187.log_max_one,max_eq_left hi,WithZero.log_one]
   rw [hz]
   exact le_max_left _ _
 have hbig:1<v (φ (a i)):=lt_of_not_ge hi
 let vF:Valuation F (WithZero (Multiplicative ℤ)):=v.comap φ
 haveI:vF.IsNontrivial:=
   ⟨a i,ne_of_gt (zero_lt_one.trans hbig),hbig.ne'⟩
 obtain ⟨u,hu0,hu⟩:=Valuation.IsNontrivial.exists_lt_one (v:=vF)
 exact BAQ v φ (algebraMap k F)
   x hx (EEQ v φ hconst htrdeg u hu0 hu) hunit a i
theorem CAO
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] {w:ℕ}
   (v:Valuation L Γ) [v.IsTrivialOn Ω] (φ:F→+*L)
   (hcompat:∀c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (x:Ω) (htrans:Transcendental k x):
   RCN059.ConstantPolynomialUnit v φ (algebraMap k F) (algebraMap Ω L x) w:=by
 classical
 intro c hc
 obtain ⟨i,hi⟩:=hc
 let q:k[X]:=∑ j:Fin (w+1),Polynomial.monomial (j:ℕ) (c j)
 have hcoef:q.coeff (i:ℕ)=c i:=by
   simp only [q,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
   rw [Finset.sum_eq_single i]
   · simp
   · intro j _ hji
     have hval:(j:ℕ)≠(i:ℕ):=fun h=>hji (Fin.ext h)
     simp [hval]
   · simp
 have hq:q≠0:=by
   intro hzero
   apply hi
   have h:=congrArg (fun p:k[X]=>p.coeff (i:ℕ)) hzero
   simpa only [hcoef,Polynomial.coeff_zero] using h
 have hneq:Polynomial.aeval x q≠0:=by
   intro hzero
   apply hq
   apply (transcendental_iff_injective.mp htrans)
   simpa only [map_zero] using hzero
 have hv:v (algebraMap Ω L (Polynomial.aeval x q))=1:=
   Valuation.IsTrivialOn.eq_one _ hneq
 simpa only [q,map_sum,Polynomial.aeval_monomial,map_mul,map_pow,
   ←hcompat] using hv
theorem CKE
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) [v.IsTrivialOn Ω]
   (φ:F→+*L)
   (hcompat:∀c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (htrdeg:Algebra.trdeg k F=1)
   (x:Ω) (htrans:Transcendental k x)
   (a:Fin (w+1)→F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i))≤
     RCN187.poleOrder v
       (∑ j,φ (a j)*(algebraMap Ω L x)^(j:ℕ)):=by
 have hconst:∀c:k,c≠0→v (φ (algebraMap k F c))=1:=by
   intro c hc
   rw [hcompat]
   apply Valuation.IsTrivialOn.eq_one
   intro hz
   apply hc
   apply (algebraMap k Ω).injective
   simpa using hz
 have hx0:x≠0:=by
   intro hz
   apply htrans
   rw [hz]
   exact isAlgebraic_zero
 have hx:v (algebraMap Ω L x)=1:=Valuation.IsTrivialOn.eq_one x hx0
 exact DKG v φ hconst htrdeg (algebraMap Ω L x) hx
   (CAO v φ hcompat x htrans) a i
end
end RCN060
end SubmissionLower
end ProximityPrize
end PackedLegacy_I0
section PackedLegacy_I1
namespace ProximityPrize
namespace SubmissionLower
namespace RCN061
open scoped BigOperators
open RCN060
noncomputable section
variable {k F L:Type*} [Field k] [Field F] [Field L] [Algebra k F]
theorem AVW
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) [v.IsTrivialOn Ω]
   (φ:F→+*L)
   (hcompat:∀c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (htrdeg:Algebra.trdeg k F≤1)
   (x:Ω) (htrans:Transcendental k x)
   (a:Fin (w+1)→F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i))≤
     RCN187.poleOrder v
       (∑ j,φ (a j)*(algebraMap Ω L x)^(j:ℕ)):=by
 classical
 letI:Decidable (Algebra.trdeg k F=0):=Classical.propDecidable _
 by_cases hz:Algebra.trdeg k F=0
 · letI:Algebra.IsAlgebraic k F:=trdeg_eq_zero_iff.mp hz
   letI:Algebra.IsIntegral k F:=
     Algebra.isAlgebraic_iff_isIntegral.mp (inferInstance:Algebra.IsAlgebraic k F)
   obtain ⟨c,hc⟩:=
     (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=k)).2 (a i)
   have hφ:φ (a i)=algebraMap Ω L (algebraMap k Ω c):=by
     rw [←hc,hcompat]
   have hpole:RCN187.poleOrder v (φ (a i))=0:=by
     rw [hφ]
     change max 0 (v (algebraMap Ω L (algebraMap k Ω c))).log=0
     rw [←RCN187.log_max_one,
       max_eq_left (Valuation.IsTrivialOn.valuation_algebraMap_le_one v _),
       WithZero.log_one]
   rw [hpole]
   exact le_max_left _ _
 · have hone:(1:Cardinal)≤Algebra.trdeg k F:=
     Cardinal.one_le_iff_ne_zero.mpr hz
   have heq:Algebra.trdeg k F=1:=le_antisymm htrdeg hone
   exact CKE v φ hcompat heq x htrans a i
end
end RCN061
end SubmissionLower
end ProximityPrize
end PackedLegacy_I1
section PackedLegacy_D0
namespace ProximityPrize
namespace SubmissionLower
namespace RCN205
open scoped Classical WithZero
open RCN187 RCN295 RCN095 RCN114 RCN162
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K L:Type} [Field K] [Field L] [Algebra K L]
theorem pole_nonneg_p19 (ν:DV L) (x:L):0≤poleOrder ν x:=
 le_max_left _ _
theorem EJT (ν:DV L) (x:L):
   ν x≤WithZero.exp (poleOrder ν x):=by
 have hn:max 1 (ν x)≠0:=ne_of_gt
   (zero_lt_one.trans_le (le_max_left _ _))
 rw [poleOrder,←log_max_one,WithZero.exp_log hn]
 exact le_max_right _ _
theorem DRP (ν:DV L) (x:L) (n:ℤ)
   (hn:0≤n) (h:ν x≤WithZero.exp n):poleOrder ν x≤n:=by
 have h1:(1:WithZero (Multiplicative ℤ))≤WithZero.exp n:=by
   rw [←WithZero.exp_zero,WithZero.exp_le_exp]
   exact hn
 have hnz:max 1 (ν x)≠0:=ne_of_gt
   (zero_lt_one.trans_le (le_max_left _ _))
 have hh:=(WithZero.log_le_log hnz WithZero.exp_ne_zero).2 (max_le h1 h)
 simpa only [log_max_one,WithZero.log_exp,poleOrder] using hh
theorem pole_add_le_p19 (ν:DV L) (x y:L):
   poleOrder ν (x+y)≤max (poleOrder ν x) (poleOrder ν y):=by
 apply DRP ν _ _ ((pole_nonneg_p19 ν x).trans (le_max_left _ _))
 exact (ν.map_add x y).trans (max_le
   ((EJT ν x).trans ((WithZero.exp_le_exp).2 (le_max_left _ _)))
   ((EJT ν y).trans ((WithZero.exp_le_exp).2 (le_max_right _ _))))
theorem GXM (ν:DV L)
   (hν:∀c:K,ν (algebraMap K L c)≤1) (c:K):
   poleOrder ν (algebraMap K L c)≤0:=by
 apply DRP ν _ _ le_rfl
 simpa using hν c
theorem FTC (ν:DV L)
   (hν:∀c:K,ν (algebraMap K L c)≤1) (c:K) (x:L):
   poleOrder ν (algebraMap K L c*x)≤poleOrder ν x:=by
 apply DRP ν _ _ (pole_nonneg_p19 ν x)
 rw [map_mul]
 exact (mul_le_mul' (hν c) (EJT ν x)).trans_eq (one_mul _)
end
end RCN205
end SubmissionLower
end ProximityPrize
end PackedLegacy_D0
section PackedLegacy_H8
namespace ProximityPrize
namespace SubmissionLower
namespace RCN058
open RCN062 RCN061 RCN187 RCN205 RCN002
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
variable {K k L:Type} [Field K] [Field k] [Field L]
 [Algebra K k] [Algebra K L] [Algebra k L] [IsScalarTower K k L]
theorem BCU
   {Ω:Type} [Field Ω] [IsAlgClosed k]
   [Algebra k Ω] [Algebra Ω L] [IsScalarTower k Ω L]
   (P:Polynomial L) (γ:L) (w:ℕ) (hP:P.natDegree≤w)
   (htr:Algebra.trdeg k (RCN062.baseCoefficientField (k:=k) P γ)≤1)
   (x:Ω) (hx:Transcendental k x) (y:L)
   (hy:P.eval (algebraMap Ω L x)=y)
   (v:RCN346.Place_p19 Ω L) (j:ℕ):
   poleOrder v.val (P.coeff j)≤poleOrder v.val y:=by
 letI:v.val.IsTrivialOn Ω:=v.property.2
 let B:IntermediateField k L:=RCN062.baseCoefficientField (k:=k) P γ
 have hcoeff (n:ℕ):P.coeff n∈B:=by
   exact IntermediateField.subset_adjoin k _ (Or.inr ⟨n,rfl⟩)
 by_cases hj:j<w+1
 · let i:Fin (w+1):=⟨j,hj⟩
   let a:Fin (w+1)→B:=fun n=>⟨P.coeff n,hcoeff n⟩
   let φ:B→+*L:=B.val.toRingHom
   have hcompat:∀c:k,φ (algebraMap k B c)=
       algebraMap Ω L (algebraMap k Ω c):=by
     intro c
     exact IsScalarTower.algebraMap_apply k Ω L c
   have hsum:(∑ n,φ (a n)*(algebraMap Ω L x)^(n:ℕ))=
       P.eval (algebraMap Ω L x):=by
     rw [P.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
     rw [←Fin.sum_univ_eq_sum_range]
     change (∑ n:Fin (w+1),P.coeff (n:ℕ)*
       (algebraMap Ω L x)^(n:ℕ))=_
     rfl
   have hle:=AVW
     v.val φ hcompat htr x hx a i
   change poleOrder v.val (P.coeff i)≤
     poleOrder v.val (∑ n,φ (a n)*(algebraMap Ω L x)^(n:ℕ)) at hle
   rw [hsum,hy] at hle
   simpa only [i] using hle
 · have hz:P.coeff j=0:=Polynomial.coeff_eq_zero_of_natDegree_lt
     (hP.trans_lt (by omega))
   rw [hz]
   simp only [poleOrder,map_zero,WithZero.log_zero,max_self]
   exact le_max_left _ _
end
end RCN058
end SubmissionLower
end ProximityPrize
end PackedLegacy_H8
section PackedLegacy_A8
namespace ProximityPrize
namespace SubmissionLower
namespace RCN063
open scoped Classical BigOperators WithZero
open RCN187 RCN205 RCN344 RCN002 RCN065 RCN136 RCN139 RCN047 RCN313 RCN233 RCN238 RCN341 RCN271 RCN257 RCN095 RCN114 RCN295
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {L:Type} [Field L]
theorem GQH (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:L) (q:ℤ) (hq:0≤q) (hx:v x≤WithZero.exp q):poleOrder v x≤q:=by
 apply max_le hq
 by_cases hzero:v x=0
 · simpa [hzero] using hq
 · simpa only [WithZero.log_exp] using (WithZero.log_le_log hzero WithZero.exp_ne_zero).mpr hx
theorem eval_pole_le_p19 (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z a:L) (ha:v a≤1):
   poleOrder v (T.eval a)≤RCN063.coefficientPoleWeight v T z:=by
 apply GQH _ _ _ (RCN063.coefficientPoleWeight_nonneg v T z)
 rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
 apply v.map_sum_le
 intro j hj
 rw [map_mul,map_pow]
 have hc:v (T.coeff j)≤WithZero.exp (RCN063.coefficientPoleWeight v T z):=
   WithZero.le_exp_of_log_le ((le_max_right _ _).trans (coeffPole_le v T z j hj))
 have hp:v a^j≤1:=pow_le_one₀ zero_le ha
 simpa only [mul_one] using mul_le_mul' hc hp
theorem FJG {Ω:Type} [Field Ω] [Algebra Ω L]
   (v:Place_p19 Ω L) (T:Polynomial L) (z:L) (a u0 u1:Ω):
   poleOrder v.val (T.eval (algebraMap Ω L a)-algebraMap Ω L u0-z*algebraMap Ω L u1)≤
     RCN063.coefficientPoleWeight v.val T z:=by
 have ht:=eval_pole_le_p19 v.val T z _ (NP Ω L v a)
 have h0:=GXM v.val (NP Ω L v) u0
 have hz:=FTC v.val (NP Ω L v) u1 z
 have hseed:=seedPole_le v.val T z
 have hn:=RCN063.coefficientPoleWeight_nonneg v.val T z
 have hsub (x y:L):poleOrder v.val (x-y)≤max (poleOrder v.val x) (poleOrder v.val y):=by
   simpa only [sub_eq_add_neg,pole_neg] using pole_add_le_p19 v.val x (-y)
 exact (hsub _ _).trans (max_le ((hsub _ _).trans (max_le ht (h0.trans hn)))
   (by simpa only [mul_comm] using hz.trans hseed))
variable {K Ω:Type} [Field K] [Field Ω]
variable (φ:Polynomial K→+*Ω) (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
def AHG (w cost:ℕ):Prop:=
 ∀W:Finset (Place_p19 Ω (RCN002.CoordinateField Ω P)),
   (∑ v∈W,RCN063.coefficientPoleWeight v.val (RCN065.truncatedPolynomial φ P F hF hH w)
     (coordinate Ω P 2))≤(cost:ℤ)
theorem AVM (w cost:ℕ)
   (hcoeff:∀(v:Place_p19 Ω (RCN002.CoordinateField Ω P)) (j:ℕ),
     poleOrder v.val ((RCN065.truncatedPolynomial φ P F hF hH w).coeff j)≤
       poleOrder v.val (coordinate Ω P 0))
   (hyz:∀W:Finset (Place_p19 Ω (RCN002.CoordinateField Ω P)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Ω P) (flagSupport unitYZFlag))≤(cost:ℤ)):
   AHG φ P F hF hH w cost:=by
 have hp (v:Place_p19 Ω (RCN002.CoordinateField Ω P)):
     RCN063.coefficientPoleWeight v.val (RCN065.truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2)≤
       max (poleOrder v.val (coordinate Ω P 0)) (poleOrder v.val (coordinate Ω P 2)):=by
   unfold RCN063.coefficientPoleWeight
   apply Finset.max'_le
   intro z hz
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact (le_max_left _ _).trans (le_max_left _ _)
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact le_max_right _ _
   obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hz
   exact (hcoeff v j).trans (le_max_left _ _)
 intro W
 exact (Finset.sum_le_sum (fun v _↦hp v)).trans
   (by simpa only [QD] using hyz W)
theorem EQH (w:ℕ) (x u0 u1:K):
   RCN002.coordinateEvaluation Ω P (FK φ F w x u0 u1)/
     (RCN002.coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)=
   (RCN065.truncatedPolynomial φ P F hF hH w).eval (RCN065.componentCoefficients φ P x)-
     RCN065.componentCoefficients φ P u0-coordinate Ω P 2*RCN065.componentCoefficients φ P u1:=by
 have hclear:=RCN047.eval_factorial_agreementNumerator (RCN065.componentCoefficients φ P) F
   (RCN065.componentPoint φ P) (RCN065.component_relation φ P F hF) (RCN065.component_regular φ P F hH)
   w x u0 u1
 rw [RCN065.component_evaluation] at hclear
 have hbase:MvPolynomial.eval₂Hom (RCN065.componentCoefficients φ P) (RCN065.componentPoint φ P) (polyH K F)=
     RCN002.coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)):=by
   exact RCN065.component_evaluation φ P _
 rw [hbase,←RCN139.globalPolynomial_eval] at hclear
 have hz:RCN065.componentPoint φ P (3:Fin 4)=coordinate Ω P 2:=rfl
 rw [hz] at hclear
 have hne:RCN002.coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0:=by
   rw [←RCN065.component_evaluation]
   exact RCN065.component_regular φ P F hH
 apply (div_eq_iff (pow_ne_zero _ hne)).mpr
 simpa only [FK,RCN065.truncatedPolynomial,mul_comm] using hclear
theorem ELR [IsAlgClosed Ω] (base:RCN341.SeparableLiteralCoordinate P)
   (w cost:ℕ) (hprofile:AHG φ P F hF hH w cost)
   (x u0 u1:K) (hproper:FK φ F w x u0 u1∉P):
   ABY P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
     (FK φ F w x u0 u1) cost:=by
 apply AIR Ω P base _ _ (2*w) cost hproper hH
 intro W
 have hlocal (v:Place_p19 Ω (RCN002.CoordinateField Ω P)):
     poleOrder v.val (RCN002.coordinateEvaluation Ω P (FK φ F w x u0 u1)/
       (RCN002.coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w))≤
     RCN063.coefficientPoleWeight v.val (RCN065.truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2):=by
   rw [EQH φ P F hF hH]
   exact FJG v _ _ (φ (Polynomial.C x)) (φ (Polynomial.C u0)) (φ (Polynomial.C u1))
 simpa only [RCN346.poleOrder_p19,RCN002.coordinateEvaluation_eq_aeval] using
   (Finset.sum_le_sum (fun v _↦hlocal v)).trans (hprofile W)
end
end RCN063
end SubmissionLower
end ProximityPrize
end PackedLegacy_A8
section PackedLegacy_BK
namespace ProximityPrize
namespace SubmissionLower
namespace RCN144
open scoped Classical BigOperators
open RCN135 RCN136 RCN313 RCN159 RCN220 RCN083 RCN228 RCN127 RCN058 RCN063 RCN065 RCN238 RCN243 RCN264 RCN231 RCN229 RCN126 RCN062 RCN047 RCN139 RCN174 RCN114 RCN295 RCN095 RCN275 RCN319 RCN002
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN095 renaming PolynomialInFlag → BI
open RCN319 renaming specialization → BM
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω_p19 (K:Type) [Field K]:=GenericField K
variable {Γ:Finset K} {x:I→K} {p e:ℕ} [CharP (Ω_p19 K) p]
 {flag:FlagDegree} {w:ℕ} {support:RCN275.ResidualSupportParameters}
theorem BJT
   (S:FH (RCN135.polynomialEmbedding K) Γ x p e flag w support)
   (x0 u0 u1:K)
   (C:RCN264.RegularComponent (Ω_p19 K) S.G
     (FK (RCN135.polynomialEmbedding K) S.F w x0 u0 u1)
     (CR (RCN135.polynomialEmbedding K) S.F)):
   surfaceMap (RCN135.polynomialEmbedding K) S.F∈C.1:=by
 obtain ⟨A,hA⟩:=S.RR
 rw [hA]
 exact C.1.mul_mem_right A
   (EN (Ω_p19 K) S.G _ _ C)
theorem AIC
   (S:FH (RCN135.polynomialEmbedding K) Γ x p e flag w support)
   (x0 u0 u1:K)
   (C:RCN264.RegularComponent (Ω_p19 K) S.G
     (FK (RCN135.polynomialEmbedding K) S.F w x0 u0 u1)
     (CR (RCN135.polynomialEmbedding K) S.F)):
   surfaceMap (RCN135.polynomialEmbedding K) (polyH K S.F)∉C.1:=
 _Q6 (Ω_p19 K) S.G _ _ C
theorem AIK
   (S:FH (RCN135.polynomialEmbedding K) Γ x p e flag w support)
   (hTail:S.G∣surfaceMap (RCN135.polynomialEmbedding K) (numerator K S.F (w+1)))
   (x0 u0 u1:K)
   (hproper:¬S.G∣FK (RCN135.polynomialEmbedding K) S.F w x0 u0 u1)
   (C:RCN264.RegularComponent (Ω_p19 K) S.G
     (FK (RCN135.polynomialEmbedding K) S.F w x0 u0 u1)
     (CR (RCN135.polynomialEmbedding K) S.F))
   (bound seedCap slopeCap cost:ℕ)
   (hw:1≤w) (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈RCN174.globalCoefficientBox K bound w seedCap slopeCap)
   (hyz:∀W:Finset (RCN346.Place_p19 (Ω_p19 K) (RCN002.CoordinateField (Ω_p19 K) C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate (Ω_p19 K) C.1)
       (flagSupport unitYZFlag))≤(cost:ℤ)):
   AHG (RCN135.polynomialEmbedding K) C.1 S.F
     (BJT S x0 u0 u1 C)
     (AIC S x0 u0 u1 C) w cost:=by
 classical
 let φ:=RCN135.polynomialEmbedding K
 let Pcurve:=C.1
 let L:=RCN002.CoordinateField (Ω_p19 K) Pcurve
 let κ:K→+*L:=RCN065.componentCoefficients φ Pcurve
 let v0:Fin 4→L:=RCN065.componentPoint φ Pcurve
 letI:CharP L p:=
   charP_of_injective_algebraMap (algebraMap (Ω_p19 K) L).injective p
 have hFC:=BJT S x0 u0 u1 C
 have hHC:=AIC S x0 u0 u1 C
 obtain ⟨F0,Q,hF0irr,hF0pos,hprod,hGF0,hGQ,hGH0,hTail0⟩:=
   CLN S hTail
 have hF0mem:surfaceMap φ F0∈Pcurve:=by
   obtain ⟨A,hA⟩:=hGF0
   rw [hA]
   exact Pcurve.mul_mem_right A (EN (Ω_p19 K) S.G _ _ C)
 have hHdecomp:surfaceMap φ (polyH K S.F)=
     surfaceMap φ (polyH K F0)*surfaceMap φ Q+
       surfaceMap φ F0*surfaceMap φ (polyH K Q):=by
   rw [hprod]
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
 have hHQnot:surfaceMap φ (polyH K F0)*surfaceMap φ Q∉Pcurve:=by
   intro hm
   apply hHC
   rw [hHdecomp]
   exact Pcurve.add_mem hm (Pcurve.mul_mem_right _ hF0mem)
 have hQnot:surfaceMap φ Q∉Pcurve:=
   fun h=>hHQnot (Pcurve.mul_mem_left _ h)
 have hH0not:surfaceMap φ (polyH K F0)∉Pcurve:=
   fun h=>hHQnot (Pcurve.mul_mem_right _ h)
 have hF0rel:MvPolynomial.eval₂Hom κ v0 F0=0:=
   (RCN065.component_evaluation_zero_iff φ Pcurve F0).mpr hF0mem
 have hF0reg:MvPolynomial.eval₂Hom κ v0 (polyH K F0)≠0:=
   (RCN065.component_evaluation_zero_iff φ Pcurve (polyH K F0)).not.mpr hH0not
 have hQeval:MvPolynomial.eval₂Hom κ v0 Q≠0:=
   (RCN065.component_evaluation_zero_iff φ Pcurve Q).not.mpr hQnot
 have hprodrel:MvPolynomial.eval₂Hom κ v0 (F0*Q)=0:=by
   rw [map_mul,hF0rel,zero_mul]
 have hprodreg:MvPolynomial.eval₂Hom κ v0 (polyH K (F0*Q))≠0:=by
   rw [←hprod]
   exact RCN065.component_regular φ Pcurve S.F hHC
 let P0:Polynomial L:=RCN139.globalPolynomial κ F0 v0 hF0rel hF0reg w
 have hP0deg:P0.natDegree≤w:=RCN139.globalPolynomial_natDegree_le κ F0 v0 hF0rel hF0reg w
 have hSne:S.F≠0:=by
   intro hz
   apply S.BLO
   rw [hz]
   simp
 have hF0box:F0∈RCN174.globalCoefficientBox K bound w seedCap slopeCap:=by
   apply RCN081.mem_globalCoefficientBox_of_dvd F0 S.F bound w seedCap slopeCap
     hSne ⟨Q,hprod⟩ hbox
 have hP0solution:RCN319.specialization L P0 (v0 3) (MvPolynomial.map κ F0)=0:=
   CNR κ F0 v0 hF0rel hF0reg
     p bound w seedCap slopeCap hw hshort hchar hF0box hTail0
 have hcanon:RCN065.truncatedPolynomial φ Pcurve S.F hFC hHC w=P0:=by
   unfold RCN065.truncatedPolynomial
   change RCN139.globalPolynomial κ S.F v0 _ _ w=P0
   have hm:=EAT κ F0 Q v0 hF0rel hQeval hF0reg
     hprodrel hprodreg w
   simpa only [hprod,P0] using hm
 have hagree:P0.eval (κ x0)=κ u0+v0 3*κ u1:=by
   have hm:=GV (Ω_p19 K) S.G
     (FK φ S.F w x0 u0 u1) (CR φ S.F) C
   have hv:=(RCN065.agreement_mem_iff_truncated_value φ Pcurve S.F hFC hHC
     w x0 u0 u1).mp (by simpa only [FK] using hm)
   rw [hcanon] at hv
   change P0.eval (RCN065.componentCoefficients φ Pcurve x0)=
     RCN065.componentCoefficients φ Pcurve u0+
       coordinate (Ω_p19 K) Pcurve 2*RCN065.componentCoefficients φ Pcurve u1 at hv
   change P0.eval (RCN065.componentCoefficients φ Pcurve x0)=
     RCN065.componentCoefficients φ Pcurve u0+
       coordinate (Ω_p19 K) Pcurve 2*RCN065.componentCoefficients φ Pcurve u1
   exact hv
 let A0:=RCN313.agreementNumerator F0 w (fun j=>(j.factorial:K)⁻¹) x0 u0 u1
 have hA0proper:¬F0∣A0:=by
   apply RCN220.DIL
     φ F0 Q S.G hGF0 w _ x0 u0 u1
   simpa only [FK,hprod] using hproper
 have hvpoint:RCN231.polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0)=v0:=by
   funext i
   fin_cases i
   · rfl
   · exact RCN139.globalPolynomial_initial_value κ F0 v0 hF0rel hF0reg w
   · exact RCN139.globalPolynomial_initial_slope κ F0 v0 hF0rel hF0reg w hw
   · rfl
 have hregspec:RCN319.specialization L P0 (v0 3)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
   have hmapped:MvPolynomial.eval₂Hom (RingHom.id L) v0
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
     simpa only [polyH,MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom,
       RingHom.id_comp] using hF0reg
   intro hz
   apply hmapped
   rw [←hvpoint]
   rw [RCN231.eval_polynomialPoint_eq_specialization,hz]
   simp
 have hA0solution:RCN319.specialization L P0 (v0 3) (MvPolynomial.map κ A0)=0:=by
   apply RatFunc.algebraMap_injective L
   rw [map_zero,←EIM]
   rw [ECX]
   have hfresh:MvPolynomial.eval₂Hom (algebraMap L (RatFunc L))
       (freshPoint_p19 P0 (v0 3))
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
     rw [EIM]
     exact RatFunc.algebraMap_ne_zero hregspec
   have heval:=(RCN229.factorial_agreement_zero_iff_original_agreement
     (algebraMap L (RatFunc L)) (MvPolynomial.map κ F0) P0 (v0 3) RatFunc.X
     hP0solution hfresh p w S.WG
     hP0deg (κ x0) (κ u0) (κ u1)).mpr hagree
   simpa only [freshPoint_p19,map_inv₀,map_natCast] using heval
 have htrK:Algebra.trdeg K (RCN062.baseCoefficientField (k:=K) P0 (v0 3))≤1:=
   ABA F0 A0 P0 (v0 3)
     hF0irr hF0pos hA0proper hP0solution hA0solution hregspec
     p w S.WG hP0deg
 let k:=algebraicClosure K (Ω_p19 K)
 have htrk:Algebra.trdeg k (RCN062.baseCoefficientField (k:=k) P0 (v0 3))≤1:=
   RCN058.baseCoefficientField_trdeg_le_one_of_algebraic_constants P0 (v0 3) htrK
 letI:IsAlgClosed k:=IsAlgClosure.isAlgClosed K
 have hxK:Transcendental K (RCN135.initialCoordinate K):=by
   rw [transcendental_iff_injective]
   intro f g hfg
   apply RCN135.polynomialEmbedding_injective K
   change f.eval₂ (RCN135.coefficientEmbedding K) (RCN135.initialCoordinate K)=
     g.eval₂ (RCN135.coefficientEmbedding K) (RCN135.initialCoordinate K) at hfg
   rw [RCN135.generic_eval_eq,RCN135.generic_eval_eq] at hfg
   exact hfg
 have hxk:Transcendental k (RCN135.initialCoordinate K):=hxK.algebraicClosure
 apply AVM φ Pcurve S.F hFC hHC w cost
 · intro place j
   rw [hcanon]
   apply BCU P0 (v0 3) w hP0deg htrk
     (RCN135.initialCoordinate K) hxk (coordinate (Ω_p19 K) Pcurve 0)
   exact RCN139.globalPolynomial_initial_value κ F0 v0 hF0rel hF0reg w
 · exact hyz
end
end RCN144
end SubmissionLower
end ProximityPrize
end PackedLegacy_BK
section PackedLegacy_BL
namespace ProximityPrize
namespace SubmissionLower
namespace RCN145
open scoped Classical BigOperators
open RCN002 RCN136 RCN231 RCN319 RCN238 RCN065 RCN271 RCN063 RCN341 RCN344
open RCN319 renaming specialization → BM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable (φ:Polynomial K→+*Ω) (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
theorem VP
   (base:RCN341.SeparableLiteralCoordinate P) (p w a e cost:ℕ) [CharP Ω p]
   (hchar:w<p) (hwa:w<a) (hcost:1≤cost)
   (hprofile:AHG φ P F hF hH w cost)
   (selected:K→Polynomial K) (Γ:Finset K)
   {ι:Type*} (nodes:Finset ι) (x u0 u1:ι→K) (hinj:Set.InjOn x nodes)
   (hsize:nodes.card=a+e)
   (hdegree:∀γ∈Γ,(selected γ).natDegree≤w)
   (hsolution:∀γ∈Γ,RCN319.specialization K (selected γ) γ F=0)
   (hregular:∀γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀γ∈Γ,P≤RingHom.ker (MvPolynomial.aeval (DK φ selected γ)).toRingHom)
   (hagreement:∀γ∈Γ,a≤(nodes.filter (fun i↦
     (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
   (hnoPencil:BL selected Γ w e):Γ.card≤(e+1)*cost:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 let I:=RCN065.identityNodes φ P F nodes x u0 u1 w
 let relation:K→ι→Prop:=fun γ i↦(selected γ).eval (x i)=u0 i+γ*u1 i
 by_cases hI:I.card≤w
 · have hfiber:∀i∈nodes \ I,(Γ.filter (fun γ↦relation γ i)).card≤cost:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:FK φ F w (x i) (u0 i) (u1 i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact BMQ φ P F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u0 i) (u1 i) cost
       (ELR φ P F hF hH base w cost hprofile _ _ _ hproper)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w cost
     (RCN065.identityNodes_subset φ P F nodes x u0 u1 w) hI hwa (by omega) hagreement hfiber
   have hg:0<a-w:=Nat.sub_pos_of_lt hwa
   have hu:nodes.card-w≤(e+1)*(a-w):=by
     have he:=Nat.mul_le_mul_left e (show 1≤a-w by omega)
     calc
       nodes.card-w=(a-w)+e:=by omega
       _≤(a-w)+e*(a-w):=by simpa only [Nat.mul_one] using Nat.add_le_add_left he (a-w)
       _=_:=by ring
   have hscaled:Γ.card*(a-w)≤((e+1)*cost)*(a-w):=by
     calc
       _≤(nodes.card-w)*cost:=hcount
       _≤((e+1)*(a-w))*cost:=Nat.mul_le_mul_right cost hu
       _=_:=by ring
   exact Nat.le_of_mul_le_mul_right hscaled hg
 · have hi:w<I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀(t:{γ:K//γ∈Γ}) i,i∈I→
       (selected t.1).eval (x i)=u0 i+t.1*u1 i:=by
     intro t
     exact RCN065.selected_agrees_on_identity_nodes φ P F nodes x u0 u1 p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=RCN065.exists_common_pencil_of_many_identities
     φ P F hF hH nodes x u0 u1 w hinj hi
     (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
     (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter (fun γ↦selected γ=P0+Polynomial.C γ*P1)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hsmall:Γ.card≤e+1:=by
     simpa only [hfilter] using hnoPencil P0 P1 h0 h1
   exact hsmall.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (e+1) hcost)
end
end RCN145
end SubmissionLower
end ProximityPrize
end PackedLegacy_BL
section PackedLegacy_GM
namespace ProximityPrize
namespace SubmissionLower
namespace RCN312
open scoped Classical BigOperators
open RCN135 RCN136 RCN313 RCN159 RCN264 RCN074 RCN086 RCN330 RCN065 RCN238 RCN243 RCN231 RCN139 RCN047 RCN137 RCN082 RCN083 RCN258 RCN217 RCN127 RCN126 RCN062 RCN058 RCN063 RCN145 RCN339 RCN095 RCN237 RCN295 RCN174 RCN319 RCN341 RCN046 RCN042 RCN344 RCN002
open RCN082 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Omega_p19 (K:Type) [Field K]:=GenericField K
variable {Gamma:Finset K} {x:I→K} {p errors w:ℕ}
 [CharP (Omega_p19 K) p]
 {flag tailFlag1:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
theorem RP
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p errors flag w support)
   (C:CM S):
   surfaceMap (RCN135.polynomialEmbedding K) S.F∈C.1:=by
 obtain ⟨Q,hQ⟩:=S.RR
 rw [hQ]
 exact C.1.mul_mem_right Q
   (EN (Omega_p19 K) S.G _ _ C)
theorem JX
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p errors flag w support)
   (C:CM S):
   surfaceMap (RCN135.polynomialEmbedding K) (polyH K S.F)∉C.1:=
 _Q6 (Omega_p19 K) S.G _ _ C
theorem ANL
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p errors flag w support)
   (C:CM S):
   ∃F0 Q:MvPolynomial (Fin 4) K,
     Irreducible F0∧0<F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
     S.F=F0*Q∧
     S.G∣surfaceMap (RCN135.polynomialEmbedding K) F0∧
     surfaceMap (RCN135.polynomialEmbedding K) F0∈C.1∧
     surfaceMap (RCN135.polynomialEmbedding K) Q∉C.1∧
     surfaceMap (RCN135.polynomialEmbedding K) (polyH K F0)∉C.1:=by
 classical
 let phi:=RCN135.polynomialEmbedding K
 let Pcurve:=C.1
 let L:=RCN002.CoordinateField (Omega_p19 K) Pcurve
 let phiC:Polynomial K→+*L:=
   (algebraMap (Omega_p19 K) L).comp phi
 let vC:Fin 3→L:=fun i=>RCN065.componentPoint phi Pcurve i.succ
 have hSne:S.F≠0:=by
   intro hzero
   apply S.BLO
   rw [hzero]
   simp
 have hsurfaceZero:MvPolynomial.eval vC (surfaceMap phiC S.F)=0:=by
   rw [RCN136.eval_surfaceMap]
   change MvPolynomial.eval₂Hom (RCN065.componentCoefficients phi Pcurve)
     (RCN065.componentPoint phi Pcurve) S.F=0
   exact (RCN065.component_evaluation_zero_iff phi Pcurve S.F).mpr
     (RP S C)
 have hphiC:Function.Injective phiC:=
   (algebraMap (Omega_p19 K) L).injective.comp (RCN135.polynomialEmbedding_injective K)
 obtain ⟨F0,hF0mem,hF0zero⟩:=
   RCN082.exists_active_factor_of_surface_zero phiC hphiC S.F hSne vC hsurfaceZero
 have hF0spec:=RCN082.activeFactors_spec S.F F0 hF0mem
 obtain ⟨Q,hprod⟩:=hF0spec.2.1
 have hF0curve:surfaceMap phi F0∈Pcurve:=by
   rw [←RCN002.coordinateEvaluation_ker (Omega_p19 K) Pcurve]
   rw [RCN136.eval_surfaceMap] at hF0zero
   change MvPolynomial.eval₂Hom (RCN065.componentCoefficients phi Pcurve)
     (RCN065.componentPoint phi Pcurve) F0=0 at hF0zero
   rw [RCN065.component_evaluation] at hF0zero
   exact hF0zero
 have hHdecomp:surfaceMap phi (polyH K S.F)=
     surfaceMap phi (polyH K F0)*surfaceMap phi Q+
       surfaceMap phi F0*surfaceMap phi (polyH K Q):=by
   rw [hprod]
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
 have hHQnot:surfaceMap phi (polyH K F0)*surfaceMap phi Q∉Pcurve:=by
   intro hm
   apply JX S C
   rw [hHdecomp]
   exact Pcurve.add_mem hm (Pcurve.mul_mem_right _ hF0curve)
 have hQnot:surfaceMap phi Q∉Pcurve:=
   fun h=>hHQnot (Pcurve.mul_mem_left _ h)
 have hH0not:surfaceMap phi (polyH K F0)∉Pcurve:=
   fun h=>hHQnot (Pcurve.mul_mem_right _ h)
 have hGprod:S.G∣surfaceMap phi F0*surfaceMap phi Q:=by
   simpa only [←map_mul,←hprod] using S.RR
 have hGsplit:=S.MW.prime.dvd_or_dvd hGprod
 have hGQfalse:¬S.G∣surfaceMap phi Q:=by
   intro hGQ
   apply hQnot
   exact Pcurve.mem_of_dvd hGQ
     (EN (Omega_p19 K) S.G _ _ C)
 have hGF0:S.G∣surfaceMap phi F0:=hGsplit.resolve_right hGQfalse
 exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGF0,
   hF0curve,hQnot,hH0not⟩
theorem AQV
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p errors flag w support)
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
   (F0 Q:MvPolynomial (Fin 4) K) (hprod:S.F=F0*Q)
   (hGF0:S.G∣surfaceMap (RCN135.polynomialEmbedding K) F0):
   ¬F0∣numerator K F0 (w+1):=by
 intro hdiv
 let phi:=RCN135.polynomialEmbedding K
 have hscaled:S.G∣surfaceMap phi
     (Q^(2*(w+1))*numerator K F0 (w+1)):=by
   exact hGF0.trans (map_dvd (surfaceMap phi)
     (dvd_mul_of_dvd_right hdiv (Q^(2*(w+1)))))
 have hdiff:S.G∣surfaceMap phi
     (numerator K (F0*Q) (w+1)-
       Q^(2*(w+1))*numerator K F0 (w+1)):=
   hGF0.trans (map_dvd (surfaceMap phi)
     (AKK F0 Q (w+1)))
 have hwhole:S.G∣surfaceMap phi (numerator K S.F (w+1)):=by
   rw [hprod]
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using
     dvd_add hdiff hscaled
 apply hfirstProper
 exact (RCN086.globalTailCut_dvd_iff phi (RCN135.polynomialEmbedding_injective K)
   S.F (w+1) S.G).mpr hwhole
theorem CSQ
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p errors flag w support)
   (C:CM S)
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈RCN174.globalCoefficientBox K bound w seedCap slopeCap)
   (hallTails:∀delay,
     RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1+delay)∈C.1):
   RCN319.specialization (RCN002.CoordinateField (Omega_p19 K) C.1)
     (RCN065.truncatedPolynomial (RCN135.polynomialEmbedding K) C.1 S.F
       (RP S C)
       (JX S C) w)
     (coordinate (Omega_p19 K) C.1 2)
     (MvPolynomial.map (RCN065.componentCoefficients (RCN135.polynomialEmbedding K) C.1) S.F)=0:=by
 let phi:=RCN135.polynomialEmbedding K
 let Pcurve:=C.1
 let coefficients:=RCN065.componentCoefficients phi Pcurve
 let v:=RCN065.componentPoint phi Pcurve
 let hF:=RP S C
 let hH:=JX S C
 let hrel:=RCN065.component_relation phi Pcurve S.F hF
 let hreg:=RCN065.component_regular phi Pcurve S.F hH
 letI:CharP (RCN002.CoordinateField (Omega_p19 K) Pcurve) p:=
   charP_of_injective_algebraMap
     (algebraMap (Omega_p19 K) (RCN002.CoordinateField (Omega_p19 K) Pcurve)).injective p
 apply RCN139.global_polynomiality_of_all_tails coefficients S.F v hrel hreg
   p bound w seedCap slopeCap hw hshort hchar hbox
 apply (RCN047.all_tail_numerators_iff_all_tail_jets coefficients S.F v hrel hreg
   p bound w hchar).mp
 intro j hj _
 have hjbase:w+1≤j:=by omega
 have hT:=hallTails (j-(w+1))
 have heq:w+1+(j-(w+1))=j:=Nat.add_sub_of_le hjbase
 rw [heq] at hT
 have hN:surfaceMap phi (numerator K S.F j)∈Pcurve:=
   (RCN330.globalTailCut_mem_iff phi (RCN135.polynomialEmbedding_injective K)
     S.F j Pcurve).mp hT
 exact (RCN065.component_evaluation_zero_iff phi Pcurve _).mpr hN
theorem AON
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p errors flag w support)
   (C:CM S)
   (hfirstProper:¬S.G∣
     RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
   (bound seedCap slopeCap cost:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈RCN174.globalCoefficientBox K bound w seedCap slopeCap)
   (hallTails:∀delay,
     RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1+delay)∈C.1)
   (hyz:∀W:Finset
     (RCN346.Place_p19 (Omega_p19 K) (RCN002.CoordinateField (Omega_p19 K) C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate (Omega_p19 K) C.1)
       (flagSupport unitYZFlag))≤(cost:ℤ)):
   AHG (RCN135.polynomialEmbedding K) C.1 S.F
     (RP S C)
     (JX S C) w cost:=by
 classical
 let phi:=RCN135.polynomialEmbedding K
 let Pcurve:=C.1
 let L:=RCN002.CoordinateField (Omega_p19 K) Pcurve
 let kappa:K→+*L:=RCN065.componentCoefficients phi Pcurve
 let v0:Fin 4→L:=RCN065.componentPoint phi Pcurve
 let hFC:=RP S C
 let hHC:=JX S C
 let P0:Polynomial L:=RCN065.truncatedPolynomial phi Pcurve S.F hFC hHC w
 letI:CharP L p:=charP_of_injective_algebraMap
   (algebraMap (Omega_p19 K) L).injective p
 have hP0deg:P0.natDegree≤w:=
   RCN065.truncatedPolynomial_natDegree_le phi Pcurve S.F hFC hHC w
 have hSsolution:RCN319.specialization L P0 (v0 3)
     (MvPolynomial.map kappa S.F)=0:=
   CSQ S C bound seedCap slopeCap hw
     hshort hchar hbox hallTails
 obtain ⟨F0,Q,hF0irr,hF0pos,hprod,hGF0,hF0curve,hQnot,hH0not⟩:=
   ANL S C
 have hF0rel:MvPolynomial.eval₂Hom kappa v0 F0=0:=
   (RCN065.component_evaluation_zero_iff phi Pcurve F0).mpr hF0curve
 have hF0regPoint:MvPolynomial.eval₂Hom kappa v0 (polyH K F0)≠0:=
   (RCN065.component_evaluation_zero_iff phi Pcurve (polyH K F0)).not.mpr hH0not
 have hQeval:MvPolynomial.eval₂Hom kappa v0 Q≠0:=
   (RCN065.component_evaluation_zero_iff phi Pcurve Q).not.mpr hQnot
 have hvpoint:RCN231.polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0)=v0:=by
   funext i
   fin_cases i
   · rfl
   · exact RCN065.truncatedPolynomial_initial_value phi Pcurve S.F hFC hHC w
   · exact RCN065.truncatedPolynomial_initial_slope phi Pcurve S.F hFC hHC w hw
   · rfl
 have hQsolution_ne:RCN319.specialization L P0 (v0 3)
     (MvPolynomial.map kappa Q)≠0:=by
   intro hz
   apply hQeval
   calc
     MvPolynomial.eval₂Hom kappa v0 Q=
         MvPolynomial.eval₂Hom (RingHom.id L)
           (RCN231.polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0))
           (MvPolynomial.map kappa Q):=by
       rw [hvpoint,MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp]
     _=(RCN319.specialization L P0 (v0 3)
         (MvPolynomial.map kappa Q)).eval (v0 0):=by
       simpa using RCN231.eval_polynomialPoint_eq_specialization
         (RingHom.id L) P0 (v0 3) (v0 0) (MvPolynomial.map kappa Q)
     _=0:=by rw [hz];simp
 have hF0solution:RCN319.specialization L P0 (v0 3)
     (MvPolynomial.map kappa F0)=0:=by
   have hmul:RCN319.specialization L P0 (v0 3) (MvPolynomial.map kappa F0)*
       RCN319.specialization L P0 (v0 3) (MvPolynomial.map kappa Q)=0:=by
     simpa only [hprod,map_mul] using hSsolution
   exact (mul_eq_zero.mp hmul).resolve_right hQsolution_ne
 have hF0reg:RCN319.specialization L P0 (v0 3)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map kappa F0))≠0:=by
   have hmapped:MvPolynomial.eval₂Hom (RingHom.id L) v0
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map kappa F0))≠0:=by
     simpa only [polyH,MvPolynomial.pderiv_map,
       MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp] using hF0regPoint
   intro hz
   apply hmapped
   rw [←hvpoint,RCN231.eval_polynomialPoint_eq_specialization,hz]
   simp
 have hTsolution:RCN319.specialization L P0 (v0 3)
     (MvPolynomial.map kappa (numerator K F0 (w+1)))=0:=by
   rw [FCD]
   exact RCN231.specialization_numerator_zero_of_degree L (MvPolynomial.map kappa F0)
     P0 (v0 3) hF0solution (w+1) (hP0deg.trans_lt (by omega))
 have hTproper:¬F0∣numerator K F0 (w+1):=
   AQV S hfirstProper F0 Q hprod hGF0
 have htrK:Algebra.trdeg K (RCN062.baseCoefficientField (k:=K) P0 (v0 3))≤1:=
   ABA
     F0 (numerator K F0 (w+1)) P0 (v0 3)
     hF0irr hF0pos hTproper hF0solution hTsolution hF0reg
     p w S.WG hP0deg
 let k:=algebraicClosure K (Omega_p19 K)
 have htrk:Algebra.trdeg k (RCN062.baseCoefficientField (k:=k) P0 (v0 3))≤1:=
   RCN058.baseCoefficientField_trdeg_le_one_of_algebraic_constants P0 (v0 3) htrK
 letI:IsAlgClosed k:=IsAlgClosure.isAlgClosed K
 have hxK:Transcendental K (RCN135.initialCoordinate K):=by
   rw [transcendental_iff_injective]
   intro f g hfg
   apply RCN135.polynomialEmbedding_injective K
   change f.eval₂ (RCN135.coefficientEmbedding K) (RCN135.initialCoordinate K)=
     g.eval₂ (RCN135.coefficientEmbedding K) (RCN135.initialCoordinate K) at hfg
   rw [RCN135.generic_eval_eq,RCN135.generic_eval_eq] at hfg
   exact hfg
 have hxk:Transcendental k (RCN135.initialCoordinate K):=hxK.algebraicClosure
 apply AVM phi Pcurve S.F hFC hHC w cost
 · intro place j
   apply BCU P0 (v0 3) w hP0deg htrk
     (RCN135.initialCoordinate K) hxk (coordinate (Omega_p19 K) Pcurve 0)
   exact RCN065.truncatedPolynomial_initial_value phi Pcurve S.F hFC hHC w
 · exact hyz
theorem ALX
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p errors flag w support)
   (C:CM S)
   (hfirstProper:¬S.G∣
     RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
   (base:RCN341.SeparableLiteralCoordinate C.1)
   (agreements bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card=agreements+errors)
   (hagreement:∀gamma∈Gamma,
     agreements≤(S.AJW gamma).card)
   (hwa:w<agreements) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈RCN174.globalCoefficientBox K bound w seedCap slopeCap)
   (B:FE
     (G:=S.G) (T:=RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
     (H:=CR (RCN135.polynomialEmbedding K) S.F) flag tailFlag1)
   (hyzPositive:1≤B.yzCost C)
   (hallTails:∀delay,
     RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1+delay)∈C.1)
   (hyz:∀W:Finset
     (RCN346.Place_p19 (Omega_p19 K) (RCN002.CoordinateField (Omega_p19 K) C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate (Omega_p19 K) C.1)
       (flagSupport unitYZFlag))≤(B.yzCost C:ℤ)):
   (RCN264.componentSeeds (Omega_p19 K) S.G
     (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
     (CR (RCN135.polynomialEmbedding K) S.F) Gamma
     (DK (RCN135.polynomialEmbedding K) S.selected) C).card≤
       (errors+1)*B.yzCost C:=by
 classical
 let T1:=RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1)
 let H:=CR (RCN135.polynomialEmbedding K) S.F
 let Gc:=RCN264.componentSeeds (Omega_p19 K) S.G T1 H Gamma
   (DK (RCN135.polynomialEmbedding K) S.selected) C
 have hGcGamma:Gc ⊆ Gamma:=
   RCN264.componentSeeds_subset (Omega_p19 K) S.G T1 H Gamma _ C
 have hprofile:=AON
   S C hfirstProper bound seedCap slopeCap (B.yzCost C) hw hshort hchar
   hbox hallTails hyz
 apply VP
   (RCN135.polynomialEmbedding K) C.1 S.F
   (RP S C)
   (JX S C)
   base p w agreements errors (B.yzCost C)
   S.WG hwa hyzPositive hprofile
   S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
 · intro gamma hgamma
   exact S.degree_le gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact S.solution gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact S.regular gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact RCN264.componentSeeds_on_prime (Omega_p19 K) S.G T1 H Gamma
     (DK (RCN135.polynomialEmbedding K) S.selected) C gamma hgamma
 · intro gamma hgamma
   have hGamma:=hGcGamma hgamma
   exact hagreement gamma hGamma
 · exact KX S.selected Gamma Gc w errors
     hGcGamma S.BNN
end
end RCN312
end SubmissionLower
end ProximityPrize
end PackedLegacy_GM
section PackedLegacy_FT
namespace ProximityPrize
namespace SubmissionLower
namespace RCN244
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN329 RCN312 RCN219 RCN218 RCN073 RCN086 RCN330 RCN237 RCN095 RCN198 RCN287 RCN313 RCN217 RCN243 RCN072 RCN238
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
abbrev fixedSupport_p19:=support 1206 42 10
abbrev Stage_p19 (K I:Type) [Field K]
   (Gamma:Finset K) (x:I→K) (p:ℕ) [CharP (GenericField K) p]
   (flag:FlagDegree)
   (errorCap:ℕ:=RCN327.errors)
   (stageSupport:RCN275.ResidualSupportParameters:=fixedSupport_p19):=
 FH (RCN135.polynomialEmbedding K) Gamma x p errorCap flag
   RCN326.w stageSupport
variable {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
structure OriginalData_p19
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S) where
 factor:MvPolynomial (Fin 4) K
 cofactor:MvPolynomial (Fin 4) K
 irreducible:Irreducible factor
 positive:0<factor.degreeOf 1+factor.degreeOf 2+factor.degreeOf 3
 product:S.F=factor*cofactor
 factor_dvd:S.G∣surfaceMap (RCN135.polynomialEmbedding K) factor
 factor_mem:surfaceMap (RCN135.polynomialEmbedding K) factor∈C.1
 EYH:surfaceMap (RCN135.polynomialEmbedding K) cofactor∉C.1
 EMN:
   surfaceMap (RCN135.polynomialEmbedding K) (polyH K factor)∉C.1
noncomputable def originalData_p19
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):
   OriginalData_p19 S C:=by
 let h:=ANL S C
 let factor:=h.choose
 let cofactor:=h.choose_spec.choose
 have hs:=h.choose_spec.choose_spec
 exact ⟨factor,cofactor,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,
   hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2⟩
abbrev QP
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):=
 RCN218.contractedPrime (RCN135.polynomialEmbedding K) C.1
theorem factorLe_p19
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):
   RCN218.factorIdeal (originalData_p19 S C).factor≤QP S C:=
 RCN218.factorIdeal_le_contractedPrime (RCN135.polynomialEmbedding K) C.1
   (originalData_p19 S C).factor (originalData_p19 S C).factor_mem
abbrev LocalRing_p19
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):=
 FactorLocal (originalData_p19 S C).factor (QP S C) (factorLe_p19 S C)
local instance factorIdealPrime_p19
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):
   (RCN218.factorIdeal (originalData_p19 S C).factor).IsPrime:=
 RCN218.factorIdeal_isPrime _ (originalData_p19 S C).irreducible
local instance quotientPrimeInstance_p19
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):
   (RCN186.quotientPrime
     (RCN218.factorIdeal (originalData_p19 S C).factor) (QP S C)).IsPrime:=
 RCN186.quotientPrime_isPrime _ _ (factorLe_p19 S C)
noncomputable def localImage_p19
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S)
   (A:MvPolynomial (Fin 4) K):LocalRing_p19 S C:=
 RCN218.factorLocalImage (originalData_p19 S C).factor (QP S C)
   (factorLe_p19 S C) A
noncomputable def FFT
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):
   Derivation K (LocalRing_p19 S C) (LocalRing_p19 S C):=
 AXE (originalData_p19 S C).factor (QP S C)
   (factorLe_p19 S C)
theorem AXU
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S):
   surfaceMap (RCN135.polynomialEmbedding K)
     (numerator K (originalData_p19 S C).factor
       (RCN326.w+1))∈C.1:=by
 let phi:=RCN135.polynomialEmbedding K
 let d:=originalData_p19 S C
 let b:=RCN326.w+1
 have hwhole:surfaceMap phi (numerator K S.F b)∈C.1:=by
   apply (RCN330.globalTailCut_mem_iff phi (RCN135.polynomialEmbedding_injective K)
     S.F b C.1).mp
   exact GV (GenericField K) S.G
     (RCN086.globalTailCut phi S.F b) (CR phi S.F) C
 have hdiff:numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b∈
       Ideal.span ({d.factor}:Set (MvPolynomial (Fin 4) K)):=by
   exact Ideal.mem_span_singleton.mpr
     (AKR d.factor d.cofactor S.F
       d.product b)
 have hdiffMap:surfaceMap phi (numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
   exact C.1.mem_of_dvd
     (map_dvd (surfaceMap phi) (Ideal.mem_span_singleton.mp hdiff))
     d.factor_mem
 have hproduct:surfaceMap phi
     (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
   have:=C.1.sub_mem hwhole hdiffMap
   simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using this
 have hproduct':surfaceMap phi (d.cofactor^(2*b))*
     surfaceMap phi (numerator K d.factor b)∈C.1:=by
   simpa only [map_mul] using hproduct
 have hsplit:surfaceMap phi (d.cofactor^(2*b))∈C.1∨
     surfaceMap phi (numerator K d.factor b)∈C.1:=
   (inferInstance:C.1.IsPrime).mem_or_mem hproduct'
 have hcofactorPow:surfaceMap phi (d.cofactor^(2*b))∉C.1:=by
   intro hpow
   apply d.EYH
   exact (inferInstance:C.1.IsPrime).mem_of_pow_mem (2*b)
     (by simpa only [map_pow] using hpow)
 rcases hsplit with hleft | hright
 · exact False.elim (hcofactorPow (by simpa only [map_pow] using hleft))
 · exact hright
theorem DYX
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S)
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1)):
   (QP S C).height=2:=by
 let d:=originalData_p19 S C
 let N:=numerator K d.factor (RCN326.w+1)
 have hproperN:¬d.factor∣N:=
   AQV S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hheightC:C.1.height≤2:=
   RCN072.component_height_le_two (GenericField K) S.G
     (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
       (RCN326.w+1)) C.1
     (AAS (GenericField K) S.G _ _ C)
 have horiginal:=RCN219.originalPrime_height_eq_two C.1 hheightC d.factor N
   d.irreducible d.factor_mem (AXU S C) hproperN
 have heq:QP S C=RCN219.originalPrime C.1:=by
   apply Ideal.ext
   intro A
   exact (RCN218.mem_contractedPrime_iff (RCN135.polynomialEmbedding K) C.1 A).trans
     (RCN219.mem_originalPrime_iff C.1 A).symm
 rw [heq]
 exact horiginal
structure ERB (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) where
 domain:∀C:CM S,IsDomain (LocalRing_p19 S C)
 dvr:∀C:CM S,
   @IsDiscreteValuationRing (LocalRing_p19 S C) _ (domain C)
theorem DN
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1)):
   ERB S where
 domain:=fun C↦inferInstance
 dvr:=fun C↦by
   exact CWC
     (originalData_p19 S C).factor (QP S C) (factorLe_p19 S C)
     (DYX S C hfirstProper)
     (originalData_p19 S C).EMN
noncomputable def FO
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (L:ERB S)
   (C:CM S):ℕ:=by
 letI:IsDomain (LocalRing_p19 S C):=L.domain C
 letI:IsDiscreteValuationRing (LocalRing_p19 S C):=L.dvr C
 exact (IsDiscreteValuationRing.addVal (LocalRing_p19 S C)
   (localImage_p19 S C (numerator K (originalData_p19 S C).factor
     (RCN326.w+1)))).toNat
theorem ALU
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S)
   (A:MvPolynomial (Fin 4) K):
   IsUnit (localImage_p19 S C A) ↔
     surfaceMap (RCN135.polynomialEmbedding K) A∉C.1:=by
 constructor
 · intro hunit hmem
   have hnon:¬IsUnit (localImage_p19 S C A):=by
     change¬IsUnit
       (RCN218.factorLocalImage
         (originalData_p19 S C).factor (QP S C) (factorLe_p19 S C) A)
     have hmax:=
       (IsLocalization.AtPrime.to_map_mem_maximal_iff
         (LocalRing_p19 S C)
         (RCN186.quotientPrime
           (RCN218.factorIdeal (originalData_p19 S C).factor) (QP S C))
         (Ideal.Quotient.mk (RCN218.factorIdeal (originalData_p19 S C).factor) A)).2 (by
           have:A∈
               (RCN186.quotientPrime
                 (RCN218.factorIdeal (originalData_p19 S C).factor) (QP S C)).comap
                 (Ideal.Quotient.mk (RCN218.factorIdeal (originalData_p19 S C).factor)):=by
             rw [RCN186.quotientPrime_comap_quotientMk
               (RCN218.factorIdeal (originalData_p19 S C).factor) (QP S C)
               (factorLe_p19 S C)]
             exact hmem
           exact this)
     simpa only [RCN218.factorLocalImage,IsLocalRing.mem_maximalIdeal,
       mem_nonunits_iff] using hmax
   exact hnon hunit
 · intro hnot
   exact RCN218.factorLocal_image_isUnit_of_not_mem
     (originalData_p19 S C).factor A (QP S C) (factorLe_p19 S C) hnot
theorem BBO
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S) (b:ℕ):
   RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F b∈C.1 ↔
     surfaceMap (RCN135.polynomialEmbedding K)
       (numerator K (originalData_p19 S C).factor b)∈C.1:=by
 let phi:=RCN135.polynomialEmbedding K
 let d:=originalData_p19 S C
 have hscaled:numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b∈
       Ideal.span ({d.factor}:Set (MvPolynomial (Fin 4) K)):=by
   exact Ideal.mem_span_singleton.mpr
     (AKR d.factor d.cofactor S.F
       d.product b)
 have hscaledMap:surfaceMap phi (numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=
   C.1.mem_of_dvd
     (map_dvd (surfaceMap phi) (Ideal.mem_span_singleton.mp hscaled))
     d.factor_mem
 have hcofactorPow:surfaceMap phi (d.cofactor^(2*b))∉C.1:=by
   intro hpow
   apply d.EYH
   exact (inferInstance:C.1.IsPrime).mem_of_pow_mem (2*b)
     (by simpa only [map_pow] using hpow)
 rw [RCN330.globalTailCut_mem_iff phi (RCN135.polynomialEmbedding_injective K) S.F b C.1]
 constructor
 · intro hwhole
   have hproduct:surfaceMap phi
       (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
     have:=C.1.sub_mem hwhole hscaledMap
     simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using this
   have hproduct':surfaceMap phi (d.cofactor^(2*b))*
       surfaceMap phi (numerator K d.factor b)∈C.1:=by
     simpa only [map_mul] using hproduct
   exact ((inferInstance:C.1.IsPrime).mem_or_mem hproduct').resolve_left
     hcofactorPow
 · intro horiginal
   have hproduct:surfaceMap phi
       (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
     rw [map_mul]
     exact C.1.mul_mem_left _ horiginal
   have:=C.1.add_mem hscaledMap hproduct
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using this
theorem CTS
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (C:CM S)
   (A:MvPolynomial (Fin 4) K)
   (hA:¬(originalData_p19 S C).factor∣A):
   localImage_p19 S C A≠0:=by
 intro hzero
 have hquot:Ideal.Quotient.mk (RCN218.factorIdeal (originalData_p19 S C).factor) A=0:=by
   apply (IsLocalization.injective (LocalRing_p19 S C)
     (RCN186.quotientPrime
       (RCN218.factorIdeal (originalData_p19 S C).factor)
       (QP S C)).primeCompl_le_nonZeroDivisors)
   simpa only [localImage_p19,RCN218.factorLocalImage,map_zero] using hzero
 exact hA (Ideal.mem_span_singleton.mp
   (Ideal.Quotient.eq_zero_iff_mem.mp hquot))
theorem AEM
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (L:ERB S)
   (C:CM S)
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1)):
   1≤FO S L C∧
     ((∃delay,1≤delay∧delay≤FO S L C∧
       RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
         (RCN326.w+1+delay)∉C.1)∨
     (∀delay,RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
       (RCN326.w+1+delay)∈C.1)):=by
 let d:=originalData_p19 S C
 let p0:=QP S C
 let hFp:=factorLe_p19 S C
 let R:=LocalRing_p19 S C
 let D:=FFT S C
 let H:R:=localImage_p19 S C (polyH K d.factor)
 let N:ℕ→R:=fun j↦localImage_p19 S C
   (numerator K d.factor (RCN326.w+1+j))
 let coeff:ℕ→R:=fun j↦
   (2*(RCN326.w+1+j):R)
 letI:IsDomain R:=L.domain C
 letI:IsDiscreteValuationRing R:=L.dvr C
 letI:CharP K p:=
   (RCN135.coefficientEmbedding K).charP (RCN135.coefficientEmbedding_injective K) p
 letI:CharP R p:=charP_of_injective_algebraMap
   (algebraMap K R).injective p
 have hpne:p≠0:=by
   have:=S.WG
   dsimp only [RCN326.w] at this
   omega
 have hp:p.Prime:=CharP.char_prime_of_ne_zero (GenericField K) hpne
 have hproperN:¬d.factor∣
     numerator K d.factor (RCN326.w+1):=
   AQV S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hN0ne:N 0≠0:=by
   exact CTS S C _ hproperN
 have hN0nonunit:¬IsUnit (N 0):=by
   have hmem:=AXU S C
   exact (ALU S C _).not.mpr (not_not.mpr hmem)
 have hHunit:IsUnit H:=
   (ALU S C _).2 d.EMN
 have hrec:∀j,N (j+1)=
     H*D (N j)-coeff j*N j*D H:=by
   intro j
   dsimp only [N,H,D,coeff,d,localImage_p19,FFT]
   convert
     (EFV
       (originalData_p19 S C).factor (QP S C) (factorLe_p19 S C)
       (RCN326.w+1+j)) using 1<;>
     push_cast<;>ring
 have hd:=DTN D H (D H) coeff N p hp
   hrec hHunit hN0ne hN0nonunit
 change 1≤FO S L C∧_
 change 1≤(IsDiscreteValuationRing.addVal R (N 0)).toNat∧_ at hd
 refine ⟨hd.1,?_⟩
 rcases hd.2 with hproper | hpersistent
 · left
   obtain ⟨delay,hdelay1,hdelayMu,hunit⟩:=hproper
   refine ⟨delay,hdelay1,hdelayMu,?_⟩
   apply (BBO S C _).not.mpr
   exact (ALU S C _).1 hunit
 · right
   intro delay
   by_contra hnot
   apply hpersistent delay
   apply (ALU S C _).2
   exact (BBO S C _).not.mp hnot
theorem YW
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1)):
   ∀C,1≤FO S
     (DN S hfirstProper) C:=by
 intro C
 exact (AEM S
   (DN S hfirstProper) C hfirstProper).1
end
end RCN244
end SubmissionLower
end ProximityPrize
end PackedLegacy_FT
section PackedLegacy_FX
namespace ProximityPrize
namespace SubmissionLower
namespace RCN248
open RCN244 RCN135 RCN095 RCN074 RCN218 RCN186 RCN310 RCN313 RCN086 RCN217
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem BHJ
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1))
   (C:CM S):
   let d:=originalData_p19 S C
   let mu:=FO S (DN S hfirstProper) C
   ∃s:MvPolynomial (Fin 4) K,
     s∉QP S C∧
     s*numerator K d.factor
       (RCN326.w+1)∈
         RCN218.factorIdeal d.factor ⊔ QP S C^mu:=by
 let d:=originalData_p19 S C
 let family:=DN S hfirstProper
 let mu:=FO S family C
 let N:=numerator K d.factor
   (RCN326.w+1)
 let p0:=QP S C
 let I0:=RCN218.factorIdeal d.factor
 let q0:=RCN186.quotientPrime I0 p0
 let R:=LocalRing_p19 S C
 letI:IsDomain R:=family.domain C
 letI:IsDiscreteValuationRing R:=family.dvr C
 have hmuPos:1≤mu:=YW S hfirstProper C
 have horder:IsDiscreteValuationRing.addVal R (localImage_p19 S C N)=mu:=by
   change IsDiscreteValuationRing.addVal R (localImage_p19 S C N)=
     (IsDiscreteValuationRing.addVal R (localImage_p19 S C N)).toNat
   apply (ENat.coe_toNat ?_).symm
   intro htop
   change 1≤(IsDiscreteValuationRing.addVal R (localImage_p19 S C N)).toNat at hmuPos
   rw [htop] at hmuPos
   simp at hmuPos
 obtain ⟨uniformizer,hUniformizer⟩:=
   IsDiscreteValuationRing.exists_irreducible R
 have hdvd:uniformizer^mu∣localImage_p19 S C N:=by
   apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
   rw [hUniformizer.addVal_pow,horder]
 have hxMax:localImage_p19 S C N∈IsLocalRing.maximalIdeal R^mu:=by
   rw [hUniformizer.maximalIdeal_eq,Ideal.span_singleton_pow,
     Ideal.mem_span_singleton]
   exact hdvd
 haveI:I0.IsPrime:=RCN218.factorIdeal_isPrime d.factor d.irreducible
 haveI:q0.IsPrime:=RCN186.quotientPrime_isPrime I0 p0 (factorLe_p19 S C)
 exact RCN310.exists_multiplier_mem_sup_pow_of_localized_mem
   I0 p0 (factorLe_p19 S C) q0 rfl N mu hxMax
theorem AGK
   {B:Type*} [CommRing B]
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1))
   (C:CM S)
   (f:MvPolynomial (Fin 4) K→+*B)
   (surface tail scalar:B) (J:Ideal B) [J.IsMaximal]
   (hfactor:f (originalData_p19 S C).factor∈Ideal.span {surface})
   (hsurface:surface∈J)
   (hcontract:Ideal.comap f J=QP S C)
   (htail:tail=f (numerator K S.F
     (RCN326.w+1))*scalar):
   tail∈Ideal.span {surface} ⊔
     J^FO S (DN S hfirstProper) C:=by
 let d:=originalData_p19 S C
 let mu:=FO S (DN S hfirstProper) C
 let b:=RCN326.w+1
 let Nfactor:=numerator K d.factor b
 let Q:=Ideal.span {surface} ⊔ J^mu
 obtain ⟨s,hsnot,hsN⟩:=
   BHJ S hfirstProper C
 have hmapI:Ideal.map f (RCN218.factorIdeal d.factor)≤Ideal.span {surface}:=by
   rw [RCN218.factorIdeal,Ideal.map_span,Set.image_singleton,Ideal.span_le]
   exact Set.singleton_subset_iff.mpr hfactor
 have hmapP:Ideal.map f (QP S C)≤J:=by
   rw [Ideal.map_le_iff_le_comap,hcontract]
 have hmapPow:Ideal.map f (QP S C^mu)≤J^mu:=by
   rw [Ideal.map_pow]
   exact pow_le_pow_left' hmapP mu
 have htarget:Ideal.map f
     (RCN218.factorIdeal d.factor ⊔ QP S C^mu)≤Q:=by
   rw [Ideal.map_sup]
   exact sup_le (hmapI.trans le_sup_left) (hmapPow.trans le_sup_right)
 have hmul:f s*f Nfactor∈Q:=by
   rw [←map_mul]
   exact htarget (Ideal.mem_map_of_mem f hsN)
 have hfs:f s∉J:=by
   intro hsJ
   apply hsnot
   rw [←hcontract]
   exact hsJ
 have hmuPos:1≤mu:=YW S hfirstProper C
 have hNfactor:f Nfactor∈Q:=
   RCN310.mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
     surface (f Nfactor) (f s) J hsurface mu hmuPos hfs hmul
 have hdiff:d.factor∣numerator K S.F b-
     d.cofactor^(2*b)*Nfactor:=
   AKR d.factor d.cofactor S.F
     d.product b
 have hdiffMap:f (numerator K S.F b-
     d.cofactor^(2*b)*Nfactor)∈Ideal.span {surface}:=
   (Ideal.span {surface}).mem_of_dvd (map_dvd f hdiff) hfactor
 have hproduct:f (d.cofactor^(2*b)*Nfactor)∈Q:=by
   rw [map_mul]
   exact Q.mul_mem_left _ hNfactor
 have hwhole:f (numerator K S.F b)∈Q:=by
   have hdiffQ:f (numerator K S.F b-
       d.cofactor^(2*b)*Nfactor)∈Q:=
     (show Ideal.span {surface}≤Q from le_sup_left) hdiffMap
   have hadd:=Q.add_mem hdiffQ hproduct
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using hadd
 rw [htail]
 exact Q.mul_mem_right scalar hwhole
end
end RCN248
end SubmissionLower
end ProximityPrize
end PackedLegacy_FX
section PackedLegacy_FU
namespace ProximityPrize
namespace SubmissionLower
namespace RCN245
open RCN244 RCN135 RCN136 RCN074 RCN095 RCN102 RCN113 RCN120 RCN086 RCN313 RCN002 RCN011 RCN125
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K]
 {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
abbrev BXT (S:Stage_p19 K I Gamma x p flag errorCap stageSupport):=CM S
def TL (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap_p19 (GenericField K) lam mu nu order S.G
def CPZ (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap_p19 (GenericField K) lam mu nu order
   (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1))
def BKL (_S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   MvPolynomial (Fin 4) K→+*Polynomial (RCN102.FiberCoefficient q hq):=
 ((RCN102.fiberLocalizePlane q hq).comp
   (flagPlaneMap_p19 (GenericField K) lam mu nu order)).comp
     (surfaceMap (RCN135.polynomialEmbedding K))
def EZF (_S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   Polynomial (RCN102.FiberCoefficient q hq):=
 RCN102.fiberLocalizePlane q hq
   (flagPlaneMap_p19 (GenericField K) lam mu nu order
     (MvPolynomial.C ((-RCN135.polynomialEmbedding K Polynomial.X)^
       (RCN326.w+1))))
end
end RCN245
end SubmissionLower
end ProximityPrize
end PackedLegacy_FU
section PackedLegacy_FV
namespace ProximityPrize
namespace SubmissionLower
namespace RCN246
open RCN244 RCN248 RCN135 RCN136 RCN095 RCN074 RCN106 RCN107 RCN102 RCN245 RCN113 RCN120 RCN086 RCN264 RCN218 RCN313 RCN002 RCN011 RCN021 RCN125 RCN093
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem BLI
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport)
   (component:A→BXT S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀a:A,Transcendental (GenericField K)
     (RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0)))) (a:A):
   TL S lam mu nu order∈
     RCN021.relationKernel (GenericField K)
       (RCN002.CoordinateField (GenericField K) (component a).1) order
       (RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
 change RCN021.planeEvaluation (GenericField K)
   (RCN002.CoordinateField (GenericField K) (component a).1) order
     (RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
       (planeMap (GenericField K) order (flagAlgHom_p19 lam mu nu S.G))=0
 rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
 change RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
   (flagAlgHom_p19 lam mu nu S.G)=0
 rw [ACO]
 change S.G∈RingHom.ker
   (RCN002.coordinateEvaluation (GenericField K) (component a).1).toRingHom
 rw [RCN002.coordinateEvaluation_ker]
 exact EN (GenericField K) S.G _ _ (component a)
structure EGN
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (component:A→BXT S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀a:A,Transcendental (GenericField K)
     (RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:RCN106.IndexedFactorFiber component lam mu nu order ht q):Prop where
 relationMax:(RCN106.indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal
 factor_mem:BKL S lam mu nu order q hq
   (originalData_p19 S (component a.1)).factor∈
     Ideal.span {RCN107.indexedFiberSurface q hq (TL S lam mu nu order)}
 surface_mem:RCN107.indexedFiberSurface q hq (TL S lam mu nu order)∈
   RCN106.indexedFiberRelation component lam mu nu order ht q hq a
 contract:(RCN106.indexedFiberRelation component lam mu nu order ht q hq a).comap
   (BKL S lam mu nu order q hq)=QP S (component a.1)
 tail_eq:RCN107.indexedFiberTail q hq (CPZ S lam mu nu order)=
   BKL S lam mu nu order q hq
     (numerator K S.F (RCN326.w+1))*
       EZF S lam mu nu order q hq
theorem CPY
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (component:A→BXT S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀a:A,Transcendental (GenericField K)
     (RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀a:A,
     letI:=RCN120.flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (RCN002.CoordinateField (GenericField K) (component a).1))
   (hgen:∀a:A,
     letI:=RCN120.flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))}:
         Set (RCN002.CoordinateField (GenericField K) (component a).1))=⊤)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:RCN106.IndexedFactorFiber component lam mu nu order ht q):
   EGN S component lam mu nu order ht q hq a:=by
 let phi:=RCN135.polynomialEmbedding K
 let plane:=flagPlaneMap_p19 (GenericField K) lam mu nu order
 let localize:=RCN102.fiberLocalizePlane q hq
 let J:=RCN106.indexedFiberRelation component lam mu nu order ht q hq a
 refine ⟨RCN106.indexedFiberRelation_isMaximal component lam mu nu order ht
   hfinite hgen q hq a,?_,?_,?_,?_⟩
 · rw [Ideal.mem_span_singleton]
   exact map_dvd (localize.comp plane) (originalData_p19 S (component a.1)).factor_dvd
 · exact Ideal.mem_map_of_mem localize
     (BLI S component lam mu nu order ht a.1)
 · have hplane:(RCN021.relationKernel (GenericField K)
       (RCN002.CoordinateField (GenericField K) (component a.1).1) order
       (RCN093.flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap plane=(component a.1).1:=by
     change (RCN021.relationKernel (GenericField K)
       (RCN002.CoordinateField (GenericField K) (component a.1).1) order
       (RCN093.flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap
       ((planeMap (GenericField K) order).comp (flagAlgHom_p19 lam mu nu).toRingHom)=_
     rw [←Ideal.comap_comap,RCN021.relationKernel_contract,
       AEE]
   change J.comap ((localize.comp plane).comp (surfaceMap phi))=
     QP S (component a.1)
   rw [←Ideal.comap_comap,←Ideal.comap_comap,
     RCN106.indexedFiberRelation_under,hplane]
   rfl
 · change localize (plane (RCN086.globalTailCut phi S.F
     (RCN326.w+1)))=
     localize (plane (surfaceMap phi (numerator K S.F
       (RCN326.w+1))))*
       localize (plane (MvPolynomial.C
         ((-phi Polynomial.X)^(RCN326.w+1))))
   rw [RCN086.globalTailCut_eq,map_mul,map_mul]
end
end RCN246
end SubmissionLower
end ProximityPrize
end PackedLegacy_FV
section PackedLegacy_FY
namespace ProximityPrize
namespace SubmissionLower
namespace RCN249
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN074 RCN245 RCN106 RCN111 RCN095 RCN120 RCN093 RCN002
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (A:Type) [Fintype A]
structure SO where
 component:A→BXT S
 injective:Function.Injective component
 lam:GenericField K
 mu:GenericField K
 nu:GenericField K
 order:Fin 3 ≃ Fin 3
 ht:∀a,Transcendental (GenericField K)
   (RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
     (MvPolynomial.X (order 0)))
 finite:∀a,
   letI:=RCN120.flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   FiniteDimensional (RatFunc (GenericField K))
     (RCN002.CoordinateField (GenericField K) (component a).1)
 generates:∀a,
   letI:=RCN120.flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   IntermediateField.adjoin (RatFunc (GenericField K))
     ({RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 2)),
       RCN093.flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 1))}:
       Set (RCN002.CoordinateField (GenericField K) (component a).1))=⊤
 positive:0<(TL S lam mu nu order).natDegree
structure BNZ (F:SO S A) where
 q:Polynomial (RatFunc (GenericField K))
 irreducible:Irreducible q
 monic:q.Monic
 witness:RCN106.IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q
noncomputable def CQI
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:SO S A)
   (q:Polynomial (RatFunc (GenericField K))):ℕ:=
 ∑ a:RCN106.IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
   FO S (DN S hfirstProper) (F.component a.1)*
     RCN111.indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
       F.ht F.finite a.1
@[simp] theorem stageFamilyGroupedExponent_eq
   (hfirstProper:¬S.G∣RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:SO S A) (q):
   CQI S A hfirstProper F q=
     ∑ a:RCN106.IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
       FO S (DN S hfirstProper) (F.component a.1)*
         RCN111.indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
           F.ht F.finite a.1:=rfl
end
end RCN249
end SubmissionLower
end ProximityPrize
end PackedLegacy_FY
section PackedLegacy_C5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN103
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
theorem ADV
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G)
   (C:RCN264.RegularComponent Omega G T H)
   (htC:Transcendental Omega
     (RCN093.flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
   Irreducible (planeMap Omega order (flagAlgHom_p19 lam mu nu G)):=by
 let e:=RCN093.flagEvaluation Omega C.1 lam mu nu
 have hroot:e (flagAlgHom_p19 lam mu nu G)=0:=by
   rw [ACO]
   change G∈RingHom.ker (RCN002.coordinateEvaluation Omega C.1).toRingHom
   rw [RCN002.coordinateEvaluation_ker]
   exact EN Omega G T H C
 exact RCN021.planeMap_irreducible_of_evaluation Omega (RCN002.CoordinateField Omega C.1)
   order e (flagAlgHom_p19 lam mu nu G)
     ((ARZ lam mu nu G).mpr hG) hroot htC
theorem BNU
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G) (hproper:¬G∣T)
   (C:RCN264.RegularComponent Omega G T H)
   (htC:Transcendental Omega
     (RCN093.flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
   ¬planeMap Omega order (flagAlgHom_p19 lam mu nu G)∣
     planeMap Omega order (flagAlgHom_p19 lam mu nu T):=by
 let e:=RCN093.flagEvaluation Omega C.1 lam mu nu
 have hroot:e (flagAlgHom_p19 lam mu nu G)=0:=by
   rw [ACO]
   change G∈RingHom.ker (RCN002.coordinateEvaluation Omega C.1).toRingHom
   rw [RCN002.coordinateEvaluation_ker]
   exact EN Omega G T H C
 intro hdiv
 have hflagDvd:=(RCN021.planeMap_dvd_iff_of_evaluation Omega
   (RCN002.CoordinateField Omega C.1) order e
     (flagAlgHom_p19 lam mu nu G) (flagAlgHom_p19 lam mu nu T)
     ((ARZ lam mu nu G).mpr hG) hroot htC).mp hdiv
 exact hproper ((flag_dvd_iff_p19 lam mu nu G T).mp hflagDvd)
end
end RCN103
end SubmissionLower
end ProximityPrize
end PackedLegacy_C5
section PackedLegacy_K3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN108
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093 RCN120 RCN102 RCN103 RCN106 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A→RCN264.RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀a:A,Transcendental Omega
 (RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
theorem AWT
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:RCN106.IndexedFactorFiber component lam mu nu order ht q):
   letI:(Ideal.span {q}).IsPrime:=
     (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
   Disjoint (((Ideal.span {q}).primeCompl.map
     (Polynomial.C:Polynomial (RatFunc Omega)→+*PlaneRing Omega).toMonoidHom):
     Set (PlaneRing Omega))
     (Ideal.span {planeMap Omega order (flagAlgHom_p19 lam mu nu G)}:
       Set (PlaneRing Omega)):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let J:=RCN021.relationKernel Omega (RCN002.CoordinateField Omega (component a.1).1) order
   (RCN093.flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let c:Polynomial (RatFunc Omega)→+*PlaneRing Omega:=Polynomial.C
 have hcomap:J.comap c=p:=by
   rw [RCN226.relationKernel_comap_C]
   exact congrArg (fun r=>Ideal.span {r}) a.property.symm
 have hsurface:planeMap Omega order (flagAlgHom_p19 lam mu nu G)∈J:=by
   change RCN021.planeEvaluation Omega (RCN002.CoordinateField Omega (component a.1).1) order
     (RCN093.flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
       (planeMap Omega order (flagAlgHom_p19 lam mu nu G))=0
   rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
   change RCN093.flagEvaluation Omega (component a.1).1 lam mu nu
     (flagAlgHom_p19 lam mu nu G)=0
   rw [ACO]
   change G∈RingHom.ker (RCN002.coordinateEvaluation Omega (component a.1).1).toRingHom
   rw [RCN002.coordinateEvaluation_ker]
   exact EN Omega G T H (component a.1)
 rw [Set.disjoint_left]
 intro x hx hxSurface
 obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
 apply hr
 have hJ:c r∈J:=J.mem_of_dvd
   (Ideal.mem_span_singleton.mp hxSurface) hsurface
 have hrJ:r∈J.comap c:=hJ
 rw [hcomap] at hrJ
 exact hrJ
theorem BKV
   (hG:Irreducible G)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:RCN106.IndexedFactorFiber component lam mu nu order ht q):
   (Ideal.span {RCN102.fiberLocalizePlane q hq
     (planeMap Omega order (flagAlgHom_p19 lam mu nu G))}).IsPrime:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=RCN102.FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega)→+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hglobal:(Ideal.span {planeMap Omega order
     (flagAlgHom_p19 lam mu nu G)}).IsPrime:=
   Ideal.isPrime_span_singleton_of_prime
     (ADV lam mu nu order hG
       (component a.1) (ht a.1)).prime
 have hmapped:=IsLocalization.isPrime_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.span {planeMap Omega order (flagAlgHom_p19 lam mu nu G)})
     hglobal (AWT
       component lam mu nu order ht q hq a)
 change (@Ideal.span (Polynomial R) Polynomial.commSemiring.toSemiring
   {algebraMap (PlaneRing Omega) (Polynomial R)
     (planeMap Omega order (flagAlgHom_p19 lam mu nu G))}).IsPrime
 simpa only [Ideal.map_span,Set.image_singleton] using hmapped
theorem BLD
   (hG:Irreducible G) (hproper:¬G∣T)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:RCN106.IndexedFactorFiber component lam mu nu order ht q):
   RCN102.fiberLocalizePlane q hq (planeMap Omega order (flagAlgHom_p19 lam mu nu T))∉
     Ideal.span {RCN102.fiberLocalizePlane q hq
       (planeMap Omega order (flagAlgHom_p19 lam mu nu G))}:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=RCN102.FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega)→+*PlaneRing Omega:=Polynomial.C
 let f:PlaneRing Omega→+*Polynomial R:=RCN102.fiberLocalizePlane q hq
 let P:=planeMap Omega order (flagAlgHom_p19 lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom_p19 lam mu nu T)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 intro hmem
 have hunder:=IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.isPrime_span_singleton_of_prime
       (ADV lam mu nu order hG
         (component a.1) (ht a.1)).prime)
     (AWT component lam mu nu order ht q hq a)
 have hmem':f Q∈Ideal.map f (Ideal.span {P}):=by
   simpa only [Ideal.map_span,Set.image_singleton] using hmem
 have hglobal:Q∈Ideal.span {P}:=by
   have hx:Q∈(Ideal.map f (Ideal.span {P})).comap f:=hmem'
   change Q∈(Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R))
     (Ideal.span {P})).under (PlaneRing Omega) at hx
   rwa [hunder] at hx
 exact BNU lam mu nu order hG hproper
   (component a.1) (ht a.1) (Ideal.mem_span_singleton.mp hglobal)
end
end RCN108
end SubmissionLower
end ProximityPrize
end PackedLegacy_K3
section PackedLegacy_GK
namespace ProximityPrize
namespace SubmissionLower
namespace RCN308
open scoped Classical
open RCN307 RCN309
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [IsLocalRing R]
theorem APZ
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree≤m) (hQcap:Q.natDegree≤n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (pieces:J→Ideal (Polynomial R))
   (hcontains:∀j,RCN307.intersectionIdeal P Q≤pieces j)
   [Module.Finite R (∀j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)))
   (multiplicity:J→ℕ)
   (hlength:∀j,(multiplicity j:ℕ∞)≤
     Module.length R (Polynomial R ⧸ pieces j)):
   ((∑ j,multiplicity j:ℕ):ℕ∞)≤
     Ring.ord R (Polynomial.resultant P Q m n):=by
 classical
 letI:DecidableEq (Fin (m+n)):=Classical.decEq _
 let f:=Polynomial.sylvesterMap P Q hPcap hQcap
 have hinj:Function.Injective f:=by
   intro x y hxy
   apply sub_eq_zero.mp
   let z:=x-y
   have hfz:f z=0:=by simp [z,f,hxy]
   have hcomp:=LinearMap.congr_fun
     (Polynomial.adjSylvester_comp_sylveserMap P Q hPcap hQcap) z
   have hscalar:Polynomial.resultant P Q m n • z=0:=by
     rw [LinearMap.comp_apply,hfz,map_zero] at hcomp
     simpa using hcomp.symm
   exact (smul_eq_zero.mp hscalar).resolve_left hresultant
 have hbound:=
   RCN196.AZE
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f hinj
     (fun j↦Polynomial R ⧸ pieces j) multiplicity hlength
     (RCN309.cokerToPieces
       P Q m n hPcap hQcap pieces hcontains)
     (RCN309.cokerToPieces_surjective_of_modMax P Q m n hPcap hQcap
       pieces hcontains hmod)
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f=
       Polynomial.sylvester P Q m n:=by
   ext i j
   obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective j
   simpa [f,Polynomial.degreeLT.basisProd,LinearMap.toMatrix_apply] using
     congr($(Polynomial.toMatrix_sylvesterMap P Q hPcap hQcap) i j)
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞)≤
       Ring.ord R (LinearMap.toMatrix
         (Polynomial.degreeLT.basisProd R m n)
         (Polynomial.degreeLT.basis R (m+n)) f).det:=hbound
   _=Ring.ord R (Polynomial.resultant P Q m n):=by
     rw [hmatrix]
     congr 1
     unfold Polynomial.resultant
     convert! rfl
end
end RCN308
end SubmissionLower
end ProximityPrize
end PackedLegacy_GK
section PackedLegacy_EP
namespace ProximityPrize
namespace SubmissionLower
namespace RCN143
open scoped Classical BigOperators
open RCN227 RCN307 RCN309 RCN308 RCN297
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Base:Type} [Field Base] [DecidableEq Base]
variable (primeIdeal:Ideal (Polynomial Base)) [primeIdeal.IsPrime]
 (factor:Polynomial Base)
theorem AZH
   {J:Type*} [Fintype J] (multiplicity:J→ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree≤m) (hQcap:Q.natDegree≤n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (C:RCN307.PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal (LocalBase primeIdeal) •
         (⊤:Submodule (LocalBase primeIdeal)
           (∀j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j))).mkQ).comp
       (rawPiecesMap P Q m n C.pieces))):
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 have hp0:primeIdeal≠⊥:=by
   rw [hprime,ne_eq,Ideal.span_singleton_eq_bot]
   exact hfactor.ne_zero
 letI:IsDiscreteValuationRing (LocalBase primeIdeal):=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial Base) hp0 _
 have hmappedResultant:Polynomial.resultant P Q m n=
     algebraMap (Polynomial Base) (LocalBase primeIdeal)
       (Polynomial.resultant P₀ Q₀ m n):=by
   rw [hPmap,hQmap,Polynomial.resultant_map_map]
 have hmappedNe:Polynomial.resultant P Q m n≠0:=by
   rw [hmappedResultant]
   simpa only [map_zero] using
     (FaithfulSMul.algebraMap_injective
       (Polynomial Base) (LocalBase primeIdeal)).ne hresultant
 have hlocal:=
   APZ
     P Q m n hPcap hQcap hmappedNe C.pieces C.contains hmod
       multiplicity C.length_le
 have hlocal':
     (((∑ j,multiplicity j:ℕ):ℕ∞))≤
       Ring.ord (LocalBase primeIdeal)
         (algebraMap (Polynomial Base) (LocalBase primeIdeal)
           (Polynomial.resultant P₀ Q₀ m n)):=by
   rw [←hmappedResultant]
   exact hlocal
 exact RCN227.pow_sum_dvd_of_sum_le_localized_ord primeIdeal factor
   (Polynomial.resultant P₀ Q₀ m n) hprime hfactor hfactorMonic
     hresultant multiplicity hlocal'
theorem RN
   {J:Type*} [Fintype J] (multiplicity:J→ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree≤m) (hQcap:Q.natDegree≤n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (hPbar:P.map (IsLocalRing.residue (LocalBase primeIdeal))≠0)
   (C:RCN307.PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]:
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 obtain ⟨M,hMMonic,hMmem,hMdegreeP⟩:=
   RCN297.exists_specialized_monic_reducer P hPbar
 have hspan:Ideal.span {P}≤RCN307.intersectionIdeal P Q:=by
   rw [Ideal.span_le]
   intro x hx
   rw [Set.mem_singleton_iff] at hx
   subst x
   exact Ideal.subset_span (Set.mem_insert P {Q})
 have hMmem':M∈RCN307.intersectionIdeal P Q ⊔
     RCN308.coefficientMaxIdeal (R:=LocalBase primeIdeal):=
   (sup_le_sup hspan le_rfl) hMmem
 have hMdegree:M.natDegree≤m+n:=
   hMdegreeP.trans (hPcap.trans (Nat.le_add_right m n))
 have hmod:=RCN308.rawPieces_modMax_surjective_of_monic_mod
   P Q m n C.pieces C.coprime C.contains M hMMonic hMmem' hMdegree
 exact AZH
   primeIdeal factor multiplicity hprime hfactor hfactorMonic
     P₀ Q₀ m n P Q hPmap hQmap hPcap hQcap hresultant C hmod
end
end RCN143
end SubmissionLower
end ProximityPrize
end PackedLegacy_EP
section PackedLegacy_EA
namespace ProximityPrize
namespace SubmissionLower
namespace RCN109
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN102 RCN106 RCN107 RCN143 RCN307 RCN014 RCN120 RCN236 RCN110 RCN111
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A→RCN264.RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀a:A,Transcendental Omega
 (RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀a:A,
 letI:=RCN120.flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega (component a).1))
variable (hgen:∀a:A,
 letI:=RCN120.flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (RCN002.CoordinateField Omega (component a).1))=⊤)
include hcomponent hfinite hgen in
theorem BKR
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {RCN107.indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   [hlocal:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (RCN102.FiberCoefficient q hq) (Localization.AtPrime
       (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (RCN102.FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   (hbarne:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:RCN106.IndexedFactorFiber component lam mu nu order ht q→ℕ)
   (htail:∀a,RCN107.indexedFiberTail q hq tail∈
     Ideal.span {RCN107.indexedFiberSurface q hq surface} ⊔
       RCN106.indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(RCN107.indexedFiberSurface q hq surface).natDegree≤m)
   (hQcap:(RCN107.indexedFiberTail q hq tail).natDegree≤n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(RCN107.indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (RCN102.FiberCoefficient q hq))≠0):
   q^(∑ a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*Module.finrank
       (IsLocalRing.ResidueField (RCN102.FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a))))∣
     Polynomial.resultant surface tail m n:=by
 letI:DecidableEq (RatFunc Omega):=Classical.decEq _
 letI:(Ideal.span {q}).IsPrime:=
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 let weight:RCN106.IndexedFactorFiber component lam mu nu order ht q→ℕ:=fun a=>
   Module.finrank (IsLocalRing.ResidueField (RCN102.FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a)))
 let cert:=BJB component hcomponent lam mu nu
   order ht hfinite hgen q hq surface tail hbarne multiplicity htail
     (hlocal:=hlocal) (hresfinite:=hresfinite)
 letI:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     Module.Finite (RCN102.FiberCoefficient q hq)
       (Polynomial (RCN102.FiberCoefficient q hq) ⧸ cert.pieces a):=fun a=>by
   obtain ⟨M,hMmonic,hMmem⟩:=RCN107.exists_monic_mem_indexedFiberRelation
     component lam mu nu order ht hfinite hgen q hq a
   apply RCN309.moduleFinite_quotient_of_monic_mem
     (cert.pieces a) (M^multiplicity a) (hMmonic.pow _)
   have hpow:M^multiplicity a∈
       Ideal.span {RCN107.indexedFiberSurface q hq surface} ⊔
         RCN106.indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a:=
     (show RCN106.indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a≤
         Ideal.span {RCN107.indexedFiberSurface q hq surface} ⊔
           RCN106.indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a
       from le_sup_right) (Ideal.pow_mem_pow hMmem (multiplicity a))
   simpa [cert,BJB,
     RCN236.primaryPiecesCertificateOfMembershipWeighted,RCN014.mappedPrimaryPiece] using hpow
 letI:Module.Finite (RCN102.FiberCoefficient q hq)
     (∀a,Polynomial (RCN102.FiberCoefficient q hq) ⧸ cert.pieces a):=inferInstance
 exact RN
   (Ideal.span {q}) q (fun a=>multiplicity a*weight a)
     rfl hq hqMonic surface tail m n
     (RCN107.indexedFiberSurface q hq surface) (RCN107.indexedFiberTail q hq tail)
     rfl rfl hPcap hQcap hresultant hPbar cert
include hcomponent hfinite hgen in
theorem ACC
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {RCN107.indexedFiberSurface q hq surface}).IsPrime]
   (hsurface:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     surface∈RCN021.relationKernel Omega (RCN002.CoordinateField Omega (component a.1).1) order
       (RCN093.flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (hbarne:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:RCN106.IndexedFactorFiber component lam mu nu order ht q→ℕ)
   (htail:∀a,RCN107.indexedFiberTail q hq tail∈
     Ideal.span {RCN107.indexedFiberSurface q hq surface} ⊔
       RCN106.indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(RCN107.indexedFiberSurface q hq surface).natDegree≤m)
   (hQcap:(RCN107.indexedFiberTail q hq tail).natDegree≤n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(RCN107.indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (RCN102.FiberCoefficient q hq))≠0):
   q^(∑ a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*RCN111.indexedPlaneResidueWeight component lam mu nu order
       ht hfinite a.1)∣Polynomial.resultant surface tail m n:=by
 letI:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal:=
   fun a=>RCN107.indexedFiberRelationBar_isMaximal component lam mu nu order ht
     hfinite hgen q hq surface hsurface a
 letI:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (RCN102.FiberCoefficient q hq) (Localization.AtPrime
       (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a=>RCN110.indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht
     hfinite q hq surface a
 letI:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (RCN102.FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a=>RCN110.indexedNaturalSurfaceResidue_finite component lam mu nu order ht
     hfinite hgen q hq surface a (hsurface a)
 have hpow:=BKR component hcomponent
   lam mu nu order ht hfinite hgen q hq hqMonic surface tail m n hbarne
     multiplicity htail hPcap hQcap hresultant hPbar
 have hweight:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     Module.finrank (IsLocalRing.ResidueField (RCN102.FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
       RCN111.indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=
   fun a=>RCN110.indexedNaturalSurfaceResidue_finrank_eq_plane component lam mu nu
     order ht hfinite hgen q hq surface a (hsurface a)
 simpa only [hweight] using hpow
end
end RCN109
end SubmissionLower
end ProximityPrize
end PackedLegacy_EA
section PackedLegacy_N3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN255
open RCN135 RCN136 RCN244 RCN249 RCN245 RCN106 RCN103 RCN093 RCN095 RCN125 RCN011 RCN021
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
theorem CVJ
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega) (hirr:Irreducible surface)
   (hpositive:0<surface.natDegree):
   surface.map (AdjoinRoot.mk q)≠0:=by
 letI:Fact (Irreducible q):=⟨hq⟩
 have hcoeff:Polynomial.eval₂RingHom
     (algebraMap (RatFunc Omega) (AdjoinRoot q))
       (AdjoinRoot.root q)=AdjoinRoot.mk q:=by
   apply Polynomial.ringHom_ext
   · intro c
     simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
       AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
   · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,AdjoinRoot.mk_X]
 have hs:=RCN360.ABJ
   (algebraMap (RatFunc Omega) (AdjoinRoot q)) surface
   (hirr.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root q)
 rw [RCN360.ART,hcoeff] at hs
 exact hs
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
def CIZ
   (F:SO S A)
   (q:Polynomial (RatFunc (GenericField K))):Prop:=
 (TL S F.lam F.mu F.nu F.order).map (AdjoinRoot.mk q)≠0
theorem COL
   (F:SO S A)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:RCN106.IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q):
   CIZ S F q:=by
 change (planeMap (GenericField K) F.order
   (flagAlgHom_p19 F.lam F.mu F.nu S.G)).map (AdjoinRoot.mk q)≠0
 exact CVJ q hq
   (planeMap (GenericField K) F.order (flagAlgHom_p19 F.lam F.mu F.nu S.G))
   (ADV F.lam F.mu F.nu F.order S.MW
     (F.component a.1) (F.ht a.1)) F.positive
end
end RCN255
end SubmissionLower
end ProximityPrize
end PackedLegacy_N3
section PackedLegacy_C4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN112
open RCN095 RCN125 RCN093 RCN123 RCN121 RCN103 RCN012 RCN011 RCN264
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
local instance:DecidableEq (RatFunc Omega):=Classical.decEq _
variable {G T H:MvPolynomial (Fin 3) Omega}
def RW (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (G T:MvPolynomial (Fin 3) Omega):Polynomial (RatFunc Omega):=
 let P:=planeMap Omega order (flagAlgHom_p19 lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom_p19 lam mu nu T)
 Polynomial.resultant P Q P.natDegree Q.natDegree
theorem BQT
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (RW lam mu nu zOrder_p19 G T).natDegree≤
     flagMixed surfaceFlag tailFlag unitZFlag:=by
 let gCaps:=LQ surfaceFlag G lam mu nu hGsupport
 let tCaps:=LQ tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega zOrder_p19 (flagAlgHom_p19 lam mu nu G))
   (planeMap Omega zOrder_p19 (flagAlgHom_p19 lam mu nu T))).natDegree≤_
 exact XY Omega zOrder_p19
   (flagAlgHom_p19 lam mu nu G) (flagAlgHom_p19 lam mu nu T)
   surfaceFlag.all tailFlag.all (surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.yz+tailFlag.all) (flagMixed surfaceFlag tailFlag unitZFlag)
   (flag_ne_zero_p19 lam mu nu hTne) gCaps.zOuter tCaps.zOuter
   gCaps.zTotal tCaps.zTotal (RCN121.z_flag_trapezoid_budget surfaceFlag tailFlag)
theorem BRJ
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (RW lam mu nu uOrder_p19 G T).natDegree≤
     flagMixed surfaceFlag tailFlag unitYZFlag:=by
 let gCaps:=LQ surfaceFlag G lam mu nu hGsupport
 let tCaps:=LQ tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega uOrder_p19 (flagAlgHom_p19 lam mu nu G))
   (planeMap Omega uOrder_p19 (flagAlgHom_p19 lam mu nu T))).natDegree≤_
 exact XY Omega uOrder_p19
   (flagAlgHom_p19 lam mu nu G) (flagAlgHom_p19 lam mu nu T)
   surfaceFlag.all tailFlag.all
   (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
   (flagMixed surfaceFlag tailFlag unitYZFlag)
   (flag_ne_zero_p19 lam mu nu hTne) gCaps.uOuter tCaps.uOuter
   gCaps.uTotal tCaps.uTotal (RCN121.u_flag_trapezoid_budget surfaceFlag tailFlag)
theorem BRI
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (RW lam mu nu vOrder_p19 G T).natDegree≤
     flagMixed surfaceFlag tailFlag unitAllFlag:=by
 let gCaps:=LQ surfaceFlag G lam mu nu hGsupport
 let tCaps:=LQ tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega vOrder_p19 (flagAlgHom_p19 lam mu nu G))
   (planeMap Omega vOrder_p19 (flagAlgHom_p19 lam mu nu T))).natDegree≤_
 exact XY Omega vOrder_p19
   (flagAlgHom_p19 lam mu nu G) (flagAlgHom_p19 lam mu nu T)
   (surfaceFlag.yz+surfaceFlag.all) (tailFlag.yz+tailFlag.all)
   (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
   (flagMixed surfaceFlag tailFlag unitAllFlag)
   (flag_ne_zero_p19 lam mu nu hTne) gCaps.vOuter tCaps.vOuter
   gCaps.vTotal tCaps.vTotal (RCN121.v_flag_trapezoid_budget surfaceFlag tailFlag)
end
end RCN112
end SubmissionLower
end ProximityPrize
end PackedLegacy_C4
section PackedLegacy_FZ
namespace ProximityPrize
namespace SubmissionLower
namespace RCN250
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN245 RCN249 RCN102 RCN106 RCN107 RCN109 RCN120 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
def DYC
   (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) (F:SO S A)
   (W:BNZ S A F):Prop:=
 (RCN107.indexedFiberSurface W.q W.irreducible
   (TL S F.lam F.mu F.nu F.order)).map
     (IsLocalRing.residue (RCN102.FiberCoefficient W.q W.irreducible))≠0
end
end RCN250
end SubmissionLower
end ProximityPrize
end PackedLegacy_FZ
section PackedLegacy_N0
namespace ProximityPrize
namespace SubmissionLower
namespace RCN252
open RCN135 RCN136 RCN074 RCN244 RCN249 RCN245 RCN106 RCN107 RCN108 RCN103 RCN102 RCN195 RCN255 RCN250 RCN093 RCN095 RCN002 RCN011 RCN021
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage_p19 K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem CQH
   (F:SO S A) (W:BNZ S A F):
   DYC S F W:=by
 rcases W with ⟨q,hq,_hqMonic,⟨a,hqeq⟩⟩
 let surface:=TL S F.lam F.mu F.nu F.order
 have hspecial:=COL S F q hq
   (⟨a,hqeq⟩:RCN106.IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q)
 change surface.map (AdjoinRoot.mk q)≠0 at hspecial
 change (RCN107.indexedFiberSurface q hq surface).map
   (IsLocalRing.residue (RCN102.FiberCoefficient q hq))≠0
 subst q
 exact RCN195.localized_surface_residue_ne_zero (GenericField K)
   (RCN002.CoordinateField (GenericField K) (F.component a).1) F.order
   (RCN093.flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu) (F.ht a)
   (F.finite a) surface hspecial
end
end RCN252
end SubmissionLower
end ProximityPrize
end PackedLegacy_N0
section PackedLegacy_Q0
namespace ProximityPrize
namespace SubmissionLower
namespace RCN333
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN249 RCN252 RCN255 RCN250 RCN247 RCN245 RCN106 RCN107 RCN108 RCN102 RCN103 RCN109 RCN112 RCN113 RCN264 RCN120 RCN243 RCN111 RCN093 RCN095 RCN125 RCN066 RCN336 RCN226 RCN002 RCN011 RCN021
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 80000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem AFZ
   {Omega:Type} [Field Omega]
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental Omega
     (RCN093.flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   {A:MvPolynomial (Fin 3) Omega} (hA:A ∈ P):
   flagPlaneMap_p19 Omega lam mu nu order A ∈
     RCN021.relationKernel Omega (RCN002.CoordinateField Omega P) order
       (RCN093.flagEvaluation Omega P lam mu nu) ht:=by
 change RCN021.planeEvaluation Omega (RCN002.CoordinateField Omega P) order
   (RCN093.flagEvaluation Omega P lam mu nu) ht
     (planeMap Omega order (flagAlgHom_p19 lam mu nu A))=0
 rw [← RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
 change RCN093.flagEvaluation Omega P lam mu nu (flagAlgHom_p19 lam mu nu A)=0
 rw [ACO]
 change A ∈ RingHom.ker (RCN002.coordinateEvaluation Omega P).toRingHom
 rw [RCN002.coordinateEvaluation_ker]
 exact hA
@[simp] theorem EMZ
   {Omega:Type} [Field Omega] (lam mu nu:Omega)
   (order:Fin 3 ≃ Fin 3) (A:MvPolynomial (Fin 3) Omega):
   flagPlaneMap_p19 Omega lam mu nu order A=
     planeMap Omega order (flagAlgHom_p19 lam mu nu A):=rfl
end
end RCN333
end SubmissionLower
end ProximityPrize
end PackedLegacy_Q0
section PackedLegacy_A1
namespace ProximityPrize
namespace SubmissionLower
namespace RCN031
open RCN002 RCN264 RCN341 RCN037 RCN038 RCN093 RCN125 RCN116 RCN120 RCN021 RCN022
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀C:RCN264.RegularComponent Omega G T H,
 RCN341.SeparableLiteralCoordinate C.1)
variable (hactive:∀C:RCN264.RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀C:RCN264.RegularComponent Omega G T H,RCN037.LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:JO base hactive hSderiv)
abbrev AFR:={C:RCN264.RegularComponent Omega G T H//
 Transcendental Omega (coordinate Omega C.1 2)}
def AHA:AFR (G:=G) (T:=T) (H:=H)→
   RCN264.RegularComponent Omega G T H:=Subtype.val
def PL
   (a:AFR (G:=G) (T:=T) (H:=H)):
   Transcendental Omega
     (RCN093.flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder_p19 0))):=by
 simpa [zOrder_p19,Equiv.swap_apply_def] using a.2
def PJ (C:RCN264.RegularComponent Omega G T H):
   Transcendental Omega
     (RCN093.flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder_p19 0))):=by
 simpa [uOrder_p19] using D.ZG C
def PK (C:RCN264.RegularComponent Omega G T H):
   Transcendental Omega
     (RCN093.flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder_p19 0))):=by
 simpa [vOrder_p19,Equiv.swap_apply_def] using D.GN C
include hZ in
theorem DUX
   (a:AFR (G:=G) (T:=T) (H:=H))
   (hx:Transcendental Omega
     (RCN093.flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder_p19 0)))):
   (letI:=RCN120.flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder_p19 hx
    FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega a.1.1))∧
   (letI:=RCN120.flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder_p19 hx
    Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega a.1.1)):=by
 have hx':Transcendental Omega (coordinate Omega a.1.1 2):=by
   simpa [zOrder_p19,Equiv.swap_apply_def] using hx
 have hemb:=RCN116.elementEmbedding_congr hx hx' (by simp [zOrder_p19,RCN093.flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega a.1.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega a.1.1))∧
   (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega a.1.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega a.1.1))
 rw [hemb]
 exact hZ a.1 hx'
theorem DRV (C:RCN264.RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (RCN093.flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder_p19 0)))):
   (letI:=RCN120.flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder_p19 hx
    FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1))∧
   (letI:=RCN120.flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder_p19 hx
    Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1)):=by
 have hx':Transcendental Omega (affineU Omega C.1 D.lam):=by
   simpa [uOrder_p19] using hx
 have hemb:=RCN116.elementEmbedding_congr hx hx' (by simp [uOrder_p19,RCN093.flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1))
 rw [hemb]
 exact D.uGate C hx'
theorem DUY (C:RCN264.RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (RCN093.flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder_p19 0)))):
   (letI:=RCN120.flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder_p19 hx
    FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1))∧
   (letI:=RCN120.flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder_p19 hx
    Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1)):=by
 have hemb:=RCN116.elementEmbedding_congr hx (D.GN C)
   (by simp [vOrder_p19,RCN093.flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1))
 rw [hemb]
 exact ⟨D.allFinite C,D.allSeparable C⟩
def DFP (a:AFR (G:=G) (T:=T) (H:=H)):=
 (DUX base hactive hZ hSderiv D a
   (PL base hactive hSderiv D a)).1
def DFL (C:RCN264.RegularComponent Omega G T H):=
 (DRV base hactive hSderiv D C
   (PJ base hactive hSderiv D C)).1
def DGE (C:RCN264.RegularComponent Omega G T H):=
 (DUY base hactive hSderiv D C
   (PK base hactive hSderiv D C)).1
end
end RCN031
end SubmissionLower
end ProximityPrize
end PackedLegacy_A1
section PackedLegacy_A0
namespace ProximityPrize
namespace SubmissionLower
namespace RCN029
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN037 RCN038 RCN125 RCN031 RCN106 RCN111 RCN112
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀C:RCN264.RegularComponent Omega G T H,
 RCN341.SeparableLiteralCoordinate C.1)
variable (hactive:∀C:RCN264.RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀C:RCN264.RegularComponent Omega G T H,RCN037.LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:JO base hactive hSderiv)
 (multiplicity:RCN264.RegularComponent Omega G T H→ℕ)
def EOM:Prop:=
 ∀q (hq:Irreducible q) (hm:q.Monic)
   (a₀:RCN106.IndexedFactorFiber
     (AHA (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder_p19
     (PL base hactive hSderiv D) q),
   q^(∑ a:RCN106.IndexedFactorFiber
     (AHA (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder_p19
     (PL base hactive hSderiv D) q,
     multiplicity a.1.1*RCN111.indexedPlaneResidueWeight
       (AHA (G:=G) (T:=T) (H:=H))
       D.lam D.mu (D.mu*D.lam) zOrder_p19
       (PL base hactive hSderiv D)
       (DFP base hactive hZ hSderiv D) a.1)∣
     RW D.lam D.mu (D.mu*D.lam) zOrder_p19 G T
def ENU:Prop:=
 ∀q (hq:Irreducible q) (hm:q.Monic)
   (C₀:RCN106.IndexedFactorFiber (fun C:RCN264.RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder_p19
     (PJ base hactive hSderiv D) q),
   q^(∑ C:RCN106.IndexedFactorFiber (fun C:RCN264.RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder_p19
     (PJ base hactive hSderiv D) q,
     multiplicity C.1*RCN111.indexedPlaneResidueWeight
       (fun C:RCN264.RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) uOrder_p19
       (PJ base hactive hSderiv D)
       (DFL base hactive hSderiv D) C.1)∣
     RW D.lam D.mu (D.mu*D.lam) uOrder_p19 G T
def EOL:Prop:=
 ∀q (hq:Irreducible q) (hm:q.Monic)
   (C₀:RCN106.IndexedFactorFiber (fun C:RCN264.RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder_p19
     (PK base hactive hSderiv D) q),
   q^(∑ C:RCN106.IndexedFactorFiber (fun C:RCN264.RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder_p19
     (PK base hactive hSderiv D) q,
     multiplicity C.1*RCN111.indexedPlaneResidueWeight
       (fun C:RCN264.RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) vOrder_p19
       (PK base hactive hSderiv D)
       (DGE base hactive hSderiv D) C.1)∣
     RW D.lam D.mu (D.mu*D.lam) vOrder_p19 G T
structure ARH:Prop where
 z:EOM base hactive hZ hSderiv D multiplicity
 u:ENU base hactive hSderiv D multiplicity
 v:EOL base hactive hSderiv D multiplicity
end
end RCN029
end SubmissionLower
end ProximityPrize
end PackedLegacy_A0
section PackedLegacy_DJ
namespace ProximityPrize
namespace SubmissionLower
namespace RCN030
open RCN002 RCN264 RCN341 RCN042 RCN344 RCN037 RCN038 RCN040 RCN046 RCN237 RCN095 RCN093 RCN125 RCN116 RCN022 RCN031
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀C:RCN264.RegularComponent Omega G T H,
 RCN341.SeparableLiteralCoordinate C.1)
variable (hactive:∀C:RCN264.RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀C:RCN264.RegularComponent Omega G T H,RCN037.LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:JO base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
noncomputable def NJ:
   EE base surfaceFlag tailFlag:=
 ALJ surfaceFlag tailFlag base hactive
   hZ hSderiv D hG hproper hGsupport hTsupport
end
end RCN030
end SubmissionLower
end ProximityPrize
end PackedLegacy_DJ
section PackedLegacy_AN
namespace ProximityPrize
namespace SubmissionLower
namespace RCN343
open scoped Classical BigOperators
open RCN337
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Base:Type} [Field Base] [DecidableEq Base]
structure LB
   {I:Type*} [Fintype I]
   (multiplicity cost:I→ℕ) (budget:ℕ) where
 resultant:Polynomial Base
 factor:I→Polynomial Base
 BTG:I→ℕ
 resultant_ne:resultant≠0
 factor_irreducible:∀i,Irreducible (factor i)
 factor_monic:∀i,(factor i).Monic
 CUZ:∀f∈Finset.univ.image factor,
   f^(∑ i with factor i=f,multiplicity i*BTG i)∣resultant
 cost_le_residue_mul_degree:∀i,
   cost i≤BTG i*(factor i).natDegree
 BHX:resultant.natDegree≤budget
theorem LB.CTA
   {I:Type*} [Fintype I]
   {multiplicity cost:I→ℕ} {budget:ℕ}
   (C:LB
     (Base:=Base) multiplicity cost budget):
   (∑ i,multiplicity i*cost i)≤budget:=by
 let weightedMultiplicity:I→ℕ:=fun i↦
   multiplicity i*C.BTG i
 have hfactor:=RCN337.sum_grouped_power_factor_degrees_le
   C.resultant C.factor weightedMultiplicity C.resultant_ne
     C.factor_irreducible C.factor_monic C.CUZ
 calc
   (∑ i,multiplicity i*cost i)≤
       ∑ i,multiplicity i*
         (C.BTG i*(C.factor i).natDegree):=
     Finset.sum_le_sum (fun i _↦
       Nat.mul_le_mul_left (multiplicity i)
         (C.cost_le_residue_mul_degree i))
   _=∑ i,weightedMultiplicity i*(C.factor i).natDegree:=by
     apply Finset.sum_congr rfl
     intro i _
     simp only [weightedMultiplicity,Nat.mul_assoc]
   _≤C.resultant.natDegree:=hfactor
   _≤budget:=C.BHX
end
end RCN343
end SubmissionLower
end ProximityPrize
end PackedLegacy_AN
section PackedLegacy_K1
namespace ProximityPrize
namespace SubmissionLower
namespace RCN104
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN106 RCN111 RCN105 RCN120 RCN226 RCN042 RCN344 RCN343
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A→RCN264.RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀a:A,Transcendental Omega
 (RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀a:A,
 letI:=RCN120.flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega (component a).1))
variable (hgen:∀a:A,
 letI:=RCN120.flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (RCN002.CoordinateField Omega (component a).1))=⊤)
include hgen in
noncomputable def RI
   (hgate:∀a:A,∀hx:Transcendental Omega
       (RCN093.flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega (component a).1):=
         RCN120.flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega (component a).1):=
         RCN120.flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega (component a).1)))
   (multiplicity:A→ℕ)
   (resultant:Polynomial (RatFunc Omega)) (budget:ℕ)
   (hresultant:resultant≠0)
   (hdegree:resultant.natDegree≤budget)
   (hfixed:∀(q:Polynomial (RatFunc Omega))
     (hq:Irreducible q) (hqMonic:q.Monic)
     (a₀:RCN106.IndexedFactorFiber component lam mu nu order ht q),
     q^(∑ a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
       multiplicity a.1*RCN111.indexedPlaneResidueWeight component
         lam mu nu order ht hfinite a.1)∣resultant):
   LB (Base:=RatFunc Omega) multiplicity
     (fun a↦RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega (component a).1)
       (RCN042.coordinateOfGate
         (RCN093.flagEvaluation Omega (component a).1 lam mu nu
           (MvPolynomial.X (order 0))) (hgate a))) budget:=by
 let factor:=RCN106.indexedComponentFactor component lam mu nu order ht
 let weight:=RCN111.indexedPlaneResidueWeight component lam mu nu order ht hfinite
 refine {
   resultant:=resultant
   factor:=factor
   BTG:=weight
   resultant_ne:=hresultant
   factor_irreducible:=?_
   factor_monic:=?_
   CUZ:=?_
   cost_le_residue_mul_degree:=?_
   BHX:=hdegree}
 · intro a
   exact RCN226.projectedFactor_irreducible Omega
     (RCN002.CoordinateField Omega (component a).1) order
       (RCN093.flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro a
   exact RCN226.projectedFactor_monic Omega
     (RCN002.CoordinateField Omega (component a).1) order
       (RCN093.flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro q hqmem
   obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hqmem
   subst q
   have hqirr:Irreducible (factor a):=RCN226.projectedFactor_irreducible Omega
     (RCN002.CoordinateField Omega (component a).1) order
       (RCN093.flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   have hqmonic:(factor a).Monic:=RCN226.projectedFactor_monic Omega
     (RCN002.CoordinateField Omega (component a).1) order
       (RCN093.flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   let a₀:RCN106.IndexedFactorFiber component lam mu nu order ht (factor a):=⟨a,rfl⟩
   have hpow:=hfixed (factor a) hqirr hqmonic a₀
   have hsum:
       (∑ b with factor b=factor a,multiplicity b*weight b)=
         ∑ b:RCN106.IndexedFactorFiber component lam mu nu order ht (factor a),
           multiplicity b.1*weight b.1:=by
     simpa only [Finset.subtype_univ,eq_comm] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset A))
         (fun b↦multiplicity b*weight b)
         (p:=fun b↦factor a=factor b)).symm
   rw [hsum]
   exact hpow
 · intro a
   have hcost:=RCN105.indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
     component lam mu nu order ht hfinite hgen hgate a
   simpa only [factor,weight,Nat.mul_comm] using hcost.le
end
end RCN104
end SubmissionLower
end ProximityPrize
end PackedLegacy_K1
section PackedLegacy_Q1
namespace ProximityPrize
namespace SubmissionLower
namespace RCN334
open scoped Classical BigOperators
open RCN135 RCN136 RCN319 RCN174 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN090 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN037 RCN038 RCN042 RCN341 RCN312 RCN339 RCN330 RCN002 RCN344
open RCN319 renaming specialization → BM
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
 {tightSupport:RCN275.ResidualSupportParameters}
def MU
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport):
   Stage_p19 K I Gamma x p flag stageErrorCap tightSupport:=S
theorem ADP
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬S.G ∣ RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1)):
   ∀C,1≤FO (MU S)
     (DN (MU S) hfirstProper) C:=by
 exact YW (MU S) hfirstProper
structure ABN
   {a b s:ℕ}
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) where
 base:∀C:RCN264.RegularComponent (GenericField K) S.G
     (RCN089.reducedGlobalTailCut (RCN135.polynomialEmbedding K) (support a b s) S.F (w+1))
     (CR (RCN135.polynomialEmbedding K) S.F),
   RCN341.SeparableLiteralCoordinate C.1
 hactive:∀C:RCN264.RegularComponent (GenericField K) S.G
     (RCN089.reducedGlobalTailCut (RCN135.polynomialEmbedding K) (support a b s) S.F (w+1))
     (CR (RCN135.polynomialEmbedding K) S.F),
   KaehlerDifferential.D (GenericField K) (RCN002.CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 0) ≠ 0∨
     KaehlerDifferential.D (GenericField K) (RCN002.CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 2) ≠ 0
 hZ:∀C:RCN264.RegularComponent (GenericField K) S.G
     (RCN089.reducedGlobalTailCut (RCN135.polynomialEmbedding K) (support a b s) S.F (w+1))
     (CR (RCN135.polynomialEmbedding K) S.F),RCN037.LiteralProjectionGate C 2
 data:JO base hactive
   (RCN315.EH S)
 lam_poly:data.lam∈Set.range (RCN135.polynomialEmbedding K)
 mu_poly:data.mu∈Set.range (RCN135.polynomialEmbedding K)
theorem AFC
   {tailFlag1:FlagDegree}
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬S.G ∣ RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
   (B:FE
     (G:=S.G) (T:=RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
     (H:=CR (RCN135.polynomialEmbedding K) S.F) flag tailFlag1)
   (htangent:∀C:CM S,
     (∀delay,RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
       (w+1+delay) ∈ C.1)→
     (RCN264.componentSeeds (GenericField K) S.G
       (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
       (CR (RCN135.polynomialEmbedding K) S.F) Gamma
       (DK (RCN135.polynomialEmbedding K) S.selected) C).card≤
         (stageErrorCap+1)*B.yzCost C):
   ∀C:CM S,
     (∃delay,1≤delay∧
       delay≤FO (MU S)
         (DN (MU S) hfirstProper) C∧
       RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1+delay) ∉ C.1)∨
     ((∀delay,RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F
         (w+1+delay) ∈ C.1)∧
       (RCN264.componentSeeds (GenericField K) S.G
         (RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1))
         (CR (RCN135.polynomialEmbedding K) S.F) Gamma
         (DK (RCN135.polynomialEmbedding K) S.selected) C).card≤
           (stageErrorCap+1)*B.yzCost C):=by
 intro C
 have dichotomy:=AEM (MU S)
   (DN (MU S) hfirstProper)
   C hfirstProper
 rcases dichotomy.2 with hproper | hall
 · exact Or.inl hproper
 · exact Or.inr ⟨hall,htangent C hall⟩
end
end RCN334
end SubmissionLower
end ProximityPrize
end PackedLegacy_Q1
section PackedLegacy_P9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN332
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN334 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN042 RCN341 RCN002 RCN344 RCN340
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I→K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
def VQ
   {a b s:ℕ}
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)):MvPolynomial (Fin 3) (GenericField K):=
 RCN089.reducedGlobalTailCut (RCN135.polynomialEmbedding K) (support a b s) S.F (w+1)
theorem EW
   {a b s:ℕ}
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)):
   S.G ∣ RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1)-
     VQ S:=
 S.RR.trans
   (RCN089.globalTailCut_sub_reduced_dvd (RCN135.polynomialEmbedding K) (support a b s)
     S.F (w+1))
theorem AHF
   {a b s:ℕ}
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬S.G ∣ RCN086.globalTailCut (RCN135.polynomialEmbedding K) S.F (w+1)):
   ¬S.G ∣ VQ S:=by
 intro hr
 apply hfirstProper
 have h:=(EW S).add hr
 simpa only [VQ,sub_add_cancel] using h
theorem AFM
   {a b s:ℕ}
   (S:FH (RCN135.polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)):
   RCN095.PolynomialInFlag (RCN263.reducedResidualAgreementFlag (support a b s) (w+1))
     (VQ S):=by
 exact AOF (RCN135.polynomialEmbedding K) (support a b s)
   ⟨S.AFS,S.ACG,S.UT⟩ (w+1)
end
end RCN332
end SubmissionLower
end ProximityPrize
end PackedLegacy_P9
section PackedLegacy_J4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN087
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275
open RCN319 renaming specialization → BM
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 25000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K→+*Ω} {Γ:Finset K} {x:I→K}
 {p e:ℕ} [CharP Ω p]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
local instance:DecidableEq I:=Classical.decEq I
def AEO
   {flag:FlagDegree} {w:ℕ} {support:RCN275.ResidualSupportParameters}
   (S:FH φ Γ x p e flag w support) (DS:ℕ):Prop:=
 ∀i∈S.nodes,
   let T:=FK φ S.F w (x i) (S.u0 i) (S.u1 i)
   (hproper:¬S.G∣T)→
   let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
   ∃cost:RCN264.RegularComponent Ω S.G T (CR φ S.F)→ℕ,
     (∀C,(RCN264.componentSeeds Ω S.G T (CR φ S.F) Gi
       (DK φ S.selected) C).card≤(e+1)*cost C)∧
     (∑ C,cost C)≤DS
theorem ETI
   {flag:FlagDegree} {w:ℕ} {support:RCN275.ResidualSupportParameters}
   (S:FH φ Γ x p e flag w support)
   (DS:ℕ) (hprovider:AEO S DS)
   (i:I) (hi:i∈S.nodes)
   (hproper:¬S.G∣FK φ S.F w (x i) (S.u0 i) (S.u1 i)):
   (Γ.filter (fun γ=>S.Agrees γ i)).card≤(e+1)*DS:=by
 let T:=FK φ S.F w (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
 obtain ⟨cost,hcomponent,hsum⟩:=hprovider i hi hproper
 have hsub:Gi⊆Γ:=Finset.filter_subset _ _
 have hGpoint:∀γ∈Gi,MvPolynomial.eval (DK φ S.selected γ) S.G=0:=by
   intro γ hγ;exact S.on_component γ (hsub hγ)
 have hTpoint:∀γ∈Gi,MvPolynomial.eval (DK φ S.selected γ) T=0:=by
   intro γ hγ
   exact (AQG φ S.F S.selected p w S.WG γ
     (S.degree_le γ (hsub hγ)) (S.solution γ (hsub hγ))
     (S.regular γ (hsub hγ)) (x i) (S.u0 i) (S.u1 i)).mpr
     (Finset.mem_filter.mp hγ).2
 have hHp:∀γ∈Gi,MvPolynomial.eval (DK φ S.selected γ)
     (CR φ S.F)≠0:=by
   intro γ hγ
   change MvPolynomial.eval (DK φ S.selected γ)
     (surfaceMap φ (MvPolynomial.pderiv 2 S.F))≠0
   rw [WQ]
   exact S.regular γ (hsub hγ)
 calc
   Gi.card≤∑ C:RCN264.RegularComponent Ω S.G T (CR φ S.F),
       (RCN264.componentSeeds Ω S.G T (CR φ S.F) Gi
         (DK φ S.selected) C).card:=
     WX Ω _ _ _ Gi _ hGpoint hTpoint hHp
   _≤∑ C,(e+1)*cost C:=Finset.sum_le_sum fun C _=>hcomponent C
   _=(e+1)*(∑ C,cost C):=by rw [Finset.mul_sum]
   _≤(e+1)*DS:=Nat.mul_le_mul_left _ hsum
theorem AQH
   {flag:FlagDegree} {w:ℕ} {support:RCN275.ResidualSupportParameters}
   (S:FH φ Γ x p e flag w support)
   (a DS:ℕ)
   (hprovider:AEO S DS)
   (hagreement:∀γ∈Γ,a≤(S.AJW γ).card)
   (hwa:w<a) (han:a≤S.nodes.card) (hdegreePos:1≤DS):
   Γ.card*(a-w)≤(S.nodes.card-w)*(e+1)*DS:=by
 classical
 letI:S.AUY.IsPrime:=S.DNW
 let relation:K→I→Prop:=fun γ i=>S.Agrees γ i
 let identities:=S.identities
 by_cases hI:identities.card≤w
 · have hfiber:∀i∈S.nodes\identities,
       (Γ.filter (fun γ=>relation γ i)).card≤(e+1)*DS:=by
     intro i hi
     obtain ⟨hiNode,hiNot⟩:=Finset.mem_sdiff.mp hi
     have hproper:¬S.G∣FK φ S.F w (x i) (S.u0 i) (S.u1 i):=by
       intro hd
       exact hiNot (Finset.mem_filter.mpr ⟨hiNode,Ideal.mem_span_singleton.mpr hd⟩)
     exact ETI S DS hprovider i hiNode hproper
   simpa only [mul_assoc] using RCN173.sharp_incidence_bound relation Γ S.nodes
     identities a w ((e+1)*DS)
     (RCN065.identityNodes_subset φ S.AUY S.F S.nodes x S.u0 S.u1 w)
     hI hwa han hagreement hfiber
 · have hi:w< identities.card:=Nat.lt_of_not_ge hI
   have hvalues:∀(t:{γ:K//γ∈Γ}) i,i∈identities→
       (S.selected t.1).eval (x i)=S.u0 i+t.1*S.u1 i:=by
     intro t
     exact RCN065.selected_agrees_on_identity_nodes φ S.AUY S.F S.nodes x S.u0 S.u1
       p w S.WG (S.selected t.1) t.1 (S.degree_le t.1 t.2)
       (S.solution t.1 t.2) (S.regular t.1 t.2) (S.FDL t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=RCN065.exists_common_pencil_of_many_identities
     φ S.AUY S.F S.CQP S.DET
     S.nodes x S.u0 S.u1 w S.x_injective hi
     (fun t:{γ:K//γ∈Γ}=>t.1) (fun t=>S.selected t.1)
     (fun t=>S.degree_le t.1 t.2) hvalues
   have hsmall:Γ.card≤e+1:=by
     have hf:Γ.filter (fun γ=>S.selected γ=P0+Polynomial.C γ*P1)=Γ:=
       Finset.filter_eq_self.mpr (fun γ hγ=>hpencil ⟨γ,hγ⟩)
     simpa only [hf] using S.BNN P0 P1 h0 h1
   calc
     Γ.card*(a-w)≤(e+1)*(a-w):=Nat.mul_le_mul_right _ hsmall
     _≤(e+1)*(S.nodes.card-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _≤(S.nodes.card-w)*(e+1)*DS:=by
       have h:=Nat.mul_le_mul_left ((S.nodes.card-w)*(e+1)) hdegreePos
       simpa [mul_assoc,mul_comm,mul_left_comm] using h
end
end RCN087
end SubmissionLower
end ProximityPrize
end PackedLegacy_J4
section PackedLegacy_DU
namespace ProximityPrize
namespace SubmissionLower
namespace RCN049
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN039 RCN040 RCN041 RCN265 RCN198
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K→+*Ω} {Γ:Finset K} {x:I→K}
 {p e w a b s:ℕ} [CharP Ω p] {flag:FlagDegree}
theorem AMV
   (S:FH φ Γ x p e flag w (support a b s))
   (x0 u0 u1:K)
   (hproper:¬S.G∣FK φ S.F w x0 u0 u1)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   ∃base:∀C:RCN264.RegularComponent Ω S.G
       (FK φ S.F w x0 u0 u1) (CR φ S.F),
       RCN341.SeparableLiteralCoordinate C.1,
     Nonempty (YQ base flag
       (RCN287.sharpResidualAgreementFlag (support a b s) w)):=by
 classical
 let T:=FK φ S.F w x0 u0 u1
 let H:=CR φ S.F
 have hsy:s+2<b+s+3:=by omega
 have hTflag:RCN095.PolynomialInFlag (RCN287.sharpResidualAgreementFlag (support a b s) w) T:=
   ANZ hsy (phi:=φ)
     ⟨S.AFS,S.ACG,S.UT⟩
     w (fun j:ℕ=>(j.factorial:K)⁻¹) x0 u0 u1
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.WD S.flag_support
 obtain ⟨hTY,hTS,_⟩:=
   RCN314.WD hTflag
 have hTY':T.degreeOf 0≤1+w*(2*(b+s+3)-2):=by
   apply hTY.trans_eq
   exact RCN287.sharpResidualAgreementFlag_ys (support a b s) hsy w
 have hTS':T.degreeOf 1≤(2*(s+2)-1)*w:=by
   apply hTS.trans_eq
   simp only [RCN287.sharpResidualAgreementFlag,RCN287.sharpAgreementDirection,
     RCN198.support]
 have hGdegree:∀j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixZ:RCN001.coordinateMixedDegree Ω S.G T 2<p:=by
   rw [RCN001.coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀C:RCN264.RegularComponent Ω S.G T H,
     ∃B:RCN341.SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C=>AEP
     φ S.F S.G T p S.RR S.MW hproper
     S.y_dependent hGdegree hmixZ C
 let base:∀C:RCN264.RegularComponent Ω S.G T H,
     RCN341.SeparableLiteralCoordinate C.1:=fun C=>(choiceData C).choose
 have hbaseIndex:∀C:RCN264.RegularComponent Ω S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀C:RCN264.RegularComponent Ω S.G T H,
     D Ω (RCN002.CoordinateField Ω C.1) (coordinate Ω C.1 0)≠0∨
       D Ω (RCN002.CoordinateField Ω C.1) (coordinate Ω C.1 2)≠0:=by
   intro C
   have hb:=RCN037.base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left;simpa only [hidx] using hb
   · right;simpa only [hidx] using hb
 let hZ:∀C:RCN264.RegularComponent Ω S.G T H,RCN037.LiteralProjectionGate C 2:=by
   intro C htr
   exact RH Ω C.1 2 htr
     p S.G T S.MW
     (EN Ω S.G T H C)
     (GV Ω S.G T H C)
     hproper hGdegree hmixZ
 obtain ⟨P⟩:=AEJ
   flag (RCN287.sharpResidualAgreementFlag (support a b s) w) base hactive hZ
   (RCN315.EH S)
   S.MW hproper
   ((RCN095.support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((RCN095.support_subset_flagSupport_iff
     (RCN287.sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end RCN049
end SubmissionLower
end ProximityPrize
end PackedLegacy_DU
section PackedLegacy_EQ
namespace ProximityPrize
namespace SubmissionLower
namespace RCN146
open scoped Classical BigOperators
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
open RCN319 renaming specialization → BM
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω_p19 (K:Type) [Field K]:=GenericField K
def IY (flag:FlagDegree) (a b s w:ℕ):ℕ:=
 flagMixed flag (paddedCut a b s (w+1)) unitZFlag+
   flagMixed flag (paddedCut a b s (w+1)) unitYZFlag
theorem BRQ (flag:FlagDegree) (a b s d:ℕ) (r:FlagDegree):
   flagMixed flag (paddedCut a b s d) r≤
     flagMixed flag (paddedCut a b s (d+1)) r:=by
 have he:paddedCut a b s (d+1)=paddedCut a b s d+
     RCN206.directionFlag a b s:=by
   change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
   congr 1<;>simp only [paddedCut,
     RCN206.centreFlag,
     RCN206.directionFlag,
     add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]<;>ring
 rw [he,RCN203.mixed_add_second]
 exact Nat.le_add_right _ _
variable {Γ:Finset K} {x:I→K} {p e a b s:ℕ} [CharP (Ω_p19 K) p]
 {flag:FlagDegree} {w:ℕ}
theorem AAB
   (S:FH (RCN135.polynomialEmbedding K) Γ x p e flag w (support a b s))
   (agreements:ℕ) (hnodes:S.nodes.card=agreements+e)
   (hagreement:∀γ∈Γ,agreements≤(S.AJW γ).card)
   (hwa:w<agreements)
   (hTail:S.G∣surfaceMap (RCN135.polynomialEmbedding K) (numerator K S.F (w+1)))
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈RCN174.globalCoefficientBox K bound w seedCap slopeCap)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   AEO S (IY flag a b s w):=by
 classical
 unfold AEO
 intro i hi
 dsimp only
 intro hproper
 let T:=FK (RCN135.polynomialEmbedding K) S.F w
   (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
 obtain ⟨base,⟨U⟩⟩:=AMV S
   (x i) (S.u0 i) (S.u1 i) hproper hflagChar hmixed
 let cost:RCN264.RegularComponent (Ω_p19 K) S.G T (CR (RCN135.polynomialEmbedding K) S.F)→ℕ:=
   fun C=>U.family.toFE.zCost C+
     U.family.toFE.yzCost C
 refine ⟨cost,?_,?_⟩
 · intro C
   let Gc:=RCN264.componentSeeds (Ω_p19 K) S.G T
     (CR (RCN135.polynomialEmbedding K) S.F) Gi
     (DK (RCN135.polynomialEmbedding K) S.selected) C
   have hGcGi:Gc⊆Gi:=RCN264.componentSeeds_subset (Ω_p19 K) S.G T _ Gi _ C
   have hGiΓ:Gi⊆Γ:=Finset.filter_subset _ _
   have hGcΓ:Gc⊆Γ:=hGcGi.trans hGiΓ
   have hyzC:∀W:Finset (RCN346.Place_p19 (Ω_p19 K)
       (RCN002.CoordinateField (Ω_p19 K) C.1)),
       (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate (Ω_p19 K) C.1)
         (flagSupport unitYZFlag))≤
         (U.family.toFE.yzCost C:ℤ):=by
     intro W
     change (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate (Ω_p19 K) C.1)
       (flagSupport unitYZFlag))≤
       (RCN344.coordinateDegree (Ω_p19 K) (RCN002.CoordinateField (Ω_p19 K) C.1)
         (U.family.yzProjection C):ℤ)
     calc
       _=∑ v∈W,RCN346.poleOrder_p19 (Ω_p19 K)
           (RCN002.CoordinateField (Ω_p19 K) C.1) v
           (RCN344.coordinateValue (Ω_p19 K) (RCN002.CoordinateField (Ω_p19 K) C.1)
             (U.family.yzProjection C)):=by
         apply Finset.sum_congr rfl
         intro v _
         exact U.family.yzPole_eq C v
       _≤_:=PY (Ω_p19 K)
         (RCN002.CoordinateField (Ω_p19 K) C.1) (U.family.yzProjection C) W
   have hprofileYZ:=AIK
     S hTail (x i) (S.u0 i) (S.u1 i) hproper C
     bound seedCap slopeCap (U.family.toFE.yzCost C)
     hw hshort hchar hbox hyzC
   have hprofile:AHG (RCN135.polynomialEmbedding K) C.1 S.F
       (BJT S (x i) (S.u0 i) (S.u1 i) C)
       (AIC S (x i) (S.u0 i) (S.u1 i) C) w (cost C):=by
     intro W
     exact (hprofileYZ W).trans (by
       change (U.family.toFE.yzCost C:ℤ)≤
         ((U.family.toFE.zCost C+
           U.family.toFE.yzCost C:ℕ):ℤ)
       exact_mod_cast Nat.le_add_left _ _)
   have hcost:1≤cost C:=
     U.one_le_zCost_add_yzCost (RCN135.polynomialEmbedding K) S.F rfl S.RR C
   apply VP
     (RCN135.polynomialEmbedding K) C.1 S.F
     (BJT S (x i) (S.u0 i) (S.u1 i) C)
     (AIC S (x i) (S.u0 i) (S.u1 i) C)
     (base C) p w agreements e (cost C) S.WG hwa hcost hprofile
     S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
   · intro γ hγ
     exact S.degree_le γ (hGcΓ hγ)
   · intro γ hγ
     exact S.solution γ (hGcΓ hγ)
   · intro γ hγ
     exact S.regular γ (hGcΓ hγ)
   · intro γ hγ
     exact RCN264.componentSeeds_on_prime (Ω_p19 K) S.G T
       (CR (RCN135.polynomialEmbedding K) S.F) Gi
       (DK (RCN135.polynomialEmbedding K) S.selected) C γ hγ
   · intro γ hγ
     have hΓ:=hGcΓ hγ
     exact hagreement γ hΓ
   · exact KX S.selected Γ Gc w e hGcΓ S.BNN
 · have hz:=U.family.ARJ
   have hyz:=U.family.ALE
   change (∑ C,U.family.toFE.zCost C)≤
     flagMixed flag (RCN287.sharpResidualAgreementFlag (support a b s) w) unitZFlag at hz
   change (∑ C,U.family.toFE.yzCost C)≤
     flagMixed flag (RCN287.sharpResidualAgreementFlag (support a b s) w) unitYZFlag at hyz
   have hz':=hz.trans (RCN203.mixed_sharp_le_padded a b s w flag unitZFlag)
   have hyz':=hyz.trans (RCN203.mixed_sharp_le_padded a b s w flag unitYZFlag)
   have hz'':=hz'.trans (BRQ flag a b s w unitZFlag)
   have hyz'':=hyz'.trans (BRQ flag a b s w unitYZFlag)
   change (∑ C,(U.family.toFE.zCost C+
     U.family.toFE.yzCost C))≤IY flag a b s w
   rw [Finset.sum_add_distrib]
   exact Nat.add_le_add hz'' hyz''
end
end RCN146
end SubmissionLower
end ProximityPrize
end PackedLegacy_EQ
section PackedLegacy_AB
namespace ProximityPrize
namespace SubmissionLower
namespace RCN259
noncomputable section
section Quotients
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def BZX (a b:A):A:=Classical.choose (gcd_dvd_left a b)
def BPA (a b:A):A:=Classical.choose (gcd_dvd_right a b)
theorem AIV (a b:A):
   a=gcd a b*BZX a b:=
 Classical.choose_spec (gcd_dvd_left a b)
theorem AGO (a b:A):
   b=gcd a b*BPA a b:=
 Classical.choose_spec (gcd_dvd_right a b)
theorem DKA {a b:A} (ha:a≠0):
   IsRelPrime (BZX a b) (BPA a b):=by
 intro d hdleft hdright
 have hg:gcd a b≠0:=gcd_ne_zero_of_left ha
 have hda:gcd a b*d∣a:=by
   calc
     gcd a b*d∣gcd a b*BZX a b:=
       mul_dvd_mul_left (gcd a b) hdleft
     _=a:=(AIV a b).symm
 have hdb:gcd a b*d∣b:=by
   calc
     gcd a b*d∣gcd a b*BPA a b:=
       mul_dvd_mul_left (gcd a b) hdright
     _=b:=(AGO a b).symm
 have hdg:gcd a b*d∣gcd a b:=dvd_gcd hda hdb
 apply isUnit_iff_dvd_one.mpr
 apply (mul_dvd_mul_iff_left hg).mp
 simpa only [mul_one] using hdg
end Quotients
end
end RCN259
end SubmissionLower
end ProximityPrize
end PackedLegacy_AB
section PackedLegacy_P2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN285
open scoped BigOperators Pointwise
open RCN119
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
noncomputable section
variable (K:Type*) [Field K]
def exponentPair_p19 (i j:ℕ):Fin 3→₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j
@[simp] theorem DVT (i j:ℕ):
   exponentPair_p19 i j 0=i:=by simp [exponentPair_p19]
@[simp] theorem EZG (i j:ℕ):
   exponentPair_p19 i j 1=j:=by simp [exponentPair_p19]
@[simp] theorem GCW (i j:ℕ):
   exponentPair_p19 i j 2=0:=by simp [exponentPair_p19]
theorem GDE (d:Fin 3→₀ ℕ) (hd:d 2=0):
   exponentPair_p19 (d 0) (d 1)=d:=by
 ext i
 fin_cases i<;>simp [hd]
theorem FTL
   {a b:ℕ} {u:Fin a} {v:Fin b}
   (hab:a=b) (huv:u.val=v.val):HEq u v:=by
 subst b
 exact heq_of_eq (Fin.ext huv)
def CLB (M L s:ℕ):
   RCN285.seedlessExponents M L s ≃ RCN285.SeedlessBoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,Nat.lt_succ_of_le d.property.1⟩,
     ⟨d.val 1,by
       rcases d.property with ⟨_,h01,h1,_⟩
       rw [lt_min_iff]
       constructor
       · omega
       · change d.val 1<L+1-d.val 0
         omega⟩⟩
 invFun q:=
   ⟨exponentPair_p19 q.1.val q.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.isLt
     rw [lt_min_iff] at hj
     simp only [RCN285.seedlessExponents,Set.mem_setOf_eq,DVT,
       EZG,GCW]
     exact ⟨by omega,by omega,by omega,by simp⟩⟩
 left_inv d:=Subtype.ext (GDE d.val d.property.2.2.2)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨j,hj⟩⟩
   apply Sigma.ext
   · apply Fin.ext
     exact DVT i j
   · apply FTL
     · simp only [DVT]
     · exact EZG i j
end
end RCN285
end SubmissionLower
end ProximityPrize
end PackedLegacy_P2
end Compact_PackedLegacy
end
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
section
set_option linter.all false
section Compact_PackedLocatorTail
section PackedLocator_LocatorNestedProjection
namespace ProximityPrize
namespace SubmissionLower
namespace IL
open scoped BigOperators
open RCN081 RCN156 RCN180 RCN234
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
noncomputable section
variable {K:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def ADH (f:ℕ→ℕ):ℕ→ℕ:=KernelEval.sumRange f
def channelCount (T YS S:ℕ):ℕ:=
  ADH (fun y=>
    let M:=min S (min (T-y) (YS-y))
    (M+1)*(T+1-y)-(M+1)*M/2) (min T YS+1)
abbrev BXU (delta T YS S:ℕ):=
  (y:Fin (min T YS+1)) ×
    (r:Fin (min S (min (T-y.val) (YS-y.val))+1)) ×
      (Fin (T+1-y.val-r.val) × Fin delta)
def DHI (w Dlow:ℕ) {delta T YS S:ℕ}
    (c:BXU delta T YS S):Fin 4→₀ ℕ:=
  Finsupp.single 0 (Dlow-w*c.1.val-(w-1)*c.2.1.val+c.2.2.2.val)+
    Finsupp.single 1 c.1.val+Finsupp.single 2 c.2.1.val+
      Finsupp.single 3 c.2.2.1.val
def highBandMap (w Dlow delta T YS S:ℕ):
    MvPolynomial (Fin 4) K→ₗ[K] (BXU delta T YS S→K):=
  LinearMap.pi (fun c=>MvPolynomial.lcoeff K (DHI w Dlow c))
@[simp] theorem FQS (w Dlow delta T YS S:ℕ)
    (P:MvPolynomial (Fin 4) K) (c:BXU delta T YS S):
    highBandMap w Dlow delta T YS S P c=
      AddMonoidAlgebra.coeff P (DHI w Dlow c):=rfl
end
end IL
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorNestedProjection
section PackedLocator_LocatorContact
namespace ProximityPrize
namespace SubmissionLower
namespace FKN
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN122 RCN156 RCN180 RCN234 RCN313 BY
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open RCN122 renaming specialization → BM
open ContactOrderBridge (Poly4)
noncomputable section
variable {K I:Type*} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
abbrev P4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
end
end FKN
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorContact
section PackedLocator_LocatorFifthPowerAvoidance
namespace ProximityPrize
namespace SubmissionLower
namespace KI
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid
theorem AMN
    (H:MvPolynomial (Fin 4) K) (F:RCN266.RegularIndex H):
    F.1 ∈ normalizedFactors H:=by
  have hactive:F.1 ∈ RCN082.activeFactors H:=
    (Finset.mem_filter.mp F.2).1
  have hnf:F.1 ∈ (normalizedFactors H).toFinset:=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf
def EBE (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):RCN052.RegularIndex F.1:=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  refine ⟨F.1,?_⟩
  change F.1 ∈ (RCN082.activeFactors F.1).filter (fun G=>0<G.degreeOf 2)
  refine Finset.mem_filter.mpr ⟨?_,hF.2.2⟩
  change F.1 ∈ (normalizedFactors F.1).toFinset.filter
    (fun G=>0<G.degreeOf 1+G.degreeOf 2+G.degreeOf 3)
  refine Finset.mem_filter.mpr ⟨?_,by omega⟩
  apply Multiset.mem_toFinset.mpr
  rw [normalizedFactors_irreducible hF.1,
    normalize_normalized_factor F.1 (AMN H F)]
  exact Multiset.mem_singleton_self _
@[simp] theorem ASI (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):(EBE H F).1=F.1:=rfl
theorem CRA (P:DG)
    (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1≤P.leftY) (hR:F.degreeOf 2≤P.leftR)
    (hZ:F.degreeOf 3≤P.leftZ):
    (RCN052.OX P F).y≤P.mixedCost.y∧
      (RCN052.OX P F).r≤P.mixedCost.r∧
      (RCN052.OX P F).z≤P.mixedCost.z:=by
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hR)
      (Nat.mul_le_mul_right P.rightR hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hY)
      (Nat.mul_le_mul_right P.rightY hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightR hY)
      (Nat.mul_le_mul_right P.rightY hR)⟩
end
end KI
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorFifthPowerAvoidance
section PackedLocator_LocatorArbitraryPowerAvoidance
namespace ProximityPrize
namespace SubmissionLower
namespace CS
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open IL KI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {K V:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def LH
    (delta dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | k+1=>
      delta*channelCount T YS S+
        LH delta dT dY dS
          (T-dT) (YS-dY) (S-dS) k
def thinTop (w Dhigh S:ℕ):ℕ:=(Dhigh+S-1)/w
def HN
    (w Dh delta dc dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | k+1=>
      delta*channelCount T (min YS (thinTop w Dh S)) S+
        HN w (Dh-delta-dc) delta dc dT dY dS
          (T-dT) (YS-dY) (S-dS) k
end
end CS
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorArbitraryPowerAvoidance
section PackedLocator_LocatorArbitraryPowerContact
namespace ProximityPrize
namespace SubmissionLower
namespace TB
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open IL
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {K I:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev P4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def NY (j:ℕ) (Q:P4 K):P4 K:=
  (fun H:P4 K=>MvPolynomial.pderiv (2:Fin 4) H)^[j] Q
@[simp] theorem EEE (Q:P4 K):
    NY 0 Q=Q:=rfl
theorem APD (j:ℕ) (Q:P4 K):
    NY (j+1) Q=
      MvPolynomial.pderiv (2:Fin 4) (NY j Q):=by
  simp only [NY,Function.iterate_succ_apply']
@[simp] theorem EON (j:ℕ):
    NY (K:=K) j 0=0:=by
  induction j with
  | zero=>rfl
  | succ j ih=>
      rw [APD,ih,map_zero]
end
end TB
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorArbitraryPowerContact
section PackedLocator_LocatorFactorAggregate
namespace ProximityPrize
namespace SubmissionLower
namespace DY
open scoped BigOperators
open RCN095
open RCN095 renaming PolynomialInFlag → BI
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (LocatorFactorAggregate.middle p) (padS p+1)
def padT (p:FlagDegree):ℕ:=max (LocatorFactorAggregate.total p) (padY p)
def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree:=
  ⟨2*(padT p-padY p)*d,
    1+2*(padY p-padS p)*d,
    2*(padS p-1)*d⟩
def paddedCost (d e:ℕ) (p:FlagDegree):ℕ:=
  flagMixed p (paddedTail p d) (paddedTail p e)
end DY
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorFactorAggregate
section PackedLocator_LocatorHybridCost
namespace ProximityPrize
namespace SubmissionLower
namespace AFI
open scoped BigOperators
open RCN095 DY
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
def rationalFlag (p:FlagDegree):FlagDegree:=
  ⟨131072*(padT p-padY p)+2*(padT p-padY p),
    131072*(padY p-padS p-1)+2*(padY p-padS p-1)+2,
    131072*(padS p-2)+2*(padS p-2)+3⟩
def movingFiber (p:FlagDegree):FlagDegree:=
  ⟨padT p-padY p,padY p-padS p,padS p+1⟩
def movingCut (p:FlagDegree):FlagDegree:=
  rationalFlag p+⟨0,131072,262144⟩
def FXZ (p:FlagDegree):Prop:=2≤p.all∧p.all+2≤LocatorFactorAggregate.middle p
instance (p:FlagDegree):Decidable (FXZ p):=by
  unfold FXZ;infer_instance
end AFI
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorHybridCost
section PackedLocator_LocatorHybridCostC1
namespace ProximityPrize
namespace SubmissionLower
namespace AVP
open scoped BigOperators
open RCN095 DY AFI
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
def ASZ (p:FlagDegree):FlagDegree:=rationalFlag p
def FFM (p:FlagDegree):Prop:=3≤p.all∧p.all+2≤LocatorFactorAggregate.middle p
instance (p:FlagDegree):Decidable (FFM p):=by
  unfold FFM;infer_instance
end AVP
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorHybridCostC1
section PackedLocator_LocatorHybridCostC2
namespace ProximityPrize
namespace SubmissionLower
namespace AAJ
open scoped BigOperators
open RCN095 DY AFI AVP
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
def reducedTail (p:FlagDegree):FlagDegree:=paddedTail p 131072
def hybridCostC2 (p:FlagDegree):ℕ:=
  flagMixed p (reducedTail p) (ASZ p)+
    131076*flagMixed p (movingFiber p) (movingCut p)
def UG (p:FlagDegree):Prop:=3≤p.all∧p.all+2≤LocatorFactorAggregate.middle p
instance (p:FlagDegree):Decidable (UG p):=by
  unfold UG;infer_instance
end AAJ
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorHybridCostC2
section PackedLocator_LocatorHybridCostSelect
namespace ProximityPrize
namespace SubmissionLower
namespace AFI
open RCN095 DY AAJ
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
def ANG (p:FlagDegree):ℕ:=
  if UG p then hybridCostC2 p else paddedCost 131072 131073 p
end AFI
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorHybridCostSelect
section PackedLocator_LocatorBatchProductRoute
namespace ProximityPrize
namespace SubmissionLower
namespace KZ
open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open IL KI CS TB
open LocatorTwoFactorAvoidance (P4)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
variable {K V:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid
abbrev P4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
def dvdSubmodule [AddCommGroup V] [Module K V]
    (q:V→ₗ[K] P4 K) (F:P4 K):Submodule K V where
  carrier:={v | F ∣ q v}
  zero_mem' :=by simp
  add_mem' :=by
    intro x y hx hy
    change F ∣ q x at hx
    change F ∣ q y at hy
    change F ∣ q (x+y)
    rw [map_add]
    exact dvd_add hx hy
  smul_mem' :=by
    intro a x hx
    change F ∣ q x at hx
    change F ∣ q (a • x)
    rw [map_smul,MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hx _
@[simp] theorem GCY [AddCommGroup V] [Module K V]
    (q:V→ₗ[K] P4 K) (F:P4 K) (v:V):
    v ∈ dvdSubmodule q F ↔ F ∣ q v:=Iff.rfl
noncomputable def AKV
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V→ₗ[K] P4 K):Finset (RCN266.RegularIndex H):=by
  classical
  exact A.filter fun F=> ∀v,F.1 ∣ q v
@[simp] theorem ASD
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V→ₗ[K] P4 K) (F:RCN266.RegularIndex H):
    F ∈ AKV H A q ↔ F ∈ A∧ ∀v,F.1 ∣ q v:=by
  classical
  simp only [AKV,Finset.mem_filter]
end
end KZ
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorBatchProductRoute
section PackedLocator_LocatorPhase6800Oracle
namespace ProximityPrize
namespace SubmissionLower
namespace FV
open scoped BigOperators
open RCN095 DY
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
open IL CS
set_option autoImplicit false
set_option maxRecDepth 100000
structure EA where
  totalCap:ℕ
  middleCap:ℕ
  slopeCap:ℕ
  gap:ℕ
  deriving DecidableEq,Repr
def sourceR1200:EA:=
  ⟨526750,10983,2450,36963750380693986577⟩
def sourceC:EA:=
  ⟨328400,6641,1480,5090867013182078230⟩
def GRU:EA:=
  ⟨165000,3320,750,315862958949324685⟩
def GOH:EA:=
  ⟨19500,539,120,91073661700890⟩
def EA.fuel (s:EA) (p:FlagDegree):ℕ:=
  min (s.totalCap/LocatorFactorAggregate.total p)
    (min (s.middleCap/LocatorFactorAggregate.middle p) (s.slopeCap/p.all))
def EA.band (s:EA) (p:FlagDegree):ℕ:=
  LH 50293 (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all
    (s.totalCap-LocatorFactorAggregate.total p) (s.middleCap-LocatorFactorAggregate.middle p)
    (s.slopeCap-p.all) (s.fuel p)
def contactDec (p:FlagDegree):ℕ:=131071*LocatorFactorAggregate.middle p-p.all
def EA.contactCap (s:EA) (p:FlagDegree):ℕ:=
  (131071*(s.middleCap+1)-s.slopeCap)-contactDec p
def EA.bandThin (s:EA) (p:FlagDegree):ℕ:=
  HN 131071 (s.contactCap p) 50293 (contactDec p)
    (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all
    (s.totalCap-LocatorFactorAggregate.total p) (s.middleCap-LocatorFactorAggregate.middle p)
    (s.slopeCap-p.all) (s.fuel p)
def EA.Routeable (s:EA) (p:FlagDegree):Prop:=
  1≤p.all∧LocatorFactorAggregate.total p≤s.totalCap∧LocatorFactorAggregate.middle p≤s.middleCap∧
    p.all≤s.slopeCap∧(s.band p<s.gap∨s.bandThin p<s.gap)
instance (s:EA) (p:FlagDegree):Decidable (s.Routeable p):=
  by unfold EA.Routeable;infer_instance
structure DGY where
  r:ℕ
  v:ℕ
  r1200:ℕ
  sourceC:ℕ
  split500:ℕ
  split1200:ℕ
  split390:ℕ
  deriving DecidableEq,Repr
def BJE (s:EA) (r v threshold:ℕ):Prop:=
  let maxZ:=6677-(r+v)
  if threshold=0 then s.Routeable (LocatorPhase6800Oracle.rawFlag r v 0)
  else if threshold≤maxZ then
    ¬s.Routeable (LocatorPhase6800Oracle.rawFlag r v (threshold-1))∧
      s.Routeable (LocatorPhase6800Oracle.rawFlag r v threshold)
  else threshold=maxZ+1∧ ¬s.Routeable (LocatorPhase6800Oracle.rawFlag r v maxZ)
instance (s:EA) (r v threshold:ℕ):
    Decidable (BJE s r v threshold):=by
  unfold BJE
  infer_instance
def DGY.Valid (q:DGY):Prop:=
  1≤q.r∧q.r≤29∧q.r+q.v≤135∧
    BJE sourceR1200 q.r q.v q.r1200∧
    BJE FV.sourceC q.r q.v q.sourceC∧
    BJE GRU q.r q.v q.split500∧
    BJE GOH q.r q.v q.split390
instance (q:DGY):Decidable q.Valid:=by
  unfold DGY.Valid
  infer_instance
def _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Oracle.BaseRow.evalAt (q:LocatorPhase6800Oracle.BaseRow) (z:ℕ):ℕ:=
  if z=0 then q.z0
  else if z=1 then q.z1
  else if z=2 then q.z2
  else LocatorPhase6800Oracle.evalBaseSegments q.segments z
def baseRowIndex (r v:ℕ):ℕ:=
  (r-1)*136-((r-1)*r)/2+v
def GSX:LocatorPhase6800Oracle.BaseRow:=⟨0,0,0,0,0,[]⟩
def EJY (rows:Array LocatorPhase6800Oracle.BaseRow) (r v:ℕ):LocatorPhase6800Oracle.BaseRow:=
  (rows[baseRowIndex r v]?).getD GSX
def baseTableCap (rows:Array LocatorPhase6800Oracle.BaseRow) (p:FlagDegree):ℕ:=
  (EJY rows p.all p.yz).evalAt p.zOnly
def FFK (rows:Array LocatorPhase6800Oracle.BaseRow):Prop:=
  rows.size=3509∧
    ∀r ∈ (List.range 29).map (fun q=>q+1),
      ∀v ∈ List.range (136-r),
        let q:=EJY rows r v
        q.r=r∧q.v=v
instance (rows:Array LocatorPhase6800Oracle.BaseRow):Decidable (FFK rows):=by
  unfold FFK
  infer_instance
def _root_.ProximityPrize.SubmissionLower.LocatorPhase6800Oracle.BaseRow.FTH (q:LocatorPhase6800Oracle.BaseRow):Prop:=
  1≤q.r∧q.r≤29∧q.r+q.v≤135∧
    q.segments ≠ []∧q.segments.head?.map LocatorPhase6800Oracle.BaseSegment.start=some 3∧
    q.segments.Pairwise (fun a b=>a.start<b.start)∧
    ∀s ∈ q.segments,s.start≤6677-(q.r+q.v)
instance (q:LocatorPhase6800Oracle.BaseRow):Decidable q.FTH:=by
  unfold LocatorPhase6800Oracle.BaseRow.FTH
  infer_instance
end FV
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorPhase6800Oracle
section PackedLocator_LocatorOrdinaryZConvex
namespace ProximityPrize
namespace SubmissionLower
namespace UB
open RCN095 DY AFI AVP AAJ
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
def rawCost (r v z:ℕ):ℕ:=ANG ⟨z,v,r⟩
end UB
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorOrdinaryZConvex
section PackedLocator_LocatorPhase6800Audit
namespace ProximityPrize
namespace SubmissionLower
namespace DSA
open scoped BigOperators
open RCN095 DY CS
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
open FV
set_option autoImplicit false
set_option maxRecDepth 100000
def baseZeroCap (rows:Array LocatorPhase6800Oracle.BaseRow) (r v:ℕ):ℕ:=
  if r=0 then 0 else baseTableCap rows (LocatorPhase6800Oracle.rawFlag r v 0)
def ESG (r v:ℕ):ℕ:=
  UB.rawCost r v 4-
    UB.rawCost r v 3
def EIB (rows:Array LocatorPhase6800Oracle.BaseRow) (R V r v z:ℕ):ℕ:=
  UB.rawCost r v 3+
    baseZeroCap rows (R-r) (V-v)+ESG r v*(z-3)
def DRG (rows:Array LocatorPhase6800Oracle.BaseRow) (R V r v:ℕ):Prop:=
  let q:=EJY rows R V
  let zero:=baseZeroCap rows (R-r) (V-v)
  UB.rawCost r v 0+zero≤q.z0∧
  UB.rawCost r v 1+zero≤q.z1∧
  UB.rawCost r v 2+zero≤q.z2∧
  match q.segments with
  | [s]=>
      s.start=3∧EIB rows R V r v s.start≤s.valueAtStart∧
        ESG r v≤s.slope
  | [s₁,s₂]=>
      s₁.start=3∧s₁.start<s₂.start∧
        EIB rows R V r v s₁.start≤s₁.valueAtStart∧
        EIB rows R V r v (s₂.start-1)≤
          s₁.evalAt (s₂.start-1)∧
        EIB rows R V r v s₂.start≤s₂.valueAtStart∧
        ESG r v≤s₂.slope
  | _=>False
instance (rows:Array LocatorPhase6800Oracle.BaseRow) (R V r v:ℕ):
    Decidable (DRG rows R V r v):=by
  unfold DRG
  dsimp only
  generalize hq:EJY rows R V=q
  cases hs:q.segments with
  | nil=>
      simp only [hs]
      infer_instance
  | cons s tail=>
      cases ht:tail with
      | nil=>
          simp only [hs,ht]
          infer_instance
      | cons s₂ rest=>
          cases hu:rest with
          | nil=>
              simp only [hs,ht,hu]
              infer_instance
          | cons s₃ rest₃=>
              simp only [hs,ht,hu]
              infer_instance
def EIY (rows:Array LocatorPhase6800Oracle.BaseRow) (R:ℕ):Prop:=
  ∀V ∈ List.range (136-R),
    ∀r ∈ List.range (R+1),1≤r→
      ∀v ∈ List.range (V+1),(r<R∨v=V)→
        DRG rows R V r v
instance (rows:Array LocatorPhase6800Oracle.BaseRow) (R:ℕ):Decidable (EIY rows R):=by
  unfold EIY
  infer_instance
def EHH (rows:Array LocatorPhase6800Oracle.BaseRow):Prop:=
  ∀R ∈ List.range 30,1≤R→EIY rows R
instance (rows:Array LocatorPhase6800Oracle.BaseRow):Decidable (EHH rows):=by
  unfold EHH
  infer_instance
end DSA
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorPhase6800Audit
section PackedLocator_LocatorHybridCells
namespace ProximityPrize
namespace SubmissionLower
namespace FA
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
open RCN095 renaming PolynomialInFlag → BI
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem CUY
    {Omega:Type} [Field Omega]
    {G T H:MvPolynomial (Fin 3) Omega}
    {surfaceFlag firstTailFlag:FlagDegree}
    (B:FE (G:=G) (T:=T) (H:=H)
      surfaceFlag firstTailFlag)
    (C:RCN264.RegularComponent Omega G T H)
    {f g:FlagDegree}
    (hz:f.zOnly≤g.zOnly) (hy:f.yz≤g.yz) (ha:f.all≤g.all):
    B.weightedCost f C≤B.weightedCost g C:=by
  simp only [FE.weightedCost]
  gcongr
end
end FA
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorHybridCells
section PackedLocator_LocatorHybridTailProvider
namespace ProximityPrize
namespace SubmissionLower
namespace IB
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341
open FA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
section BoundedProvider
variable {K0 Omega Iota:Type} [Field K0] [Field Omega] [IsAlgClosed Omega]
  {phi:Polynomial K0→+*Omega} {Gamma0:Finset K0} {x0:Iota→K0}
  {pchar errorCap d:ℕ} [CharP Omega pchar]
  {flag0 tailFlag1 tailFlag2:FlagDegree}
  {support0:RCN275.ResidualSupportParameters}
structure AKI
    (S:FH phi Gamma0 x0 pchar errorCap flag0 d support0)
    (divisorBound:optParam ℕ (flagMixed flag0 tailFlag1 tailFlag2)) where
  budgetFamily:FE
    (G:=S.G) (T:=RCN086.globalTailCut phi S.F (d+1))
    (H:=CR phi S.F) flag0 tailFlag1
  multiplicity:CM S→ℕ
  cost:CM S→ℕ
  one_le_multiplicity: ∀C,1≤multiplicity C
  EHX:errorCap+1≤tailFlag2.yz
  cost_sum_le:(∑ C,cost C)≤divisorBound
  CRK: ∀C,
    (RCN264.componentSeeds Omega S.G (RCN086.globalTailCut phi S.F (d+1))
      (CR phi S.F) Gamma0
      (DK phi S.selected) C).card≤cost C
  dichotomy: ∀C,
    (∃delay,1≤delay∧delay≤multiplicity C∧
      RCN086.globalTailCut phi S.F (d+1+delay) ∉ C.1)∨
    ((∀delay,RCN086.globalTailCut phi S.F (d+1+delay) ∈ C.1)∧
      (RCN264.componentSeeds Omega S.G (RCN086.globalTailCut phi S.F (d+1))
        (CR phi S.F) Gamma0
        (DK phi S.selected) C).card≤
          (errorCap+1)*budgetFamily.yzCost C)
theorem BIF
    (S:FH phi Gamma0 x0 pchar errorCap flag0 d support0)
    {divisorBound:ℕ}
    (P:AKI
      (tailFlag1:=tailFlag1) (tailFlag2:=tailFlag2) S divisorBound):
    Gamma0.card≤divisorBound:=by
  classical
  let T1:=RCN086.globalTailCut phi S.F (d+1)
  let H:=CR phi S.F
  let point:=DK phi S.selected
  have hG: ∀gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) S.G=0:=S.on_component
  have hT1: ∀gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) T1=0:=by
    intro gamma hgamma
    exact CJY phi S.F S.selected gamma d
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH: ∀gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) H ≠ 0:=by
    intro gamma hgamma
    exact WQ phi S.selected gamma
      (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
  have hcover:Gamma0.card≤
      ∑ C:RCN264.RegularComponent Omega S.G T1 H,
        (RCN264.componentSeeds Omega S.G T1 H Gamma0 point C).card:=
    WX Omega S.G T1 H Gamma0 point hG hT1 hH
  calc
    Gamma0.card≤ ∑ C:RCN264.RegularComponent Omega S.G T1 H,
        (RCN264.componentSeeds Omega S.G T1 H Gamma0 point C).card:=hcover
    _≤ ∑ C:RCN264.RegularComponent Omega S.G T1 H,P.cost C:=
      Finset.sum_le_sum (fun C _↦P.CRK C)
    _≤divisorBound:=P.cost_sum_le
end BoundedProvider
end
end IB
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorHybridTailProvider
section PackedLocator_LocatorDerivativeChain
namespace ProximityPrize
namespace SubmissionLower
namespace UA
open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN082 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN318 renaming TightParameters → GH
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
  UniqueFactorizationMonoid.strongNormalizationMonoid
def dR (j:ℕ) (F:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
  (MvPolynomial.pderiv (2:Fin 4))^[j] F
@[simp] theorem dR_zero (F:MvPolynomial (Fin 4) K):dR 0 F=F:=rfl
end
end UA
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorDerivativeChain
section PackedLocator_LocatorHybridTransportC2
namespace ProximityPrize
namespace SubmissionLower
namespace JN
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086
open RCN095 renaming PolynomialInFlag → BI
open RCN066 RCN135 RCN159 RCN074 RCN237 RCN244 RCN327 RCN263 RCN206 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
section Transport
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
  {G T T' H:MvPolynomial (Fin 3) Omega}
def YV (h:G ∣ T-T')
    {base' : ∀C:RCN264.RegularComponent Omega G T' H,RCN341.SeparableLiteralCoordinate C.1}
    {p q:FlagDegree}
    (U:EE base' p q)
    (base: ∀C:RCN264.RegularComponent Omega G T H,RCN341.SeparableLiteralCoordinate C.1):
    EE base p q where
  zProjection C:=U.zProjection (JA h C)
  yzProjection C:=U.yzProjection (JA h C)
  NV C:=U.NV (JA h C)
  zValue C:=U.zValue (JA h C)
  ACE C:=U.ACE (JA h C)
  zPole_eq C:=U.zPole_eq (JA h C)
  yzPole_eq C:=U.yzPole_eq (JA h C)
  allPole_eq C:=U.allPole_eq (JA h C)
  ARJ:=by
    refine Eq.trans_le ?_ U.ARJ
    exact Fintype.sum_equiv (JA h) _ _ (fun _=>rfl)
  ALE:=by
    refine Eq.trans_le ?_ U.ALE
    exact Fintype.sum_equiv (JA h) _ _ (fun _=>rfl)
  AQB:=by
    refine Eq.trans_le ?_ U.AQB
    exact Fintype.sum_equiv (JA h) _ _ (fun _=>rfl)
end Transport
end
end JN
end SubmissionLower
end ProximityPrize
end PackedLocator_LocatorHybridTransportC2
end Compact_PackedLocatorTail
section Compact_AsymmetricLocator
namespace ProximityPrize
namespace SubmissionLower
namespace GB
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260 KI
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
def KP (P:DG):ℕ:=
  (P.n-P.w)*RCN294.dot P.KO P.mixedCost+
    (P.errors+1)*P.gap*P.mixedCost.z
def FU (P:DG):ℕ:=
  KP P/P.gap
end
end GB
end SubmissionLower
end ProximityPrize
end Compact_AsymmetricLocator
section Compact_Oracle80791
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80791
namespace Oracle
open RCN095 DY IL CS
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
set_option autoImplicit false
set_option maxRecDepth 100000
structure EA where
  totalCap:ℕ
  middleCap:ℕ
  slopeCap:ℕ
  gap:ℕ
  deriving DecidableEq,Repr
def EA.fuel (s:EA) (p:FlagDegree):ℕ:=
  min (s.totalCap/LocatorFactorAggregate.total p)
    (min (s.middleCap/LocatorFactorAggregate.middle p) (s.slopeCap/p.all))
def EA.band (s:EA) (p:FlagDegree):ℕ:=
  LH 50283 (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all
    (s.totalCap-LocatorFactorAggregate.total p) (s.middleCap-LocatorFactorAggregate.middle p)
    (s.slopeCap-p.all) (s.fuel p)
def contactDec (p:FlagDegree):ℕ:=131071*LocatorFactorAggregate.middle p-p.all
def EA.contactCap (s:EA) (p:FlagDegree):ℕ:=
  (131071*(s.middleCap+1)-s.slopeCap)-contactDec p
def EA.bandThin (s:EA) (p:FlagDegree):ℕ:=
  HN 131071 (s.contactCap p) 50283 (contactDec p)
    (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all
    (s.totalCap-LocatorFactorAggregate.total p) (s.middleCap-LocatorFactorAggregate.middle p)
    (s.slopeCap-p.all) (s.fuel p)
def EA.Routeable (s:EA) (p:FlagDegree):Prop:=
  1≤p.all∧LocatorFactorAggregate.total p≤s.totalCap∧LocatorFactorAggregate.middle p≤s.middleCap∧
    p.all≤s.slopeCap∧(s.band p<s.gap∨s.bandThin p<s.gap)
instance (s:EA) (p:FlagDegree):Decidable (s.Routeable p):=
  by unfold EA.Routeable;infer_instance
end Oracle
end Lower80791
end SubmissionLower
end ProximityPrize
end Compact_Oracle80791
section Compact_FiniteMonomials
namespace ProximityPrize
namespace SubmissionLower
namespace SC
open scoped BigOperators
noncomputable section
set_option autoImplicit false
variable {K σ I:Type*} [Field K] [Fintype I]
local instance:DecidableEq σ:=Classical.decEq σ
local instance:DecidableEq I:=Classical.decEq I
def reconstruct (e:I→σ→₀ ℕ):(I→K)→ₗ[K] MvPolynomial σ K:=
  ∑ i,(MvPolynomial.monomial (e i)).comp (LinearMap.proj i)
theorem CWA (e:I→σ→₀ ℕ) (c:I→K):
    reconstruct e c= ∑ i,MvPolynomial.monomial (e i) (c i):=by
  simp [reconstruct]
theorem ERW (e:I→σ→₀ ℕ) (he:Function.Injective e)
    (c:I→K) (i:I):AddMonoidAlgebra.coeff (reconstruct e c) (e i)=c i:=by
  classical
  rw [CWA,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial,he.eq_iff]
  simp
theorem ABR (e:I→σ→₀ ℕ) (he:Function.Injective e):
    Function.Injective (reconstruct (K:=K) e):=by
  intro c d h
  funext i
  have hh:=congrArg (AddMonoidAlgebra.coeff · (e i)) h
  simpa only [ERW e he] using hh
theorem CLS (e:I→σ→₀ ℕ) (c:I→K)
    (d:σ→₀ ℕ) (hd:d ∉ Set.range e):
    AddMonoidAlgebra.coeff (reconstruct e c) d=0:=by
  classical
  rw [CWA,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_monomial,if_neg (fun h=>hd ⟨i,h⟩)]
theorem mem_range_iff (e:I→σ→₀ ℕ) (he:Function.Injective e)
    (P:MvPolynomial σ K):P ∈ (reconstruct (K:=K) e).range ↔
      ∀d ∈ P.support,d ∈ Set.range e:=by
  classical
  constructor
  · rintro ⟨c,rfl⟩ d hd
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp hd (CLS e c d hn)
  · intro h
    refine ⟨fun i=>P.coeff (e i),?_⟩
    ext d
    by_cases hd:d ∈ Set.range e
    · obtain ⟨i,rfl⟩:=hd
      exact ERW e he _ i
    · rw [CLS e _ d hd]
      exact (MvPolynomial.notMem_support_iff.mp (fun hs=>hd (h d hs))).symm
end
end SC
end SubmissionLower
end ProximityPrize
end Compact_FiniteMonomials
section Compact_SecondJetSpace
namespace ProximityPrize
namespace SubmissionLower
namespace ANF
open scoped BigOperators
open SecondJetBasis (lift)
open SecondJetSupport (Box Poly)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]
def sourceMap (m L s1 s2:ℕ):(SecondJetSpace.Index m L s1 s2→K)→ₗ[K]
    SecondJetBasis.Jet (MvPolynomial (Fin 3) K):=
  (SecondJetSupport.flatEquiv (K:=K)).toLinearMap.comp (SC.reconstruct SecondJetSpace.exponent)
def source (m L s1 s2:ℕ):Submodule K (SecondJetBasis.Jet (MvPolynomial (Fin 3) K)):=
  (sourceMap (K:=K) m L s1 s2).range
instance source_finite (m L s1 s2:ℕ):FiniteDimensional K (source (K:=K) m L s1 s2):=by
  unfold source
  infer_instance
end
end ANF
end SubmissionLower
end ProximityPrize
end Compact_SecondJetSpace
section Compact_SecondJetFacetSpace
namespace ProximityPrize
namespace SubmissionLower
namespace DGJ
open scoped BigOperators
open SecondJetBasis (lift)
open SecondJetSupport (Box Poly)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]
def Index (m L B s:ℕ):=
  {d:SecondJetSpace.Index m L B s//(d.val 1).val+(d.val 3).val≤B}
instance (m L B s:ℕ):Fintype (Index m L B s):=by
  unfold Index
  infer_instance
def exponent {m L B s:ℕ} (d:Index m L B s):Fin 5→₀ ℕ:=
  SecondJetSpace.exponent d.val
def sourceMap (m L B s:ℕ):(Index m L B s→K)→ₗ[K]
    SecondJetBasis.Jet (MvPolynomial (Fin 3) K):=
  (SecondJetSupport.flatEquiv (K:=K)).toLinearMap.comp (SC.reconstruct exponent)
def source (m L B s:ℕ):Submodule K (SecondJetBasis.Jet (MvPolynomial (Fin 3) K)):=
  (sourceMap (K:=K) m L B s).range
instance source_finite (m L B s:ℕ):FiniteDimensional K (source (K:=K) m L B s):=by
  unfold source
  infer_instance
end
end DGJ
end SubmissionLower
end ProximityPrize
end Compact_SecondJetFacetSpace
section Compact_SecondJetGlobalMap
namespace ProximityPrize
namespace SubmissionLower
namespace DLW
open scoped BigOperators
open SecondJetSupport (Box Poly)
open SecondJetBasis (lift)
open SecondJetGlobalSupport (localize)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N:Type*} [Field K] [Fintype I] [Fintype N]
def APX (e:I→Fin 5→₀ ℕ) (m:ℕ) (x u0 u1:K):
    (I→K)→ₗ[K] SecondJetBasis.Jet (MvPolynomial (Fin 3) K):=
  (SecondJetBasis.truncateOuter (K:=K) m).comp ((SecondJetSupport.flatEquiv (K:=K)).toLinearMap.comp
    ((SecondJetGlobalSupport.localize x u0 u1).toLinearMap.comp (SC.reconstruct e)))
end
end DLW
end SubmissionLower
end ProximityPrize
end Compact_SecondJetGlobalMap
section Compact_SecondJetVanish
namespace ProximityPrize
namespace SubmissionLower
namespace CAG
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open SecondJetSpecialize (specialize)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq N:=Classical.decEq N
theorem ALK (P:SecondJetSupport.Poly (K:=K)) (f:Polynomial K) (z:K)
    (nodes:N ↪ K) (u0 u1:N→K) (S:Finset N) (m:ℕ)
    (hcontact: ∀i ∈ S,MvPolynomial.X 0^m ∣ SecondJetDifferentiation.substitute (K:=K)
      (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P))
    (hvalues: ∀i ∈ S,f.eval (nodes i)=u0 i+u1 i*z)
    (hdegree:(SecondJetSpecialize.specialize f z P).natDegree<m*S.card):SecondJetSpecialize.specialize f z P=0:=by
  classical
  by_contra hn
  have hmult: ∀i ∈ S,m≤(SecondJetSpecialize.specialize f z P).rootMultiplicity (nodes i):=by
    intro i hi
    exact (Polynomial.le_rootMultiplicity_iff hn).mpr
      (SecondJetSpecialize.root_contact P f (nodes i) (u0 i) (u1 i) z m (hvalues i hi) (hcontact i hi))
  have hh:=BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
    (SecondJetSpecialize.specialize f z P) nodes S m hmult
  exact (Nat.not_le_of_gt hdegree) hh
end
end CAG
end SubmissionLower
end ProximityPrize
end Compact_SecondJetVanish
section Compact_RootMultiplicityHeight
namespace ProximityPrize
namespace SubmissionLower
namespace DNX
open scoped Classical BigOperators WithZero
open RCN026 RCN187
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
theorem EPP (c:L) (hc:c ≠ 0) (W:Finset (Place_p19 K L))
    (hW:placesFor_p19 K L c hc ⊆ W):(∑ v ∈ W,(v.val c).log)=0:=by
  classical
  have hz:(∑ v ∈ placesFor_p19 K L c hc,(v.val c).log)=0:=by
    simpa only [order_p19,Finset.sum_neg_distrib,neg_eq_zero] using
      DAL K L c hc
  calc
    (∑ v ∈ W,(v.val c).log)= ∑ v ∈ placesFor_p19 K L c hc,(v.val c).log:=by
      symm
      apply Finset.sum_subset hW
      intro v hv hnot
      have ho:order_p19 K L v c=0:=by
        by_contra h
        exact hnot (ALB K L c hc v h)
      simpa only [order_p19,neg_eq_zero] using ho
    _=0:=hz
end
end DNX
end SubmissionLower
end ProximityPrize
end Compact_RootMultiplicityHeight
section Compact_RootMultiplicityWeightedHeight
namespace ProximityPrize
namespace SubmissionLower
namespace BQK
open scoped Classical BigOperators WithZero
open RCN026 RCN187 DNX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L:Type*} [Field L]
section FunctionField
variable (K:Type*) [Field K] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
theorem FIX (P:Polynomial L) (hP:P ≠ 0) (t:L) (d:ℕ)
    (hd:(Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta:Place_p19 K L→ℤ) (C:ℤ)
    (ha: ∀v,0≤alpha v) (hba: ∀v,beta v≤alpha v)
    (hcoeff: ∀v (i:ℕ),v.val (P.coeff i)≤
      WithZero.exp (B v-(i:ℤ)*(2*alpha v-beta v)))
    (hbudget: ∀V:Finset (Place_p19 K L),
      (∑ v ∈ V,(B v+(d:ℤ)*beta v-
        ((P.natDegree-d:ℕ):ℤ)*(2*alpha v-beta v)))≤C)
    (W:Finset (Place_p19 K L)):
    (d:ℤ)*(∑ v ∈ W,max (2*alpha v) (beta v+poleOrder v.val t))≤C:=by
  obtain ⟨Q,rfl⟩:=hd
  have hQ:Q ≠ 0:=right_ne_zero_of_mul hP
  have hf:(Polynomial.X-Polynomial.C t)^d ≠ 0:=left_ne_zero_of_mul hP
  have hi:Q.coeff Q.natDegree ≠ 0:=Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hdeg:((Polynomial.X-Polynomial.C t)^d*Q).natDegree-d=Q.natDegree:=by
    rw [Polynomial.natDegree_mul hf hQ,Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C]
    omega
  simp only [hdeg] at hbudget
  let V:=W ∪ placesFor_p19 K L (Q.coeff Q.natDegree) hi
  have hbalance:=EPP K L (Q.coeff Q.natDegree) hi V
    Finset.subset_union_right
  have hl: ∀v,0≤2*alpha v-beta v:=by intro v;have:=ha v;have:=hba v;omega
  have hh:=RootMultiplicityWeightedHeight.finite_log_height_bound V (fun v=>v.val) t Q d B
    (fun v=>2*alpha v-beta v) (fun v _=>hl v)
    (fun v _=>RootMultiplicityWeightedHeight.coeff_weighted_of_affine v.val _ _ _ (hcoeff v)) Q.natDegree hi hbalance
  have heq (v:Place_p19 K L):
      max (2*alpha v) (beta v+poleOrder v.val t)=
        beta v+max (2*alpha v-beta v) (poleOrder v.val t):=by omega
  have hbound:(d:ℤ)*(∑ v ∈ V,max (2*alpha v) (beta v+poleOrder v.val t))≤C:=by
    have hbud:=hbudget V
    simp_rw [heq]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hbud ⊢
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hh
    nlinarith
  apply le_trans _ hbound
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg d)
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
  intro v _ _
  exact (by have:=ha v;omega:0≤2*alpha v).trans (le_max_left _ _)
theorem DWF (P:Polynomial L) (hP:P ≠ 0)
    (t:L) (d n0:ℕ) (hn:n0≤P.natDegree)
    (hd:(Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta:Place_p19 K L→ℤ) (C:ℤ)
    (ha: ∀v,0≤alpha v) (hba: ∀v,beta v≤alpha v)
    (hcoeff: ∀v (i:ℕ),v.val (P.coeff i)≤
      WithZero.exp (B v-(i:ℤ)*(2*alpha v-beta v)))
    (hbudget: ∀V:Finset (Place_p19 K L),
      (∑ v ∈ V,(B v+(d:ℤ)*beta v-
        ((n0-d:ℕ):ℤ)*(2*alpha v-beta v)))≤C)
    (W:Finset (Place_p19 K L)):
    (d:ℤ)*(∑ v ∈ W,max (2*alpha v) (beta v+poleOrder v.val t))≤C:=by
  apply FIX K P hP t d hd B alpha beta C ha hba hcoeff _ W
  intro V
  apply le_trans _ (hbudget V)
  apply Finset.sum_le_sum
  intro v _
  have hl:0≤2*alpha v-beta v:=by have:=ha v;have:=hba v;omega
  have hsub:((n0-d:ℕ):ℤ)≤((P.natDegree-d:ℕ):ℤ):=by
    exact_mod_cast Nat.sub_le_sub_right hn d
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hsub hl) _
end FunctionField
end
end BQK
end SubmissionLower
end ProximityPrize
end Compact_RootMultiplicityWeightedHeight
section Compact_SecondJetRelaxedFlag
namespace ProximityPrize
namespace SubmissionLower
namespace EJ
open scoped BigOperators WithZero
open MvPolynomial RCN095 RCN026 RCN187 RCN204
open RCN095 renaming PolynomialInFlag → BI
open SecondJetCoefficients (liftExponent)
open SecondJetSupport (Box Poly)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K L:Type*} [Field K] [Field L]
section FunctionField
variable [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
theorem moving_bound (P:SecondJetSupport.Poly (K:=K)) (freezeX:K) (B U T d n0:ℕ)
    (hBU:B≤U) (hUT:U≤T) (hdn:d≤n0) (hB:2*(n0-d)≤B)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (x:Fin 3→L) (Q:Polynomial L)
    (hQcoeff: ∀j,Q.coeff j=MvPolynomial.eval₂Hom (algebraMap K L) x
      (SecondJetFlagCoefficients.freeze freezeX ((SecondJetCoefficients.asS (K:=K) P).coeff j)))
    (hQ:Q ≠ 0) (hn:n0≤Q.natDegree) (t:L)
    (hd:(Polynomial.X-Polynomial.C t)^d ∣ Q) (C:ℤ)
    (hbudget: ∀V:Finset (Place_p19 K L),
      (∑ v ∈ V,flagPole v.val x (SecondJetRelaxedFlag.budgetFlag B U T d n0))≤C)
    (V:Finset (Place_p19 K L)):
    (d:ℤ)*(∑ v ∈ V,max (2*flagPole v.val x unitAllFlag)
      (flagPole v.val x unitYZFlag+poleOrder v.val t))≤C:=by
  apply BQK.DWF K Q hQ t d n0 hn hd
    (fun v=>flagPole v.val x (SecondJetRelaxedFlag.coefficientFlag B U T 0))
    (fun v=>flagPole v.val x unitAllFlag) (fun v=>flagPole v.val x unitYZFlag) C
    (fun v=>RCN204.flagPole_nonneg v.val x unitAllFlag) ?_ ?_ ?_ V
  · intro v
    rw [RCN204.flagPole_unitYZ,RCN204.flagPole_unitAll]
    exact le_max_right _ _
  · intro v j
    rw [hQcoeff j]
    exact SecondJetRelaxedFlag.frozen_coefficient_valuation P freezeX B U T hBU hUT hP v.val
      (algebraMap K L) (RCN344.NP K L v) x j
  · intro W
    convert hbudget W using 1
    apply Finset.sum_congr rfl
    intro v _
    exact (SecondJetRelaxedFlag.budget_flag_pole v.val x B U T d n0 hdn hB).symm
end FunctionField
end
end EJ
end SubmissionLower
end ProximityPrize
end Compact_SecondJetRelaxedFlag
section Compact_SecondJetPoleScaling
namespace ProximityPrize
namespace SubmissionLower
namespace CWV
open RCN026 RCN187
noncomputable section
set_option autoImplicit false
variable {K E:Type*} [Field K] [Field E] [Algebra K E]
theorem FSB (v:Place_p19 K E) (a:K) (ha:a ≠ 0) (x:E):
    poleOrder v.val (x/algebraMap K E a)=poleOrder v.val x:=by
  letI:v.val.IsTrivialOn K:=v.property.2
  have hc:v.val (algebraMap K E a)=1:=Valuation.IsTrivialOn.eq_one a ha
  simp only [poleOrder,Valuation.map_div,hc,div_one]
theorem pole_half (v:Place_p19 K E) (h2:(2:K) ≠ 0) (x:E):
    poleOrder v.val (x/2)=poleOrder v.val x:=by
  simpa only [map_ofNat] using FSB v 2 h2 x
end
end CWV
end SubmissionLower
end ProximityPrize
end Compact_SecondJetPoleScaling
section Compact_SecondJetExceptionalComponents
namespace ProximityPrize
namespace SubmissionLower
namespace AEF
open MvPolynomial RCN264
open scoped Classical
noncomputable section
set_option autoImplicit false
variable {K:Type} [Field K] {Seed:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Seed:=Classical.decEq Seed
theorem BOK (F A H T:MvPolynomial (Fin 3) K)
    (Gamma:Finset Seed) (point:Seed→Fin 3→K)
    (C:RCN264.RegularComponent K F A H) (hT:T ∈ C.1)
    (hne: ∀x ∈ Gamma,MvPolynomial.eval (point x) T ≠ 0):
    (RCN264.componentSeeds K F A H Gamma point C).card=0:=by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxG:=RCN264.componentSeeds_subset K F A H Gamma point C hx
  have hpoint:=RCN264.componentSeeds_on_prime K F A H Gamma point C x hx
  have hz:=hpoint hT
  exact hne x hxG hz
end
end AEF
end SubmissionLower
end ProximityPrize
end Compact_SecondJetExceptionalComponents
section Compact_C2Geometry80788
section Adapted_LocatorFixedStage
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80788
namespace FixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN146 RCN087 RCN203 RCN084 RCN313 RCN074
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN095 renaming PolynomialInFlag → BI
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq LocatorBatchPhase6800.K:=Classical.decEq LocatorBatchPhase6800.K
local instance:DecidableEq Lower80811.Counting.I:=Classical.decEq Lower80811.Counting.I
local instance:DecidableEq (GenericField LocatorBatchPhase6800.K):=Classical.decEq _
local instance:CharP LocatorBatchPhase6800.K RCN223.prime:=by
  simpa [RCN223.prime,RCN223.prime] using
    RCN128.FJ
theorem APP (flag:FlagDegree) (a b s:ℕ):
    IY flag a b s w=
      flag.zOnly*(393219+262146*s)+
      flag.yz*(786438+524292*s)+
      flag.all*(1048586+262146*a+524292*b+524292*s):=by
  simp only [IY,paddedCut,
    RCN206.centreFlag,
    RCN206.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring
theorem CVP (flag:FlagDegree) (a b s:ℕ)
    (hpos:0<flag.zOnly+flag.yz+flag.all):
    1≤IY flag a b s w:=by
  rw [APP]
  have hz:=Nat.mul_le_mul_left flag.zOnly
    (show 1≤393219+262146*s by omega)
  have hy:=Nat.mul_le_mul_left flag.yz
    (show 1≤786438+524292*s by omega)
  have ha:=Nat.mul_le_mul_left flag.all
    (show 1≤1048586+262146*a+524292*b+524292*s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega
end
end FixedStage
end Lower80788
end SubmissionLower
end ProximityPrize
end Adapted_LocatorFixedStage
end Compact_C2Geometry80788
section Compact_SecondJetProperCounting
namespace ProximityPrize
namespace SubmissionLower
namespace BCH
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052
open RCN318 renaming TightParameters → GH
open RCN082 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
open RCN222 renaming GeometricFactor → EX
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K:Type} [Field K] {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem BUM
   (P:DG) (F T:MvPolynomial (Fin 4) K)
   (hFirr:Irreducible F) (hFRpos:0<F.degreeOf 2) (hrel:IsRelPrime F T)
   (p:ℕ) [CharP K p]
   (hFY:F.degreeOf 1≤P.leftY)
   (hFR:F.degreeOf 2≤P.leftR)
   (hFZ:F.degreeOf 3≤P.leftZ)
   (hTY:T.degreeOf 1≤P.rightY)
   (hTR:T.degreeOf 2≤P.rightR)
   (hTZ:T.degreeOf 3≤P.rightZ)
   (hleftR:1≤P.leftR)
   (hleftYSmall:P.leftY<p) (hleftRSmall:P.leftR<p)
   (hleftZSmall:P.leftZ<p)
   (hmixedYSmall:P.mixedCost.y<p)
   (hmixedRSmall:P.mixedCost.r<p)
   (hmixedZSmall:P.mixedCost.z<p)
   (selected:K→Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι→K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1≤P.w) (hchar:P.w<p) (hwa:P.w<P.a)
   (han:P.a≤P.n)
   (hdegree:∀gamma∈Gamma,(selected gamma).natDegree≤P.w)
   (hagreement:∀gamma∈Gamma,
     P.a≤(nodes.filter (fun i=>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:BL selected Gamma P.w P.errors)
   (hsolution:∀gamma∈Gamma,RCN319.specialization K (selected gamma) gamma F=0)
   (hregular:∀gamma∈Gamma,RCN319.specialization K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hTsolution:∀gamma∈Gamma,RCN319.specialization K (selected gamma) gamma T=0):
   Gamma.card*P.gap≤
     (P.n-P.w)*dot P.KO (OX P F)+
       (P.errors+1)*P.gap*(OX P F).z:=by
 classical
 let phi:=RCN135.polynomialEmbedding K
 let Delta:=Gamma
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFne:F≠0:=hFirr.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=Finset.Subset.refl _
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     RCN286.RegularSolution F (selected gamma) gamma∧
       RCN319.specialization K (selected gamma) gamma T=0:=
   ⟨⟨hsolution gamma hgamma,hregular gamma hgamma⟩,hTsolution gamma hgamma⟩
 have hproper (g:RCN222.GeometricFactor K F):¬g.1∣surfaceMap phi T:=by
   have hg:=RCN137.surfaceFactors_spec phi F g.1 g.2
   have hpos:0<F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by omega
   have hgeo:g.1∣RCN138.geometricSurfaceMap K (GenericField K) F:=by
     simpa only [RCN138.canonical_geometricSurfaceMap] using hg.2
   intro hgT
   apply hFirr.not_isUnit
   apply hrel (dvd_refl F)
   apply (RCN138.geometric_factor_dvd_iff K (GenericField K) F T hFirr hpos g.1 hg.1 hgeo).mp
   simpa only [RCN138.canonical_geometricSurfaceMap] using hgT
 have hcover:=AAD K F hFne selected Delta
   (fun gamma hgamma=>(hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=RCN135.genericField_charP K p
 have hsingle (g:RCN222.GeometricFactor K F):
     (KK K F selected Delta g).card*P.gap≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.KO i*
           RCN001.coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           RCN001.coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=RCN137.surfaceFactors_spec phi F g.1 g.2
   have hsub:=WK K F selected Delta g
   have hgCaps:HasCaps_p19 g.1 carrierCap:=by
     intro i
     have hi:=RCN222.geometricFactor_degree_le K F hFne g i
     fin_cases i
     · exact hi.trans hFY
     · exact hi.trans hFR
     · exact hi.trans hFZ
   have hTCaps:HasCaps_p19 (surfaceMap phi T) cutCap:=by
     intro i
     fin_cases i
     · exact (RCN136.surfaceMap_degreeOf_le phi T 0).trans hTY
     · exact (RCN136.surfaceMap_degreeOf_le phi T 1).trans hTR
     · exact (RCN136.surfaceMap_degreeOf_le phi T 2).trans hTZ
   have hcarrierSmall:∀i,capAt carrierCap i<p:=by
     intro i
     fin_cases i
     · exact hleftYSmall
     · exact hleftRSmall
     · exact hleftZSmall
   have hgates:=APW g.1 (surfaceMap phi T)
     carrierCap cutCap p hgCaps hTCaps hcarrierSmall
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitY,DG.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedYSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitR,DG.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedRSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitZ,DG.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedZSmall)
   have hregular:∀gamma∈KK K F selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F)≠0:=by
     intro gamma hgamma
     exact RCN222.selectedPoint_regular_of_specialization K F selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀gamma∈KK K F selected Delta g,
       MvPolynomial.eval (DK phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [UM,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀j,
       (FK phi F P.w (x node) (u₀ node) (u₁ node)).degreeOf j≤
         regularCapAt P.KO j:=by
     have h:=BHT phi F P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j=>(j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (FK phi F P.w (x node) (u₀ node) (u₁ node)).degreeOf j≤
           capAt (RCN068.agreementCaps P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [FK] using h j
     fin_cases j<;>exact hj
   have hcount:=COT phi F g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (hproper g)
     selected (KK K F selected Delta g) nodes x u₀ u₁ hinj
     p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
     hgates.1 hgates.2
     (fun gamma hgamma=>hdegree gamma (hDeltaSub (hsub hgamma)))
     (fun gamma hgamma=>(hDeltaData gamma (hsub hgamma)).1.1)
     hregular (fun gamma hgamma=>(Finset.mem_filter.mp hgamma).2)
     hTpoint
     (fun gamma hgamma=>hagreement gamma (hDeltaSub (hsub hgamma)))
     (KX selected Gamma _ P.w P.errors
       (fun _ hgamma=>hDeltaSub (hsub hgamma)) hnoPencil)
     (regularCapAt P.KO) (fun node _=>hcap node)
   simpa [hnodes,DG.gap] using hcount
 have hbudget (i:Fin 3):=
   ABX P F T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:RCN222.GeometricFactor K F,∑ i:Fin 3,
         regularCapAt P.KO i*
           RCN001.coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.KO i*
         (∑ g:RCN222.GeometricFactor K F,
           RCN001.coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap≤
       (∑ g:RCN222.GeometricFactor K F,
         (KK K F selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:RCN222.GeometricFactor K F,
       (KK K F selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _≤ ∑ g:RCN222.GeometricFactor K F,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.KO i*
         RCN001.coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           RCN001.coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _=>hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.KO i*
         (∑ g:RCN222.GeometricFactor K F,
           RCN001.coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:RCN222.GeometricFactor K F,
           RCN001.coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hfubini]
   _≤(P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.KO i*regularCapAt (OX P F) i)+
       (P.errors+1)*P.gap*regularCapAt (OX P F) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _=>Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.KO (OX P F)+
       (P.errors+1)*P.gap*(OX P F).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]
end
end BCH
end SubmissionLower
end ProximityPrize
end Compact_SecondJetProperCounting
section Compact_SecondJetPairBounds
namespace ProximityPrize
namespace SubmissionLower
namespace ZM
open MvPolynomial RCN260 RCN052 RCN294 RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K:Type} [Field K]
theorem ATW (Q:MvPolynomial (Fin 4) K) (r y t:ℕ)
    (hw:wt RCN156.residualSWeights Q≤r∧wt RCN156.residualYSWeights Q≤y∧
      wt RCN156.residualTotalWeights Q≤t):
    Q.degreeOf 1≤y∧Q.degreeOf 2≤r∧Q.degreeOf 3≤t:=by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
  · have h:=(RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.2.1 e he
    simp only [RCN156.residualYSWeights,RCN081.weight_fin4] at h
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Fin.isValue,Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero] at h
    omega
  · have h:=(RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.1 e he
    simpa [RCN156.residualSWeights,RCN081.weight_fin4] using h
  · have h:=(RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.2.2 e he
    simp [RCN156.residualTotalWeights,RCN081.weight_fin4] at h
    omega
end
end ZM
end SubmissionLower
end ProximityPrize
end Compact_SecondJetPairBounds
section Compact_SecondJetWeightedBasis
namespace ProximityPrize
namespace SubmissionLower
namespace AHC
open scoped BigOperators
open SecondJetBasis (lift)
open SecondJetSupport (Box Poly)
open SecondJetRank (Block a b q)
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]
variable {m s:ℕ} {I:Fin m→Fin s→Type*} [∀r h,Fintype (I r h)]
theorem FFO (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (p:SecondJetWeightedBasis.Parameters (K:=K) (I:=I)) (r:Fin m)
    (hp: ∀j,j.val<r.val→p j=0):
    (SecondJetWeightedBasis.weightedMake a b e p).coeff r.val= ∑ h,Polynomial.X^h.val*
      Polynomial.C (SecondJetLocal.v^(a r h+b r h)*SC.reconstruct (e r h) (p r h)):=by
  rw [SecondJetWeightedBasis.weightedMake_apply,Polynomial.finsetSum_coeff,Finset.sum_eq_single r]
  · simp_rw [Polynomial.finsetSum_coeff,Polynomial.coeff_smul,SecondJetWeightedBasis.weightedTerm_coeff_self]
    apply Finset.sum_congr rfl
    intro h _
    rw [SC.CWA,Finset.mul_sum,map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hm:MvPolynomial.monomial (e r h i) (p r h i)=
        p r h i • MvPolynomial.monomial (e r h i) (1:K):=by
      simpa only [smul_eq_mul,mul_one] using
        (map_smul (MvPolynomial.monomial (e r h i)) (p r h i) (1:K))
    rw [hm]
    simp only [mul_smul_comm,SecondJetWeightedBasis.C_smul_base]
  · intro j _ hj
    simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_smul]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro i _
    by_cases hlt:j.val<r.val
    · simp [hp j hlt]
    · rw [SecondJetWeightedBasis.weightedTerm_coeff_lt]
      · simp
      · have hne:j.val ≠ r.val:=fun he=>hj (Fin.ext he)
        omega
  · simp
theorem DRO (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (p:SecondJetWeightedBasis.Parameters (K:=K) (I:=I)) (r:Fin m)
    (hp: ∀j,j.val<r.val→p j=0):
    SecondJetBasis.truncate (K:=K) (m:=m) (s:=s) (SecondJetWeightedBasis.weightedMake a b e p) r=
      fun h=>SecondJetLocal.v^(a r h+b r h)*SC.reconstruct (e r h) (p r h):=by
  funext h
  rw [SecondJetBasis.truncate_apply,FFO a b e p r hp,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_mul_C,Polynomial.coeff_X_pow,Fin.val_inj]
  simp
theorem DMG (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (he: ∀r h,Function.Injective (e r h)):
    Function.Injective ((SecondJetBasis.truncate (K:=K) (m:=m) (s:=s)).comp (SecondJetWeightedBasis.weightedMake a b e)):=by
  let D: ∀r:Fin m,(∀h:Fin s,I r h→K)→ₗ[K] (Fin s→SecondJetLocal.Base (K:=K)):=fun r=>
    LinearMap.pi (fun h=>(LinearMap.mulLeft K (SecondJetLocal.v^(a r h+b r h))).comp
      ((SC.reconstruct (e r h)).comp (LinearMap.proj h)))
  apply TriangularKernel.injective_of_triangular _ D
  · intro r p q hpq
    funext h i
    have hh:=congrFun hpq h
    change SecondJetLocal.v^(a r h+b r h)*SC.reconstruct (e r h) (p h)=
      SecondJetLocal.v^(a r h+b r h)*SC.reconstruct (e r h) (q h) at hh
    have hz:=mul_left_cancel₀ (pow_ne_zero _ (SecondJetLocal.v_ne_zero (K:=K))) hh
    exact congrFun (SC.ABR (e r h) (he r h) hz) i
  · intro p r hp
    exact DRO a b e p r hp
theorem CSK (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (he: ∀r h,Function.Injective (e r h)):
    Function.Injective ((SecondJetBasis.truncateOuter (K:=K) m).comp (SecondJetWeightedBasis.weightedMake a b e)):=by
  intro p q hpq
  apply DMG a b e he
  have hh:=congrArg (SecondJetBasis.truncate (K:=K) (m:=m) (s:=s)) hpq
  simpa only [LinearMap.comp_apply,SecondJetBasis.truncate_truncateOuter] using hh
theorem FMA {T:Type*} [AddCommGroup T] [Module K T]
    (W:Submodule K (SecondJetBasis.Jet (SecondJetLocal.Base (K:=K)))) [FiniteDimensional K W]
    (f:W→ₗ[K] T) (a b:Fin m→Fin s→ℕ)
    (e: ∀r h,I r h→Fin 3→₀ ℕ) (he: ∀r h,Function.Injective (e r h))
    (hW: ∀p,SecondJetBasis.truncateOuter (K:=K) m (SecondJetWeightedBasis.weightedMake a b e p) ∈ W)
    (hzero: ∀p,f ⟨SecondJetBasis.truncateOuter (K:=K) m (SecondJetWeightedBasis.weightedMake a b e p),hW p⟩=0):
    Module.finrank K f.range+(∑ r:Fin m,∑ h:Fin s,Fintype.card (I r h))≤
      Module.finrank K W:=by
  let g:=(SecondJetBasis.truncateOuter (K:=K) m).comp (SecondJetWeightedBasis.weightedMake a b e)
  have hg:Function.Injective g:=CSK a b e he
  let gw:SecondJetWeightedBasis.Parameters (K:=K) (I:=I)→ₗ[K] W:=g.codRestrict W hW
  let gk:SecondJetWeightedBasis.Parameters (K:=K) (I:=I)→ₗ[K] f.ker:=gw.codRestrict f.ker hzero
  have hi:Function.Injective gk:=by
    intro p q hpq
    apply hg
    exact congrArg (fun x:f.ker=>(x.val:SecondJetBasis.Jet (SecondJetLocal.Base (K:=K)))) hpq
  letI:AddCommGroup W:=inferInstance
  letI:Module K W:=W.module
  letI:FiniteDimensional K f.ker:=inferInstance
  have hdim:=LinearMap.finrank_le_finrank_of_injective hi
  have hsum:=f.finrank_range_add_finrank_ker
  have hd:Module.finrank K (SecondJetWeightedBasis.Parameters (K:=K) (I:=I))=
      ∑ r:Fin m,∑ h:Fin s,Fintype.card (I r h):=by
    simp [SecondJetWeightedBasis.Parameters,Module.finrank_pi_fintype]
  rw [hd] at hdim
  omega
end
end AHC
end SubmissionLower
end ProximityPrize
end Compact_SecondJetWeightedBasis
section Compact_SecondJetRelaxedSpace
namespace ProximityPrize
namespace SubmissionLower
namespace ABQ
open scoped BigOperators
open SecondJetBasis (lift)
open SecondJetSupport (Box Poly)
open SecondJetWeightedSupport (weight)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]
def sourceMap (m L B s U:ℕ) (caps:ℕ→ℕ):(SecondJetRelaxedSpace.Index m L B s U caps→K)→ₗ[K]
    SecondJetBasis.Jet (MvPolynomial (Fin 3) K):=
  (SecondJetSupport.flatEquiv (K:=K)).toLinearMap.comp (SC.reconstruct SecondJetRelaxedSpace.exponent)
def source (m L B s U:ℕ) (caps:ℕ→ℕ):Submodule K (SecondJetBasis.Jet (MvPolynomial (Fin 3) K)):=
  (sourceMap (K:=K) m L B s U caps).range
instance source_finite (m L B s U:ℕ) (caps:ℕ→ℕ):FiniteDimensional K (source (K:=K) m L B s U caps):=by
  unfold source
  infer_instance
theorem FHX (m L B s U:ℕ) (caps:ℕ→ℕ):
    Function.Injective (sourceMap (K:=K) m L B s U caps):=
  (SecondJetSupport.flatEquiv (K:=K)).injective.comp
    (SC.ABR _ (SecondJetRelaxedSpace.exponent_injective m L B s U caps))
theorem GSG (m L B s U:ℕ) (caps:ℕ→ℕ):
    Module.finrank K (source (K:=K) m L B s U caps)=Fintype.card (SecondJetRelaxedSpace.Index m L B s U caps):=by
  unfold source
  rw [← (LinearEquiv.ofInjective (sourceMap (K:=K) m L B s U caps)
    (FHX m L B s U caps)).finrank_eq]
  simp
theorem FKZ (m L B s U:ℕ) (caps:ℕ→ℕ) (P:SecondJetBasis.Jet (MvPolynomial (Fin 3) K)):
    P ∈ source (K:=K) m L B s U caps ↔
      ∀d ∈ ((SecondJetSupport.flatEquiv (K:=K)).symm P).support,
        SecondJetSupport.Allowed m L B s d∧2*d 1+d 3≤B∧d 1+d 2+d 3≤U∧d 1+d 2+d 3≤caps (d 1):=by
  have hm:P ∈ source (K:=K) m L B s U caps ↔
      (SecondJetSupport.flatEquiv (K:=K)).symm P ∈ (SC.reconstruct (K:=K)
        (SecondJetRelaxedSpace.exponent (m:=m) (L:=L) (B:=B) (s:=s) (U:=U) (caps:=caps))).range:=by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h:=congrArg (SecondJetSupport.flatEquiv (K:=K)).symm hc
      simpa [sourceMap] using h
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h:=congrArg (SecondJetSupport.flatEquiv (K:=K)) hc
      simpa [sourceMap] using h
  rw [hm,SC.mem_range_iff _ (SecondJetRelaxedSpace.exponent_injective m L B s U caps)]
  simp only [SecondJetRelaxedSpace.mem_range_exponent]
theorem EFF (m L B s U:ℕ) (caps:ℕ→ℕ)
    (r h a b:ℕ) (e:Fin 3→₀ ℕ)
    (hi:e 0+a+b≤r) (hS:h+a≤s)
    (hB:2*h+2*a+b+e 1-min a (e 1)≤B)
    (hU:e 0+e 1+h+a+b≤U)
    (hL:e 0+e 1+h+a+b+e 2≤L)
    (hcaps: ∀j,h≤j→j≤h+a→e 0+e 1+h+a+b≤caps j):
    SecondJetBasis.truncateOuter (K:=K) m (SecondJetWeightedBasis.weightedTerm r h a b e) ∈
      source (K:=K) m L B s U caps:=by
  rw [← SecondJetWeightedLocal.flatEquiv_weightedVector,← SecondJetSupport.flatEquiv_truncFlat,FKZ]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  have ht:=SecondJetSupport.support_truncFlat m _ d hd
  obtain ⟨h0,hA,hR,hlo,hhi,hM,hT,hRS⟩:=SecondJetWeightedSupport.weightedVector_support r h a b
    (e 0) (e 1) (e 2) (min a (e 1)) (min_le_left _ _) (min_le_right _ _) d ht.2
  refine ⟨?_,hRS.trans hB,hM.trans hU,hM.trans (hcaps (d 1) hlo hhi)⟩
  dsimp only [SecondJetSupport.Allowed]
  exact ⟨ht.1,by omega,by omega,by omega,hT.trans hL⟩
end
end ABQ
end SubmissionLower
end ProximityPrize
end Compact_SecondJetRelaxedSpace
section Compact_SecondJetRelaxedRank
namespace ProximityPrize
namespace SubmissionLower
namespace AEB
open scoped BigOperators
open ABQ
open SecondJetBasis (lift)
open SecondJetSupport (Box Poly)
open SecondJetRelaxedSpace (Index exponent)
open SecondJetRelaxedSpace renaming exponent_injective → ACD, mem_range_exponent → DMI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]
theorem GIQ (m L B s U:ℕ) (caps:ℕ→ℕ)
    (p:SecondJetRelaxedRank.Parameters (K:=K) m L B s U caps):
    SecondJetRelaxedRank.make m L B s U caps p ∈ source (K:=K) m L B s U caps:=by
  simp only [SecondJetRelaxedRank.make,LinearMap.comp_apply,SecondJetWeightedBasis.weightedMake_apply,map_sum,map_smul]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.sum_mem
  intro h _
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  have hb:=SecondJetRelaxedRank.budgets m s r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)
  have he:=e.property
  apply EFF
  · simp only [SecondJetRelaxedRank.exponent_apply]
    omega
  · exact hb.2.1
  · simp only [SecondJetRelaxedRank.exponent_apply]
    omega
  · simp only [SecondJetRelaxedRank.exponent_apply]
    omega
  · simp only [SecondJetRelaxedRank.exponent_apply]
    omega
  · intro j hj hj'
    have hd:=he.2.2.2.2.2 (⟨j-h.val,by omega⟩:Fin (SecondJetRelaxedRank.a m s r.val h.val+1))
    simp only [SecondJetRelaxedRank.exponent_apply]
    dsimp at hd
    have hjj:h.val+(j-h.val)=j:=by omega
    rw [hjj] at hd
    omega
def COQ (m L B s U:ℕ) (caps:ℕ→ℕ):
    source (K:=K) m L B s U caps→ₗ[K] SecondJetLocal.Target (K:=K):=
  (SecondJetRank.contactMap (K:=K) m).comp (source (K:=K) m L B s U caps).subtype
theorem GBK (m L B s U:ℕ) (caps:ℕ→ℕ):
    Module.finrank K (COQ (K:=K) m L B s U caps).range+
      (∑ r:Fin m,∑ h:Fin (s+1),Fintype.card (SecondJetRelaxedRank.Block m L B s U caps r.val h.val))≤
        Fintype.card (SecondJetRelaxedSpace.Index m L B s U caps):=by
  have h:=AHC.FMA
    (source (K:=K) m L B s U caps) (COQ (K:=K) m L B s U caps)
    (fun r h=>SecondJetRelaxedRank.a m s r.val h.val) (fun r h=>SecondJetRelaxedRank.b m s r.val h.val)
    (fun _ _=>SecondJetRelaxedRank.exponent) (fun r h=>SecondJetRelaxedRank.exponent_injective m L B s U caps r.val h.val)
    (GIQ m L B s U caps) (SecondJetRelaxedRank.make_zero m L B s U caps)
  rwa [GSG] at h
end
end AEB
end SubmissionLower
end ProximityPrize
end Compact_SecondJetRelaxedRank
section Compact_SecondJetRelaxedGlobalSupport
namespace ProximityPrize
namespace SubmissionLower
namespace BYD
open scoped BigOperators
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetBasis (lift)
open SecondJetGlobalSupport (localize)
open SecondJetWeightedSupport (weight)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K:Type*} [Field K]
theorem DWW (x u0 u1:K) (m L B s U w:ℕ)
    (D:ℕ→ℕ) (hw:2≤w) (e:Fin 5→₀ ℕ) (c:K)
    (hB:2*e 1+e 3≤B) (hs:e 1≤s)
    (hU:e 1+e 2+e 3≤U) (hL:e 1+e 2+e 3+e 4≤L)
    (hD:e 0+w*e 2+(w-1)*e 3+(w-2)*e 1<D (e 1)):
    SecondJetBasis.truncateOuter (K:=K) m (SecondJetSupport.flatEquiv (K:=K)
      (SecondJetGlobalSupport.localize x u0 u1 (MvPolynomial.monomial e c))) ∈
        ABQ.source (K:=K) m L B s U (fun h=>(D h+B-1)/w):=by
  rw [← SecondJetSupport.flatEquiv_truncFlat,ABQ.FKZ]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  obtain ⟨hm,hd'⟩:=SecondJetSupport.support_truncFlat m _ d hd
  have hb:=SecondJetGlobalSupport.localize_monomial x u0 u1 e c d hd'
  obtain ⟨hS,hRS,hM⟩:=SecondJetRelaxedGlobalSupport.localize_support x u0 u1 e d c hd'
  have hcap:=SecondJetRelaxedGlobalSupport.middle_cap e w B (D (e 1)) hw hB hD
  refine ⟨⟨hm,hb.1,by omega,by omega,hb.2.2.2.trans hL⟩,hRS.trans hB,hM.trans hU,?_⟩
  simpa only [hS] using hM.trans hcap
end
end BYD
end SubmissionLower
end ProximityPrize
end Compact_SecondJetRelaxedGlobalSupport
section Compact_SecondJetRelaxedGlobalMap
namespace ProximityPrize
namespace SubmissionLower
namespace EG
open scoped BigOperators
open SecondJetSupport (Box Poly)
open SecondJetBasis (lift)
open SecondJetGlobalSupport (localize)
open DLW (APX)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N:Type*} [Field K] [Fintype I] [Fintype N]
theorem EEU (m L B s U:ℕ) (caps:ℕ→ℕ):
    Module.finrank K (AEB.COQ (K:=K) m L B s U caps).range≤
      SecondJetRelaxedGlobalMap.rankBound m L B s U caps:=by
  have hh:=AEB.GBK (K:=K) m L B s U caps
  unfold SecondJetRelaxedGlobalMap.rankBound
  omega
theorem EAG (e:I→Fin 5→₀ ℕ) (m L B s U w:ℕ) (D:ℕ→ℕ)
    (hw:2≤w) (x u0 u1:K)
    (hB: ∀i,2*e i 1+e i 3≤B) (hs: ∀i,e i 1≤s)
    (hU: ∀i,e i 1+e i 2+e i 3≤U)
    (hL: ∀i,e i 1+e i 2+e i 3+e i 4≤L)
    (hD: ∀i,e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1<D (e i 1)) (c:I→K):
    APX e m x u0 u1 c ∈
      ABQ.source (K:=K) m L B s U (fun h=>(D h+B-1)/w):=by
  change SecondJetBasis.truncateOuter (K:=K) m (SecondJetSupport.flatEquiv (K:=K)
    (SecondJetGlobalSupport.localize x u0 u1 (SC.reconstruct e c))) ∈ _
  rw [SC.CWA]
  simp_rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  exact BYD.DWW
    x u0 u1 m L B s U w D hw (e i) (c i) (hB i) (hs i) (hU i) (hL i) (hD i)
end
end EG
end SubmissionLower
end ProximityPrize
end Compact_SecondJetRelaxedGlobalMap
section Compact_SecondJetRelaxedDifferentiation
namespace ProximityPrize
namespace SubmissionLower
namespace AQ
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open SecondJetSpecialize (specialize)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N:Type*} [Field K]
theorem AMU (P:SecondJetSupport.Poly (K:=K)) (m a w k n0 d:ℕ)
    (ha:0<a) (hwa:w-2≤a) (hdm:d<m) (hdk:d≤k)
    (hP: ∀e ∈ P.support,
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+
        SecondJetRelaxedDifferentiation.reserve k n0 (e 1)*(a-(w-2))<m*a)
    (nodes:N ↪ K) (u0 u1:N→K)
    (hcontact: ∀i,MvPolynomial.X 0^m ∣ SecondJetDifferentiation.substitute (K:=K)
      (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P))
    (f:Polynomial K) (hf:f.natDegree≤w) (z:K) (S:Finset N)
    (hS:a≤S.card) (hvalues: ∀i ∈ S,f.eval (nodes i)=u0 i+u1 i*z):
    SecondJetSpecialize.specialize f z ((pderiv 1)^[d] P)=0:=by
  refine CAG.ALK _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
  · intro i _
    apply SecondJetGlobalDifferentiation.local_derivative_contact (nodes i) (u0 i) (u1 i) P (m-d) d
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
  · have hd:=SecondJetSpecialize.specialization_degree ((pderiv 1)^[d] P) f z w ((m-d)*a) hf (Nat.mul_pos (Nat.sub_pos_of_lt hdm) ha)
      (SecondJetRelaxedDifferentiation.derivative_weight P m a w k n0 d hwa (Nat.le_of_lt hdm) hdk hP)
    exact hd.trans_le (Nat.mul_le_mul_left (m-d) hS)
end
end AQ
end SubmissionLower
end ProximityPrize
end Compact_SecondJetRelaxedDifferentiation
section Compact_SecondJetRowIntervals
namespace ProximityPrize
namespace SubmissionLower
namespace DSM
open FV
set_option autoImplicit false
set_option maxHeartbeats 3000000
def BaseCell (q:LocatorPhase6800Oracle.BaseRow) (lo hi:ℕ):Prop:=
  lo=hi∨(3≤lo∧match q.segments with
    | []=>True
    | a::ss=>a.start≤lo∧ ∀s ∈ ss,s.start≤lo∨hi<s.start)
instance (q:LocatorPhase6800Oracle.BaseRow) (lo hi:ℕ):Decidable (BaseCell q lo hi):=by
  unfold BaseCell
  cases q.segments<;>infer_instance
end DSM
end SubmissionLower
end ProximityPrize
end Compact_SecondJetRowIntervals
end
section
section MergedPart1
namespace ProximityPrize
namespace SubmissionLower
namespace ZM
open RCN260 RCN052 RCN294
theorem DUQ {K:Type} [Field K]
    (P:DG) (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1≤P.leftY) (hR:F.degreeOf 2≤P.leftR)
    (hZ:F.degreeOf 3≤P.leftZ) (count:ℕ) (hgap:0<P.gap)
    (hc:count*P.gap≤(P.n-P.w)*dot P.KO (OX P F)+
      (P.errors+1)*P.gap*(OX P F).z):
    count≤GB.FU P:=by
  have hv:=KI.CRA P F hY hR hZ
  have hdot:dot P.KO (OX P F)≤dot P.KO P.mixedCost:=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.KO.y hv.1)
        (Nat.mul_le_mul_left P.KO.r hv.2.1))
      (Nat.mul_le_mul_left P.KO.z hv.2.2)
  apply (Nat.le_div_iff_mul_le hgap).mpr
  exact hc.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n-P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors+1)*P.gap) hv.2.2))
end ZM
end SubmissionLower
end ProximityPrize
end MergedPart1
section MergedPart3
namespace ProximityPrize
namespace SubmissionLower
namespace EK
set_option autoImplicit false
structure Carrier where
  c0:ℕ
  c1:ℕ
  c2:ℕ
  c3:ℕ
  c4:ℕ
  deriving DecidableEq,Repr
structure Run where
  stop:ℕ
  who:ℕ
  deriving DecidableEq,Repr
end EK
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace PhaseRows
set_option autoImplicit false
structure PhaseRun where
  stop:ℕ
  witness:ℕ
  deriving DecidableEq,Repr
end PhaseRows
end Lower80899
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace LedgerAudit
set_option autoImplicit false
structure LedgerRun where
  stop:ℕ
  witness:ℕ
  mode:ℕ
  deriving DecidableEq,Repr
end LedgerAudit
end Lower80899
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace BLW
set_option autoImplicit false
structure Run where
  stop:ℕ
  code:ℕ
  deriving DecidableEq,Repr
end BLW
end Lower80899
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace EAY
open FV Lower80899.PhaseRows
set_option autoImplicit false
structure BaseRun where
  stop:Nat
  sheet:Nat
  deriving DecidableEq,Repr
structure Numbers where
  carrier:EK.Carrier
  base:LocatorPhase6800Oracle.BaseRow
  threshold:Array Nat
  prefixValues:Array Nat
  singletons:List EK.Run
  baseChoices:List BaseRun
  phaseRuns:Array (List PhaseRun)
  ledgerRuns:List Lower80899.LedgerAudit.LedgerRun
  thresholdRuns:Array (List Lower80899.BLW.Run)
end EAY
end SubmissionLower
end ProximityPrize
end MergedPart3
section MergedPart5
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace FactorSwitch
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open RCN319 renaming specialization → BM
open KI IL
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq LocatorBatchPhase6800.K:=Classical.decEq LocatorBatchPhase6800.K
local instance:DecidableEq Lower80811.Counting.I:=Classical.decEq Lower80811.Counting.I
local instance:CharP LocatorBatchPhase6800.K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ
def helperPair (L YS S leftY leftR leftZ:ℕ):DG:=
  ⟨262144,131071,181059,leftY,leftR,leftZ,YS,S,L⟩
def LX (L YS S leftY leftR leftZ:ℕ):Prop:=
  let P:=helperPair L YS S leftY leftR leftZ
  1≤P.leftR∧P.leftY<2130706433∧P.leftR<2130706433∧
    P.leftZ<2130706433∧P.mixedCost.y<2130706433∧
    P.mixedCost.r<2130706433∧P.mixedCost.z<2130706433
end
end FactorSwitch
end Lower80899
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace PowerRoute
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open RCN319 renaming specialization → BM
open KI IL
open CS TB
open Lower80899.FactorSwitch
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq LocatorBatchPhase6800.K:=Classical.decEq LocatorBatchPhase6800.K
local instance:DecidableEq Lower80811.Counting.I:=Classical.decEq Lower80811.Counting.I
local instance:CharP LocatorBatchPhase6800.K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ
structure DTX where
  tLo:ℕ
  tHi:ℕ
  yLo:ℕ
  yHi:ℕ
  rLo:ℕ
  rHi:ℕ
  deriving DecidableEq
def stagePair (L YS S:ℕ) (b:DTX) (j:ℕ):
    DG:=
  helperPair (L-j*b.tLo) (YS-j*b.yLo) (S-j*b.rLo)
    b.yHi b.rHi b.tHi
def stageCost (L YS S:ℕ) (b:DTX) (j:ℕ):ℕ:=
  GB.FU (stagePair L YS S b j)
end
end PowerRoute
end Lower80899
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace AGR
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open RCN319 renaming specialization → BM
open IL KI CS TB Lower80899.FactorSwitch Lower80899.PowerRoute KZ
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq LocatorBatchPhase6800.K:=Classical.decEq LocatorBatchPhase6800.K
local instance:DecidableEq Lower80811.Counting.I:=Classical.decEq Lower80811.Counting.I
local instance:CharP LocatorBatchPhase6800.K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ
def LP {H:LocatorBatchPhase6800.P4} (F:RegularIndex H):DTX where
  tLo:=wt RCN156.residualTotalWeights F.1
  tHi:=wt RCN156.residualTotalWeights F.1
  yLo:=wt RCN156.residualYSWeights F.1
  yHi:=wt RCN156.residualYSWeights F.1
  rLo:=wt RCN156.residualSWeights F.1
  rHi:=wt RCN156.residualSWeights F.1
end
end AGR
end Lower80899
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace Oracle
open RCN095 DY IL CS
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
open Lower80899.PowerRoute Lower80899.FactorSwitch
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
set_option autoImplicit false
set_option maxRecDepth 100000
structure EA where
  totalCap:ℕ
  middleCap:ℕ
  slopeCap:ℕ
  gap:ℕ
  deriving DecidableEq,Repr
def EA.fuel (s:EA) (p:FlagDegree):ℕ:=
  min (s.totalCap/LocatorFactorAggregate.total p)
    (min (s.middleCap/LocatorFactorAggregate.middle p) (s.slopeCap/p.all))
def EA.band (s:EA) (p:FlagDegree):ℕ:=
  LH 49989 (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all
    (s.totalCap-LocatorFactorAggregate.total p) (s.middleCap-LocatorFactorAggregate.middle p)
    (s.slopeCap-p.all) (s.fuel p)
def contactDec (p:FlagDegree):ℕ:=131071*LocatorFactorAggregate.middle p-p.all
def EA.contactCap (s:EA) (p:FlagDegree):ℕ:=
  (131071*(s.middleCap+1)-s.slopeCap)-contactDec p
def EA.bandThin (s:EA) (p:FlagDegree):ℕ:=
  HN 131071 (s.contactCap p) 49989 (contactDec p)
    (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all
    (s.totalCap-LocatorFactorAggregate.total p) (s.middleCap-LocatorFactorAggregate.middle p)
    (s.slopeCap-p.all) (s.fuel p)
def EA.Routeable (s:EA) (p:FlagDegree):Prop:=
  1≤p.all∧LocatorFactorAggregate.total p≤s.totalCap∧LocatorFactorAggregate.middle p≤s.middleCap∧
    p.all≤s.slopeCap∧(s.band p<s.gap∨s.bandThin p<s.gap)
instance (s:EA) (p:FlagDegree):Decidable (s.Routeable p):=
  by unfold EA.Routeable;infer_instance
def LP (p:FlagDegree):DTX:=
  ⟨LocatorFactorAggregate.total p,LocatorFactorAggregate.total p,LocatorFactorAggregate.middle p,LocatorFactorAggregate.middle p,p.all,p.all⟩
structure YF where
  source:EA
  potential:LocatorPhase6800Oracle.Potential
  stageCost_le: ∀(p:FlagDegree) (j:ℕ),
    1≤p.all→p.all≤40→LocatorFactorAggregate.middle p≤181→LocatorFactorAggregate.total p≤14007→
    j≤source.fuel p→
    stageCost source.totalCap source.middleCap source.slopeCap
      (LP p) j≤potential.eval p
  stageGates: ∀(p:FlagDegree) (j:ℕ),
    1≤p.all→p.all≤40→LocatorFactorAggregate.middle p≤181→LocatorFactorAggregate.total p≤14007→
    j≤source.fuel p→
    LX
      (source.totalCap-j*LocatorFactorAggregate.total p)
      (source.middleCap-j*LocatorFactorAggregate.middle p)
      (source.slopeCap-j*p.all)
      (LocatorFactorAggregate.middle p) p.all (LocatorFactorAggregate.total p)
end Oracle
end Lower80899
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace BatchPhase
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN095 renaming PolynomialInFlag → BI
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open DY CS KZ Lower80899.AGR Lower80899.FactorSwitch Lower80899.Oracle
open LocatorFactorAggregate (middle total)
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq LocatorBatchPhase6800.K:=Classical.decEq LocatorBatchPhase6800.K
local instance:DecidableEq Lower80811.Counting.I:=Classical.decEq Lower80811.Counting.I
structure WZ (sound:YF)
    (u0 u1:Lower80811.Counting.I→LocatorBatchPhase6800.K) where
  D:ℕ
  m:ℕ
  weighted:D≤m*181059∧m*49989<D
  shape:D+sound.source.slopeCap≤
    131071*(sound.source.middleCap+1)
  slope_le_m:sound.source.slopeCap≤m
  m_lt_char:m<2130706433
  gap_le_finrank:sound.source.gap≤Module.finrank LocatorBatchPhase6800.K
    (IJ (K:=LocatorBatchPhase6800.K) D 131071 sound.source.totalCap
      sound.source.slopeCap m IRSProfile.domain u0 u1)
end
end BatchPhase
end Lower80899
end SubmissionLower
end ProximityPrize
end MergedPart5
section MergedPart7
namespace ProximityPrize
namespace SubmissionLower
namespace AJN
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN087 RCN203 RCN084 RCN313 RCN074
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN095 renaming PolynomialInFlag → BI
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def gap:ℕ:=49988
end
end AJN
end SubmissionLower
end ProximityPrize
end MergedPart7
end
section
section MergedPart0
section Compact_MovingFiberScalarList6815
namespace ProximityPrize
namespace SubmissionLower
namespace FQ
open ProximityPrize.Benchmark
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def errors:ℕ:=81085
def agreements:ℕ:=Pilot6832ScalarArithmetic.n-errors
def gap:ℕ:=agreements-Koala6831MovingSources.weight
def slopeCap:ℕ:=42
end
end FQ
end SubmissionLower
end ProximityPrize
namespace ProximityPrize
namespace SubmissionLower
namespace CVH
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001 RCN281 RCN019 RCN018
open RCN319 renaming specialization → BM
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN222 renaming GeometricFactor → EX
open RCN279 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR, reconstruct_zero → ECW
open RCN223 (prime)
open RCN281 renaming GeometricFactor → EX
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
abbrev n:=Pilot6832ScalarArithmetic.n
abbrev gap:=FQ.gap
abbrev prime:=RCN223.prime
abbrev slopeCap:=FQ.slopeCap
end
end CVH
end SubmissionLower
end ProximityPrize
end Compact_MovingFiberScalarList6815
end MergedPart0
section MergedPart1
section Compact_MovingFiberProtocol6815
namespace ProximityPrize
namespace SubmissionLower
namespace AAZ
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem RCN018 RCN019 RCN284 RCN280
open scoped NNReal
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
def n:ℕ:=262144
end
end AAZ
end SubmissionLower
end ProximityPrize
end Compact_MovingFiberProtocol6815
end MergedPart1
section MergedPart2
namespace ProximityPrize
namespace SubmissionLower
namespace CPX
open scoped BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN095 RCN136 RCN187 RCN204 RCN207 RCN257 RCN313 RCN341
open RCN095 renaming PolynomialInFlag → BI
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
theorem BIH {L:Type*} [Field L]
    (v:Valuation L (WithZero (Multiplicative ℤ))) (x:L) (b:ℤ)
    (hb:0≤b) (hx:v x≤WithZero.exp b):poleOrder v x≤b:=by
  unfold poleOrder
  apply max_le hb
  by_cases hz:v x=0
  · simpa only [hz,WithZero.log_zero] using hb
  · simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hz WithZero.exp_ne_zero).mpr hx
theorem EIF {E L:Type*} [Field E] [Field L]
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (coeff:E→+*L) (hc: ∀c,v (coeff c)≤1)
    (x:Fin 3→L) (sigma:L) (Q U:MvPolynomial (Fin 3) E) (target:E)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hU:RCN095.PolynomialInFlag unitYZFlag U):
    poleOrder v (coeff target-MvPolynomial.eval₂Hom coeff x Q-
      MvPolynomial.eval₂Hom coeff x U*sigma)≤
      max (2*flagPole v x unitAllFlag)
        (flagPole v x unitYZFlag+poleOrder v sigma):=by
  let theta:=max (2*flagPole v x unitAllFlag)
    (flagPole v x unitYZFlag+poleOrder v sigma)
  have htheta:0≤theta:=
    (mul_nonneg (by norm_num) (RCN204.flagPole_nonneg _ _ _)).trans (le_max_left _ _)
  apply BIH v _ theta htheta
  apply v.map_sub_le
  · have hv:=RCN204.valuation_eval_le_flag v coeff hc x (2 • unitAllFlag)
      (MvPolynomial.C target-Q) (RCN207.inFlag_sub_poly (inFlag_const _ _) hQ)
    have he:flagPole v x (2 • unitAllFlag)=2*flagPole v x unitAllFlag:=by
      simp only [flagPole,nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag]
      norm_num
    simp only [map_sub,MvPolynomial.eval₂Hom_C,he] at hv
    exact hv.trans (WithZero.exp_le_exp.mpr (le_max_left _ _))
  · have hu:=RCN204.valuation_eval_le_flag v coeff hc x unitYZFlag U hU
    have hs:v sigma≤WithZero.exp (poleOrder v sigma):=
      WithZero.le_exp_of_log_le (le_max_right _ _)
    rw [map_mul]
    exact (mul_le_mul' hu hs).trans (by
      rw [← WithZero.exp_add]
      exact WithZero.exp_le_exp.mpr (le_max_right _ _))
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
theorem EPX
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base:RCN341.SeparableLiteralCoordinate C)
    (P:SecondJetSupport.Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(SecondJetCoefficients.asS P).natDegree)
    (hF:surfaceMap phi F ∈ C)
    (hH:surfaceMap phi (polyH K F) ∉ C)
    (hlead:surfaceMap phi (SecondJetCoefficients.asS P).leadingCoeff ∉ C)
    (hdiv: ∀j≤k,F ∣ SecondJetClearedHelper.helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) E) (target:E)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (CV:ℕ)
    (hbudget: ∀W:Finset (Place_p19 E (RCN002.CoordinateField E C)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0))≤(CV:ℤ))
    (W:Finset (Place_p19 E (RCN002.CoordinateField E C))):
    ((k+1:ℕ):ℤ)*(∑ nu ∈ W,poleOrder nu.val
      (algebraMap E (RCN002.CoordinateField E C) target-RCN002.coordinateEvaluation E C Q-
        RCN002.coordinateEvaluation E C A*RCN064.movingRatio C
          (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F))))≤(CV:ℤ):=by
  letI:=RCN006.polynomialBaseAlgebra E C base.index
  letI:=RCN005.rationalBaseAlgebra E C base.index base.transcendental
  letI:=RCN006.polynomialBaseScalarTower E C base.index
  letI:=RCN006.polynomialRationalScalarTower E C base.index base.transcendental
  letI:=RCN005.rationalBaseScalarTower E C base.index base.transcendental
  letI:FiniteDimensional (RatFunc E) (RCN002.CoordinateField E C):=base.finite
  letI:Algebra.IsSeparable (RatFunc E) (RCN002.CoordinateField E C):=base.separable
  have hdeg:=SecondJetComponentRoots.degree_retained phi C P hlead
  have hroot:=SecondJetComponentRoots.roots_retained phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree:n0≤(SecondJetComponentRoots.componentPolynomial phi C P).natDegree:=by
    rw [hdeg.2]
    exact hn
  have hs:=EJ.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (SecondJetSurfaceMap.mapped_support_bounds _ P B U T hP)
    (coordinate E C) (SecondJetComponentRoots.componentPolynomial phi C P)
    (SecondJetComponentRoots.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV:ℤ) hbudget W
  simp only [CWV.pole_half _ h2] at hs
  apply le_trans _ hs
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
  apply Finset.sum_le_sum
  intro nu _
  have hh:=EIF nu.val (algebraMap E (RCN002.CoordinateField E C))
    (RCN344.NP E (RCN002.CoordinateField E C) nu) (coordinate E C)
    (RCN064.movingRatio C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
    Q A target hQ hA
  simpa only [RCN002.coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom] using hh
theorem DVQ
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (C:Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base:RCN341.SeparableLiteralCoordinate C)
    (P:SecondJetSupport.Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(SecondJetCoefficients.asS P).natDegree)
    (hF:surfaceMap phi F ∈ C)
    (hH:surfaceMap phi (polyH K F) ∉ C)
    (hlead:surfaceMap phi (SecondJetCoefficients.asS P).leadingCoeff ∉ C)
    (hdiv: ∀j≤k,F ∣ SecondJetClearedHelper.helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) E) (target:E)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (hproper:RCN207.movingEquation (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) Q A target ∉ C)
    (CV:ℕ)
    (hbudget: ∀W:Finset (Place_p19 E (RCN002.CoordinateField E C)),
      (∑ nu ∈ W,flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0))≤(CV:ℤ)):
    RCN271.ABY C (surfaceMap phi (polyH K F))
      (RCN207.movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) (CV/(k+1)):=by
  let H:=surfaceMap phi (polyH K F)
  let G:=surfaceMap phi (polyG K F)
  have hHne:RCN002.coordinateEvaluation E C H ≠ 0:=by
    intro hz
    exact hH ((SecondJetComponentRoots.evaluation_zero_iff C _).mp hz)
  have hnorm:MvPolynomial.aeval (coordinate E C) (RCN207.movingEquation H G Q A target)/
      MvPolynomial.aeval (coordinate E C) H=
      algebraMap E (RCN002.CoordinateField E C) target-RCN002.coordinateEvaluation E C Q-
        RCN002.coordinateEvaluation E C A*RCN064.movingRatio C H G:=by
    simp only [RCN207.movingEquation,map_sub,map_mul,MvPolynomial.aeval_C,
      RCN064.movingRatio,RCN002.coordinateEvaluation_eq_aeval] at*
    field_simp
  apply AIR E C base H _ 1 (CV/(k+1)) hproper hH
  intro W
  have hsource:=EPX phi F C base P B U T s k n0
    hS hP hBU hUT hdn hB hn hF hH hlead hdiv h2 hfact Q A target hQ hA CV hbudget W
  simp only [pow_one]
  change (∑ nu ∈ W,poleOrder nu.val
    (MvPolynomial.aeval (coordinate E C) (RCN207.movingEquation H G Q A target)/
      MvPolynomial.aeval (coordinate E C) H))≤((CV/(k+1):ℕ):ℤ)
  simp_rw [hnorm]
  rw [Int.natCast_ediv]
  apply (Int.le_ediv_iff_mul_le (by positivity:(0:ℤ)<((k+1:ℕ):ℤ))).mpr
  simpa only [H,G,mul_comm] using hsource
end
end CPX
end SubmissionLower
end ProximityPrize
end MergedPart2
section MergedPart3
namespace ProximityPrize
namespace SubmissionLower
namespace CBU
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN039 RCN046 RCN084 RCN095
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN114 RCN136 RCN187 RCN204 RCN207 RCN237 RCN257 RCN264 RCN271 RCN313 RCN340 RCN341
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open CPX
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
local instance:DecidableEq E:=Classical.decEq E
local notation "Poly3" =>MvPolynomial (Fin 3) E
theorem GHB
    {G N R:Poly3} {p q:FlagDegree}
    {base: ∀C:RCN264.RegularComponent E G N R,RCN341.SeparableLiteralCoordinate C.1}
    (U:QZ base p q) (C:RCN264.RegularComponent E G N R)
    (V:FlagDegree) (W:Finset (Place_p19 E (RCN002.CoordinateField E C.1))):
    (∑ nu ∈ W,flagPole nu.val (coordinate E C.1) V)≤
      (U.toFE.weightedCost V C:ℤ):=by
  have hz:=U.zPole C W
  have hy:=U.yzPole C W
  have ha:=U.allPole C W
  simp only [UC] at hz
  simp only [QD] at hy
  simp only [SF] at ha
  have h:=add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg V.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg V.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg V.all))
  simpa only [flagPole,Finset.sum_add_distrib,← Finset.mul_sum,
    FE.weightedCost,QZ.toFE,
    Nat.cast_add,Nat.cast_mul] using h
theorem DSR
    (phi:Polynomial K→+*E) (F:MvPolynomial (Fin 4) K)
    (carrier N:Poly3) (p q:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:RCN095.PolynomialInFlag p carrier) (hNflag:RCN095.PolynomialInFlag q N)
    (c:ℕ) [CharP E c]
    (hdeg:p.zOnly+p.yz+p.all<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c)
    (P:SecondJetSupport.Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(SecondJetCoefficients.asS P).natDegree)
    (hdiv: ∀j≤k,F ∣ SecondJetClearedHelper.helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:Poly3) (target:E)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (points:Finset (Fin 3→E))
    (hpoints: ∀x ∈ points,
      MvPolynomial.eval x carrier=0∧MvPolynomial.eval x N=0∧
      MvPolynomial.eval x (RCN207.movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target)=0∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)) ≠ 0∧
      MvPolynomial.eval x (surfaceMap phi (SecondJetCoefficients.asS P).leadingCoeff) ≠ 0∧
      MvPolynomial.eval x (MvPolynomial.pderiv (1:Fin 3) carrier) ≠ 0)
    (hisolated: ∀x ∈ points,RCN084.IsolatedPoint carrier N
      (RCN207.movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) x):
    (k+1)*points.card≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0):=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let L:=surfaceMap phi (SecondJetCoefficients.asS P).leadingCoeff
  let R:=H*L
  let M:=RCN207.movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let V:=SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0
  have hR: ∀x ∈ points,MvPolynomial.eval x R ≠ 0:=by
    intro x hx
    simpa only [R,map_mul] using mul_ne_zero (hpoints x hx).2.2.2.1 (hpoints x hx).2.2.2.2.1
  have hcover: ∀x ∈ points,∃g: ↥(RCN084.activeFactors carrier N),MvPolynomial.eval x g.1=0:=by
    intro x hx
    exact AAU carrier N M R hcarrier x
      (hpoints x hx).1 (hpoints x hx).2.2.1 (hR x hx)
      (hpoints x hx).2.2.2.2.2 (hisolated x hx)
  obtain ⟨base,hY,hZ⟩:=AOE carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g: ↥(RCN084.activeFactors carrier N)):Finset (Fin 3→E):=
    points.filter (fun (x:Fin 3→E)=>MvPolynomial.eval x g.1=(0:E))
  have hcoverage:points ⊆ Finset.univ.biUnion S:=by
    intro x hx
    obtain ⟨g,hg⟩:=hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g: ↥(RCN084.activeFactors carrier N)):
      (k+1)*(S g).card≤flagMixed (exactFlag g.1) q V:=by
    have hg:=RCN084.activeFactors_spec carrier N g
    obtain ⟨unit⟩:=ACA (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((RCN095.support_subset_flagSupport_iff _ _).mpr (RCN084.polynomialIn_exactFlag g.1))
      ((RCN095.support_subset_flagSupport_iff _ _).mpr hNflag)
    let budget:=unit.toFE
    have hcard:=WX E g.1 N R (S g) id
      (fun x hx=>(Finset.mem_filter.mp hx).2)
      (fun x hx=>(hpoints x (Finset.mem_filter.mp hx).1).2.1)
      (fun x hx=>hR x (Finset.mem_filter.mp hx).1)
    have hlocal (C:RCN264.RegularComponent E g.1 N R):
        (k+1)*(RCN264.componentSeeds E g.1 N R (S g) id C).card≤budget.weightedCost V C:=by
      by_cases he:(RCN264.componentSeeds E g.1 N R (S g) id C).Nonempty
      · obtain ⟨x,hx⟩:=he
        have hxS:=RCN264.componentSeeds_subset E g.1 N R (S g) id C hx
        have hxpoints:=(Finset.mem_filter.mp hxS).1
        have hxC:=RCN264.componentSeeds_on_prime E g.1 N R (S g) id C x hx
        have hcar:carrier ∈ C.1:=C.1.mem_of_dvd hg.2.1 (EN E g.1 N R C)
        have hF:surfaceMap phi F ∈ C.1:=C.1.mem_of_dvd hcarrierF hcar
        have hH:H ∉ C.1:=by
          intro hh
          exact _Q6 E g.1 N R C (C.1.mul_mem_right L hh)
        have hL:L ∉ C.1:=by
          intro hl
          exact _Q6 E g.1 N R C (C.1.mul_mem_left H hl)
        have hproper:M ∉ C.1:=hisolated x hxpoints C.1 inferInstance
          (PU E g.1 N R C) hxC hcar (GV E g.1 N R C)
        have hb:=DVQ phi F C.1 (base g C) P B U T s k n0
          hS hP hBU hUT hdn hB hn hF hH hL hdiv h2 hfact Q A target hQ hA hproper
          (budget.weightedCost V C) (fun W=>GHB unit.toQZ C V W)
        have hc:=hb (RCN264.componentSeeds E g.1 N R (S g) id C)
          (fun y hy=>RCN264.componentSeeds_on_prime E g.1 N R (S g) id C y hy)
          (fun y hy=>(hpoints y (Finset.mem_filter.mp
            (RCN264.componentSeeds_subset E g.1 N R (S g) id C hy)).1).2.2.2.1)
          (fun y hy=>(hpoints y (Finset.mem_filter.mp
            (RCN264.componentSeeds_subset E g.1 N R (S g) id C hy)).1).2.2.1)
        exact (Nat.mul_le_mul_left (k+1) hc).trans (by
          simpa only [Nat.mul_comm] using Nat.div_mul_le_self (budget.weightedCost V C) (k+1))
      · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.mul_zero,Nat.zero_le]
    calc
      (k+1)*(S g).card≤(k+1)*∑ C:RCN264.RegularComponent E g.1 N R,
          (RCN264.componentSeeds E g.1 N R (S g) id C).card:=Nat.mul_le_mul_left _ hcard
      _= ∑ C:RCN264.RegularComponent E g.1 N R,
          (k+1)*(RCN264.componentSeeds E g.1 N R (S g) id C).card:=Finset.mul_sum _ _ _
      _≤ ∑ C:RCN264.RegularComponent E g.1 N R,budget.weightedCost V C:=Finset.sum_le_sum (fun C _=>hlocal C)
      _≤_:=budget.DGB V
  have hc:=(Finset.card_le_card hcoverage).trans Finset.card_biUnion_le
  calc
    (k+1)*points.card≤(k+1)*∑ g: ↥(RCN084.activeFactors carrier N),(S g).card:=Nat.mul_le_mul_left _ hc
    _= ∑ g: ↥(RCN084.activeFactors carrier N),(k+1)*(S g).card:=Finset.mul_sum _ _ _
    _≤ ∑ g: ↥(RCN084.activeFactors carrier N),flagMixed (exactFlag g.1) q V:=Finset.sum_le_sum (fun g _=>hcount g)
    _≤_:=RCN084.activeFactors_mixed_sum_le carrier N hcarrier p q V hflag
end
end CBU
end SubmissionLower
end ProximityPrize
end MergedPart3
section MergedPart4
namespace ProximityPrize
namespace SubmissionLower
namespace AUK
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN072 RCN076 RCN084 RCN095 RCN134 RCN136
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN207 RCN208 RCN237 RCN264 RCN313 RCN341 RCN344
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open CBU
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E:Type} [Field K] [Field Ω] [Field E] [IsAlgClosed Ω] [IsAlgClosed E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]
local instance:DecidableEq Ω:=Classical.decEq Ω
local instance:DecidableEq E:=Classical.decEq E
omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E] in
theorem US (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K):
    RCN208.scalarPolynomialMap Ω E (surfaceMap phi F)=
      surfaceMap ((algebraMap Ω E).comp phi) F:=by
  simp only [RCN208.scalarPolynomialMap,surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]
theorem FSO {R:Type*} [CommRing R] (F H G:R):
    filteredCut 0 (fun _:Fin 1=>F) H G=F:=by
  simp [filteredCut]
omit [IsAlgClosed Ω] in
theorem DLA {ι:Type} [Fintype ι]
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (carrier:MvPolynomial (Fin 3) Ω) (p q:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:RCN095.PolynomialInFlag p carrier)
    (ell:MvPolynomial (Fin 3) Ω) (hell:RCN095.PolynomialInFlag q ell)
    (c:ℕ) [CharP E c]
    (hdeg:p.zOnly+p.yz+p.all<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c)
    (P:SecondJetSupport.Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(SecondJetCoefficients.asS P).natDegree)
    (hdiv: ∀j≤k,F ∣ SecondJetClearedHelper.helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) Ω) (target:Ω)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (old:ι→RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (SecondJetCoefficients.asS P).leadingCoeff))
    (hold:Function.Injective old)
    (projection: ∀i,RCN344.SeparableCoordinate Ω (RCN002.CoordinateField Ω (old i).1))
    (hvalue: ∀i,RCN344.SeparableCoordinate.value Ω (RCN002.CoordinateField Ω (old i).1) (projection i)=
      RCN002.coordinateEvaluation Ω (old i).1 ell):
    (k+1)*(∑ i,RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old i).1) (projection i))≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0):=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let G:=surfaceMap phi (polyG K F)
  let L:=surfaceMap phi (SecondJetCoefficients.asS P).leadingCoeff
  let R:=H*L
  let M:=RCN207.movingEquation H G Q A target
  have hderiv:H ∈ Ideal.span
      ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set (MvPolynomial (Fin 3) Ω)):=by
    let carrierIdeal:=Ideal.span
      ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set (MvPolynomial (Fin 3) Ω))
    have hcar:carrier ∈ carrierIdeal:=Ideal.subset_span (by simp)
    have hdc:MvPolynomial.pderiv (1:Fin 3) carrier ∈ carrierIdeal:=Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩:=hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F) ∈ carrierIdeal
    rw [← RCN267.surfaceMap_pderiv_R,hb,MvPolynomial.pderiv_mul]
    exact carrierIdeal.add_mem (carrierIdeal.mul_mem_right b hdc)
      (carrierIdeal.mul_mem_right (MvPolynomial.pderiv (1:Fin 3) b) hcar)
  let mu:=RCN208.scalarPolynomialMap Ω E
  let phiE:=(algebraMap Ω E).comp phi
  let prime:=fun i=>(old i).1
  letI: ∀i,Algebra (RatFunc Ω) (RCN002.CoordinateField Ω (prime i)):=
    fun i=>(projection i).embedding.toRingHom.toAlgebra
  letI: ∀i,IsScalarTower Ω (RatFunc Ω) (RCN002.CoordinateField Ω (prime i)):=
    fun i=>IsScalarTower.of_algebraMap_eq (fun a=>((projection i).embedding.commutes a).symm)
  letI: ∀i,FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω (prime i)):=fun i=>(projection i).finite
  letI: ∀i,Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω (prime i)):=fun i=>(projection i).separable
  let points:=RCN134.genericFiberPoints (B:=RatFunc Ω) (L:=E) prime
  let t:=algebraMap (RatFunc Ω) E (RCN202.rationalVariable Ω)
  let N:=MvPolynomial.C t-mu ell
  have hprime:Function.Injective prime:=by
    intro i j hij
    exact hold (Subtype.ext hij)
  have hNflag:RCN095.PolynomialInFlag q N:=
    RCN207.inFlag_sub_poly (inFlag_const _ _) (inFlag_map _ hell)
  have hmuM:mu M=RCN207.movingEquation (surfaceMap phiE (polyH K F))
      (surfaceMap phiE (polyG K F)) (mu Q) (mu A) (algebraMap Ω E target):=by
    simp only [M,RCN207.movingEquation,map_sub,map_mul]
    rw [show mu H=surfaceMap phiE (polyH K F) from US phi _,
      show mu G=surfaceMap phiE (polyG K F) from US phi _]
    simp only [mu,RCN208.scalarPolynomialMap,MvPolynomial.map_C]
  have certificate (i:ι) (f:RCN002.CoordinateField Ω (prime i)→ₐ[RatFunc Ω] E):
      let x:=RCN134.embeddingPoint (prime i) (f.restrictScalars Ω)
      MvPolynomial.eval x (mu carrier)=0∧MvPolynomial.eval x N=0∧
      MvPolynomial.eval x (mu M)=0∧MvPolynomial.eval x (mu R) ≠ 0∧
      RCN084.IsolatedPoint (mu carrier) N (mu M) x:=by
    let C0:RCN264.RegularComponent Ω carrier (filteredCut 0 (fun _:Fin 1=>M) R 0) R:=
      ⟨(old i).1,by simpa only [FSO] using (old i).2⟩
    letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C0.1):=
      (projection i).embedding.toRingHom.toAlgebra
    have hj:algebraMap (RatFunc Ω) (RCN002.CoordinateField Ω C0.1) (RCN202.rationalVariable Ω)=
        movingValue C0.1 R 0 ell 1:=by
      change RCN344.SeparableCoordinate.value Ω (RCN002.CoordinateField Ω (old i).1) (projection i)=_
      simpa only [movingValue,map_one,map_zero,mul_zero,zero_div,add_zero] using hvalue i
    have hone:(1:MvPolynomial (Fin 3) Ω) ∉ C0.1:=by
      intro h
      have hz:=(SecondJetComponentRoots.evaluation_zero_iff C0.1 1).mpr h
      exact one_ne_zero (by simpa only [map_one] using hz)
    have hc:=RCN202.VX carrier R 0 ell 1 0
      (fun _:Fin 1=>M) C0 hj hone f
    have hc' :
        let x:=RCN134.embeddingPoint (prime i) (f.restrictScalars Ω)
        MvPolynomial.eval x (mu carrier)=0∧MvPolynomial.eval x (mu R*N)=0∧
        MvPolynomial.eval x (mu M)=0∧MvPolynomial.eval x (mu R) ≠ 0∧
        RCN084.IsolatedPoint (mu carrier) (mu R*N) (mu M) x:=by
      simpa only [map_zero,map_one,RCN207.movingEquation,RCN207.eliminatedCut,FSO,
        mul_zero,sub_zero,mul_one,MvPolynomial.aeval_eq_eval] using hc
    dsimp only at hc' ⊢
    have hn:MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Ω)) N=0:=
      (mul_eq_zero.mp (by simpa only [map_mul] using hc'.2.1)).resolve_left hc'.2.2.2.1
    refine ⟨hc'.1,hn,hc'.2.2.1,hc'.2.2.2.1,?_⟩
    intro D hD hnot hp hF hN
    exact hc'.2.2.2.2 D hD hnot hp hF (D.mul_mem_left (mu R) hN)
  have hpoints: ∀x ∈ points,
      MvPolynomial.eval x (mu carrier)=0∧MvPolynomial.eval x N=0∧
      MvPolynomial.eval x (mu M)=0∧
      MvPolynomial.eval x (surfaceMap phiE (polyH K F)) ≠ 0∧
      MvPolynomial.eval x (surfaceMap phiE (SecondJetCoefficients.asS P).leadingCoeff) ≠ 0∧
      MvPolynomial.eval x (MvPolynomial.pderiv (1:Fin 3) (mu carrier)) ≠ 0:=by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩:=Finset.mem_image.mp hx
    have hc:=certificate i f
    have hRne:=hc.2.2.2.1
    have hHL:MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Ω)) (mu H) ≠ 0∧
        MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Ω)) (mu L) ≠ 0:=by
      simpa only [R,map_mul,mul_ne_zero_iff] using hRne
    have hHne:MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (polyH K F)) ≠ 0:=by simpa only [H,mu,US,phiE] using hHL.1
    have hLne:MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (SecondJetCoefficients.asS P).leadingCoeff) ≠ 0:=by simpa only [L,mu,US,phiE] using hHL.2
    have hd:=RCN076.map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval (RCN134.embeddingPoint (prime i) (f.restrictScalars Ω)))
      (mu carrier) (mu H) (RCN076.scalar_derivative_span carrier H hderiv) hc.1 hHL.1
    exact ⟨hc.1,hc.2.1,hc.2.2.1,hHne,hLne,hd⟩
  have hiso: ∀x ∈ points,RCN084.IsolatedPoint (mu carrier) N (mu M) x:=by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩:=Finset.mem_image.mp hx
    exact (certificate i f).2.2.2.2
  have hcar:mu carrier ∣ surfaceMap phiE F:=by
    simpa only [mu,US,phiE] using map_dvd mu hcarrierF
  have hmu:Function.Injective mu:=MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
  have hne:mu carrier ≠ 0:=fun hz=>hcarrier (hmu (by simpa only [map_zero] using hz))
  rw [hmuM] at hpoints hiso
  have hc:=DSR phiE F (mu carrier) N p q hne hcar
    (inFlag_map _ hflag) hNflag c hdeg hmix P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2 hfact
    (mu Q) (mu A) (algebraMap Ω E target) (inFlag_map _ hQ) (inFlag_map _ hA) points hpoints hiso
  have hcard:=RCN134.genericFiberPoints_card (B:=RatFunc Ω) (L:=E) prime hprime
  simpa only [points,hcard,RCN344.SeparableCoordinate.degree,prime] using hc
omit [IsAlgClosed Ω] in
theorem BIQ {ι:Type} [Fintype ι]
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (carrier:MvPolynomial (Fin 3) Ω) (p q:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:RCN095.PolynomialInFlag p carrier)
    (ell:MvPolynomial (Fin 3) Ω) (hell:RCN095.PolynomialInFlag q ell)
    (c:ℕ) [CharP E c]
    (hdeg:p.zOnly+p.yz+p.all<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c)
    (P:SecondJetSupport.Poly (K:=K)) (B U T s k n0:ℕ)
    (hS: ∀e ∈ P.support,e 1≤s)
    (hP: ∀e ∈ P.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧
      e 1+e 2+e 3+e 4≤T)
    (hBU:B≤U) (hUT:U≤T) (hdn:k+1≤n0)
    (hB:2*(n0-(k+1))≤B) (hn:n0≤(SecondJetCoefficients.asS P).natDegree)
    (hdiv: ∀j≤k,F ∣ SecondJetClearedHelper.helper P F (s-j) j)
    (h2:(2:E) ≠ 0) (hfact:(k.factorial:E) ≠ 0)
    (Q A:MvPolynomial (Fin 3) Ω) (target:Ω)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
    (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (old:ι→RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (SecondJetCoefficients.asS P).leadingCoeff))
    (hold:Function.Injective old)
    (projection: ∀i,Coordinate Ω (RCN002.CoordinateField Ω (old i).1))
    (hvalue: ∀i,RCN344.coordinateValue Ω (RCN002.CoordinateField Ω (old i).1) (projection i)=
      RCN002.coordinateEvaluation Ω (old i).1 ell):
    (k+1)*(∑ i,RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old i).1) (projection i))≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0):=by
  classical
  let Alive:Set ι:={i | ∃C,projection i=Sum.inr C}
  let sep:=fun i:Alive=>Classical.choose i.2
  have hsep (i:Alive):projection i.1=Sum.inr (sep i):=Classical.choose_spec i.2
  let old0:=fun i:Alive=>old i.1
  have hi0:Function.Injective old0:=by
    intro i j h
    exact Subtype.ext (hold h)
  have hv0 (i:Alive):
      RCN344.SeparableCoordinate.value Ω (RCN002.CoordinateField Ω (old0 i).1) (sep i)=
        RCN002.coordinateEvaluation Ω (old0 i).1 ell:=by
    have h:=hvalue i.1
    rw [hsep i] at h
    exact h
  have hsum:(∑ i,RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old i).1) (projection i))=
      ∑ i:Alive,RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old0 i).1) (sep i):=by
    apply Finset.sum_congr_set Alive
      (fun i=>RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω (old i).1) (projection i))
      (fun i=>RCN344.SeparableCoordinate.degree Ω (RCN002.CoordinateField Ω (old0 i).1) (sep i))
    · intro i hi
      simp only [hsep ⟨i,hi⟩,RCN344.coordinateDegree,Sum.elim_inr,old0]
    · intro i hi
      cases hp:projection i with
      | inl C=>simp only [RCN344.coordinateDegree,Sum.elim_inl]
      | inr C=>exact (hi ⟨C,hp⟩).elim
  rw [hsum]
  exact DLA (E:=E) phi F carrier p q hcarrier hcarrierF hflag ell hell
    c hdeg hmix P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2 hfact Q A target hQ hA
    old0 hi0 sep hv0
end
end AUK
end SubmissionLower
end ProximityPrize
end MergedPart4
section MergedPart5
namespace ProximityPrize
namespace SubmissionLower
namespace BFL
open scoped Classical BigOperators
open RCN002 RCN022 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN093 RCN095 RCN135 RCN136 RCN207
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open AUK
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 40000
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
local notation "Poly3" =>MvPolynomial (Fin 3) Ω
def linearZ:Poly3:=MvPolynomial.X 2
def linearU (a:Ω):Poly3:=MvPolynomial.X 0+MvPolynomial.C a*MvPolynomial.X 2
def linearA (b a:Ω):Poly3:=MvPolynomial.X 1+MvPolynomial.C b*MvPolynomial.X 0+
  MvPolynomial.C (b*a)*MvPolynomial.X 2
omit [IsAlgClosed Ω] in
theorem flag_X (i:Fin 3) (p:FlagDegree)
    (hi:InFlag p (Finsupp.single i 1)):RCN095.PolynomialInFlag p (MvPolynomial.X i:Poly3):=by
  intro e he
  have:e=Finsupp.single i 1:=by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
omit [IsAlgClosed Ω] in
theorem flag_add {p:FlagDegree} {A B:Poly3}
    (hA:RCN095.PolynomialInFlag p A) (hB:RCN095.PolynomialInFlag p B):RCN095.PolynomialInFlag p (A+B):=by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
omit [IsAlgClosed Ω] in
theorem flag_scale {p:FlagDegree} {A:Poly3} (c:Ω)
    (hA:RCN095.PolynomialInFlag p A):RCN095.PolynomialInFlag p (MvPolynomial.C c*A):=by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)
theorem linearZ_flag:RCN095.PolynomialInFlag unitZFlag (linearZ:Poly3):=
  flag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem linearU_flag (a:Ω):RCN095.PolynomialInFlag unitYZFlag (linearU a):=
  flag_add (flag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (flag_scale a (flag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem linearA_flag (b a:Ω):RCN095.PolynomialInFlag unitAllFlag (linearA b a):=
  flag_add (flag_add (flag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (flag_scale b (flag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (flag_scale (b*a) (flag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))
theorem EHY {G N R:Poly3} (p q:FlagDegree)
    (base: ∀C:RCN264.RegularComponent Ω G N R,RCN341.SeparableLiteralCoordinate C.1)
    (hY: ∀C:RCN264.RegularComponent Ω G N R,RCN037.LiteralProjectionGate C 0)
    (hZ: ∀C:RCN264.RegularComponent Ω G N R,RCN037.LiteralProjectionGate C 2)
    (hderiv:MvPolynomial.pderiv (1:Fin 3) G ≠ 0)
    (hG:Irreducible G) (hproper: ¬G ∣ N)
    (hGflag:RCN095.PolynomialInFlag p G) (hNflag:RCN095.PolynomialInFlag q N):
    ∃(unit:EE base p q) (a b:Ω),
      (∀C:RCN264.RegularComponent Ω G N R,RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.zProjection C)=
        RCN002.coordinateEvaluation Ω C.1 linearZ)∧
      (∀C:RCN264.RegularComponent Ω G N R,RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.yzProjection C)=
        RCN002.coordinateEvaluation Ω C.1 (linearU a))∧
      (∀C:RCN264.RegularComponent Ω G N R,RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.NV C)=
        RCN002.coordinateEvaluation Ω C.1 (linearA b a)):=by
  obtain ⟨D⟩:=ALD base hY hZ hderiv
  let unit:=AUZ p q base hY hZ hderiv D hG hproper
    ((RCN095.support_subset_flagSupport_iff _ _).mpr hGflag) ((RCN095.support_subset_flagSupport_iff _ _).mpr hNflag)
  refine ⟨unit,D.lam,D.mu,?_,?_,?_⟩
  · intro C
    exact unit.zValue C
  · intro C
    have hv:RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.yzProjection C)=affineU Ω C.1 D.lam:=by
      change RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1)
        (RCN042.coordinateOfGate (affineU Ω C.1 D.lam) (D.uGate C))=_
      exact RCN042.coordinateOfGate_value _ _
    rw [hv,RCN002.coordinateEvaluation_eq_aeval]
    simp only [linearU,affineU,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]
  · intro C
    have hv:RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (unit.NV C)=
        affineV Ω C.1 D.mu (D.mu*D.lam):=by
      change (RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω C.1)
        (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.GN C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)=_
      exact RCN022.elementEmbedding_variable Ω (RCN002.CoordinateField Ω C.1) _ _
    rw [hv,RCN002.coordinateEvaluation_eq_aeval]
    simp only [linearA,affineV,map_add,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.smul_def]
end
end BFL
end SubmissionLower
end ProximityPrize
end MergedPart5
section MergedPart6
namespace ProximityPrize
namespace SubmissionLower
namespace BD
open scoped Classical BigOperators
open RCN002 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN095 RCN136 RCN207 RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
open SecondJetSupport (Box Poly)
open SecondJetCoefficients (liftExponent)
open SecondJetClearedHelper (cleared helper)
open BFL AUK
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 60000
set_option maxRecDepth 50000
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
local notation "Poly3" =>MvPolynomial (Fin 3) Ω
theorem EXX
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (source:Fin 3→MovingFiberThreeSources6811.Source F) (D:ℕ) (hD: ∀j,(source j).d ∣ D)
    (carrier:Poly3) (p q W:FlagDegree)
    (hcarrier:Irreducible carrier) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:RCN095.PolynomialInFlag p carrier)
    (c:ℕ) [CharP Ω c] (hunit:2*(p.zOnly+p.yz+p.all)<c)
    (h2:(2:Ω) ≠ 0) (hfact: ∀j,((source j).k.factorial:Ω) ≠ 0)
    (Q A:Poly3) (target:Ω)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (hderiv:MvPolynomial.pderiv (1:Fin 3) carrier ≠ 0)
    (hproper: ¬carrier ∣ RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
    (hNflag:RCN095.PolynomialInFlag q (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target))
    (base: ∀C:RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi),RCN341.SeparableLiteralCoordinate C.1)
    (hY: ∀C:RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi),RCN037.LiteralProjectionGate C 0)
    (hZ: ∀C:RCN264.RegularComponent Ω carrier
      (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi),RCN037.LiteralProjectionGate C 2)
    (cut:Poly3) (hcut:RCN095.PolynomialInFlag W cut) (points:Finset (Fin 3→Ω))
    (hpoints: ∀x ∈ points,MvPolynomial.eval x carrier=0∧
      MvPolynomial.eval x (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)=0∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi) ≠ 0∧
      MvPolynomial.aeval x cut=0)
    (hisolated: ∀x ∈ points,RCN084.IsolatedPoint carrier
      (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x):
    D*points.card≤ ∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*(D/(source j).d)*flagMixed p (MovingFiberThreeSources6811.direction j) (source j).flag:=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let N:=RCN207.movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let R:=H*∏ j,(source j).leading phi
  let Family:=RCN264.RegularComponent Ω carrier N R
  obtain ⟨unit,a,b,hzv,hyv,hav⟩:=EHY p q base hY hZ hderiv hcarrier hproper hflag hNflag
  let ell:Fin 3→Poly3:= ![linearZ,linearU a,linearA b a]
  let projection:(j:Fin 3)→(C:Family)→Coordinate Ω (RCN002.CoordinateField Ω C.1):=
    ![unit.zProjection,unit.yzProjection,unit.NV]
  have hell (j:Fin 3):RCN095.PolynomialInFlag (MovingFiberThreeSources6811.direction j) (ell j):=by
    fin_cases j
    · exact linearZ_flag
    · exact linearU_flag a
    · exact linearA_flag b a
  have hvalue (j:Fin 3) (C:Family):
      RCN344.coordinateValue Ω (RCN002.CoordinateField Ω C.1) (projection j C)=RCN002.coordinateEvaluation Ω C.1 (ell j):=by
    fin_cases j
    · exact hzv C
    · exact hyv C
    · exact hav C
  have hH (C:Family):H ∉ C.1:=by
    intro h
    exact _Q6 Ω carrier N R C
      (C.1.mul_mem_right (∏ j,(source j).leading phi) h)
  have hL (j:Fin 3) (C:Family):(source j).leading phi ∉ C.1:=by
    intro h
    have hd:(source j).leading phi ∣ R:=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j=>(source j).leading phi) (Finset.mem_univ j)) H
    exact _Q6 Ω carrier N R C (C.1.mem_of_dvd hd h)
  let forget (j:Fin 3) (C:Family):RCN264.RegularComponent Ω carrier N (H*(source j).leading phi):=
    ⟨C.1,(AJF Ω).mpr ⟨AAS Ω carrier N R C,by
      intro h
      exact ((inferInstance:C.1.IsPrime).mem_or_mem h).elim (hH C) (hL j C)⟩⟩
  have hinj (j:Fin 3):Function.Injective (forget j):=by
    intro C C' h
    have hh:=congrArg (fun C0:RCN264.RegularComponent Ω carrier N (H*(source j).leading phi)=>C0.1) h
    exact Subtype.ext hh
  let Ext:=AlgebraicClosure (RatFunc Ω)
  letI:Algebra Ω Ext:=((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI:SMul (RatFunc Ω) Ext:=(inferInstance:Algebra (RatFunc Ω) Ext).toSMul
  letI:SMul Ω Ext:=(inferInstance:Algebra Ω Ext).toSMul
  letI:IsScalarTower Ω (RatFunc Ω) Ext:=by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI:CharP Ext c:=by infer_instance
  have h2e:(2:Ext) ≠ 0:=by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hproj (j:Fin 3):
      (source j).d*(∑ C:Family,RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω C.1) (projection j C))≤
        flagMixed p (MovingFiberThreeSources6811.direction j) (source j).flag:=by
    have hfe:((source j).k.factorial:Ext) ≠ 0:=by
      simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne (hfact j)
    have hdirection:(MovingFiberThreeSources6811.direction j).zOnly+(MovingFiberThreeSources6811.direction j).yz+(MovingFiberThreeSources6811.direction j).all=1:=by fin_cases j<;>rfl
    exact BIQ (E:=Ext) phi F carrier p (MovingFiberThreeSources6811.direction j) hcarrier.ne_zero hcarrierF hflag
      (ell j) (hell j) c (by omega) (by rw [hdirection,mul_one];exact hunit)
      (source j).P (source j).B (source j).U (source j).T (source j).s (source j).k (source j).n0
      (source j).hS (source j).hshape (source j).hBU (source j).hUT (source j).hdn (source j).hB
      (source j).hn (source j).hdiv h2e hfe Q A target hQ hA (forget j) (hinj j) (projection j) (hvalue j)
  have hscaled (j:Fin 3):
      D*(∑ C:Family,RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω C.1) (projection j C))≤
        (D/(source j).d)*flagMixed p (MovingFiberThreeSources6811.direction j) (source j).flag:=by
    have h:=Nat.mul_le_mul_left (D/(source j).d) (hproj j)
    simpa only [← Nat.mul_assoc,Nat.div_mul_cancel (hD j)] using h
  let budget:=unit.toFE
  have hcard:points.card≤ ∑ C:Family,budget.weightedCost W C:=by
    apply (WX Ω carrier N R points id
      (fun x hx=>(hpoints x hx).1) (fun x hx=>(hpoints x hx).2.1)
      (fun x hx=>(hpoints x hx).2.2.1)).trans
    apply Finset.sum_le_sum
    intro C _
    by_cases he:(RCN264.componentSeeds Ω carrier N R points id C).Nonempty
    · obtain ⟨x,hx⟩:=he
      have hxS:=RCN264.componentSeeds_subset Ω carrier N R points id C hx
      have hxC:=RCN264.componentSeeds_on_prime Ω carrier N R points id C x hx
      apply (budget.primeBudget C).zero_le W cut hcut
        (hisolated x hxS C.1 inferInstance (PU Ω carrier N R C)
          hxC (EN Ω carrier N R C) (GV Ω carrier N R C))
      · intro y hy
        exact RCN264.componentSeeds_on_prime Ω carrier N R points id C y hy
      · intro y hy
        exact (hpoints y (RCN264.componentSeeds_subset Ω carrier N R points id C hy)).2.2.2
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  have hs:=Finset.sum_le_sum (fun j (_:j ∈ (Finset.univ:Finset (Fin 3)))=>
    Nat.mul_le_mul_left (MovingFiberThreeSources6811.weight W j) (hscaled j))
  have hb:D*(∑ C:Family,budget.weightedCost W C)≤
      ∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*(D/(source j).d)*flagMixed p (MovingFiberThreeSources6811.direction j) (source j).flag:=by
    have hl:D*(∑ C:Family,budget.weightedCost W C)=
        ∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*(D*∑ C:Family,RCN344.coordinateDegree Ω (RCN002.CoordinateField Ω C.1) (projection j C)):=by
      simp only [Fin.sum_univ_three,projection,MovingFiberThreeSources6811.weight,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
        budget,FE.weightedCost,EE.toFE,
        QZ.toFE,EE.toQZ,
        Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    have hr:(∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*(D/(source j).d)*flagMixed p (MovingFiberThreeSources6811.direction j) (source j).flag)=
        ∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*((D/(source j).d)*flagMixed p (MovingFiberThreeSources6811.direction j) (source j).flag):=by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hl,hr]
    exact hs
  exact (Nat.mul_le_mul_left D hcard).trans hb
theorem DMO
    (phi:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
    (source:Fin 3→MovingFiberThreeSources6811.Source F) (D:ℕ) (hD: ∀j,(source j).d ∣ D)
    (carrier:Poly3) (p q W:FlagDegree)
    (hcarrier:carrier ≠ 0) (hcarrierF:carrier ∣ surfaceMap phi F)
    (hflag:RCN095.PolynomialInFlag p carrier)
    (c:ℕ) [CharP Ω c] (hunit:2*(p.zOnly+p.yz+p.all)<c)
    (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c)
    (h2:(2:Ω) ≠ 0) (hfact: ∀j,((source j).k.factorial:Ω) ≠ 0)
    (Q A:Poly3) (target:Ω)
    (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hA:RCN095.PolynomialInFlag unitYZFlag A)
    (hNflag:RCN095.PolynomialInFlag q (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target))
    (cut:Poly3) (hcut:RCN095.PolynomialInFlag W cut) (points:Finset (Fin 3→Ω))
    (hpoints: ∀x ∈ points,MvPolynomial.eval x carrier=0∧
      MvPolynomial.eval x (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)=0∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*∏ j,(source j).leading phi) ≠ 0∧
      MvPolynomial.aeval x cut=0)
    (hisolated: ∀x ∈ points,RCN084.IsolatedPoint carrier
      (RCN207.movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x):
    D*points.card≤ ∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*(D/(source j).d)*flagMixed p (MovingFiberThreeSources6811.direction j) (source j).flag:=by
  classical
  let H:=surfaceMap phi (polyH K F)
  let N:=RCN207.movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let R:=H*∏ j,(source j).leading phi
  have hdeg:p.zOnly+p.yz+p.all<c:=by omega
  have hderiv:H ∈ Ideal.span ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set Poly3):=by
    let I:=Ideal.span ({carrier,MvPolynomial.pderiv (1:Fin 3) carrier}:Set Poly3)
    have hc:carrier ∈ I:=Ideal.subset_span (by simp)
    have hd:MvPolynomial.pderiv (1:Fin 3) carrier ∈ I:=Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩:=hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F) ∈ I
    rw [← RCN267.surfaceMap_pderiv_R,hb,MvPolynomial.pderiv_mul]
    exact I.add_mem (I.mul_mem_right b hd) (I.mul_mem_right (MvPolynomial.pderiv (1:Fin 3) b) hc)
  have hcover: ∀x ∈ points,∃g: ↥(RCN084.activeFactors carrier N),MvPolynomial.eval x g.1=0:=by
    intro x hx
    have hp:=hpoints x hx
    have hh:MvPolynomial.eval x H ≠ 0:=by
      have hr:MvPolynomial.eval x H*MvPolynomial.eval x (∏ j,(source j).leading phi) ≠ 0:=by
        simpa only [map_mul] using hp.2.2.1
      exact (mul_ne_zero_iff.mp hr).1
    exact AAU carrier N cut R hcarrier x hp.1 hp.2.2.2 hp.2.2.1
      (RCN076.map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval x) carrier H hderiv hp.1 hh) (hisolated x hx)
  obtain ⟨base,hY,hZ⟩:=AOE carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g: ↥(RCN084.activeFactors carrier N)):Finset (Fin 3→Ω):=
    points.filter (fun x=>MvPolynomial.eval x g.1=(0:Ω))
  have hcoverage:points ⊆ Finset.univ.biUnion S:=by
    intro x hx
    obtain ⟨g,hg⟩:=hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g: ↥(RCN084.activeFactors carrier N)):
      D*(S g).card≤ ∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*(D/(source j).d)*flagMixed (exactFlag g.1) (MovingFiberThreeSources6811.direction j) (source j).flag:=by
    have hg:=RCN084.activeFactors_spec carrier N g
    have hgtotal:(exactFlag g.1).zOnly+(exactFlag g.1).yz+(exactFlag g.1).all≤
        p.zOnly+p.yz+p.all:=by
      rw [(RCN084.exactFlag_cumulative g.1).2.2]
      exact (RCN071.weightedTotalDegree_le_of_dvd_fin3 RCN095.flagTotalWeights g.1 carrier hg.2.1 hcarrier).trans
        (RCN084.inFlag_weight_caps carrier p hflag).2.2
    apply EXX phi F source D hD g.1 (exactFlag g.1) q W hg.1
      (dvd_trans hg.2.1 hcarrierF) (RCN084.polynomialIn_exactFlag g.1) c (by omega) h2 hfact
      Q A target hQ hA hg.2.2.2 hg.2.2.1 hNflag (base g) (hY g) (hZ g) cut hcut (S g)
    · intro x hx
      have hs:=Finset.mem_filter.mp hx
      have hp:=hpoints x hs.1
      exact ⟨hs.2,hp.2.1,hp.2.2.1,hp.2.2.2⟩
    · intro x hx J hj hnot hpoint hG hN
      exact hisolated x (Finset.mem_filter.mp hx).1 J hj hnot hpoint (J.mem_of_dvd hg.2.1 hG) hN
  calc
    D*points.card≤D*∑ g: ↥(RCN084.activeFactors carrier N),(S g).card:=
      Nat.mul_le_mul_left _ ((Finset.card_le_card hcoverage).trans Finset.card_biUnion_le)
    _= ∑ g: ↥(RCN084.activeFactors carrier N),D*(S g).card:=Finset.mul_sum _ _ _
    _≤ ∑ g: ↥(RCN084.activeFactors carrier N),∑ j:Fin 3,
        MovingFiberThreeSources6811.weight W j*(D/(source j).d)*flagMixed (exactFlag g.1) (MovingFiberThreeSources6811.direction j) (source j).flag:=
      Finset.sum_le_sum (fun g _=>hcount g)
    _= ∑ j:Fin 3,MovingFiberThreeSources6811.weight W j*(D/(source j).d)*
        ∑ g: ↥(RCN084.activeFactors carrier N),flagMixed (exactFlag g.1) (MovingFiberThreeSources6811.direction j) (source j).flag:=by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _≤_:=Finset.sum_le_sum (fun j _=>Nat.mul_le_mul_left _
      (RCN084.activeFactors_mixed_sum_le carrier N hcarrier p (MovingFiberThreeSources6811.direction j) (source j).flag hflag))
end
end BD
end SubmissionLower
end ProximityPrize
end MergedPart6
section MergedPart9
namespace ProximityPrize
namespace SubmissionLower
namespace MZ
open RCN260 GB
set_option autoImplicit false
set_option maxHeartbeats 1400000
def EIX (L U S Rcap Ycap Tcap qt qy qr:ℕ):Prop:=
  2*131073*131071*((S:ℤ)*Ycap+(U:ℤ)*Rcap)+131073*((S:ℤ)-131071*U)≤49988*(qt:ℤ)∧
  2*131073*131071*((L:ℤ)*Rcap+(S:ℤ)*Tcap)+131073*((S:ℤ)-131071*L)+81086*49988*S≤49988*(qy:ℤ)∧
  2*131073*131071*((L:ℤ)*Ycap+(U:ℤ)*Tcap)+131073*((L:ℤ)+U)+81086*49988*U≤49988*(qr:ℤ)
instance (L U S Rcap Ycap Tcap qt qy qr:ℕ):Decidable (EIX L U S Rcap Ycap Tcap qt qy qr):=by
  unfold EIX;infer_instance
end MZ
end SubmissionLower
end ProximityPrize
end MergedPart9
section MergedPart10
namespace ProximityPrize
namespace SubmissionLower
namespace Lower80899
namespace SourceSound
open RCN095 RCN223 RCN260 RCN294 DY
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
open Lower80899.FactorSwitch Lower80899.PowerRoute
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
open Lower80899.Oracle
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Phase00
def potential:LocatorPhase6800Oracle.Potential:=⟨4856907113462,294416931316545,1328544529344752⟩
end Phase00
namespace Phase01
def potential:LocatorPhase6800Oracle.Potential:=⟨2424497498887,181552970037742,823938069474974⟩
end Phase01
namespace Phase02
def potential:LocatorPhase6800Oracle.Potential:=⟨2424497498887,172890044818405,784022818260644⟩
end Phase02
namespace Phase03
def potential:LocatorPhase6800Oracle.Potential:=⟨1211739014415,76173542431626,344856718688116⟩
end Phase03
namespace Phase04
def potential:LocatorPhase6800Oracle.Potential:=⟨452668004921,49942536091672,172064434241885⟩
end Phase04
namespace Phase05
def potential:LocatorPhase6800Oracle.Potential:=⟨75620347319,5363489347858,24356253950417⟩
end Phase05
namespace Phase06
def potential:LocatorPhase6800Oracle.Potential:=⟨1053400409421,139503507383908,639880263888768⟩
end Phase06
namespace PhaseFinal
def potential:LocatorPhase6800Oracle.Potential:=⟨0,5883042805024,48590536410482⟩
end PhaseFinal
end SourceSound
end Lower80899
end SubmissionLower
end ProximityPrize
end MergedPart10
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace BB
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open SecondJetSpecialize (specialize)
open AQ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {K N:Type*} [Field K] [Fintype N]
def cutoff (m k n0 h:ℕ):ℕ:=m*181059-SecondJetRelaxedDifferentiation.reserve k n0 h*49990
end
end BB
end MergedPart0
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace BIM
open MvPolynomial
open SecondJetSupport (Box Poly)
open SecondJetGlobalSupport (localize)
open SecondJetSpecialize (specialize)
open SecondJetCoefficients (liftExponent)
open AQ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N:Type*} [Field K]
theorem ATR (P:SecondJetSupport.Poly (K:=K)) (m k n0 d:ℕ)
    (hdm:d<m) (hdn:d<n0) (hfact:(d.factorial:K) ≠ 0)
    (hP: ∀e ∈ P.support,
      e 0+131071*e 2+131070*e 3+131069*e 1+
        SecondJetRelaxedDifferentiation.reserve k n0 (e 1)*49990<m*181059)
    (nodes:N ↪ K) (u0 u1:N→K)
    (hcontact: ∀i,MvPolynomial.X 0^m ∣ SecondJetDifferentiation.substitute (K:=K)
      (SecondJetGlobalSupport.localize (nodes i) (u0 i) (u1 i) P))
    (f:Polynomial K) (hf:f.natDegree≤131071) (z:K) (S:Finset N)
    (hS:181059≤S.card) (hvalues: ∀i ∈ S,f.eval (nodes i)=u0 i+u1 i*z)
    (hh: ∀j,d<j→SecondJetCoefficientSpecialization.coefficientSpecialize f z ((SecondJetCoefficients.asS P).coeff j)=0):
    SecondJetCoefficientSpecialization.coefficientSpecialize f z ((SecondJetCoefficients.asS P).coeff d)=0:=by
  have hweight: ∀e ∈ ((SecondJetCoefficients.asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2<(m-d)*181059:=by
    intro e he
    have hb:=hP _ (SecondJetCoefficients.coefficient_support P d e he)
    obtain ⟨h0,h1,h2,h3,h4⟩:=SecondJetCoefficients.lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [SecondJetRelaxedDifferentiation.reserve,if_pos hdn] at hb
    omega
  have hdeg:=MovingFiberLeadingCoefficient6815.coefficient_degree ((SecondJetCoefficients.asS P).coeff d) f z 131071 ((m-d)*181059)
    hf (by omega) hweight
  have htop:=MovingFiberLeadingCoefficient6815.specialize_top P f z d hh
  have hv:SecondJetSpecialize.specialize f z ((pderiv 1)^[d] P)=0:=by
    refine CAG.ALK _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
    · rw [htop]
      have hs:=Polynomial.natDegree_smul_le d.factorial
        (SecondJetCoefficientSpecialization.coefficientSpecialize f z ((SecondJetCoefficients.asS P).coeff d))
      exact (hs.trans_lt hdeg).trans_le (Nat.mul_le_mul_left (m-d) hS)
  rw [htop,nsmul_eq_mul] at hv
  apply (mul_eq_zero.mp hv).resolve_left
  simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr hfact)
end
end BIM
end MergedPart0
section MergedPart2
namespace Lower80899
namespace Caps
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq LocatorBatchPhase6800.K:=Classical.decEq LocatorBatchPhase6800.K
local instance:DecidableEq Lower80811.Counting.I:=Classical.decEq Lower80811.Counting.I
abbrev AKernel (u0 u1:Lower80811.Counting.I→LocatorBatchPhase6800.K):=
  IJ (K:=LocatorBatchPhase6800.K) 24285490 131071 104142 40 134 IRSProfile.domain u0 u1
end
end Caps
end Lower80899
end MergedPart2
end SubmissionLower
end ProximityPrize
end
section
section MergedPart4
namespace ProximityPrize
namespace SubmissionLower
namespace CBN
open RCN055 RCN313
variable {K:Type*} [Field K]
local notation "Poly4" =>MvPolynomial (Fin 4) K
noncomputable section
@[simp] theorem signedOddScalar_zero:BoundaryTailCoefficientFacts.signedOddScalar (K:=K) 0=1:=rfl
end
end CBN
end SubmissionLower
end ProximityPrize
end MergedPart4
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart3
namespace _Q19
set_option maxHeartbeats 1000000
open RCN002 RCN004 RCN005 RCN095 RCN125 RCN371
open RCN095 renaming PolynomialInFlag → BI
open RCN371 renaming RationalPolynomials → KU
open scoped BigOperators
theorem BOC {Omega:Type} [Field Omega]
    (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hZ:Transcendental Omega (coordinate Omega P 2))
    (prime:Nat) [CharP Omega prime]
    (G T:MvPolynomial (Fin 3) Omega)
    (hG:Irreducible G) (hGmem:G ∈ P) (hTmem:T ∈ P)
    (hproper: ¬G ∣ T)
    (hR:MvPolynomial.pderiv (1:Fin 3) G ≠ 0)
    (pG pT:FlagDegree)
    (hGflag:RCN095.PolynomialInFlag pG G)
    (hTflag:RCN095.PolynomialInFlag pT T)
    (hsmall:flagMixed pG pT unitZFlag<prime):
    letI:=RCN005.rationalBaseAlgebra Omega P 2 hZ
    FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega P)∧
      Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega P):=by
  let Q:Unit→Ideal (MvPolynomial (Fin 3) Omega):=fun _=>P
  have hinj:Function.Injective Q:=by
    intro i j _
    exact Subsingleton.elim i j
  letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega P):=
    RCN005.rationalBaseAlgebra Omega P 2 hZ
  have htZ: ∀i:Unit,Transcendental Omega
      (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder_p19 0))):=by
    intro i
    simpa [Q,zOrder_p19,Equiv.swap_apply_def] using hZ
  have hembZ (i:Unit):
      RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega (Q i))
        (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder_p19 0))) (htZ i)=
      RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega P) (coordinate Omega P 2) hZ:=
    by
      have hx:RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder_p19 0))=
          coordinate Omega P 2:=by simp [Q,zOrder_p19]
      simp only [hx]
      rfl
  have hgenZ: ∀i:Unit,
      letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega (Q i)):=
        (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega (Q i))
          (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder_p19 0)))
          (htZ i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc Omega)
        ({RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder_p19 2)),
          RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder_p19 1))}:
            Set (RCN002.CoordinateField Omega (Q i)))= ⊤ :=by
    intro i
    rw [hembZ i]
    simpa [Q,zOrder_p19,Equiv.swap_apply_def] using RCN093.BKE Omega P 0 0 0 hZ
  have hfamily:=RCN093.RG
    (K:=Omega) (Q:=Q) hinj 0 0 0 zOrder_p19 htZ hgenZ
      G T hG (fun _=>hGmem) (fun _=>hTmem) hproper
      (by simpa using (RCN117.MV 0 0 G hR).2)
      pG.all pT.all (pG.yz+pG.all) (pT.yz+pT.all)
      (flagMixed pG pT unitZFlag) (by
        intro hzero
        apply hproper
        rw [hzero]
        exact dvd_zero G)
      (by
        simpa using (RCN123.LQ pG G 0 0 0
          ((RCN095.support_subset_flagSupport_iff pG G).2 hGflag)).zOuter)
      (by
        simpa using (RCN123.LQ pT T 0 0 0
          ((RCN095.support_subset_flagSupport_iff pT T).2 hTflag)).zOuter)
      (by
        simpa using (RCN123.LQ pG G 0 0 0
          ((RCN095.support_subset_flagSupport_iff pG G).2 hGflag)).zTotal)
      (by
        simpa using (RCN123.LQ pT T 0 0 0
          ((RCN095.support_subset_flagSupport_iff pT T).2 hTflag)).zTotal)
      (RCN121.z_flag_trapezoid_budget pG pT)
  have hfd:FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega P):=by
    convert hfamily.1 () using 1
    congr 1
    exact congrArg (fun e:RatFunc Omega→ₐ[Omega] RCN002.CoordinateField Omega P=>e.toRingHom.toAlgebra) (hembZ ()).symm
  have hrank:Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega P)≤
      flagMixed pG pT unitZFlag:=by
    have hs:=hfamily.2
    simp only [Fintype.sum_unique] at hs
    convert hs using 1
    congr 2
    exact congrArg (fun e:RatFunc Omega→ₐ[Omega] RCN002.CoordinateField Omega P=>e.toRingHom.toAlgebra) (hembZ ()).symm
  letI:=hfd
  refine ⟨hfd,⟨fun x=> ?_⟩⟩
  have hint:IsIntegral (RatFunc Omega) x:=Algebra.IsIntegral.isIntegral x
  exact (RCN364.WS prime
    (minpoly (RatFunc Omega) x) x (minpoly.ne_zero hint) (minpoly.aeval _ _)
    ((minpoly.natDegree_le (A:=RatFunc Omega) x).trans_lt (hrank.trans_lt hsmall))).2
end _Q19
end MergedPart3
section MergedPart4
namespace AGZ
open scoped Classical BigOperators
open _Q19
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN198 RCN086 RCN263 RCN089
open RCN319 renaming specialization → BM
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K→+*Omega} {Gamma:Finset K} {x:Iota→K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem UI
   (S:FH phi Gamma x pchar e flag w (support a b s))
   (hproper:¬S.G ∣ RCN086.globalTailCut phi S.F (w+1))
   (hflagChar:flag.yz+flag.all<pchar∧flag.all<pchar∧
     flag.zOnly+flag.yz+flag.all<pchar)
   (hmixed:flagMixed flag (RCN263.reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag<pchar):
   ∃(base:∀C:RCN264.RegularComponent Omega S.G
       (RCN089.reducedGlobalTailCut phi (support a b s) S.F (w+1))
       (CR phi S.F),RCN341.SeparableLiteralCoordinate C.1),
     ∃(hactive:∀C:RCN264.RegularComponent Omega S.G
         (RCN089.reducedGlobalTailCut phi (support a b s) S.F (w+1))
         (CR phi S.F),
         KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
             (coordinate Omega C.1 0) ≠ 0∨
           KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
             (coordinate Omega C.1 2) ≠ 0),
       ∃(hZ:∀C:RCN264.RegularComponent Omega S.G
           (RCN089.reducedGlobalTailCut phi (support a b s) S.F (w+1))
           (CR phi S.F),RCN037.LiteralProjectionGate C 2),
         Nonempty (JO base hactive
           (RCN315.EH S)):=by
 classical
 let supp:=support a b s
 let T:=RCN086.globalTailCut phi S.F (w+1)
 let Tred:=RCN089.reducedGlobalTailCut phi supp S.F (w+1)
 let H:=CR phi S.F
 have hd:S.G ∣ T-Tred:=
   S.RR.trans (RCN089.globalTailCut_sub_reduced_dvd phi supp S.F (w+1))
 have hproperRed:¬S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T,Tred,sub_add_cancel] using this
 have hGflag:RCN095.PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:RCN275.ResidualSupportData supp S.F:=
   ⟨S.AFS,S.ACG,S.UT⟩
 have hTflag:RCN095.PolynomialInFlag
     (RCN263.reducedResidualAgreementFlag supp (w+1)) Tred:=
   AOF phi supp Hsupport (w+1)
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.WD
     hGflag
 have hGdegree:∀j:Fin 3,S.G.degreeOf j<pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hR:=RCN315.EH S
 let hZ:∀C:RCN264.RegularComponent Omega S.G Tred H,RCN037.LiteralProjectionGate C 2:=by
   intro C htr
   exact BOC C.1 htr pchar S.G Tred
     S.MW (EN Omega S.G Tred H C)
     (GV Omega S.G Tred H C) hproperRed hR
     flag (RCN263.reducedResidualAgreementFlag supp (w+1)) hGflag hTflag hmixed
 let choiceData:∀C:RCN264.RegularComponent Omega S.G Tred H,
     ∃B:RCN341.SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=by
   intro C
   by_cases hz:Transcendental Omega (coordinate Omega C.1 2)
   · exact ⟨⟨2,hz,(hZ C hz).1,(hZ C hz).2⟩,Or.inr rfl⟩
   · have hy:=(AAO phi S.F S.G Tred
       S.RR C).resolve_right hz
     have hsep:=AKM C.1 pchar S.G
       S.MW (EN Omega S.G Tred H C)
       S.y_dependent hGdegree hy (not_not.mp hz)
     exact ⟨⟨0,hy,hsep.1,hsep.2⟩,Or.inl rfl⟩
 let base:∀C:RCN264.RegularComponent Omega S.G Tred H,
     RCN341.SeparableLiteralCoordinate C.1:=fun C↦(choiceData C).choose
 have hbaseIndex:∀C:RCN264.RegularComponent Omega S.G Tred H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀C:RCN264.RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0∨
       KaehlerDifferential.D Omega (RCN002.CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=RCN037.base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 exact ⟨base,hactive,hZ,
   AFF base hactive
     (RCN315.EH S)⟩
end
end AGZ
namespace AGZ
open scoped Classical BigOperators
open _Q19
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN039 RCN040 RCN041 RCN265 RCN198
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K→+*Ω} {Γ:Finset K} {x:I→K}
 {p e w a b s:ℕ} [CharP Ω p] {flag:FlagDegree}
theorem AMV
   (S:FH φ Γ x p e flag w (support a b s))
   (x0 u0 u1:K)
   (hproper:¬S.G∣FK φ S.F w x0 u0 u1)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (RCN287.sharpResidualAgreementFlag (support a b s) w) unitZFlag<p):
   ∃base:∀C:RCN264.RegularComponent Ω S.G
       (FK φ S.F w x0 u0 u1) (CR φ S.F),
       RCN341.SeparableLiteralCoordinate C.1,
     Nonempty (YQ base flag
       (RCN287.sharpResidualAgreementFlag (support a b s) w)):=by
 classical
 let T:=FK φ S.F w x0 u0 u1
 let H:=CR φ S.F
 have hsy:s+2<b+s+3:=by omega
 have hTflag:RCN095.PolynomialInFlag (RCN287.sharpResidualAgreementFlag (support a b s) w) T:=
   ANZ hsy (phi:=φ)
     ⟨S.AFS,S.ACG,S.UT⟩
     w (fun j:ℕ=>(j.factorial:K)⁻¹) x0 u0 u1
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.WD S.flag_support
 have hGdegree:∀j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hR:=RCN315.EH S
 let hZ:∀C:RCN264.RegularComponent Ω S.G T H,RCN037.LiteralProjectionGate C 2:=by
   intro C htr
   exact BOC C.1 htr p S.G T
     S.MW (EN Ω S.G T H C)
     (GV Ω S.G T H C) hproper hR
     flag (RCN287.sharpResidualAgreementFlag (support a b s) w) S.flag_support hTflag hmixed
 let choiceData:∀C:RCN264.RegularComponent Ω S.G T H,
     ∃B:RCN341.SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=by
   intro C
   by_cases hz:Transcendental Ω (coordinate Ω C.1 2)
   · exact ⟨⟨2,hz,(hZ C hz).1,(hZ C hz).2⟩,Or.inr rfl⟩
   · have hy:=(AAO φ S.F S.G T
       S.RR C).resolve_right hz
     have hsep:=AKM C.1 p S.G
       S.MW (EN Ω S.G T H C)
       S.y_dependent hGdegree hy (not_not.mp hz)
     exact ⟨⟨0,hy,hsep.1,hsep.2⟩,Or.inl rfl⟩
 let base:∀C:RCN264.RegularComponent Ω S.G T H,
     RCN341.SeparableLiteralCoordinate C.1:=fun C=>(choiceData C).choose
 have hbaseIndex:∀C:RCN264.RegularComponent Ω S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀C:RCN264.RegularComponent Ω S.G T H,
     D Ω (RCN002.CoordinateField Ω C.1) (coordinate Ω C.1 0)≠0∨
       D Ω (RCN002.CoordinateField Ω C.1) (coordinate Ω C.1 2)≠0:=by
   intro C
   have hb:=RCN037.base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left;simpa only [hidx] using hb
   · right;simpa only [hidx] using hb
 obtain ⟨P⟩:=AEJ
   flag (RCN287.sharpResidualAgreementFlag (support a b s) w) base hactive hZ
   (RCN315.EH S)
   S.MW hproper
   ((RCN095.support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((RCN095.support_subset_flagSupport_iff
     (RCN287.sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end AGZ
end MergedPart4
section MergedPart7
namespace ABO
open RCN095 RCN198 RCN263 RCN287 RCN327 FA
open RCN095 renaming PolynomialInFlag → BI
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def Safe (r y:ℕ):Prop:=
  r*(LocatorHybridCells.cellFirstTail y y r).yz+y*(LocatorHybridCells.cellFirstTail y y r).all<2130706433∧
  r*(RCN287.sharpResidualAgreementFlag (LocatorHybridCells.cellSupport y y r) w).yz+
    y*(RCN287.sharpResidualAgreementFlag (LocatorHybridCells.cellSupport y y r) w).all<2130706433
instance (r y:ℕ):Decidable (Safe r y):=by unfold Safe;infer_instance
theorem DVW (f q:FlagDegree) (r y:ℕ)
    (hr:f.all≤r) (hy:f.yz+f.all≤y):
    flagMixed f q unitZFlag≤r*q.yz+y*q.all:=by
  have h1:=Nat.mul_le_mul_right q.yz hr
  have h2:=Nat.mul_le_mul_right q.all hy
  simp only [flagMixed,unitZFlag]
  nlinarith
theorem EJG (f:FlagDegree) (t y r:ℕ)
    (hsafe:Safe r y) (hfa:f.all≤r) (hfy:f.yz+f.all≤y):
    flagMixed f (RCN287.sharpResidualAgreementFlag (LocatorHybridCells.cellSupport t y r) w) unitZFlag<2130706433:=by
  have hy:(RCN287.sharpResidualAgreementFlag (LocatorHybridCells.cellSupport t y r) w).yz=
      (RCN287.sharpResidualAgreementFlag (LocatorHybridCells.cellSupport y y r) w).yz:=rfl
  have hr:(RCN287.sharpResidualAgreementFlag (LocatorHybridCells.cellSupport t y r) w).all=
      (RCN287.sharpResidualAgreementFlag (LocatorHybridCells.cellSupport y y r) w).all:=rfl
  exact (DVW f _ r y hfa hfy).trans_lt (by rw [hy,hr];exact hsafe.2)
end ABO
end MergedPart7
section MergedPart8
namespace BRK
open scoped Classical BigOperators
open RCN146
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
open RCN319 renaming specialization → BM
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Γ:Finset K} {x:I→K} {p e a b s:ℕ} [CharP (GenericField K) p]
 {flag:FlagDegree} {w:ℕ}
theorem AAB
   (S:FH (RCN135.polynomialEmbedding K) Γ x p e flag w (support a b s))
   (agreements:ℕ) (hnodes:S.nodes.card=agreements+e)
   (hagreement:∀γ∈Γ,agreements≤(S.AJW γ).card)
   (hwa:w<agreements)
   (hTail:S.G∣surfaceMap (RCN135.polynomialEmbedding K) (numerator K S.F (w+1)))
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈RCN174.globalCoefficientBox K bound w seedCap slopeCap)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (RCN287.sharpResidualAgreementFlag (support a b s) w) unitZFlag<p):
   AEO S (IY flag a b s w):=by
 classical
 unfold AEO
 intro i hi
 dsimp only
 intro hproper
 let T:=FK (RCN135.polynomialEmbedding K) S.F w
   (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
 obtain ⟨base,⟨U⟩⟩:=AGZ.AMV S
   (x i) (S.u0 i) (S.u1 i) hproper hflagChar hmixed
 let cost:RCN264.RegularComponent (GenericField K) S.G T (CR (RCN135.polynomialEmbedding K) S.F)→ℕ:=
   fun C=>U.family.toFE.zCost C+
     U.family.toFE.yzCost C
 refine ⟨cost,?_,?_⟩
 · intro C
   let Gc:=RCN264.componentSeeds (GenericField K) S.G T
     (CR (RCN135.polynomialEmbedding K) S.F) Gi
     (DK (RCN135.polynomialEmbedding K) S.selected) C
   have hGcGi:Gc⊆Gi:=RCN264.componentSeeds_subset (GenericField K) S.G T _ Gi _ C
   have hGiΓ:Gi⊆Γ:=Finset.filter_subset _ _
   have hGcΓ:Gc⊆Γ:=hGcGi.trans hGiΓ
   have hyzC:∀W:Finset (RCN346.Place_p19 (GenericField K)
       (RCN002.CoordinateField (GenericField K) C.1)),
       (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate (GenericField K) C.1)
         (flagSupport unitYZFlag))≤
         (U.family.toFE.yzCost C:ℤ):=by
     intro W
     change (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate (GenericField K) C.1)
       (flagSupport unitYZFlag))≤
       (RCN344.coordinateDegree (GenericField K) (RCN002.CoordinateField (GenericField K) C.1)
         (U.family.yzProjection C):ℤ)
     calc
       _=∑ v∈W,RCN346.poleOrder_p19 (GenericField K)
           (RCN002.CoordinateField (GenericField K) C.1) v
           (RCN344.coordinateValue (GenericField K) (RCN002.CoordinateField (GenericField K) C.1)
             (U.family.yzProjection C)):=by
         apply Finset.sum_congr rfl
         intro v _
         exact U.family.yzPole_eq C v
       _≤_:=PY (GenericField K)
         (RCN002.CoordinateField (GenericField K) C.1) (U.family.yzProjection C) W
   have hprofileYZ:=AIK
     S hTail (x i) (S.u0 i) (S.u1 i) hproper C
     bound seedCap slopeCap (U.family.toFE.yzCost C)
     hw hshort hchar hbox hyzC
   have hprofile:AHG (RCN135.polynomialEmbedding K) C.1 S.F
       (BJT S (x i) (S.u0 i) (S.u1 i) C)
       (AIC S (x i) (S.u0 i) (S.u1 i) C) w (cost C):=by
     intro W
     exact (hprofileYZ W).trans (by
       change (U.family.toFE.yzCost C:ℤ)≤
         ((U.family.toFE.zCost C+
           U.family.toFE.yzCost C:ℕ):ℤ)
       exact_mod_cast Nat.le_add_left _ _)
   have hcost:1≤cost C:=
     U.one_le_zCost_add_yzCost (RCN135.polynomialEmbedding K) S.F rfl S.RR C
   apply VP
     (RCN135.polynomialEmbedding K) C.1 S.F
     (BJT S (x i) (S.u0 i) (S.u1 i) C)
     (AIC S (x i) (S.u0 i) (S.u1 i) C)
     (base C) p w agreements e (cost C) S.WG hwa hcost hprofile
     S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
   · intro γ hγ
     exact S.degree_le γ (hGcΓ hγ)
   · intro γ hγ
     exact S.solution γ (hGcΓ hγ)
   · intro γ hγ
     exact S.regular γ (hGcΓ hγ)
   · intro γ hγ
     exact RCN264.componentSeeds_on_prime (GenericField K) S.G T
       (CR (RCN135.polynomialEmbedding K) S.F) Gi
       (DK (RCN135.polynomialEmbedding K) S.selected) C γ hγ
   · intro γ hγ
     have hΓ:=hGcΓ hγ
     exact hagreement γ hΓ
   · exact KX S.selected Γ Gc w e hGcΓ S.BNN
 · have hz:=U.family.ARJ
   have hyz:=U.family.ALE
   change (∑ C,U.family.toFE.zCost C)≤
     flagMixed flag (RCN287.sharpResidualAgreementFlag (support a b s) w) unitZFlag at hz
   change (∑ C,U.family.toFE.yzCost C)≤
     flagMixed flag (RCN287.sharpResidualAgreementFlag (support a b s) w) unitYZFlag at hyz
   have hz':=hz.trans (RCN203.mixed_sharp_le_padded a b s w flag unitZFlag)
   have hyz':=hyz.trans (RCN203.mixed_sharp_le_padded a b s w flag unitYZFlag)
   have hz'':=hz'.trans (BRQ flag a b s w unitZFlag)
   have hyz'':=hyz'.trans (BRQ flag a b s w unitYZFlag)
   change (∑ C,(U.family.toFE.zCost C+
     U.family.toFE.yzCost C))≤IY flag a b s w
   rw [Finset.sum_add_distrib]
   exact Nat.add_le_add hz'' hyz''
end
end BRK
end MergedPart8
section MergedPart9
namespace VN
open RCN095 RCN146
open RCN095 renaming PolynomialInFlag → BI
open Lower80788.FixedStage
open LocatorBatchPhase6800 (K)
open Lower80811.Counting (I)
open RCN223 (prime)
def newCost (f:FlagDegree) (a b s:ℕ):ℕ:=
  BoundaryTailIdentityArithmetic.newNormal f a b s+65539*flagMixed f (RCN206.fiberFlag a b s) (Lower80788.HybridIdentityC2.mcutABS a b s)
end VN
end MergedPart9
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart1
namespace AMT
open RCN095 RCN146 DY FV
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
open AAJ FA
open VN
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section
def high (r v z:ℕ):ℕ:=newCost ⟨z,v,r⟩ z (v-1) (r-2)
end
end AMT
end MergedPart1
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace Lower80811
namespace Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN313 RCN318 RCN319
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN318 renaming TightParameters → GH
open RCN319 renaming specialization → BM
open UA GB
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev P4:=MvPolynomial (Fin 4) K
end
end Counting
end Lower80811
end MergedPart0
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
namespace Lower80899
namespace PhaseRows
open RCN095 DY CS
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
open Lower80899.Oracle
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def BSY:ℕ→LocatorPhase6800Oracle.Potential
  | 0=>Lower80899.SourceSound.Phase00.potential
  | 1=>Lower80899.SourceSound.Phase01.potential
  | 2=>Lower80899.SourceSound.Phase02.potential
  | 3=>Lower80899.SourceSound.Phase03.potential
  | 4=>Lower80899.SourceSound.Phase04.potential
  | 5=>Lower80899.SourceSound.Phase05.potential
  | 6=>Lower80899.SourceSound.Phase06.potential
  | 7=>Lower80899.SourceSound.Phase03.potential
  | 8=>Lower80899.SourceSound.Phase04.potential
  | _=>Lower80899.SourceSound.PhaseFinal.potential
def thresholdAt (q:Array ℕ) (j:ℕ):ℕ:=(q[j]?).getD 11193
def FKT (q:Array ℕ) (j:ℕ):ℕ:=(q[j]?).getD 0
structure ABS where
  R:ℕ
  V:ℕ
  base:LocatorPhase6800Oracle.BaseRow
  threshold:Array ℕ
  here:Array ℕ
  parent:Array ℕ
def baseAt (c:ABS) (z:ℕ):ℕ:=c.base.evalAt z
def parentCharge (c:ABS) (phase z:ℕ):ℕ:=
  (BSY phase).eval (LocatorPhase6800Oracle.rawFlag c.R c.V z)+FKT c.parent phase
def hereCharge (c:ABS) (phase z:ℕ):ℕ:=
  (BSY phase).eval (LocatorPhase6800Oracle.rawFlag c.R c.V z)+FKT c.here phase
def sourceLine (c:ABS):ℕ→ℕ→ℕ
  | 0,z=>baseAt c z
  | j+1,z=>parentCharge c j z
def SourceActive (c:ABS):ℕ→ℕ→Prop
  | 0,_=>True
  | j+1,z=>thresholdAt c.threshold j≤z
instance (c:ABS) (w z:ℕ):Decidable (SourceActive c w z):=by
  cases w<;>simp only [SourceActive]<;>infer_instance
open DSM
def SourceCell (c:ABS):ℕ→ℕ→ℕ→Prop
  | 0,lo,hi=>BaseCell c.base lo hi
  | _+1,_,_=>True
instance (c:ABS) (w lo hi:ℕ):Decidable (SourceCell c w lo hi):=by
  cases w<;>simp only [SourceCell]<;>infer_instance
def RunValid (c:ABS) (phase start:ℕ) (run:PhaseRun):Prop:=
  let hi:=run.stop-1
  start<run.stop∧run.witness≤phase∧
    SourceActive c run.witness start∧
    SourceCell c run.witness start hi∧
    sourceLine c run.witness start≤hereCharge c phase start∧
    sourceLine c run.witness hi≤hereCharge c phase hi
instance (c:ABS) (phase start:ℕ) (run:PhaseRun):
    Decidable (RunValid c phase start run):=by
  unfold RunValid
  infer_instance
def RunsValid (c:ABS) (phase finish:ℕ):
    ℕ→List PhaseRun→Prop
  | start,[]=>start=finish
  | start,run::runs=>
      run.stop≤finish∧RunValid c phase start run∧
        RunsValid c phase finish run.stop runs
instance (c:ABS) (phase finish start:ℕ)
    (runs:List PhaseRun):Decidable (RunsValid c phase finish start runs):=by
  induction runs generalizing start with
  | nil=>simp only [RunsValid];infer_instance
  | cons run runs ih=>simp only [RunsValid];infer_instance
def phaseFinish (c:ABS) (phase:ℕ):ℕ:=
  min (thresholdAt c.threshold phase) (11193-(c.R+c.V))
def RowRunsValid (c:ABS) (runs:Array (List PhaseRun)):Prop:=
  ∀j ∈ List.range 10,RunsValid c j (phaseFinish c j) 0 ((runs[j]?).getD [])
instance (c:ABS) (runs:Array (List PhaseRun)):
    Decidable (RowRunsValid c runs):=by
  unfold RowRunsValid
  infer_instance
end PhaseRows
end Lower80899
namespace Lower80899
namespace AMY
open scoped BigOperators
open IL
set_option autoImplicit false
set_option maxRecDepth 100000
open CS Lower80899.Oracle
open RCN095 DY
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
def evalBand (s:EA) (p:FlagDegree):ℕ:=
  Lower80899.ThresholdFast.evalPowerBandBudget 49989 (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all
    (s.totalCap-LocatorFactorAggregate.total p) (s.middleCap-LocatorFactorAggregate.middle p)
    (s.slopeCap-p.all) (s.fuel p)
def ABC
    (w Dh delta dc dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | fuel+1=>
      delta*Lower80899.ThresholdFast.evalChannelCount T (min YS (thinTop w Dh S)) S+
        ABC w (Dh-delta-dc) delta dc dT dY dS
          (T-dT) (YS-dY) (S-dS) fuel
def evalBandThin (s:EA) (p:FlagDegree):ℕ:=
  ABC 131071 (s.contactCap p) 49989 (contactDec p)
    (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all
    (s.totalCap-LocatorFactorAggregate.total p) (s.middleCap-LocatorFactorAggregate.middle p)
    (s.slopeCap-p.all) (s.fuel p)
def DDX (s:EA) (p:FlagDegree):Prop:=
  1≤p.all∧LocatorFactorAggregate.total p≤s.totalCap∧LocatorFactorAggregate.middle p≤s.middleCap∧
    p.all≤s.slopeCap∧(evalBandThin s p<s.gap∨evalBand s p<s.gap)
instance (s:EA) (p:FlagDegree):
    Decidable (DDX s p):=by
  unfold DDX
  infer_instance
def QM
    (s:EA) (r v threshold:ℕ):Prop:=
  11192-(r+v)<threshold∨DDX s (LocatorPhase6800Oracle.rawFlag r v threshold)
instance (s:EA) (r v threshold:ℕ):
    Decidable (QM s r v threshold):=by
  unfold QM
  infer_instance
end AMY
end Lower80899
end MergedPart0
section MergedPart1
set_option Elab.async false
namespace Lower80899
namespace EZE
open RCN095 DY CS
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
open Lower80899.Oracle Lower80899.AMY
open Lower80899.PhaseRows
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def indexedThin (w Dh delta dc dT dY dS T YS S:ℕ):ℕ→ℕ
  | 0=>0
  | n+1=>indexedThin w Dh delta dc dT dY dS T YS S n+
      delta*Lower80899.ThresholdFast.evalChannelCount (T-n*dT)
        (min (YS-n*dY) (thinTop w (Dh-n*(delta+dc)) (S-n*dS))) (S-n*dS)
def indexedBand (s:EA) (p:FlagDegree):ℕ:=
  indexedThin 131071 (s.contactCap p) 49989 (contactDec p)
    (LocatorFactorAggregate.total p) (LocatorFactorAggregate.middle p) p.all (s.totalCap-LocatorFactorAggregate.total p)
    (s.middleCap-LocatorFactorAggregate.middle p) (s.slopeCap-p.all) (s.fuel p)
def DVX (s:EA) (r v threshold:ℕ):Prop:=
  11192-(r+v)<threshold∨
    let p:=LocatorPhase6800Oracle.rawFlag r v threshold
    1≤p.all∧LocatorFactorAggregate.total p≤s.totalCap∧LocatorFactorAggregate.middle p≤s.middleCap∧
      p.all≤s.slopeCap∧indexedBand s p<s.gap
instance (s:EA) (r v threshold:ℕ):
    Decidable (DVX s r v threshold):=by
  unfold DVX;infer_instance
end EZE
end Lower80899
namespace Lower80899
namespace EUA
open scoped BigOperators
open IL Lower80899.AMY
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
structure Affine where
  constant:ℤ
  slope:ℤ
  deriving DecidableEq,Repr
def Affine.eval (a:Affine) (i:ℕ):ℤ:=a.constant+a.slope*i
def Affine.add (a b:Affine):Affine:=⟨a.constant+b.constant,a.slope+b.slope⟩
def Affine.sub (a b:Affine):Affine:=⟨a.constant-b.constant,a.slope-b.slope⟩
def Affine.scale (a:Affine) (k:ℤ):Affine:=⟨k*a.constant,k*a.slope⟩
def Affine.plus (a:Affine) (k:ℤ):Affine:=⟨a.constant+k,a.slope⟩
@[simp] theorem Affine.eval_add (a b:Affine) (i:ℕ):
    (a.add b).eval i=a.eval i+b.eval i:=by simp [Affine.add,Affine.eval];ring
@[simp] theorem Affine.eval_sub (a b:Affine) (i:ℕ):
    (a.sub b).eval i=a.eval i-b.eval i:=by simp [Affine.sub,Affine.eval];ring
@[simp] theorem Affine.eval_scale (a:Affine) (k:ℤ) (i:ℕ):
    (a.scale k).eval i=k*a.eval i:=by simp [Affine.scale,Affine.eval];ring
@[simp] theorem Affine.eval_plus (a:Affine) (k:ℤ) (i:ℕ):
    (a.plus k).eval i=a.eval i+k:=by simp [Affine.plus,Affine.eval];ring
def BID (a b c:Affine) (n:ℕ):ℤ:=
  if n=0 then 0 else
  let x:ℤ:=n
  let w:ℤ:=131071
  let A:=a.constant
  let B:=b.constant
  let C:=c.constant
  let α:=a.slope
  let β:=b.slope
  let γ:=c.slope
  let q0:=3*(A+w)*(C+2*w)+C*(C+2*w)+6*A*B+9*w*B+3*B*C+3*B*B
  let q1:=3*((A+w)*γ+α*(C+2*w))+γ*(2*C+2*w)+
    6*(A*β+α*B)+9*w*β+3*(B*γ+β*C)+6*B*β
  let q2:=3*α*γ+γ*γ+6*α*β+3*β*γ+3*β*β
  let s0:=12*x
  let s1:=6*x*(x-1)
  let s2:=2*x*(x-1)*(2*x-1)
  let s3:=3*x*x*(x-1)*(x-1)
  q0*(s0*(C+w)+s1*γ)+q1*(s1*(C+w)+s2*γ)+q2*(s2*(C+w)+s3*γ)
end EUA
end Lower80899
namespace Lower80899
namespace BLW
open scoped BigOperators
open Lower80899.EUA Lower80899.EZE
open Lower80899.AMY IL
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
structure Input where
  T:ℕ
  YS:ℕ
  S:ℕ
  Dh:ℕ
  dT:ℕ
  dY:ℕ
  dS:ℕ
  dDh:ℕ
  fuel:ℕ
  deriving DecidableEq,Repr
def Input.atT (p:Input):Affine:=⟨p.T,-(p.dT:ℤ)⟩
def Input.atY (p:Input):Affine:=⟨p.YS,-(p.dY:ℤ)⟩
def Input.atS (p:Input):Affine:=⟨p.S,-(p.dS:ℤ)⟩
def Input.atDh (p:Input):Affine:=⟨p.Dh,-(p.dDh:ℤ)⟩
def Input.count (p:Input) (i:ℕ):ℕ:=
  channelCount (p.T-i*p.dT)
    (min (p.YS-i*p.dY) ((p.Dh-i*p.dDh+(p.S-i*p.dS)-1)/131071)) (p.S-i*p.dS)
def Input.dh (p:Input) (code:ℕ):Affine:=if 6≤code then p.atDh else ⟨0,0⟩
def Input.u (p:Input) (code:ℕ):Affine:=
  if code/2%3=0 then p.atT.scale 131071
  else if code/2%3=1 then p.atY.scale 131071
  else (p.dh code).add p.atS
def Input.c (p:Input) (code:ℕ):Affine:=
  if code%2=0 then p.atS.scale 131071 else p.u code
def Input.a (p:Input) (code:ℕ):Affine:=((p.atT.scale 131071).sub (p.u code)).plus 131071
def Input.b (p:Input) (code:ℕ):Affine:=(p.u code).sub (p.c code)
def conditions (p:Input) (code:ℕ):List Affine:=
  [p.atT,p.atY,p.atS,if 6≤code then p.atDh else p.atDh.scale (-1),
    (p.atT.scale 131071).sub (p.u code),
    (p.atY.scale 131071).sub (p.u code),
    ((p.dh code).add p.atS).sub (p.u code),
    (p.atS.scale 131071).sub (p.c code),
    (p.u code).sub (p.c code)]
def ValidAt (p:Input) (code i:ℕ):Prop:=
  ∀a ∈ conditions p code,0≤a.eval i
def FastValidAt (p:Input) (code i:ℕ):Prop:=
  let t:=p.atT.eval i
  let y:=p.atY.eval i
  let s:=p.atS.eval i
  let u:=(p.u code).eval i
  let c:=(p.c code).eval i
  0≤t∧0≤y∧0≤s∧
    0≤(if 6≤code then p.atDh else p.atDh.scale (-1)).eval i∧
    u≤131071*t∧u≤131071*y∧u≤(p.dh code).eval i+s∧
    c≤131071*s∧c≤u
instance (p:Input) (code i:ℕ):Decidable (FastValidAt p code i):=by
  unfold FastValidAt
  infer_instance
theorem EZH (p:Input) (code i:ℕ):
    ValidAt p code i ↔ FastValidAt p code i:=by
  simp only [ValidAt,FastValidAt,conditions,List.mem_cons,
    List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Affine.eval_sub,Affine.eval_scale,Affine.eval_add,sub_nonneg]
instance (p:Input) (code i:ℕ):Decidable (ValidAt p code i):=
  decidable_of_iff (FastValidAt p code i) (EZH p code i).symm
def RunValid (p:Input) (start:ℕ) (run:Run):Prop:=
  start<run.stop∧run.stop≤p.fuel∧
    ValidAt p run.code start∧ValidAt p run.code (run.stop-1)
instance (p:Input) (start:ℕ) (run:Run):Decidable (RunValid p start run):=by
  unfold RunValid;infer_instance
def runUpper (p:Input) (start:ℕ) (run:Run):ℤ:=
  BID (p.a run.code) (p.b run.code) (p.c run.code) run.stop-
  BID (p.a run.code) (p.b run.code) (p.c run.code) start
def RunsValid (p:Input):ℕ→List Run→Prop
  | start,[]=>start=p.fuel
  | start,run::runs=>RunValid p start run∧RunsValid p run.stop runs
instance (p:Input) (start:ℕ) (runs:List Run):Decidable (RunsValid p start runs):=by
  induction runs generalizing start with
  | nil=>unfold RunsValid;infer_instance
  | cons run runs ih=>unfold RunsValid;infer_instance
def runsUpper (p:Input):ℕ→List Run→ℤ
  | _,[]=>0
  | start,run::runs=>runUpper p start run+runsUpper p run.stop runs
open Lower80899.Oracle CS
open RCN095 DY
open RCN095 renaming PolynomialInFlag → BI
open LocatorFactorAggregate (middle total)
def ofSource (s:EA) (p:FlagDegree):Input:=
  ⟨s.totalCap-LocatorFactorAggregate.total p,s.middleCap-LocatorFactorAggregate.middle p,s.slopeCap-p.all,s.contactCap p,
    LocatorFactorAggregate.total p,LocatorFactorAggregate.middle p,p.all,49989+contactDec p,s.fuel p⟩
def Sufficient (s:EA) (r v threshold:ℕ) (runs:List Run):Prop:=
  11192-(r+v)<threshold∨
    let p:=LocatorPhase6800Oracle.rawFlag r v threshold
    1≤p.all∧LocatorFactorAggregate.total p≤s.totalCap∧LocatorFactorAggregate.middle p≤s.middleCap∧p.all≤s.slopeCap∧
      RunsValid (ofSource s p) 0 runs∧
      49989*runsUpper (ofSource s p) 0 runs<(s.gap:ℤ)*(72*131071^3)
instance (s:EA) (r v threshold:ℕ) (runs:List Run):
    Decidable (Sufficient s r v threshold runs):=by
  unfold Sufficient;infer_instance
end BLW
end Lower80899
end MergedPart1
section MergedPart10
namespace ADZ
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 GB
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def stage (y z d j:ℕ):DG:=
  ⟨262144,131071,181059,y,d-j,z,y,d,z⟩
end ADZ
end MergedPart10
end SubmissionLower
end ProximityPrize
end
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart0
section InitialGeometry
namespace Lower80899
namespace FCR
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN243 RCN259 RCN260 RCN266 RCN275 RCN319
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN095 renaming PolynomialInFlag → BI
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN319 renaming specialization → BM
open DY KZ
open LocatorBatchPhase6800 (K P4)
open Lower80811.Counting (I)
open LocatorFactorAggregate (middle total)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance:DecidableEq LocatorBatchPhase6800.K:=Classical.decEq _
local instance:DecidableEq Lower80811.Counting.I:=Classical.decEq _
local instance:GCDMonoid LocatorBatchPhase6800.P4:=UniqueFactorizationMonoid.toGCDMonoid LocatorBatchPhase6800.P4
def initialAMap (u0 u1:Lower80811.Counting.I→LocatorBatchPhase6800.K):Caps.AKernel u0 u1→ₗ[LocatorBatchPhase6800.K] LocatorBatchPhase6800.P4:=
  LZ (K:=LocatorBatchPhase6800.K) 24285490 131071 104142 40 134
    IRSProfile.domain u0 u1
def ADN (u0 u1:Lower80811.Counting.I→LocatorBatchPhase6800.K) (H:LocatorBatchPhase6800.P4):
    Finset (RegularIndex H):=
  AKV H (Finset.univ:Finset (RegularIndex H))
    (initialAMap u0 u1)
@[simp] theorem DXO
    (u0 u1:Lower80811.Counting.I→LocatorBatchPhase6800.K) (H:LocatorBatchPhase6800.P4) (F:RegularIndex H):
    F ∈ ADN u0 u1 H ↔
      ∀v:Caps.AKernel u0 u1,
        F.1 ∣ reconstruct LocatorBatchPhase6800.K 24285490 131071 104142 40 v.1:=by
  simp only [ADN,ASD,Finset.mem_univ,
    true_and,initialAMap,SE]
end
end FCR
end Lower80899
end InitialGeometry
end MergedPart0
section MergedPart1
namespace Lower80899
namespace Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN313 RCN318 RCN319
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN318 renaming TightParameters → GH
open RCN319 renaming specialization → BM
open UA ADZ GB
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq LocatorBatchPhase6800.K:=Classical.decEq _
local instance:DecidableEq Lower80811.Counting.I:=Classical.decEq _
local instance:CharP LocatorBatchPhase6800.K 2130706433:=by
  simpa [RCN223.prime] using RCN128.FJ
local instance:StrongNormalizationMonoid LocatorBatchPhase6800.P4:=UniqueFactorizationMonoid.strongNormalizationMonoid
structure Input (u0 u1:Lower80811.Counting.I→LocatorBatchPhase6800.K) (selected:LocatorBatchPhase6800.K→Polynomial LocatorBatchPhase6800.K) (Gamma:Finset LocatorBatchPhase6800.K):Prop where
  degree: ∀gamma ∈ Gamma,(selected gamma).natDegree≤131071
  agreement: ∀gamma ∈ Gamma,181059≤((Finset.univ:Finset Lower80811.Counting.I).filter (fun i=>
    (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card
  noPencil:BL selected Gamma 131071 81085
variable {u0 u1:Lower80811.Counting.I→LocatorBatchPhase6800.K} {selected:LocatorBatchPhase6800.K→Polynomial LocatorBatchPhase6800.K} {Gamma:Finset LocatorBatchPhase6800.K}
theorem Input.restrict (inp:Input u0 u1 selected Gamma) (Delta:Finset LocatorBatchPhase6800.K) (h:Delta ⊆ Gamma):
    Input u0 u1 selected Delta:=
  ⟨fun g hg=>inp.degree g (h hg),fun g hg=>inp.agreement g (h hg),
    KX selected Gamma Delta 131071 81085 h inp.noPencil⟩
end
end Counting
end Lower80899
end MergedPart1
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart6
namespace LD
set_option autoImplicit false
set_option maxHeartbeats 600000
def ceilBlend (T0 T1 L0 L1 T:ℕ):ℕ:=
  ((T1-T)*L0+(T-T0)*L1+(T1-T0)-1)/(T1-T0)
end LD
end MergedPart6
section MergedPart8
namespace LD
open RCN100
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
set_option autoImplicit false
set_option maxHeartbeats 700000
def oneSlope (q r w s:ℕ):ℕ:=
  (r+q)*(LocatorFastKernelArithmetic.smallChoose (q+2) 2-LocatorFastKernelArithmetic.smallChoose (q+1-s) 2)+
    (w-2)*(LocatorFastKernelArithmetic.smallChoose (q+2) 3-LocatorFastKernelArithmetic.smallChoose (q+1-s) 3)
def oneIntercept (q r w s:ℕ):ℤ:=
  (LocatorFastKernelArithmetic.oneResidueCoefficientCount q r w q s:ℤ)-(oneSlope q r w s:ℤ)*q
def ECJ (q r w s:ℕ):ℕ:=
  if r+s≤w then oneSlope q r w s else
    oneSlope q r w (w-r-1)+oneSlope (q+1-(w-r)) 0 w (s-(w-r))
def CSW (q r w s:ℕ):ℤ:=
  if r+s≤w then oneIntercept q r w s else
    oneIntercept q r w (w-r-1)+oneIntercept (q+1-(w-r)) 0 w (s-(w-r))-
      (oneSlope (q+1-(w-r)) 0 w (s-(w-r)):ℤ)*(w-r)
end LD
end MergedPart8
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
section MergedPart1
namespace DR
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
structure Point where
  s:ℕ
  b:ℕ
  u:ℕ
  t:ℕ
  deriving DecidableEq
structure Box where
  slo:ℕ
  shi:ℕ
  blo:ℕ
  bhi:ℕ
  ulo:ℕ
  uhi:ℕ
  tlo:ℕ
  thi:ℕ
  deriving DecidableEq
def Contains (a:Box) (p:Point):Prop:=
  a.slo≤p.s∧p.s≤a.shi∧a.blo≤p.b∧p.b≤a.bhi∧
  a.ulo≤p.u∧p.u≤a.uhi∧a.tlo≤p.t∧p.t≤a.thi
def Empty (a:Box):Prop:=a.shi<a.slo∨a.bhi<a.blo∨a.uhi<a.ulo∨a.thi<a.tlo
instance (a:Box):Decidable (Empty a):=by unfold Empty;infer_instance
def lower (a:Box) (axis:Fin 4) (v:ℕ):Box:=
  match axis.val with
  | 0=>{a with shi:=v}
  | 1=>{a with bhi:=v}
  | 2=>{a with uhi:=v}
  | _=>{a with thi:=v}
def upper (a:Box) (axis:Fin 4) (v:ℕ):Box:=
  match axis.val with
  | 0=>{a with slo:=v+1}
  | 1=>{a with blo:=v+1}
  | 2=>{a with ulo:=v+1}
  | _=>{a with tlo:=v+1}
theorem EQB (a:Box) (p:Point) (axis:Fin 4) (v:ℕ) (hp:Contains a p):
    Contains (lower a axis v) p∨Contains (upper a axis v) p:=by
  fin_cases axis<;>simp [lower,upper,Contains] at* <;>omega
end DR
end MergedPart1
section MergedPart2
namespace BAL
set_option autoImplicit false
set_option maxHeartbeats 1200000
def Chord (lo hi:ℕ) (f:ℕ→ℕ):Prop:=
  ∀x,lo≤x→x≤hi→(hi-lo)*f x≤(hi-x)*f lo+(x-lo)*f hi
theorem add {lo hi:ℕ} {f g:ℕ→ℕ} (hf:Chord lo hi f) (hg:Chord lo hi g):
    Chord lo hi (fun x=>f x+g x):=by
  intro x hl hh
  have h:=Nat.add_le_add (hf x hl hh) (hg x hl hh)
  simpa only [Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
theorem mul_left {lo hi:ℕ} {f:ℕ→ℕ} (hf:Chord lo hi f) (c:ℕ):
    Chord lo hi (fun x=>c*f x):=by
  intro x hl hh
  have h:=Nat.mul_le_mul_left c (hf x hl hh)
  simpa only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
end BAL
end MergedPart2
section MergedPart3
namespace TP
set_option autoImplicit false
set_option maxHeartbeats 1800000
def left (cc cs clo charge slope x z:ℕ):=cc+cs*(x-clo)+charge+slope*(z-x)
def right (pc ps plo z:ℕ):=pc+ps*(z-plo)
def EndAt (cc cs clo chi charge slope pc ps plo z:ℕ):Prop:=
  left cc cs clo charge slope clo z≤right pc ps plo z∧
  left cc cs clo charge slope (min chi z) z≤right pc ps plo z
instance (cc cs clo chi charge slope pc ps plo z:ℕ):
    Decidable (EndAt cc cs clo chi charge slope pc ps plo z):=by unfold EndAt;infer_instance
end TP
end MergedPart3
section MergedPart4
namespace DZ
set_option autoImplicit false
set_option maxHeartbeats 1300000
structure Piece where
  stop:ℕ
  base:ℕ
  slope:ℕ
  deriving DecidableEq
def value (p:Piece) (start z:ℕ):=p.base+p.slope*(z-start)
def evalFrom:ℕ→List Piece→ℕ→ℕ
  | _,[],_=>0
  | start,p::ps,z=>if z<p.stop then value p start z else evalFrom p.stop ps z
def eval (ps:List Piece) (z:ℕ):=evalFrom 0 ps z
end DZ
end MergedPart4
end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize
namespace SubmissionLower
namespace Codec0
open DZ
set_option autoImplicit false
set_option maxRecDepth 100000
def s0:ℕ:=0x3a352944000015d3ef79800003a35294400009184e72a00001d1a94a200000bd937adbe8c01d1a94a200012309ce54000005e99d54584c8c273950000000bd33aa8b0a48c27395000048c2739500000002f3b37eb6448c273950000000000000000
def s1:ℕ:=0x5bf9973aba50b08acfc7dec1c9faff6023414bec3399178e55e5e9b43bbf2ae644c565d79d76b66806ed86bfe93bb579e300bd47558b1893ad40605977415d3ef7980000e8d4a51000028b792a74b409384f720839b801490954808200f51e0201a1
def s2:ℕ:=0x5dc09a06bb51adf74b87dd17568725062e42e5829960245171f6810400023123a7e7dd30a070403a30008433d00dbd6e3b1989d5a6cc541178090600128774d1aba26f8398f4b69c31e1c7efee04bc90e32eb9da62306ee157b3124a36aba931a3c3
def s3:ℕ:=0x27d6832c551a0eb5b16156db057c02db00074bc0335ab77c32f30b39d1a4112abb14a14bec930bf724a7e831d019e0003e5c89986ebaf491314dc1bf4408736c4af35c842718da838b91e660bab38e52d88cb03dd03caf396d7a06ca4c2ef15366b0
def s4:ℕ:=0x52b588bfb523987297546e665678a5126e5e2629d80cd80c720de372ee2c51046cf5a7e8348139883593bc26501400003658889212b89dac90c936dc2cd5cc63d1adc92ae5d1fb76f8555418c1fb5efa9a8c47c5a5d4b171b14ddcd8523e6e7f572b
def s5:ℕ:=0x1e0538cfd8ef0efe5bdb0272876ed2317d7663ae28b639e451d4081b1da970e932f372261c73754a4f155a39b41b9ead0d1cadbcb52b708e24afbaddc507122e36ffd5e3835ef70f8931bb763e8a8280d93077aa87c94fc62b1ad7b2212011580032
def s6:ℕ:=0x217eddb87bf610be75c209dc083a3e19827ae41d1ce08ecee20a3dc7c6b46902a82a4000fc814bc141c3e0401de44974611fc11229f6538fbd03e6848d87cb47c2fb21c3df1a14fd0181ee51d7558050f4c95f6f15d87a3832a570523ca0663b4dde
def s7:ℕ:=0x2515067ecb15928152f84e78c92d913890b7e48f3de456b72246caf3c97729210ad4548e4c8f7b5f1a817247ad711123e6238c7032e0b411a1e035458008d03075231d045ef0bb65f3c22aacb2086f4915454873ad1c885351b205d6441b2364c08e
def s8:ℕ:=0x552d8ccdb6b5940e3da59af209e058fbc821e4ea44c8777be26e64c930b2b1362450656b789ae13c1baae24cea07d2ac42264b3536f5ce931749ac53f809879df28664a4bc033234a1625b01ddae07212cc4e52513849612823521b24a965e73e7eb
def s9:ℕ:=0x30d3a306c1ef14282c59f9d5493ab2541dd1a48a1e4274c412405e0b1421e91db8d6b6a7d08d0b24b4b30844ff63522ecb2269301bf0b68df185dd20fe46f24f544a744329a83b40fed18f080ab75248c2b95d80efac38a01dc0005cb09522436fd1
def s10:ℕ:=0x231d439a03d41141b62e9957087a654818620436e32ac475421727a564aea9093c6c8cb0387ef3e671ade23164f9aab1a017bdd6b4c6c605f80326000a804a3533440089e39042d641b4da680b3b22aa6873f5fd86352c01eda2bdfe91e4f0235c71
def s11:ℕ:=0x29fa09dc61a714e47b239eae4a6b1209aa00052404943a8552915ded32800143163af8951c853ef78e4188416bcd4d7e781ce8659501bc8e155daa983cc5c9206e5be5c13d00a8000265a459473b93fa76241455970cc0b58b4bf1325816d7eafc3a
def s12:ℕ:=0x2373f643d4ef117a3c5347cf88ae37b1efe4a31c1764fe87856788e2ab6c5aa534599dad153f8a1186ce625eeb2dfa37992e70e7bf39c116d88df0aca08b3c5400de30456c26a946f292b1854f68e771556cfc9a64f0a9f036ed4ae454c49d1d3677
def s13:ℕ:=0x2b94a06d96b615666a43db1b0a814228756d8527a7977ea6c287570d614b614309867dc2d09e8ca97f147a4e36d7607f7b26e523efd1e313302a1a15308989c75ff7a9e4b4a79702a092569170feb6c1275129dffd4090bc36ffa92e47988938e03e
def s14:ℕ:=0x100d1b458abd87c60d3c4535c3b4464fa27d21b2a2e6f12570cda15fd88b4a8b0c2e8d9c2d3dc60aaac9429b02ff0762374b917c5cafe6a4d0bc9ad758d04a5ada2a56a7dfacfc350033cd1645aa6a89d52b069d2a7cbfc1fdebeb045a487072af6c
def s15:ℕ:=0x1cbaff949ade8e3f17dfc95b47194be2e4a5e376c5ccf243d1b602de891ff8d9496c248e746908b046452233da56fb220b19242a3a90918c5894bb481e46018a18e3f6a2dd04d191e4715ca24b58e6c88d08ef4c5dec452475322e1a21cc395f168d
def s16:ℕ:=0x205135ef94ff900c9ad04a7947f60d512536e3f886a19295f1edd339994298f6c99c44a0947ae8cdb650923cd465ab27a91da1319293608ece18cb49b6c75bdc6287dd83ab6466b249d1d3dc4814a058e921fb21de587440c27a4be639a0bc81c64f
def s17:ℕ:=0x23413abd96d991991d64cb8048bbfe364222a4522735d2d092278397a96659114f9308aa788850e3ca5926439270ad2bd921bc9a25020910b1f5f49109c8554de9e56ee424efe3aff21211e3743958a907cc1507656483d8dc6e564a413bcae25db0
def s18:ℕ:=0x2ee94df49e5e972f2697cf134b5012d6275be5844930339712b0447aa9c0194f322e9cda549e0233184caa4d6181b0655525e0f4ea522a9288947e38d5491f01723bc064882ba1d225523d23bb1974091e69ddacba6c8ed7fd43ef1846e322416155
def s19:ℕ:=0x36515a1ea3149b182d085193cd59161f2897e6a2ab02f449735125839a2709a052b22d0c24cfd1598a86e667b2ac21430532d6548ba102994eaa04d05ccc6e14ad2812e6323bb1d7db0316152029ff0984d286ecfca4c0953fee7c9e5ef89e0d3dbb
def s20:ℕ:=0x3c396394a6969e1331c7d3534ef198d0e9aea7682c4754c713acc6158a5cb9d60b096d2d4ceaa185b2980e740ac0674adf398a5f95a54c9cb92f90d2784e32578b2929a70d8bb7d492b38185ceaa4159bc6ae12d1eecdd396f9e8f7a6d7cb5674675
def s21:ℕ:=0x40a16ac9a95da01f354fd4cb500d1a8d2a4de8062d4ad52b93f296862a8709f903464546fcfbd5a13ea24e7db4cffb50b93eac675ea7d59f013378d4144f6e599229f2a7b62cbf74f073d8065c6a7819e72328d53b8cf279901e9a3a78fac8834e03
def s22:ℕ:=0x450971feac24a26b38b1d5d5512d9c7eeb1ca8884e1b3579143e5706babb7a1cc381255ddd0e45be5eacde85d0dd4555db42c86e0caa63a154b7325577509e9b936ac128432da615495418e6c6baa12a0b6b62ed512d0571b1daa9368174d56b5239
def s23:ℕ:=0x2d305410242016400b80001807bc0eb0065c02100120000601000088000200679d23358dc02200140000c9020ef015d2f47997680ae12a37b3aa3d6bf51bc9d6a6b7828dc8e97559e3465d7479ad49a2ea39e95694d1671cc42b28e8a42e4e55901
def s24:ℕ:=0xa1cd6203d6884c0083c4347c256013e0004c10bb9bbb027307711a580f7583ac73432795c1952d8d805e40aada7e0766b04f508c0fca1024d843581cc0123c20c40da808ad7cd222bd03bb06c302d401db836b017680bb4158008f405ce0aaa047c
def s25:ℕ:=0xbcfcdc79f5d05de0a1343fec2ed84a2b6c52174fcaeadd9a0ba4b56c604405cd0c488c71c2dbb2d9a5ad416c32cab0e9c0b5005fc00150594f843d88ec2c824c5bdba4163bacada42f0b1d13298799857abb459fc302b587dde61a0153c249f0e8d
def s26:ℕ:=0xc5b6ad4e979862c8a9844314315b8a057fe218a82013cc520c50a9012876861902c87270430a4e96317f2183ef4a21ed60c165acb5fb005feb7c89e1882ff43e7bbd1c17eb336f71610be82041ede485efce89036d82f7a0254e19017a4915e7b07
def s27:ℕ:=0xcf78a9f88b7867b5cb3a138433949bad94a219b593f138860cd855149a8f866c2926167a83360582a22d6197df5297f4d0cadf896eead0655479e0e95c327a190ba1c419347e6b7d240c929d05a67c063db316a0d84318987fad80818c2ea3a8a27
def s28:ℕ:=0xda85ad24a9c86c7e47f8e70035edf6b64a101af3a156af9a0d780718001706b3f5ec0a27c35725239cf041aaa7ea8974b0d541ed3f37206a2789c6292c34af907dd16c1a53d739f0f20d23708a9987068a820d36dc8343b7cffb5201a15151b3aca
def s29:ℕ:=0xe2d4519fbb2870f4607a0834382a378f301a1c0cf87891350dff70bb9c5006fc0bea44b5c37d99c901eb81bdca63347440deab0c4c37686f257fbe3ab8378dd8e126501bc1ada1751b0dcd73af4aa186e573ee65524370eeb4313f21b5a72059714
def s30:ℕ:=0xe9472e84e1a07445e1923c403a11b58feba61d06c7934c390e77a804fad187383043fd55039b5d6c5ca761cd29393d3970e651913015987286f4068120393b487369641c8d911543a10e4102bc365b07190c20c4c8438ba37988ae61c5b30e4d41a
def s31:ℕ:=0xf0756d7afe887807e78290043bf52b5eaf001de0753c43890eede39c0c408774adaaa412c3b67a5a3bed41dadaa49ab460eccf5d2402707600eb2fc8003aeda29393d81d70bace32680eb22f61acc887588c8dc4f1c3abf8b25e7a21d559cb30fa5
def s32:ℕ:=0xf72ff8ad0eb07b93eb7175a83d9402d414461eb99791b6450f58e8e849f387a8b7766c18c3d0c896f216c1e75ff0460cc0f397241502f079b8cd4aeef43cdc428f3a7a1e630d48bc270f3137acd118079134ca29cc83c6f4e1973921e2c33571445
def s33:ℕ:=0xfe4dbfe53bf87f161367050c3f83539f7dc21fa0109800320fcde750778207e3ccae296d83f0d4bb855ac1f8681c924720fbc03f10ef407d9638e53af43eca3240a11c1f60c080b2300faeeada724107c5a4f2dcda43e29476ea4c01f146a4eb9ab
def s34:ℕ:=0x1040ee38c00a081f2b762f4bc40d06e0a2b662067c2e6feed102c1bf7fe8e08148dc1456844099b7fbb72a202e3eee1bd71016706db57a0809d363802f840433bf87862201e79e787021004b532770087fb8ba0289503fd711de00481fe0300234dc
def s35:ℕ:=0x10994f149975084aa53f71580424cc00735342103d6a7b91b107bec43f4cd083dd88939cf841ecbd34bf2a20f112c85e721070cf145d8b88345c88731044173039761dc20b475ca19c61058ac4526a9082a199b3aa7c413e54e170dc2084045d0f3b
def s36:ℕ:=0x10ee15d92fa68871b89ceae7c438334425f1221c0e1e2d40b10dbd782a303086a8cc14e7d043313661905a218bb100e24010ba611cf796885a9b2b6b52c42d1daf6a2d6215038b9164710a570d355bd085204e35f80c428e4feb34fe2139f764af1d
def s37:ℕ:=0x114ac2c82235889b459d16ea844d963ddf19a2261e82ce02e112de8f6bbea0894c66894be044994276baf6223d8b5d59d91117e207e20c888b9187eb8c8445c0e8028a6220c8d328a4e11004ae49613887e611533ac043ed3943798021de4a797bf1
def s38:ℕ:=0x119b161de0e588cc0d45020dc464577956a0e23116a80e2481184e4b6b88888c207ca3787445fdab321b5622fc267b1b0e11703c9f4a8588b71b17427b445b59baae8e422d061ad64ad115a4444699608a90eacc5c84453950ec058c229648fa52f4
def s39:ℕ:=0x1200084d2b0588fda41563d9847e8031372b823f1f646683b11e83af06f1508f1781984fd047891d642cbc239f5a1fa69711c91df42b8d88e1416c6f2f846f7799884b4237b9e46e09111b7e01d850408d90d7e0fc3046be962417b4235bb177cf17
def s40:ℕ:=0x124ac8b5d2430921e7b7f685849007b9a3086247c3de71845123da3aec96e891c9a806e19c48e3e9d174702452d6a7d802121f092beab1890e3a98b7f004863e7b08092242950acf5e012116f655b4b09085fdfef0284825fa236bf42401b054795b
def s41:ℕ:=0x12871c6da21209434d4f7f9184a147d4e313e2507802fc68912839d16ebd4894049d07e0ec49eaefa3a9e824ec74ee29f61276319c749409380f984623c496f8bc36ad024b01330003612571cbb00d3892a4babc230c494845d6dc52249a64b069c5
def s42:ℕ:=0x12c24f5fb44b895fe63fd78304aea2790cd8a255bc887a27412a78c7d853c8953655340a584a8bf0e7d1f6254429666a6812a09b6c84bc894e1c4c927c84a5f1af0f636251fa7f6170b128e5f7edd0f89470c2d7eb904a2b1102c9e8250ec7aed602
def s43:ℕ:=0x130e850c926b898516ca8f63c4c1a29140672260cc40735f7130428487a1389820c8e04d4c4be3fee740c625e65db41a9812eea7ed89db0975db4e91a444ba126d128fc25cca78ffbc112dd6f6ca9ee896ce311f94504b66067cd5dc25af660b06b1
def s44:ℕ:=0x133bdec78a92099c6941a3b704cd0245a11662666d34d18c71332a3c99a9909964741474444ca8cf46ddba265045b0d2c61326ef47fe4a0992ad49b84004c85db4bc9b0263f3f51d80b131920508caa89899a3c90cbc4c4ac8b47f9c26250f3d95f4
def s45:ℕ:=0x138e21078cfe89c641eab23d84e3203a41c7027124de09445138361105f9b89c0b6751c8104e0141fd16f426fadbeec1b1137d3b2a8a6e89b7de6bfc04c4d927554d1ba26bcd7cdcd1a135bbfa5b8d209a5d22585bd44d0b3a6e094026831f5660e4
def s46:ℕ:=0x13c1215a8d1889dedd8ad7fac4ef4ceab87042771033130aa13b48e2707c889d7b5ab6642c4eab895820582754a6a956f4139fce53440c89cf10599449c4e68847633f227329402832413974bff425b89caf50cc0a3c4e487bd1fe4a271cc71243a6
def s47:ℕ:=0x140aa1fa09580a02d9c5fec444fdecb2f0a7a27ed85a5701013f187a4e58489f1ab174bd184f7152bf7e6227af71e666cc13d56c6d69e309ea7c9b315504f50862a348627a096e1964b13cfee9e49e309e6a59ae66584f12fa678e4a2786a29eebfe
def s48:ℕ:=0x143f3704ad058a1f44471c78450cb51e4c976286427a264bf142ed56411e28a163416b340850976342eeaa28481debe172142015a085120a0f3c363a7c050741ba1abba2837cba2c9a11414ea6168320a0a18f3741485049de34326c2817d7b9f293
def s49:ℕ:=0x1477ba642a638a3b8cda475fc51c8195e315e28e245291b0d14706299e2278a380bd7079b851b28d2b91f028d91b9623e41468407648b88a30a405bdbf451793886e76428ac271a75841448d261c5520a23d2bd8e9285111d2ba888428843e1517f4
def s50:ℕ:=0x14b9020788f60a5964390dd7452bb4faa7f80295c1899152214ac22de8db58a552657a7ab452a6110e2a9c294dedc72ea014a5166482db8a503fd1c3a28526ea9000c1e2930dc6224351493a5f1cc6a8a48915bc6cbc523ac326a1c028fce3e92d34
def s51:ℕ:=0x14e7688091f10a729089d4a6453725b86a02429b5799e650314d9eac06c7a0a69f4d6ed57453419f12afb4299f7db1c6e614cf02b28d858a6303779e16053054995809e297fbae3204014bf2dcc12d98a5e695325b7452e9b71fa76029731f9114a9
def s52:ℕ:=0x151f862a0ae38a8f326a8bccc546b693b89aa2a26f3fbef081511deb93de68a88badb2bcb854402bf000742a1d40835d99150b5c4447b00a80c6d14ac8c53fcfb1e03f629fa46c31bc314f423548dd78a76955efce7453a5b225999a29cf461a2211
def s53:ℕ:=0x1555641b64b30aaa53924fd88552b4cdbfbce2a8b37c356d615413254e74f0a9f0f12d68dc54f05d283d382a7805f120201539bbe046768a9ccc6fa783854daee0095ea2a6341e8110e152f9917d6368a9416d44c1c0549465d6a6e82a47c69eba06
def s54:ℕ:=0x156dd42347de0ab6549c4a44855a8e65729602ad448431c4115650f039f080ab2633b723e8558b0592f6562abe01f3e016155ece606e058aae4f3215f7455716b6ad6e62ab7784fa5e41559fa0d45f80aac9855e53f055620b1da8242aad0ae7be6e
def s55:ℕ:=0x15aca3bded0d8ad5a27656ca456ace8af45042b53668f985e15a45b791d188ad066c7870c45674d60e19f42b39d9d3139915984693f8c60acb3bfd2353c5650ea8c1af82b025650e0831578bd73e9208ab90a82d572455c6d9d933e82ae1eff0d06f
def s56:ℕ:=0x15d2b807cf908ae91adde6efc57320373d6762b97187bc00615c9f9a4958f8ae3cbd407030571d47bfad8e2b88bba7fc5c15c3b4044bc10ae1439c1f3f456ff12da4e022b757d46a9df15baae8e2f470adb6e175f3a856da458833802b6339ec8442
def s57:ℕ:=0x16007b877a0f8b002b0cfab3857f1a88831ba2bf58fac4c0615fa4ce3bf670afb7fa6adfd057c75f0b04e22be193f608e615efbe80b50d8af74d072742c57b7b4ad3f102bd4308c0acf15e84df0bf858af08104d46a45770590053142bab94ebd9e6
def s58:ℕ:=0x162e5c30c2f10b17268cf751c58ad8947def62c54a43a4530162530e3a9dc0b1292adc74bc58947959e8382c3b6f9d7e5d161a0563aad80b0b7fc7daf285828499d013e2c1327308b3e1609822c2d7a0b04928f47424581e2e0e4e902c01d6eeba75
def s59:ℕ:=0x16556b1b6bf40b2a5c5fb5264594bc7e665402ca554bb5f41165264400f678b27916456aa45938962e3aca2c9189c690561647d415f3b60b23b4614e1a4590f706e56b62c855f1a6b9b163ea19c39130b1d961fc5fe058e495a23aaa2c634226db38
def s60:ℕ:=0x167f4fb93b3a0b3f32de1782c59efa65434402cea5f24358816744106c9518b378edae5f1c599dfd8fa73c2ccea3d3e40a1664af1e44960b2fa2ecd2624597b3e57c1522cbb1cb8270b165cf50fb2a08b2cdd261f7e45966a31888f22cafe0a1361d
def s61:ℕ:=0x16ab92f38f6c0b552848216585a99f7dfdad22d49e0182fb716a14de20dfa0b4f851c3667c5a70d77fb3ba2d36ceb52efe169aa20e70448b4ce23e328605a5b02fc27c82d280596e52e168b2cbe18678b456aee653505a0e873c5a582d03c092b321
def s62:ℕ:=0x16d8e815bc6c8b6b65919db345b4283e6d47e2d9dfc1463b916cebff6c3238b64e898c5ac05b2446120f682d8a61fdd9ba16c294aa42df0b611332c77e45b0132a6a34c2d65cdd8223116b21b335af18b58b9ba6c26c5ac12304a05c2d58cbf03986
def s63:ℕ:=0x170046de30208b801a0e698f05c009ae23c7e2df980546f3216fbebcc147a0b7a237e783fc5bce144064122de415aca7d716efc09432380b75b4b8096485b979bf282382dc8dc002c5616e22dc74b5b0b705aee948485b679ef571ee2db245f722f7
def s64:ℕ:=0x17348ab8edaa0b965e26f75705c9cab732fa82e4e343f0fe71725ed38dfc68b8e44b48a1945c5e313885682e2dd2f758c71715d367635c8b8718b507c2c5c33dae9b7162e19092a959917099985f5ac0b82a397eb3dc5c0dca27ce6e2e01a7b97c4c
def s65:ℕ:=0x174fb15613160ba74bcadd4f85d345673c7c82e972fa8a8a2174989fe3a508ba40a690d2945d1a1ee132ae2e8d0bc4881817436857a7ca8b9f82c18603c5cf2de0c3dc42e78033b9add17391997ee7a0b9bc05f19c685cdcdf8429042e6c7eca5b2d
def s66:ℕ:=0x1784cfd303128bc093c2c7b8c5e041fa8e27e2efd785a3889177cf2cbfa820bbcce7fb5ec05de00d28d4f82eee336f2df51775276f8f738bb9eed4530685db412ca36982ec9a2c65d451764acb20ba28bab552fd26445d54dc0567a42ea9b6378c72
def s67:ℕ:=0x17a6acb6fd228bd0f7e0bd8845e7f5e3933d62f3ecb5ffacf179f4e55c3598bcefe8bf802c5e6251f447e02f2c974b89e917959c0047ae8bca3b46e93805e4216b8dbbc2f184e65b9d4178b5e2a457d0bc4bde20f4205e171b7095ce2f0b7c48de78
def s68:ℕ:=0x17cc8e31c01e0be5f7e95e8ec5f29eb1959de2f90633ced8c17c7dac59b3b8be2283595a645f041253d48c2f7d6a8319c717be114145dd8bde1b04998ac5ef06a4158082f7462e73aa017b7a1fd03068bd741f6d36105ea71a15b4a42f504f851f1b
def s69:ℕ:=0x1801c1cbba250c00cfb5d2dcc5fe031e0007c2fee077dd58217f5b7ae06518bf96bd190ef05fbf6aa684622fdee34d759317ee23f05cc50bf510ac857f85f8ab91c53c22fc0a56eb1c117dbcd5badee8bec941147d445f4395373be82fa19c43a00a
def s70:ℕ:=0x181fa0911c240c0fb93c12018607687516c52303984fa1f00181cb4a62a378c0de6920c578606069239ada302f6fa15352181794cfb2390c0b3abb2d6cc605441ce71e63022c19b070c1810f7e097728c0554361028c601274915ecc3003a8a95719
def s71:ℕ:=0x184a84cdc59d8c2497d47935461132da264ec30867fbd01d61842eef262520c2116569c4a86102d189e1dc307b7346edea183d445380e08c1dac6b0399c60eae504618c306c857d25cd182dc8c5d0858c14b466a62c060947e41658e30442684e501
def s72:ℕ:=0x187c1c410bcc8c3dcc8cc737461e8da6da7c030d513f262fa1868b103af7a0c334083b6b1c61706fc429fe30b1b444dc661854b316f05e0c29b72aabec0613d98d27432309cdba8c087184d48c7b2ac8c266093ece88612eafc49d52309584de8f5f
def s73:ℕ:=0x18a18cc270360c4ddf02fcc68626eb99f69ac312ef315b2bd1896294f901e8c4a14ae480fc624af789fce831253f6ca07f189136fe7a278c47e5805885c623e4acf459e311c961a69381888a50b1a6f8c406ef18a8cc61fc2ec2f05230fa7a2e13ec
def s74:ℕ:=0x18bd9473b1058c5d6466815dc62e8eef9f624317372e4f7b118b6cf9ccb410c5ab49614c1062d3ac3a84fa31660e5f43f218b1d36c0bea8c5744edab67862b364df3e0631552356426718aa59cc61600c547abe39a98629360bc869e31481abde105
def s75:ℕ:=0x18f58783f6d68c77ecec51afc63981959deba31cb88e43e9218e4398a98658c70300de40486364d26cb36031ae97f8220018d260e26a100c68d660c0608632a123126683191685bc73b18c87b69cb1c8c6411a89f0a0631538d26bae317ba10a5b7f
def s76:ℕ:=0x191b64d76eee8c8d13bb5d8606459f4bced263228f9f704fb1913f6086d2a8c891f37c442c64393335378e32166a99cb631904fb9019170c815cbb71ccc6408a7e641a23200f9731ff418fec3653cb10c7c94f6482f463e162f423b631ee669a3fb8
def s77:ℕ:=0x1940e7c9431c0c9ef85c3d20864f47b24421c326eafa9435e193564c2ff668c99f40b7626464c9299f2a0a326254cd210919300074fa4e8c974de78ff7864b2903a164a3258d19fe4b319279d1bd0ce0c8ee86c4e4e4647706b2da2a3239188bd5db
def s78:ℕ:=0x1958de3cab0a8cac678e7afbc655fc28f937832adab513ffc195653f073dc0ca8da67e6d346543f7ae9de0329ca6a93c9a194e19f543930ca6b010c8c2c652f65be83243296bfc05e031949e806bd608ca3ecd9ff93065129ccfb5a6328388bbd991
def s79:ℕ:=0x1998486f707a0cc925549a9c46648c15a7792331f8109907c198d2ae990b98cc681aa1bd60662476ea342c331200d21ab019881f8c96c78cbb4dbd55e0865cdddbf759632e67e4435981972aec1d05f0cb9080da5b5865967f7e2a3632b6e8960fca
def s80:ℕ:=0x19bb9f5321b18cdd984aa7b7466deed6a6bbc336e23acd84419b618932e638cd8ed6ca906c66c2ff5b5b54335c7fe986ff19abb858bc0a0cd535595f88866a98821ffd43351c0c03c8119a04c98a5fd0ccea1925d01c6671cf4b17523332ce866726
def s81:ℕ:=0x19e1569434808ceeeffdf930c6774af3dc81633b7e38d884719da46fe7da88cec14e7d746c67524a4c95b833a82132922519cfe3c5bfae0ce740ec6feac6734b94bdfe233930c8eca6f19c3ff0d58788ce13832a28ac670268e7dcd83377e7160836
def s82:ℕ:=0x1a085ebab8fb0d03e41c73698681eecdf0388340d1d87e5841a0509cc47dd8d01b287514d4680c203fe8ea33ff322302e919fcd16ab4d70cfcc97eca2cc67db55b3a4cc33e6df2584e619eef4a7acf78cf5d9f666664679f2ad7801033c5da6d8184
def s83:ℕ:=0x1a422d8c6b198d20139151b2068f72adf3d5834791a8002041a39af04c1890d1c661b76ec068dc12338618346cceb118821a30142550fa0d16b102a54a468b49bd4bc7034586a3d44cf1a2c2be6911d8d0f28c572548686a15e5dd94341e64904930
def s84:ℕ:=0x1a62a8c26ed48d2f631b650886978e8321dd234bbc8b21dc71a5c2c3091438d2d7e2997f7469681cf53a4634aa37aca05c1a53fc361d380d27419b2793c692c46b5549034921b99d0921a47e6a10de70d238b28b6ea86913d0f9e3843485a54d6097
def s85:ℕ:=0x1a8c8361328a8d4165f1b32246a0a347657e83503e817f1e61a808bb8e6988d3d776e2eda469ea255cabb434ef0e31c66e1a774d483a000d39f321f2ce869c4b14e452e34dcc7369dc31a6cf77d52858d348d5625db06998b14e450a34c9e49aced4
def s86:ℕ:=0x1aafebe1de430d576e396a4cc6ab87df03e5c35564adc5cc91aa54a6e268c0d51bfe156a646a8cef4a56fc354189317d461a9e29bb0c6f0d4cd30c040f46a536ef371ba35297403f3931a90097ce4e78d46e886e99fc6a36186e78963519d6c764ed
def s87:ℕ:=0x1ae0b1653b250d6ffef0aa0886b4f66dc5ecc35a56a1f00d81acf4c82b7c40d672494e80846b37a7cb16a035945b2b06631ac879615ff10d63efed98bd06b1e96c31c2235873cce07f61abdc19fb41d8d5c4023056706adcb03e12ec356a9254d421
def s88:ℕ:=0x1b0c20fb05ab8d84f645ec6c86c16c07bbd8e360979e13c541afede4baa090d7ea901229086bf30caccc1635f5902220dd1af633366cc10d7ad3e3855f06bd5b6fc77ee35e1cd2b9c9b1aee1deea8e30d744c02672c06b9c5fd070bc35c45a352281
def s89:ℕ:=0x1b300f62d5b28d965eb60ebd86cb28d9c1d723655c43f6feb1b28261a46d48d9292d5848686c85e4e69fc836425b1b23731b20801b306c8d8d2b68ac5706c65b6c38e8236301382f98d1b1064b069080d880706001086c350ff0fdfc3619992d7a99
def s90:ℕ:=0x1b5936e824f38dac809f6d8246d5e78549cfe36ab38b9990f1b52c3bd2ee38da8967e7ec306d3513666238369364dc4db21b47189438308da25be3643786d04b6c2472a36820678abc21b33d765c67b0d99710667d506ccac33a35a83661cd24586c
def s91:ℕ:=0x1b8c025bcd450dc4195de69146defa3c7cae436f02dcde8901b73c807a7590db931f3669046db11bd0986e36d3e7ddd3ec1b679f6731820db310144d8686d97d215664036c7217aea9b1b62339a1b268dafe66690bfc6d7eae4447e836b697311b99
def s92:ℕ:=0x1bbad45784d98ddd697b584406ed7fc513504376aeb7679211bb56c57b1be0dd833290f3346eb5ef933f8e375a20c3efd51ba6580094b60dd19d58227f06e82eb74a082373829755cc51b9a93cef0ee8dcc31e9576c06e3743d5fd8e37191db2270b
def s93:ℕ:=0x1be4188af0610df1c984690346f83cc01f9bc37b3bb7b736d1bd71763b95c8de940f02a5ac6f43a1730b963796426b24461bcada6927070de46c6ddeba86f19db7cd7ae378a9e50343c1bc2c36091660de1173ec90e46eff5300cb5e377c5d2f243d
def s94:ℕ:=0x1c157b4ae27d0e098bb737264703c782730f238089ca874a01bffa9422c580dff540cc55506ff226fb8a6037f1659618691bf8b2780cb60dfbee41888946fdddd1bc9e837e5b79746dd1bebeb295f0f0df5dff195a5c6fa84cda936437d25d752471
def s95:ℕ:=0x1c52ec1448340e2505c359f0c7120be823d60388b329868011c3a5f8cd16e8e1c98b2253ec70e0ea9faede38705e9524cb1c3554bf4a958e19a12822e6070c7eaa6a4023861d986fcb61c2c595828328e14e737cd4a470942dabfd4a3838b50de80b
def s96:ℕ:=0x1c75caf22dc10e3ace855ea5471c78735923a38e31369af0c1c6f2fd705bd8e3777565b10871b81912ba9438db4160a52b1c6c6da33b6b0e35567d5229c71a91faf567838d1b2ad47871c66cf97c2f40e2aa3d55831c7152c657e0b438a7ad8757c9
def s97:ℕ:=0x1cbc08797d520e5c49577becc72db93c56858396b402c63af1caf65c04fac8e56131a6a42c72a13178c7fc39337eeb400d1c91741693ad8e47a17e697d0720dc847f024390193a109431c7fe415acf20e3f1c54d3bfc71e8e67f2cd038ef65f26a2f
def s98:ℕ:=0x1cf7d8716a0d8e7a983bc96dc73ccc6c6b2aa39e50e94dcc11cf1f952b8718e7301b42ec8473808b9c52bc39bfa9af1ba01cde88c2c9530e6d15a558f7473575cacbdc2399e50309ff91ccbc67be8420e6571a2276647301f977b4d83980593fedc4
def s99:ℕ:=0x1d2a0d0c81de0e93875959bd07497a9b680b83a2dbf6d2dfe1d12646740ea0e88985a49774743c1e839c003a19e9f952b91d04c653c8738e81d3079f72073fe0183741439fc85231e941cfd137090e38e7d23918d8d073e0094ae58239eff6dcdfb0
def s100:ℕ:=0x1d685fef9a798eb28f662abe0759240524a943ac26243264b1d5d9db0b9688eadd509869b07569f4b194243ab0622926371d4d16efa7f80e9f68203bee874efc78ad4163a779e7216581d3596d00e410e9a6b68dab1874c54076f3703a5e482ef893
def s101:ℕ:=0x1d9a9d2fd1f68ecaed9fc085c764760a1e9043b1f324a91601d8d770ce2848ec42521e6db076172e4587a63b0abcde60ed1d82af1a2f4c8ebee78ab7c6875eb064b821a3af3ee1124dd1d791abc72ed0ebaf630611ec75ae5ba8dd5a3ad1e5d25cd0
def s102:ℕ:=0x1dda013f590d8ee7f716e55fc7730c7ba4d963b97e18b26d31dc4e6168a3a8ee17ecfc69547702e602f1083b8112dbf2591dbeda6893fa0edc2d95a334876abed3272603b4f8e78a0b01da5f91ebee00ed26f9b38b1c768af43f37ca3b3674c65416
def s103:ℕ:=0x1e0c321088498f051920c9c4478165261e9963c078b72ea181e017a7443bb0eff60bb9149477f35ac1ac623bf62b00b5f61df9df6ecc098efab156f760877c8dc71ae7e3bdee9cb151d1ded2490973a8ef2f41520ba877919e4748e23bc81d1e5abf
def s104:ℕ:=0x1e4caafc51e38f25f0d3ba238792f482554943c8e543a58ae1e45a3c86d580f21a72d542987902cf2f4dc63c74f5e01f991e256dbf65378f10c6df1e6b0787eafea46723c371876a4f91e1b6db8e8038f0ce16339774785775637df83c20eb768ba6
def s105:ℕ:=0x1e814c1a5bb48f3ee93e6aeb079f03924f3163ce5d8ecfaec1e71f71d86a50f38568f784e079ac162780703cd265f127951e66eb8f0a238f2f28f7a5f4479603ee0008c3caf261461b01e56a61e747a0f2b28ef9fb3c794fbfab117c3ca02c535c6c
def s106:ℕ:=0x1eb0ac048fc20f581e0a564b87aa59193b60a3d52667d27d91ea77f515c488f50ec6d9bf787a7d259276963d3cc9a7e9a11e9b8d075b2f8f4c7c836f3ac7a5dfc179e543d25931adb551e910c34607a0f44de2ebd4587a20f89be1e23d0a448b7597
def s107:ℕ:=0x1ef3d5debb398f792362f82647bb9c75153e83ddc675728351ee860f04bc98f7173db170ac7b7aaa1f63c43daf092484aa1eca8e101e6d8f6309a3abbd07b1259890ac83d858f9121281ebadd205e540f5cc74229b747ae40d5940ba3d6a5d179e82
def s108:ℕ:=0x1f17e20f8eb60f8991a7966d47c47620521823e22d2b6a9881f0fb301800a8f83af6c08ac07c187397d5e23e0bcaec1bd71f0448b351678f820a4e6eb647c07a03d9e0c3e03cd6d93bd1f01c58adfa20f8099edca11c7bedc84e7f0c3de8ed8464c7
def s109:ℕ:=0x1f62957b4e2a8fade1b8528f47d656908cfba3e9ef0af9f071f4c98ed3b250fa54b3cfe78c7d13c0fd352e3e86324380961f375b10f3020f99b933b30a47cc982e2cc083e4e05d0cbf31f26a453708c0f91e9e2f1b7c7c83cb59c2c63e2ffaeaf3c1
def s110:ℕ:=0x1faa129bd0cc8fd27d41ff0047e84d1082b543f38851025c71f95a9a585898fc7de516f88c7e35ed991f503f0c7b146af41f85b898e96e8fc11c168e77c7e0300b9b13c3ef94287bce01f78e390518f8fba7d34d7e087dcd4e6307ce3ecbfdf486e4
def s111:ℕ:=0x1fda354594ac8febef7c9dce07f518a7e02663f9df26cc7da1fcc80d76a208fe5ce905ae407f15e033217a3f8aa379f1021fbf6964ce660fdfb2beb7f087ef80f35b4703f6fdceeb57d1fb72aa5f1d80fd8ddcfc2f447ebf760b3d763f547eeeadce
def s112:ℕ:=0x201e094015fa100e07b4f70ac806e81262c2440352fffc7df201993cfb0379006d53f0eb288026ae9bccea400db5b974f620010ffdc5ca0ffed6f7092707fe4980051ba3fd22c7cb19d1fe807a362a80ff01742130dc7f7eb7d5bcd83fb86a712957
def s113:ℕ:=0x20640a2560579030ef38d8a648174d81653f640b5fe0772ba20594ce731af102c47b06edd8814d21a3f8024096b126f35a20440e4df363901e6975cda2880f12e7880c6406dd40089962036d1b8cf26901b358e6ba8080d3191e41044064c2d25d55
def s114:ℕ:=0x20a36afc815e1050cb76c8440826a533739ec4131e37be9dd2095367f952390458f83bc024821e614dfdf441086c852a33207cff9657289039e20d8889481b7d37d37e840da2989dc3e206c2d826e2b103592ff5749481ac909f78ac40cdece7a4b0
def s115:ℕ:=0x20f694a2a453907a78381c03483d24895c30441e26e052ab120ef44c683879075ed09e9f1c83ae9ad3cc5e41c27e2a06ff20d762fa358e106ba5d4c1bc88322a3b68134418fd46f614320b5d4f5f67a1058f92467ebc82c315889eaa414ef3b69f6c
def s116:ℕ:=0x215d09b4e53410ad401138b98854c060f17f842a2ca046f29214da0abd6fa10a2705d674f8850abf3e536642717af7aadd212e366b8d611096a114a942084ac17d929924247f68e826b2119aa4791cc908b6120d96c0841d66c7f02442045aae1e55
def s117:ℕ:=0x21d1761d724c90e8a6e7d15ec874045f00094438d1c1f26b021b4696d30a690da2f01a8a0886cbdb80ad08435c705f2b9d219aef48e70010c9d2ecda31c8648a9063d2842fd7c1210e821725c0a98e410b7a2e0981b085bcd70423fa42c7b9ac7a0e
def s118:ℕ:=0x2216f44a52639108eaae8ee848844e332583a44104241f52121fdc74baa3610fe9636873f087d5cd3ab90243e9f552451621ec5757429910f41c4e4af9c8795b186dde843bc319fb6b521da01af347110ec862b1ed00876224e6d7ba43a3f289df55
def s119:ℕ:=0x228b231913fd1144a0f9a96648a1c4ad8c36e44fc5d18277e227854f7966e913b2ceeb9ec089d194cee06844e853c263822270fd501e7d9120a9de70de488edc67e538e446e234e216c222e84dfd1f69116dff03d2088872b2c2bc7c443471b32c31
def s120:ℕ:=0x231503cd787a118802e0727288bfb7633c4d845e88ed00c2622e33d65756391709d14cb46c8b38f8324b484594177ccf8022c9557f653791610d3b5e7688b04e81a59f24566711a1fda22a4ecb1332d1150e299681548a62414036084520102e4f59
def s121:ℕ:=0x237d23327d1c11b2758f281748d793fe4952646b650b887d02355b00da7e411a3073f8d7408d043724cd3246784bedf0f1233804054889919a8c8b120b88ccfd6fc4904465e07802373232625ab5458118c8ce28cbe48c6082d5dbba462ef92f9aed
def s122:ℕ:=0x23e945a492da91f40955fa7f08f7eee778dbe47abe2f269b023cb1b595de611e354b968db08f14ee4e5c7e477527f7c5a623b7ec73576e91d81db84b8bc8eb33e0d63e8474e20e23df723a1dcf5b60b11c58495aaf1c8e00ec9a5bc646febd6836df
def s123:ℕ:=0x2457b83137ee92281e504bdbc91126ce4e5e8486a0e3a48f62433b42a873192196a789b31c90ca2fd5dac24860754d24f1240a760030cc1204b3b29d530900202f4ec9447f829ce1c4723f8d99f13cc91fb1df9cb9d48fcf0673cb0447da146009ea
def s124:ℕ:=0x24d13d5097c29262c5afac2bc92e4f4925f1a4968fda2a00524b38d7ad34112590da780af892c295d3d1324956213ff061249c165c261b924ac6a6231449239d562c8d8490b7a8e2ab024835144ce66123e6d9dbee8c9178cab5cd0a48bb56bff05f
def s125:ℕ:=0x2537abfb1112929ac48a7aec094b0f7a2606e4a5534781e522526e6ebb95d1290524c2dc289441c349a3204a127b79302d2500c2c40d8c127bc1f78c37493c52806227c49da7b1b2fab24e3521aa7d5126f10d230d3893719bbc67e849b5416e2dc7
def s126:ℕ:=0x25a3da2822e892cba7d67c7749659a63af4c64b136ea6993c258461559dfb92c1363e7bb1c95e4f96a60c24ae86549f4f425735958b3c112b71f3bcc37495a1c52b53324ad0436de936255f963d655f12ab209f495b09548f87660524a8c7c0f302d
def s127:ℕ:=0x26354d0237949319929b4a20898c4fe2e62ce4c547085afc726203d20b54c930f140f73eb498783491ccd84c2a86c044b5260aada97abb93021fa54c40c97b4ca57c4144bcaa9c5acb025d34199fc0912e53e495229c96aeef91c3864b480cd2a77e
def s128:ℕ:=0x26c1407798f7935ae28ac80c09aaa3ff722d24d3671ebc881269520b0b6d8134620274c92c9a19007e63da4cddae71ce00266e12398f4a1324c08169470991bc630e1144c8a7f8731bf263a433ced6f931bce001f5ac98dc6dab65ba4c6da6610c7c
def s129:ℕ:=0x27194114992e9388d3f03d2089c29b35f47da4df930edcfd526f2f11474c11375047826d0c9b9764294ed84dc1c562451726e04994e0ab136e204f4c8ac9b6023da57324dadce5173dd26d42e86db12136902045c31c9b2cc65ca6b04d83d4f93735
def s130:ℕ:=0x278b604bd05113c51a776726c9e193fb34f9a4f0283953351277a81d731b713bce7e74c71c9ddacb9a69ba4ec1b9034ae9275ec72e14a313a680e4587b89d24fd575df24e89d8fd2eb0273da751de111396a090cca0c9caecc02d7324e488229326f
def s131:ℕ:=0x27f4b84c77d813f92e627fccc9f81095a67464fbe916f418627d81914c65393e85f52f9b6c9ed4f61d94de4f6579e4aa8227afafeafd4713d6d2781a1b09ea9089667724f5283e5334127a60276bced93c7ea663b2649e3481518bf84f18f0c01b04
def s132:ℕ:=0x287243359a149431eafd04650a18cc1836ec050b1a65ca05d2847a0a256cc9420cc0ad3f20a100ed5b062450701c1df0f1283037b8785a94162b2263910a0a59a6f0e3250433728f2c728167ea47aee94092150cce44a02fcfb6eb424fee8b6b9570
def s133:ℕ:=0x28e143e89a52946e96da496d4a34d3c7236dc51a4b93974bb28c9675a59e3946421fe4d49ca31db3aedb20517a87a334e328b70b59d02d145b25312db74a2c50e7a68b2514a982b7be728a4841a585814496f3745dd0a217c96faa4250e511a06b82
def s134:ℕ:=0x29544fe838d814a9a93ad8978a54aa80d8274528ce84aed612945449b9a87949d2246cd564a4c952b85904524288b3351b291987f2d587147fb63c1ba64a3f1a354ec9451edda9c3c4d28f6440b9a5a947b20df5a624a3b91eb3c43251c7477bc6df
def s135:ℕ:=0x29f5e1de1c6e94f91045fb608a7b7057dd7e6536e709c2f9929b0899299a994d68ec4e03eca67ff9f0986e531e72d99ccc298a04a2338314bc61a9bee8ca5e18bd2b66652eccd014627297133203a6394b2b99dd501ca5888b17962652ac2c4077dd
def s136:ℕ:=0x2a468fda8ce51521ca1188894a902cc82add254759e3772ba2a2045f89b0f950f34a6506a8a8746fd9237e5432fbc970e02a18fee61ae3950a2c7934640a834e8c7eb9854108b9936272a041bb619581501bcc5ce9f8a805635691aa53f28bb13675
def s137:ℕ:=0x2ac46fa4941095606555fdb1caaf2552337325570a33c20852ab3e783f9d81558f634eba08aabfba454efc555ebe6b2f4c2aa17fdb907b1550a362cdb0caa651b026dea552b5b37f9dd2a9546af9b63954a23624dc3caa2362ee2d5854de0847f099
def s138:ℕ:=0x2b7148229be095b53afe43a60ada259c76f8e56cfbc9d02c42b63b351da5815aeb2cac570cad2e10c0fad6567f0c57076d2b357959dd6e959aa3efce01cac9b3fe7633255ce5393f8122ae664caa453956e4b1140104ab5122de59ac55908e0536fb
def s139:ℕ:=0x2c137f1fbad81608a493ce33cb041f151ea1e5820c46f78c72c08a2b2669815fdb9f2b62c4afb923ee718a57ce339e53582bde9bcfb94c95eec63dbb790af55145ef7ba573c90c738252b91fa798f4a15c55fb873800adca71a9cd7256e3708f6f82
def s140:ℕ:=0x2d4e337b7a4c96a425994e9ecb4d12bea74465a5315c2c1f42d14dc937eef1661a576cdac0b2e0b7f6738e593493f339412c9667a599cc9648df95c03d0b24527b2725a58ea21ab3cde2c7149e69ccc9624a4bb4e3a4b0c610966104585c929f38ad
def s141:ℕ:=0x2ea24d699e189740a689cee5cb9b133c2770e5ca8e81e7fde2e3c4ca69d9d97117144ae2c0b81f1625778e5c0bfea2b5992dfd4c3d9d8596e0ab4ba0bd0b6d2a1457dbc5b5a97db3b2b2d9d4ba99d3996c4a5c74eaa4b5cc5aedef605abff386fac7
def s142:ℕ:=0x303245f2fdd817ff946d7fb1cbff13e827bce5f929e613d252fb14f049e9697ca05c580778be22e6e38be85f04f44a3ab02f575d151ee39780a6facf20cbbd0ff3481bc5de1dc0604f42ed2ae573cd8176526c8cf084baf72c9ced325d5f229e7cc7
def s143:ℕ:=0x32615361a035992c29aa5015cc8414b7a802663eca57f401d31f552b79feb98f8a961d00dcc595472e7e9e62aca3af3f9d30e211c0de5818537a506ff1cc1e541727cba60e2a0753e01306050289f0f982527fecf724c0f93f9e7b9a6067ae91c2de
def s144:ℕ:=0x36745a02a2b99b2cacfc51714d93567168a766c82b35f453f35b458cca24f9a912bf6d1064d3855e4687d6699aaeb34393346656aba1729a28ab4450b54d08558fa851267c4abab4259338c5556a10d99b4aa9550844cc65524a82e26560a81d4153
def s145:ℕ:=0x3b2a61b1a5b89d48305852a3ce8857ff6942673d2bf5d49f939e45fb2a5099cac2f5d524ace5257b1a92f27104bab3480138795d4ca3f69c272e8dd2054e0d5739e8fae7062b9ad47a937d15c5fa3cf9bc32de1d1b94dae16a128c2e6d02b44145b5
def s146:ℕ:=0x41e16c99a9dda0e93652d502502e5ab2aa5028140d52d5243403c6a0ea9059ff8b4b954544fc15a00ea0be7d9ccf3f4ffd3ea66777a8069f00b325d3b9cf54594f29c7a7a20c9c14e0f3cfc64a8a6db9e08b192531f4ee7589d6983676f4c4934c11
def s147:ℕ:=0x47ad75fdad65a3c4baf356c251a51d1aab4068d02e8cb5a234616737bac8aa2eab98fd639d1705cb9eb11e8b02e4ed581944fe71d3ac02a222384255b3d1085c162ad8a87a2df81562543686f3cab03a1aab777d559d09c9b636a91284dadb2354a3
def s148:ℕ:=0x4a4c7b2eb005a508bd4757d252765e612bafa9380f3315dff49ba7969aed0a4d53cdad79a525c5e4cebbae927af15b5d2b492e7957af4ea46abc43d76dd2141ddfab9669054ee035c0147f976ccadfea3f43b3956d6d1f75a880df388f62ec1d5af9
def s149:ℕ:=0x4db8805ab1c5a6af3fabd88b533b1fb1ac3f6994afc77616f4c897e9cb136a6443f6e58b9d3185f806c31698bcfc4761d54c057d0bb017a5c63e3057f9d2da9f416c2f296acf85f5ffd4b4d7c95b06da5823df65807d2bc5edd2be9a95d2f7355fb1
def s150:ℕ:=0x51008638b44fa864c29b59c6541b21322cdeea0bb08336593503d84b1b391a80c41fa597dd40360f26cb669ea3059f653f4f30824eb239a7894148d95053c060aaacb229d0502bb63f94e598102b1c8a718c04958b85376601a2c6ca9b8b014763ff
def s151:ℕ:=0x53b98a04b566a9bac4abda7dd4d12248ad3e6a67913cd6b7b533888c4b49ba990449b5a98d4b5220f2d1fea5130f4168455241879db479a90f4407da835471a1bfed15aa3830d2167d551ae868bb3faa8bcc35c5a2d544aa15b6cd52a2050a8b66b9
def s152:ℕ:=0x58219139b82dac034873dbfb55e96436ee11eaea91ee56e5356e18eaeb6d4ab6ec772db8ed5aa63b4add02ace11ca16def56698ed4b77eaaea46d25b73d551a306ed78aaa6318d76ca755298c1eb60caa6d45dcdafc552d62c9ed5eea8f516db6c19
def s153:ℕ:=0x5d0198bbbac3ae4b4c5bdd975725663deedaeb6e12c41736f5b5996f0baa2ad9e4b405d29d6ce656f2e61ab6652c2b73e95b119594b98ead0eca74dcecd66724dfae3d6b33327417235596292c9b870ac86c91adc16d63864b8ae442b1232359705d
def s154:ℕ:=0x60a49f5cbdbfafdf582667d2d7e776687a0b6bf2539fb78e95f919ccabc38afc64e675e22d7de674f2f33abe99bccfd62f5f4a9d25bce4af9d57246706d7c3abc673c82be0fc729dc755ef19be2bbf8aef84d775e04d75fa65deebfabacb328775bf
def s155:ℕ:=0x63e9a3d8beeab1f0d238dfcad8ea28df2fb4ec6b147957eeb6336a2ebbebab19051845f77d8b4688c2f98ac59344ad7d296269a20abea8b0ff50c9df4d586f68146f646c335404b7b19618aa071bdf0b0b24ffa5ecbd83c67e8ef6eec1c33e137a5b
def s156:ℕ:=0x67e2aacdc1ecb3e2551560b0d9b6aa3670402cda3527f82df66b1a87ec0ccb326541b6076d98c69f9302dacc2b4ebf8087660ca838c12bb2db5369e00d595669b63020aca114bc57fbb64c1a557bf97b25b52cfdff7592ca98070142c8fb4a3b7f4b
def s157:ℕ:=0x6be0b0d8c3efb5a6d81ce1f4dace6c1d310dad61d5ff787d56a91aeccc336b53f5763e1a35a9b6b9b70bd6d3a55b03855169c1ae0dc349b4ccd6b9616c5a5e2b5930baed15957a1844768a1aba5c201b424d5d3612e5a106ab9b0672cfcb5557838f
def s158:ℕ:=0x6ff4b7acc6afb7e85be06373dbe86dea71bf6dd8b6af78b4f6eb5b5c7c60bb738da8d62d05b8ead4a717a2dc536a858c216e22b4b5c58cb6f75a17e29b5b406cc0313ead96365b78a476ca4b292c4e9b64cd8fa62275b206c7cf11aed8a1637d88d3
def s159:ℕ:=0x7492bf85c9e4ba20df47e49fdd062f8d3242ee7a37c39927d7398bd9ac8f5b98ede44e42cdcbf2f3bb2396e4a376d19015721dbb55c82db9055d6ee3e25c71aea8f1f4ae2cd74af8fcd70f1b902c700b834dc47638e5c186e1071b56dff96f0d8cfb
def s160:ℕ:=0x79a1c71ecc64bcaa63a56670de43b19ff317af1db8ce398e37834c4e2cb99bc10e26ee5d4ddefb12cf2f8aeeeb872f9617773cc388cb3bbb9ce1d565b05d8c706db29d2ec51843995c77626c18bca52bac2e071e527dd5ab02472862ea9380219365
def s161:ℕ:=0x7fe1d179d07dbfdee8c6e85adfa133d933f1efcbd9dcf9edd7e09cec6cfa4befce716678b5f7c7394b3d22f96598db9d497c55cbffce93be2865c86713df0072caf384ef79b954b9b7b7ae0c976cd81bd50e49c66c15e90b20e73382f423900999bd
def s162:ℕ:=0x8696dc43d48ac2e66da06a29e16c76bbb50730911b1d9a687847dd8c1d321c1fd6c24e99860f075f1f4b9f064bae37a5af827ad595d1fcc128ea9d68e4608a3554b483703a3a941a3658171d454d1c6c036691f685ae015b496f43ab004ba367a0df
def s163:ℕ:=0x8ecee99fd9a6c6b8f3c56c78634b79b7762171a29ce39b1bf8cc0e648d85fc5c0f231ebdde2d0b90975ef31603c6adae598ab2e2f1d718c4c8f09e6b43625c384bb5a6711abbf9faba788a4df9ad5d1c3d0ef0aeaa8e1e7b78df55db0d53b891a8f5
end Codec0
end SubmissionLower
end ProximityPrize
end
