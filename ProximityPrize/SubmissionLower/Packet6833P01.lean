/- Apache-2.0. Built on the BitWonka 68.34 packet engine and Bome2017, Lucieno and 0xAndoroid contributions. Retuned for 81,095 errors. -/
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
import ProximityPrize.SubmissionLower.BoundaryTailGates
import ProximityPrize.SubmissionLower.HFreeBudget6812
import ProximityPrize.SubmissionLower.HFreeChar6812
import ProximityPrize.SubmissionLower.HFreeCore6812
import ProximityPrize.SubmissionLower.HFreeDedekind6812
import ProximityPrize.SubmissionLower.HFreeDefer6812
import ProximityPrize.SubmissionLower.HFreeDir6813
import ProximityPrize.SubmissionLower.HFreeElim6812
import ProximityPrize.SubmissionLower.HFreeInfLaw6813
import ProximityPrize.SubmissionLower.HFreeLocal6812
import ProximityPrize.SubmissionLower.HFreeNormalize6812
import ProximityPrize.SubmissionLower.HFreePlace6812
import ProximityPrize.SubmissionLower.HFreeRegular6812
import ProximityPrize.SubmissionLower.HFreeSlice6812
import ProximityPrize.SubmissionLower.HFreeValuation6812
import ProximityPrize.SubmissionLower.Koala6831IntrinsicTail
import ProximityPrize.SubmissionLower.Koala6831MovingSources
import ProximityPrize.SubmissionLower.Koala6831OrdinaryJet
import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_1
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_12
import ProximityPrize.SubmissionLower.MergedInfra6815_13
import ProximityPrize.SubmissionLower.MergedInfra6815_18
import ProximityPrize.SubmissionLower.MergedInfra6815_2
import ProximityPrize.SubmissionLower.MergedInfra6815_4
import ProximityPrize.SubmissionLower.MergedInfra6815_5
import ProximityPrize.SubmissionLower.MergedInfra6815_6
import ProximityPrize.SubmissionLower.MergedInfra6815_8
import ProximityPrize.SubmissionLower.MergedInfra6815_9
import ProximityPrize.SubmissionLower.Pilot6832Scalar
set_option autoImplicit false
set_option linter.all false
set_option maxErrors 100000

noncomputable abbrev _root_.ProximityPrize.SubmissionLower.RCN275.ResidualSupportParameters.FGV := @ProximityPrize.SubmissionLower.RCN275.ResidualSupportParameters.acceptedSupport
noncomputable abbrev _root_.ProximityPrize.SubmissionLower.RCN275.ResidualSupportData.IZ := @ProximityPrize.SubmissionLower.RCN275.ResidualSupportData.coordinate_bounds

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
set_option linter.all false
set_option autoImplicit false
section
set_option linter.all false
section Compact_KernelEval
namespace KernelEval
@[simp] theorem sumRange_zero (f:ℕ→ℕ):sumRange f 0=0:=rfl
end KernelEval
end Compact_KernelEval
section Compact_PackedLegacyCore0
section PackedLegacy_E6
namespace ProximityPrize
namespace SubmissionLower
namespace RCN264
open RCN072
noncomputable section
variable (K:Type) [Field K]
theorem AJF {G T H:MvPolynomial (Fin 3) K} {P:Ideal (MvPolynomial (Fin 3) K)}:
   P∈RCN264.regularComponents K G T H ↔ P∈RCN072.componentFamily K G T∧H∉P:=by
 classical
 rw [RCN264.regularComponents_def]
 exact Finset.mem_filter
variable (G T H:MvPolynomial (Fin 3) K)
theorem AAS (C:RCN264.RegularComponent K G T H):
   C.1∈RCN072.componentFamily K G T:=by
 exact ((AJF K).mp C.2).1
instance CYY (C:RCN264.RegularComponent K G T H):C.1.IsPrime:=
 RCN072.component_isPrime K G T C.1 (AAS K G T H C)
theorem _Q6 (C:RCN264.RegularComponent K G T H):H∉C.1:=by
 exact ((AJF K).mp C.2).2
theorem EN (C:RCN264.RegularComponent K G T H):G∈C.1:=
 RCN072.cutIdeal_le_component K G T C.1 (AAS K G T H C)
   (Ideal.subset_span (Set.mem_insert G {T}))
theorem GV (C:RCN264.RegularComponent K G T H):T∈C.1:=
 RCN072.cutIdeal_le_component K G T C.1 (AAS K G T H C)
   (Ideal.subset_span (Set.mem_insert_of_mem G (Set.mem_singleton T)))
theorem PU (C:RCN264.RegularComponent K G T H) (v:Fin 3→K):
   C.1≠RingHom.ker (MvPolynomial.aeval v).toRingHom:=
 RCN072.component_ne_pointKernel K G T C.1 (AAS K G T H C) v
theorem AZA (v:Fin 3→K)
   (hG:MvPolynomial.eval v G=0) (hT:MvPolynomial.eval v T=0)
   (hH:MvPolynomial.eval v H≠0):
   ∃C:RCN264.RegularComponent K G T H,
     C.1≤RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
 classical
 obtain ⟨P,hP,hv⟩:=RCN072.exists_component_of_common_point K G T v hG hT
 have hnot:H∉P:=by
   intro h
   exact hH (hv h)
 exact ⟨⟨P,(AJF K).mpr ⟨hP,hnot⟩⟩,hv⟩
theorem WX {Seed:Type*}
   (S:Finset Seed) (v:Seed→Fin 3→K)
   (hG:∀γ∈S,MvPolynomial.eval (v γ) G=0)
   (hT:∀γ∈S,MvPolynomial.eval (v γ) T=0)
   (hH:∀γ∈S,MvPolynomial.eval (v γ) H≠0):
   S.card≤ ∑ C:RCN264.RegularComponent K G T H,(RCN264.componentSeeds K G T H S v C).card:=by
 classical
 letI:DecidableEq Seed:=Classical.decEq Seed
 have hcover:S ⊆ Finset.univ.biUnion (RCN264.componentSeeds K G T H S v):=by
   intro γ hγ
   obtain ⟨C,hC⟩:=AZA K G T H (v γ) (hG γ hγ) (hT γ hγ) (hH γ hγ)
   apply Finset.mem_biUnion.mpr
   exact ⟨C,Finset.mem_univ C,Finset.mem_filter.mpr ⟨hγ,hC⟩⟩
 exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
theorem AXW {Seed:Type*}
   (S:Finset Seed) (v:Seed→Fin 3→K)
   (hG:∀γ∈S,MvPolynomial.eval (v γ) G=0)
   (hT:∀γ∈S,MvPolynomial.eval (v γ) T=0)
   (hH:∀γ∈S,MvPolynomial.eval (v γ) H≠0)
   (gap nodes pencil:ℕ) (cap budget:Fin 3→ℕ)
   (degree:RCN264.RegularComponent K G T H→Fin 3→ℕ)
   (hcomponent:∀C,
     (RCN264.componentSeeds K G T H S v C).card*gap≤
       nodes*(∑ i,cap i*degree C i)+pencil*gap*degree C 2)
   (hbudget:∀i,(∑ C,degree C i)≤budget i):
   S.card*gap≤nodes*(∑ i,cap i*budget i)+pencil*gap*budget 2:=by
 classical
 have hfubini:(∑ C:RCN264.RegularComponent K G T H,∑ i:Fin 3,cap i*degree C i)=
     ∑ i:Fin 3,cap i*(∑ C:RCN264.RegularComponent K G T H,degree C i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   S.card*gap≤(∑ C:RCN264.RegularComponent K G T H,
       (RCN264.componentSeeds K G T H S v C).card)*gap:=
     Nat.mul_le_mul_right gap (WX K G T H S v hG hT hH)
   _=∑ C:RCN264.RegularComponent K G T H,
       (RCN264.componentSeeds K G T H S v C).card*gap:=by rw [Finset.sum_mul]
   _≤ ∑ C:RCN264.RegularComponent K G T H,
       (nodes*(∑ i,cap i*degree C i)+pencil*gap*degree C 2):=
     Finset.sum_le_sum (fun C _=>hcomponent C)
   _=nodes*(∑ i:Fin 3,cap i*(∑ C:RCN264.RegularComponent K G T H,degree C i))+
       pencil*gap*(∑ C:RCN264.RegularComponent K G T H,degree C 2):=by
     rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hfubini]
   _≤nodes*(∑ i,cap i*budget i)+pencil*gap*budget 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left nodes (Finset.sum_le_sum
         (fun i _=>Nat.mul_le_mul_left (cap i) (hbudget i))))
       (Nat.mul_le_mul_left (pencil*gap) (hbudget 2))
end
end RCN264
end SubmissionLower
end ProximityPrize
end PackedLegacy_E6
section PackedLegacy_W9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN367
noncomputable section
section Domains
variable (R S:Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
 [Algebra R S] [Module.IsTorsionFree R S]
local instance:Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
local notation3 "K" =>FractionRing R
local notation3 "L" =>FractionRing S
local notation3 "E" =>IntermediateField.normalClosure (FractionRing R)
 (FractionRing S) (AlgebraicClosure (FractionRing S))
local notation3 "T" =>Ring.NormalClosure R S
local instance:Algebra S E:=
 ((algebraMap L E).comp (algebraMap S L)).toAlgebra
local instance:IsScalarTower S L E:=IsScalarTower.of_algebraMap_eq' rfl
local instance:Algebra T E:=
 inferInstanceAs (Algebra (integralClosure S E) E)
local instance:IsScalarTower S T E:=
 inferInstanceAs (IsScalarTower S (integralClosure S E) E)
local instance:IsIntegralClosure T S E:=integralClosure.isIntegralClosure S E
local instance:IsScalarTower R L E:=IsScalarTower.to₁₃₄ R K L E
local instance:IsScalarTower R S E:=IsScalarTower.to₁₂₄ R S L E
local instance:IsScalarTower R T E:=IsScalarTower.to₁₃₄ R S T E
local instance:FaithfulSMul S E:=
 (faithfulSMul_iff_algebraMap_injective S E).mpr<|
   (FaithfulSMul.algebraMap_injective L E).comp
     (FaithfulSMul.algebraMap_injective S L)
variable [Module.Finite R S]
 [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
local instance:FiniteDimensional L E:=Module.Finite.right K L E
local instance:IsFractionRing T E:=
 integralClosure.isFractionRing_of_finite_extension L E
local instance:Algebra.IsSeparable K E:=
 RCN367.normalClosure_isSeparable K L (AlgebraicClosure L)
local instance:IsGalois K E where
local instance:Algebra.IsSeparable L E:=
 Algebra.isSeparable_tower_top_of_isSeparable K L E
theorem CSX:
   IsGalois K (FractionRing T):=by
 refine IsGalois.of_equiv_equiv (F:=K) («E»:=E)
   (f:=(FractionRing.algEquiv R K).symm.toRingEquiv)
   (g:=(FractionRing.algEquiv T E).symm.toRingEquiv) ?_
 ext
 simpa using! IsFractionRing.algEquiv_commutes
   (FractionRing.algEquiv R K).symm (FractionRing.algEquiv T E).symm _
variable [IsDedekindDomain S]
theorem FDH:Module.Finite S T:=
 IsIntegralClosure.finite S L E T
local instance:Module.Finite S T:=FDH R S
local instance:Module.Finite R T:=Module.Finite.trans S T
theorem DPY:IsDedekindDomain T:=
 integralClosure.isDedekindDomain S L E
local instance:IsDedekindDomain T:=DPY R S
local instance:IsGalois K (FractionRing T):=
 CSX R S
variable [IsDedekindDomain R]
attribute [local instance] FractionRing.liftAlgebra
theorem FDP
   (P:Ideal S) (p:Ideal R) [P.LiesOver p]
   [P.IsMaximal] [p.IsMaximal]:
   Ideal.relNorm R P=p^P.inertiaDeg R:=by
 obtain ⟨Q,hQmax,hQP⟩:
     ∃Q:Ideal T,Q.IsMaximal∧Q.LiesOver P:=
   Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
 have:Q.LiesOver p:=Ideal.LiesOver.trans Q P p
 have h:=Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
 have:IsGalois (FractionRing S) (FractionRing T):=
   IsGalois.tower_top_of_isGalois
     (FractionRing R) (FractionRing S) (FractionRing T)
 rwa [←Ideal.relNorm_relNorm R S,
   Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P,map_pow,
   Ideal.inertiaDeg_tower (R:=R) P Q,pow_mul,
   pow_left_inj (Ideal.inertiaDeg_pos Q S).ne'] at h
end Domains
end
end RCN367
end SubmissionLower
end ProximityPrize
end PackedLegacy_W9
section PackedLegacy_G2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN356
open scoped BigOperators nonZeroDivisors
open UniqueFactorizationMonoid IsDedekindDomain
noncomputable section
section FixedExtension
variable (R S:Type*) [CommRing R] [CommRing S]
 [IsDedekindDomain R] [IsDedekindDomain S]
 [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
local instance:Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
theorem EKX (v:HeightOneSpectrum R)
   (P:Ideal S) (hPzero:P≠⊥) (hPprime:P.IsPrime):
   (normalizedFactors (Ideal.relNorm R P)).count v.asIdeal=
     if P.under R=v.asIdeal then P.inertiaDeg R else 0:=by
 classical
 letI:P.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hPzero hPprime
 have hUnderZero:P.under R≠⊥:=
   mt Ideal.eq_bot_of_comap_eq_bot hPzero
 have hUnderPrime:(P.under R).IsPrime:=inferInstance
 have hUnderIrred:Irreducible (P.under R):=
   (Ideal.prime_of_isPrime hUnderZero hUnderPrime).irreducible
 rw [RCN367.FDP R S P (P.under R),
   hUnderIrred.normalizedFactors_pow,normalize_eq,Multiset.count_replicate]
theorem FIB (v:HeightOneSpectrum R)
   (I:Ideal S) (hI:I≠⊥):
   (normalizedFactors (Ideal.relNorm R I)).count v.asIdeal=
     ∑ P∈primeFiber R S v,
       P.inertiaDeg R*(normalizedFactors I).count P:=by
 classical
 let C:Ideal S→Prop:=fun J↦J≠0∧
   (normalizedFactors (Ideal.relNorm R J)).count v.asIdeal=
     ∑ P∈primeFiber R S v,
       P.inertiaDeg R*(normalizedFactors J).count P
 have hC:C (normalizedFactors I).prod:=by
   refine Multiset.prod_induction C (normalizedFactors I) ?_ ?_ ?_
   · intro J K hJ hK
     change _∧_ at hJ hK ⊢
     refine ⟨mul_ne_zero hJ.1 hK.1,?_⟩
     have hNJ:Ideal.relNorm R J≠0:=by simpa using hJ.1
     have hNK:Ideal.relNorm R K≠0:=by simpa using hK.1
     rw [map_mul,normalizedFactors_mul hNJ hNK,Multiset.count_add,
       hJ.2,hK.2,normalizedFactors_mul hJ.1 hK.1]
     simp only [Multiset.count_add,mul_add,Finset.sum_add_distrib]
   · change _∧_
     exact ⟨one_ne_zero,by
       simp only [map_one,normalizedFactors_one,Multiset.count_zero,
         mul_zero,Finset.sum_const_zero]⟩
   · intro P hP
     have hPzero:P≠⊥:=ne_zero_of_mem_normalizedFactors hP
     have hPprime:P.IsPrime:=(Ideal.mem_normalizedFactors_iff hI).mp hP |>.1
     have hPirred:Irreducible P:=
       (Ideal.prime_of_isPrime hPzero hPprime).irreducible
     have hFactors:normalizedFactors P={P}:=by
       simpa using normalizedFactors_irreducible hPirred
     change _∧_
     refine ⟨hPzero,?_⟩
     rw [EKX R S v P hPzero hPprime,hFactors]
     by_cases hUnder:P.under R=v.asIdeal
     · letI:P.LiesOver v.asIdeal:=by rw [←hUnder];infer_instance
       have hMem:P∈primeFiber R S v:=
         (RCN356.mem_primeFiber_iff R S v P).mpr ⟨hPprime,inferInstance⟩
       simp [hUnder,Multiset.count_singleton,hMem]
     · have hNotMem:P∉primeFiber R S v:=by
         intro hMem
         letI:P.LiesOver v.asIdeal:=
           ((RCN356.mem_primeFiber_iff R S v P).mp hMem).2
         exact hUnder (Ideal.over_def P v.asIdeal).symm
       simp [hUnder,Multiset.count_singleton,hNotMem]
 have hCI:C I:=by
   rwa [Ideal.prod_normalizedFactors_eq_self hI] at hC
 exact hCI.2
theorem FGE (v:HeightOneSpectrum R) (x:S) (hx:x≠0):
   orderAt v (algebraMap R (FractionRing R) (Algebra.intNorm R S x))=
     ∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*
         orderAt (fiberPlace R S v P)
           (algebraMap S (FractionRing S) x):=by
 classical
 have hCount:=FIB R S v (Ideal.span {x}) (by simpa using hx)
 rw [Ideal.relNorm_singleton] at hCount
 have hTerms:
     (∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*
         orderAt (fiberPlace R S v P)
           (algebraMap S (FractionRing S) x))=
     ∑ P∈primeFiber R S v,
       (P.inertiaDeg R:ℤ)*((normalizedFactors (Ideal.span {x})).count P:ℤ):=by
   calc
     _=∑ P∈(primeFiber R S v).attach,
         (P.1.inertiaDeg R:ℤ)*
           ((normalizedFactors (Ideal.span {x})).count P.1:ℤ):=by
       apply Finset.sum_congr rfl
       intro P _
       rw [RCN356.orderAt_algebraMap _ x hx]
       rfl
     _=_:=Finset.sum_attach (primeFiber R S v)
       (fun P:Ideal S↦(P.inertiaDeg R:ℤ)*
         ((normalizedFactors (Ideal.span {x})).count P:ℤ))
 rw [hTerms,RCN356.orderAt_algebraMap v (Algebra.intNorm R S x) (by simpa using hx)]
 exact_mod_cast hCount
theorem FTM (v:HeightOneSpectrum R)
   (x:FractionRing S) (hx:x≠0):
   orderAt v (Algebra.norm (FractionRing R) x)=
     ∑ P∈(primeFiber R S v).attach,
       (P.1.inertiaDeg R:ℤ)*orderAt (fiberPlace R S v P) x:=by
 classical
 obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=S) x
 have hbzero:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have hazero:a≠0:=by
   intro ha
   apply hx
   simp [ha]
 have hNorm:
     Algebra.norm (FractionRing R)
         (algebraMap S (FractionRing S) a/algebraMap S (FractionRing S) b)=
       algebraMap R (FractionRing R) (Algebra.intNorm R S a)/
         algebraMap R (FractionRing R) (Algebra.intNorm R S b):=by
   simp [div_eq_mul_inv,Algebra.norm_inv,Algebra.algebraMap_intNorm_fractionRing]
 rw [hNorm,orderAt_div v _ _ (by simpa using hazero) (by simpa using hbzero),
   FGE R S v a hazero,FGE R S v b hbzero,
   ←Finset.sum_sub_distrib]
 apply Finset.sum_congr rfl
 intro P _
 rw [orderAt_div _ _ _ (by simpa using hazero) (by simpa using hbzero),mul_sub]
end FixedExtension
end
end RCN356
end SubmissionLower
end ProximityPrize
end PackedLegacy_G2
section PackedLegacy_W3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN357
open scoped BigOperators Classical
open IsDedekindDomain
noncomputable section
section TwoRings
variable (R S:Type*) [CommRing R] [CommRing S]
 [IsDedekindDomain R] [IsDedekindDomain S]
 [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
local instance:Algebra (FractionRing R) (FractionRing S):=
 FractionRing.liftAlgebra _ _
variable (F L:Type*) [Field F] [Field L]
 [Algebra R F] [IsFractionRing R F]
 [Algebra S L] [IsFractionRing S L]
 [Algebra F L] [Algebra R L]
 [IsScalarTower R F L] [IsScalarTower R S L]
variable [Algebra.IsSeparable F L]
theorem FFA (v:HeightOneSpectrum R) (x:L) (hx:x≠0):
   fieldOrder R F v (Algebra.norm F x)=
     ∑ P∈(IsDedekindDomain.primesOverFinset v.asIdeal S).attach,
       (P.1.inertiaDeg R:ℤ)*fieldOrder S L (placeAbove R S v P) x:=by
 letI:Algebra.IsSeparable (FractionRing R) (FractionRing S):=
   RCN357.canonical_separable R S F L
 have h:=RCN356.FTM R S v
   ((FractionRing.algEquiv S L).symm x) (by simpa using hx)
 calc
   fieldOrder R F v (Algebra.norm F x)=
       RCN356.orderAt v
         ((FractionRing.algEquiv R F).symm (Algebra.norm F x)):=
     RCN357.fieldOrder_transport R F v (Algebra.norm F x)
   _=∑ P∈(IsDedekindDomain.primesOverFinset v.asIdeal S).attach,
       (P.1.inertiaDeg R:ℤ)*RCN356.orderAt (placeAbove R S v P)
         ((FractionRing.algEquiv S L).symm x):=by
     simpa only [RCN357.norm_transport R S F L x,RCN356.primeFiber,
       RCN356.fiberPlace,placeAbove] using h
   _=_:=by
     apply Finset.sum_congr rfl
     intro P _
     congr 1
     exact (RCN357.fieldOrder_transport S L (placeAbove R S v P) x).symm
end TwoRings
end
end RCN357
end SubmissionLower
end ProximityPrize
end PackedLegacy_W3
section PackedLegacy_R5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN349
open scoped BigOperators Classical nonZeroDivisors
open IsDedekindDomain RCN357
noncomputable section
variable (K L:Type*) [Field K] [Field L]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev FC:=integralClosure (InfinityBase K) L
def ML:HeightOneSpectrum (InfinityBase K):=
 IsDiscreteValuationRing.maximalIdeal (InfinityBase K)
def AHQ (x:L):ℤ:=
 ∑ P∈(IsDedekindDomain.primesOverFinset
     (ML K).asIdeal (FC K L)).attach,
   (P.1.inertiaDeg (InfinityBase K):ℤ)*
     fieldOrder (FC K L) L
       (placeAbove (InfinityBase K) (FC K L) (ML K) P) x
theorem DFS (x:L) (hx:x≠0):
   AHQ K L x=
     RCN366.infinityOrder K (Algebra.norm (RatFunc K) x):=by
 have h:=FFA (InfinityBase K) (FC K L)
   (RatFunc K) L (ML K) x hx
 change-((ML K).valuation (RatFunc K)
     (Algebra.norm (RatFunc K) x)).log=AHQ K L x at h
 rw [ML,RCN353.infinity_valuation_eq] at h
 exact h.symm
theorem ESB (x:RatFunc K):
   RCN366.asFraction K x=
     (FractionRing.algEquiv (Polynomial K) (RatFunc K)).symm x:=by
 letI:Subsingleton
     ((RatFunc K)→ₐ[Polynomial K] FractionRing (Polynomial K)):=
   IsLocalization.algHom_subsingleton (nonZeroDivisors (Polynomial K))
 have h:=Subsingleton.elim
   (RatFunc.toFractionRingAlgEquiv K (Polynomial K)).toAlgHom
   (FractionRing.algEquiv (Polynomial K) (RatFunc K)).symm.toAlgHom
 exact DFunLike.congr_fun h x
theorem DSI
   (p:Polynomial K) (hp:Irreducible p) (x:RatFunc K):
   RCN366.finiteOrder K p hp x=
     fieldOrder (Polynomial K) (RatFunc K) (RCN366.primePlace K p hp) x:=by
 rw [RCN366.finiteOrder,ESB K]
 exact (RCN357.fieldOrder_transport (Polynomial K) (RatFunc K)
   (RCN366.primePlace K p hp) x).symm
theorem CRU
   (p:Polynomial K) (hp:Irreducible p) (x:L) (hx:x≠0):
   (∑ P∈(IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p hp).asIdeal (RCN349.FiniteNormalization K L)).attach,
     (P.1.inertiaDeg (Polynomial K):ℤ)*
       fieldOrder (RCN349.FiniteNormalization K L) L
         (placeAbove (Polynomial K) (RCN349.FiniteNormalization K L)
           (RCN366.primePlace K p hp) P) x)=
     RCN366.finiteOrder K p hp (Algebra.norm (RatFunc K) x):=by
 have h:=FFA (Polynomial K) (RCN349.FiniteNormalization K L) (RatFunc K) L
   (RCN366.primePlace K p hp) x hx
 rw [←DSI K p hp] at h
 exact h.symm
def ANO (s:Finset (Polynomial K))
   (hs:∀p∈s,Irreducible p∧p.Monic) (x:L):ℤ:=
 ∑ p∈s.attach,(p.1.natDegree:ℤ)*
   ∑ P∈(IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p.1 (hs p.1 p.2).1).asIdeal
       (RCN349.FiniteNormalization K L)).attach,
     (P.1.inertiaDeg (Polynomial K):ℤ)*
       fieldOrder (RCN349.FiniteNormalization K L) L
         (placeAbove (Polynomial K) (RCN349.FiniteNormalization K L)
           (RCN366.primePlace K p.1 (hs p.1 p.2).1) P) x
theorem DJS
   (s:Finset (Polynomial K)) (hs:∀p∈s,Irreducible p∧p.Monic)
   (x:L) (hx:x≠0):
   ANO K L s hs x=
     ∑ p∈s.attach,(p.1.natDegree:ℤ)*
       RCN366.finiteOrder K p.1 (hs p.1 p.2).1
         (Algebra.norm (RatFunc K) x):=by
 unfold ANO
 apply Finset.sum_congr rfl
 intro p _
 rw [CRU K L p.1 (hs p.1 p.2).1 x hx]
theorem FLK
   (s:Finset (Polynomial K)) (hs:∀p∈s,Irreducible p∧p.Monic)
   (x:L) (hx:x≠0)
   (hnum:(UniqueFactorizationMonoid.normalizedFactors
     (Algebra.norm (RatFunc K) x).num).toFinset ⊆ s)
   (hden:(UniqueFactorizationMonoid.normalizedFactors
     (Algebra.norm (RatFunc K) x).denom).toFinset ⊆ s):
   ANO K L s hs x+AHQ K L x=0:=by
 have hnorm:Algebra.norm (RatFunc K) x≠0:=Algebra.norm_ne_zero_iff.mpr hx
 rw [DJS K L s hs x hx,
   DFS K L x hx,
   RCN366.weighted_finite_order_sum K _ hnorm s hs hnum hden,
   RCN366.infinityOrder_eq_neg_intDegree K _ hnorm,
   add_neg_cancel]
theorem DWY (x:L) (hx:x≠0):
   Function.HasFiniteSupport
     (fun w:HeightOneSpectrum (RCN349.FiniteNormalization K L)↦
       fieldOrder (RCN349.FiniteNormalization K L) L w x):=by
 obtain ⟨a,b,hb,rfl⟩:=
   IsFractionRing.div_surjective (A:=RCN349.FiniteNormalization K L) x
 have hbzero:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have hazero:a≠0:=by
   intro ha
   apply hx
   simp [ha]
 have hspanA:(Ideal.span {a}:Ideal (RCN349.FiniteNormalization K L))≠0:=by
   simpa using hazero
 have hspanB:(Ideal.span {b}:Ideal (RCN349.FiniteNormalization K L))≠0:=by
   simpa using hbzero
 have hA:{w:HeightOneSpectrum (RCN349.FiniteNormalization K L) |
     w.asIdeal∣Ideal.span {a}}.Finite:=Ideal.finite_factors hspanA
 have hB:{w:HeightOneSpectrum (RCN349.FiniteNormalization K L) |
     w.asIdeal∣Ideal.span {b}}.Finite:=Ideal.finite_factors hspanB
 apply (hA.union hB).subset
 intro w hw
 by_contra hout
 have hn:=not_or.mp hout
 have hna:a∉w.asIdeal:=fun ha↦hn.1 (Ideal.dvd_span_singleton.mpr ha)
 have hnb:b∉w.asIdeal:=fun hb↦hn.2 (Ideal.dvd_span_singleton.mpr hb)
 have hva:w.intValuation a=1:=
   (HeightOneSpectrum.intValuation_eq_one_iff (v:=w)).mpr hna
 have hvb:w.intValuation b=1:=
   (HeightOneSpectrum.intValuation_eq_one_iff (v:=w)).mpr hnb
 apply hw
 simp only [fieldOrder,map_div₀,HeightOneSpectrum.valuation_of_algebraMap,
   hva,hvb,div_self one_ne_zero,WithZero.log_one,neg_zero]
def DNP (x:L) (hx:x≠0):
   Finset (HeightOneSpectrum (RCN349.FiniteNormalization K L)):=
 (DWY K L x hx).toFinset
theorem EVV (x:L) (hx:x≠0)
   (w:HeightOneSpectrum (RCN349.FiniteNormalization K L)):
   w∈DNP K L x hx ↔
     fieldOrder (RCN349.FiniteNormalization K L) L w x≠0:=by
 unfold DNP
 exact Set.Finite.mem_toFinset _
def BNT (w:HeightOneSpectrum (RCN349.FiniteNormalization K L)):Polynomial K:=
 (RCN366.exists_monic_primePlace K
   (HeightOneSpectrum.under (Polynomial K) w)).choose
theorem DKI (w:HeightOneSpectrum (RCN349.FiniteNormalization K L)):
   ∃hp:Irreducible (BNT K L w),
     (BNT K L w).Monic∧
       RCN366.primePlace K (BNT K L w) hp=
         HeightOneSpectrum.under (Polynomial K) w:=
 (RCN366.exists_monic_primePlace K
   (HeightOneSpectrum.under (Polynomial K) w)).choose_spec
def DEX (x:L) (hx:x≠0):Finset (Polynomial K):=
 (DNP K L x hx).image (BNT K L) ∪
   RCN366.factorSupport K (Algebra.norm (RatFunc K) x)
theorem BRS (x:L) (hx:x≠0)
   (p:Polynomial K) (hp:p∈DEX K L x hx):Irreducible p∧p.Monic:=by
 rcases Finset.mem_union.mp hp with hleft | hright
 · obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hleft
   obtain ⟨hp,hm,_⟩:=DKI K L w
   exact ⟨hp,hm⟩
 · exact RCN366.factorSupport_primes K _
     (Algebra.norm_ne_zero_iff.mpr hx) p hright
theorem FET (x:L) (hx:x≠0)
   (w:HeightOneSpectrum (RCN349.FiniteNormalization K L))
   (hw:fieldOrder (RCN349.FiniteNormalization K L) L w x≠0):
   ∃p∈DEX K L x hx,∃hp:Irreducible p,
     w.asIdeal∈IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K p hp).asIdeal (RCN349.FiniteNormalization K L):=by
 obtain ⟨hp,hm,hplace⟩:=DKI K L w
 refine ⟨BNT K L w,
   Finset.mem_union_left _ (Finset.mem_image.mpr
     ⟨w,(EVV K L x hx w).mpr hw,rfl⟩),hp,?_⟩
 rw [hplace]
 letI:w.asIdeal.LiesOver (HeightOneSpectrum.under (Polynomial K) w).asIdeal:=by
   change w.asIdeal.LiesOver (w.asIdeal.under (Polynomial K))
   infer_instance
 exact (IsDedekindDomain.mem_primesOverFinset_iff
   (HeightOneSpectrum.under (Polynomial K) w).ne_bot (RCN349.FiniteNormalization K L)).mpr
     ⟨w.isPrime,inferInstance⟩
theorem EGT (x:L) (hx:x≠0):
   ANO K L (DEX K L x hx)
     (BRS K L x hx) x+AHQ K L x=0:=by
 apply FLK K L (DEX K L x hx)
   (BRS K L x hx) x hx
 · intro p hp
   exact Finset.mem_union_right _ (Finset.mem_union_left _ hp)
 · intro p hp
   exact Finset.mem_union_right _ (Finset.mem_union_right _ hp)
end
end RCN349
end SubmissionLower
end ProximityPrize
end PackedLegacy_R5
section PackedLegacy_R1
namespace ProximityPrize
namespace SubmissionLower
namespace RCN345
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L]
 [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
abbrev ET:=RCN349.FiniteNormalization K L
abbrev InfinityBase_p19:=RCN349.InfinityBase K
local instance:IsFractionRing (InfinityBase_p19 K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase_p19 K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase_p19 K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase_p19 K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev FC:=RCN349.FC K L
def parameter_p19:L:=algebraMap (Polynomial K) L Polynomial.X
theorem FEN:
   parameter_p19 K L=algebraMap (RatFunc K) L (RatFunc.X:RatFunc K):=by
 change algebraMap (Polynomial K) L Polynomial.X=
   algebraMap (RatFunc K) L (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 exact IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L Polynomial.X
theorem GIS (f:Polynomial K):
   Polynomial.aeval (parameter_p19 K L) f=algebraMap (Polynomial K) L f:=by
 rw [parameter_p19,Polynomial.aeval_algebraMap_apply,Polynomial.aeval_X_left_apply]
theorem EYM (c:K):
   algebraMap (Polynomial K) L (Polynomial.C c)=algebraMap K L c:=
 (IsScalarTower.algebraMap_apply K (Polynomial K) L c).symm
section GivenValuation
variable (v:Valuation L ℤᵐ⁰) [htriv:v.IsTrivialOn K]
theorem FLO (c:K):v (algebraMap K L c)≤1:=by
 by_cases hc:c=0
 · simp [hc]
 · rw [htriv.eq_one c hc]
theorem _Q25 (ht:v (parameter_p19 K L)≤1) (f:Polynomial K):
   v (algebraMap (Polynomial K) L f)≤1:=by
 induction f using Polynomial.induction_on' with
 | add f g hf hg=>
     rw [map_add]
     exact (v.map_add _ _).trans (max_le hf hg)
 | monomial n c=>
     rw [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
       map_mul,map_pow,EYM]
     exact mul_le_one₀ (FLO K L v c) zero_le
       (pow_le_one₀ zero_le ht)
theorem EGG (ht:v (parameter_p19 K L)≤1)
   (s:ET K L):
   v (algebraMap (ET K L) L s)≤1:=by
 exact RCN359.integral_le_one (Polynomial K) L v
   (_Q25 K L v ht) s.property
theorem AZR (ht:1<v (parameter_p19 K L))
   (f:Polynomial K) (hf:f≠0):
   v (algebraMap (Polynomial K) L f)=v (parameter_p19 K L)^f.natDegree:=by
 rw [←GIS K L f]
 exact Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
   (v:=v) (parameter_p19 K L) ht hf
theorem FJL (ht:1<v (parameter_p19 K L)) (r:InfinityBase_p19 K):
   v (algebraMap (InfinityBase_p19 K) L r)≤1:=by
 change v (algebraMap (RatFunc K) L r.val)≤1
 by_cases hr:r.val=0
 · simp [hr]
 have hdegree:r.val.num.natDegree≤r.val.denom.natDegree:=by
   have hmem:RatFunc.inftyValuation K r.val≤1:=r.property
   rw [RatFunc.inftyValuation_apply,RatFunc.inftyValuation_of_nonzero K hr,
     ←WithZero.exp_zero,WithZero.exp_le_exp] at hmem
   dsimp [RatFunc.intDegree] at hmem
   omega
 have hnum:=AZR K L v ht
   r.val.num (RatFunc.num_ne_zero hr)
 have hden:=AZR K L v ht
   r.val.denom r.val.denom_ne_zero
 rw [←RatFunc.num_div_denom r.val,map_div₀,map_div₀,
   ←IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
   ←IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
   hnum,hden]
 apply (div_le_one₀ (pow_pos (zero_lt_one.trans ht) _)).mpr
 exact pow_le_pow_right₀ ht.le hdegree
theorem DXB (ht:1<v (parameter_p19 K L))
   (s:FC K L):
   v (algebraMap (FC K L) L s)≤1:=by
 exact RCN359.integral_le_one (InfinityBase_p19 K) L v
   (FJL K L v ht) s.property
theorem EGL (hv:Function.Surjective v)
   (ht:v (parameter_p19 K L)≤1):
   ∃! p:HeightOneSpectrum (ET K L),v=p.valuation L:=
 RCN359.exists_unique_place (ET K L) L v
   (EGG K L v ht) hv
theorem CAT (hv:Function.Surjective v)
   (ht:1<v (parameter_p19 K L)):
   ∃! q:HeightOneSpectrum (FC K L),v=q.valuation L:=
 RCN359.exists_unique_place (FC K L) L v
   (DXB K L v ht) hv
theorem EPK (hv:Function.Surjective v):
   (∃p:HeightOneSpectrum (ET K L),v=p.valuation L)∨
   (∃q:HeightOneSpectrum (FC K L),v=q.valuation L):=by
 by_cases ht:v (parameter_p19 K L)≤1
 · exact Or.inl (EGL K L v hv ht).exists
 · exact Or.inr (CAT K L v hv (lt_of_not_ge ht)).exists
end GivenValuation
theorem AHI
   (q:HeightOneSpectrum (FC K L)):
   q.asIdeal.LiesOver (RCN349.ML K).asIdeal:=by
 have hbase:HeightOneSpectrum.under (InfinityBase_p19 K) q=
     RCN349.ML K:=by
   apply HeightOneSpectrum.ext
   exact IsLocalRing.eq_maximalIdeal
     ((HeightOneSpectrum.under (InfinityBase_p19 K) q).isPrime.isMaximal
       (HeightOneSpectrum.under (InfinityBase_p19 K) q).ne_bot)
 have hq:q.asIdeal.LiesOver
     (HeightOneSpectrum.under (InfinityBase_p19 K) q).asIdeal:=by
   change q.asIdeal.LiesOver (q.asIdeal.under (InfinityBase_p19 K))
   infer_instance
 rwa [hbase] at hq
theorem CAY
   (p:HeightOneSpectrum (ET K L)):
   p.valuation L (parameter_p19 K L)≤1:=by
 rw [parameter_p19,IsScalarTower.algebraMap_apply (Polynomial K) (ET K L) L]
 exact p.valuation_le_one _
theorem BVZ
   (q:HeightOneSpectrum (FC K L)):
   q.valuation L (parameter_p19 K L)=
     WithZero.exp ((RCN349.ML K).asIdeal.ramificationIdx'
       q.asIdeal:ℤ):=by
 letI:=AHI K L q
 have h:=HeightOneSpectrum.valuation_liesOver (K:=RatFunc K) L
   (RCN349.ML K) q (RatFunc.X:RatFunc K)
 rw [RCN349.ML,RCN353.infinity_valuation_eq,
   RatFunc.inftyValuation.X] at h
 rw [FEN]
 simpa [RCN349.ML] using h.symm
theorem BQZ
   (q:HeightOneSpectrum (FC K L)):
   1<q.valuation L (parameter_p19 K L):=by
 letI:=AHI K L q
 rw [BVZ,←WithZero.exp_zero,WithZero.exp_lt_exp]
 exact_mod_cast Nat.pos_iff_ne_zero.mpr
   (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal
     (RCN349.ML K).ne_bot)
theorem FJC
   (p:HeightOneSpectrum (ET K L)):
   (p.valuation L).IsTrivialOn K:=by
 constructor
 intro c hc
 let cS:ET K L:=
   algebraMap (Polynomial K) (ET K L) (Polynomial.C c)
 have hunit:IsUnit cS:=
   ((isUnit_iff_ne_zero.mpr hc).map Polynomial.C).map
     (algebraMap (Polynomial K) (ET K L))
 have hval:p.valuation L (algebraMap (ET K L) L cS)=1:=
   Valuation.Integers.one_of_isUnit' hunit (p.valuation_le_one (K:=L))
 change p.valuation L (algebraMap (ET K L) L
   (algebraMap (Polynomial K) (ET K L) (Polynomial.C c)))=1 at hval
 rw [←IsScalarTower.algebraMap_apply (Polynomial K) (ET K L) L,
   EYM] at hval
 exact hval
theorem FAT
   (q:HeightOneSpectrum (FC K L)):
   (q.valuation L).IsTrivialOn K:=by
 constructor
 intro c hc
 letI:=AHI K L q
 have h:=HeightOneSpectrum.valuation_liesOver (K:=RatFunc K) L
   (RCN349.ML K) q (algebraMap K (RatFunc K) c)
 rw [RCN349.ML,RCN353.infinity_valuation_eq] at h
 have hC:RatFunc.inftyValuation K (algebraMap K (RatFunc K) c)=1:=
   RatFunc.inftyValuation.C K hc
 rw [hC,one_pow,←IsScalarTower.algebraMap_apply K (RatFunc K) L] at h
 exact h.symm
abbrev ChartPlace_p19:=
 Sum (HeightOneSpectrum (ET K L))
   (HeightOneSpectrum (FC K L))
def DZH:ChartPlace_p19 K L→Valuation L ℤᵐ⁰:=
 Sum.elim (fun p↦p.valuation L) (fun q↦q.valuation L)
theorem EKG (p:ChartPlace_p19 K L):
   Function.Surjective (DZH K L p):=by
 rcases p with p | q
 · exact p.valuation_surjective L
 · exact q.valuation_surjective L
theorem EWQ (p:ChartPlace_p19 K L):
   (DZH K L p).IsTrivialOn K:=by
 rcases p with p | q
 · exact FJC K L p
 · exact FAT K L q
theorem ENI:Function.Injective (DZH K L):=by
 intro p q h
 rcases p with p | p<;>rcases q with q | q
 · congr 1
   exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
     (K:=L) (Valuation.IsEquiv.of_eq h)
 · have hp:=CAY K L p
   have hq:=BQZ K L q
   change p.valuation L=q.valuation L at h
   rw [h] at hp
   exact False.elim (not_lt_of_ge hp hq)
 · have hp:=BQZ K L p
   have hq:=CAY K L q
   change p.valuation L=q.valuation L at h
   rw [h] at hp
   exact False.elim (not_lt_of_ge hq hp)
 · congr 1
   exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
     (K:=L) (Valuation.IsEquiv.of_eq h)
def ACR:=
 {v:Valuation L ℤᵐ⁰//Function.Surjective v∧v.IsTrivialOn K}
def chartMap_p19 (p:ChartPlace_p19 K L):ACR K L:=
 ⟨DZH K L p,EKG K L p,EWQ K L p⟩
theorem CMN:Function.Bijective (chartMap_p19 K L):=by
 constructor
 · intro p q h
   exact ENI K L (congrArg Subtype.val h)
 · intro v
   letI:v.val.IsTrivialOn K:=v.property.2
   rcases EPK K L v.val v.property.1 with ⟨p,hp⟩ | ⟨q,hq⟩
   · refine ⟨Sum.inl p,?_⟩
     apply Subtype.ext
     exact hp.symm
   · refine ⟨Sum.inr q,?_⟩
     apply Subtype.ext
     exact hq.symm
end
end RCN345
end SubmissionLower
end ProximityPrize
end PackedLegacy_R1
section PackedLegacy_W4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN358
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev InfinityBase_p19:=RCN349.InfinityBase K
local instance:Algebra K (InfinityBase_p19 K):=
 (RCN352.constantMap K).toAlgebra
def ERZ:InfinityBase_p19 K→ₐ[K] K where
 toRingHom:=(RCN352.residueEquiv K).symm.toRingHom.comp
   (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase_p19 K)))
 commutes' c:=by
   change (RCN352.residueEquiv K).symm
     (RCN352.residueConstant K c)=c
   rw [←RCN352.residueEquiv_apply,RingEquiv.symm_apply_apply]
theorem EOD:
   RingHom.ker (ERZ K).toRingHom=
     (RCN349.ML K).asIdeal:=by
 ext r
 change (RCN352.residueEquiv K).symm
     (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase_p19 K)) r)=0 ↔
   r∈IsLocalRing.maximalIdeal (InfinityBase_p19 K)
 constructor
 · intro h
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   apply (RCN352.residueEquiv K).symm.injective
   simpa only [map_zero] using h
 · intro h
   rw [Ideal.Quotient.eq_zero_iff_mem.mpr h,map_zero]
variable [IsAlgClosed K]
theorem EBO (f:Polynomial K) (hf:Irreducible f):
   f.natDegree=1:=
 Polynomial.natDegree_eq_of_degree_eq_some
   (IsAlgClosed.degree_eq_one_of_irreducible K hf)
theorem ERL (p:HeightOneSpectrum (Polynomial K)):
   ∃phi:Polynomial K→ₐ[K] K,RingHom.ker phi.toRingHom=p.asIdeal:=by
 obtain ⟨f,hf,hm,hplace⟩:=RCN366.exists_monic_primePlace K p
 obtain ⟨alpha,hroot⟩:=IsAlgClosed.exists_root f (by
   rw [IsAlgClosed.degree_eq_one_of_irreducible K hf]
   exact one_ne_zero)
 let phi:Polynomial K→ₐ[K] K:=Polynomial.aeval alpha
 have hkermax:(RingHom.ker phi.toRingHom).IsMaximal:=
   RCN354.pointKernel_isMaximal phi
 have hle:p.asIdeal≤RingHom.ker phi.toRingHom:=by
   rw [←hplace]
   change Ideal.span {f}≤RingHom.ker phi.toRingHom
   apply (Ideal.span_singleton_le_iff_mem (I:=RingHom.ker phi.toRingHom)).mpr
   change f.eval alpha=0
   exact hroot
 refine ⟨phi,?_⟩
 exact ((p.isPrime.isMaximal p.ne_bot).eq_of_le hkermax.ne_top hle).symm
variable (L:Type*) [Field L]
 [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
abbrev ET:=RCN349.FiniteNormalization K L
local instance:IsFractionRing (InfinityBase_p19 K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase_p19 K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase_p19 K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase_p19 K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev FC:=RCN349.FC K L
theorem ERU
   (q:HeightOneSpectrum (ET K L)):
   q.asIdeal.inertiaDeg (Polynomial K)=1:=by
 letI:Algebra K (ET K L):=
   ((algebraMap (Polynomial K) (ET K L)).comp Polynomial.C).toAlgebra
 letI:IsScalarTower K (Polynomial K) (ET K L):=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 obtain ⟨phi,hphi⟩:=ERL K
   (HeightOneSpectrum.under (Polynomial K) q)
 apply RCN373.inertiaDeg_eq_one_of_point_fiber phi q.asIdeal
 exact hphi.symm
theorem CUU
   (q:HeightOneSpectrum (FC K L)):
   q.asIdeal.inertiaDeg (InfinityBase_p19 K)=1:=by
 letI:Algebra K (FC K L):=
   ((algebraMap (InfinityBase_p19 K) (FC K L)).comp
     (algebraMap K (InfinityBase_p19 K))).toAlgebra
 letI:IsScalarTower K (InfinityBase_p19 K) (FC K L):=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 letI:=RCN345.AHI K L q
 apply RCN373.inertiaDeg_eq_one_of_point_fiber
   (ERZ K) q.asIdeal
 rw [EOD]
 exact (Ideal.over_def q.asIdeal (RCN349.ML K).asIdeal).symm
theorem infinitePlace_inertia'_one_p19
   (q:HeightOneSpectrum (FC K L)):
   (RCN349.ML K).asIdeal.inertiaDeg' q.asIdeal=1:=by
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 letI:=RCN345.AHI K L q
 rw [Ideal.inertiaDeg'_eq_inertiaDeg]
 exact CUU K L q
theorem EPI
   (Q:{Q:Ideal (FC K L)//
     Q∈IsDedekindDomain.primesOverFinset
       (RCN349.ML K).asIdeal (FC K L)}):
   (Q.1.inertiaDeg (InfinityBase_p19 K):ℤ)=1:=by
 have hQ:=CUU K L
   (RCN357.placeAbove (InfinityBase_p19 K) (FC K L)
     (RCN349.ML K) Q)
 exact_mod_cast hQ
end
end RCN358
end SubmissionLower
end ProximityPrize
end PackedLegacy_W4
section PackedLegacy_R2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN346
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place_p19:=RCN345.ACR K L
def poleOrder_p19 (v:Place_p19 K L) (x:L):ℤ:=
 RCN187.poleOrder v.val x
theorem GDA (v:Place_p19 K L) (x:L):0≤poleOrder_p19 K L v x:=
 le_max_left _ _
theorem _Q11 (v:Place_p19 K L) (x:L) (h:v.val x≤1):
   poleOrder_p19 K L v x=0:=by
 change max 0 (v.val x).log=0
 rw [←RCN187.log_max_one,max_eq_left h,WithZero.log_one]
variable [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place_p19 K L):=Classical.decEq _
abbrev InfinityBase_p19:=RCN349.InfinityBase K
local instance:IsFractionRing (InfinityBase_p19 K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase_p19 K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase_p19 K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase_p19 K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev FC:=RCN349.FC K L
def AOV:Finset (Ideal (FC K L)):=
 IsDedekindDomain.primesOverFinset (RCN349.ML K).asIdeal
   (FC K L)
def ML
   (Q:{Q:Ideal (FC K L)//Q∈AOV K L}):
   HeightOneSpectrum (FC K L):=
 RCN357.placeAbove (InfinityBase_p19 K) (FC K L)
   (RCN349.ML K) Q
def BTM
   (Q:{Q:Ideal (FC K L)//Q∈AOV K L}):
   Place_p19 K L:=
 RCN345.chartMap_p19 K L (Sum.inr (ML K L Q))
theorem ECI:Function.Injective (BTM K L):=by
 intro P Q h
 apply Subtype.ext
 have hc:=(RCN345.CMN K L).1 h
 have hp:=Sum.inr.inj hc
 exact congrArg (fun p:HeightOneSpectrum (FC K L)↦p.asIdeal) hp
theorem DSX
   (Q:{Q:Ideal (FC K L)//Q∈AOV K L}):
   poleOrder_p19 K L (BTM K L Q) (RCN345.parameter_p19 K L)=
     ((RCN349.ML K).asIdeal.ramificationIdx' Q.1:ℤ):=by
 change max 0 (((ML K L Q).valuation L)
   (RCN345.parameter_p19 K L)).log=_
 rw [RCN345.BVZ,
   WithZero.log_exp,max_eq_right (Int.natCast_nonneg _)]
 rfl
theorem CSP:
   (∑ Q∈(AOV K L).attach,
     (RCN349.ML K).asIdeal.ramificationIdx' Q.1)=
     Module.finrank (RatFunc K) L:=by
 have h:=Ideal.sum_ramification_inertia (FC K L) (RatFunc K) L
   (RCN349.ML K).ne_bot
 calc
   (∑ Q∈(AOV K L).attach,
       (RCN349.ML K).asIdeal.ramificationIdx' Q.1)=
     ∑ Q∈AOV K L,
       (RCN349.ML K).asIdeal.ramificationIdx' Q*
         (RCN349.ML K).asIdeal.inertiaDeg' Q:=by
     rw [←Finset.sum_attach (AOV K L)
       (fun Q:Ideal (FC K L)↦
         (RCN349.ML K).asIdeal.ramificationIdx' Q*
           (RCN349.ML K).asIdeal.inertiaDeg' Q)]
     apply Finset.sum_congr rfl
     intro Q _
     have hf:=RCN358.infinitePlace_inertia'_one_p19 K L (ML K L Q)
     change (RCN349.ML K).asIdeal.inertiaDeg' Q.1=1 at hf
     rw [hf,mul_one]
   _=Module.finrank (RatFunc K) L:=h
theorem DRH:
   (∑ Q∈(AOV K L).attach,
     poleOrder_p19 K L (BTM K L Q) (RCN345.parameter_p19 K L))=
     (Module.finrank (RatFunc K) L:ℤ):=by
 simp_rw [DSX]
 exact_mod_cast CSP K L
def CRE:Finset (Place_p19 K L):=
 (AOV K L).attach.image (BTM K L)
theorem CTR:
   (∑ v∈CRE K L,
     poleOrder_p19 K L v (RCN345.parameter_p19 K L))=
     (Module.finrank (RatFunc K) L:ℤ):=by
 rw [CRE,Finset.sum_image (fun _ _ _ _ h↦ECI K L h)]
 exact DRH K L
theorem CNV (v:Place_p19 K L)
   (hv:v∉CRE K L):
   poleOrder_p19 K L v (RCN345.parameter_p19 K L)=0:=by
 by_contra hnonzero
 have ht:1<v.val (RCN345.parameter_p19 K L):=
   lt_of_not_ge fun hle↦hnonzero (_Q11 K L v _ hle)
 letI:v.val.IsTrivialOn K:=v.property.2
 obtain ⟨q,hq,_⟩:=
   RCN345.CAT K L v.val v.property.1 ht
 have hmem:q.asIdeal∈AOV K L:=
   (IsDedekindDomain.mem_primesOverFinset_iff
     (RCN349.ML K).ne_bot (FC K L)).mpr
     ⟨q.isPrime,RCN345.AHI K L q⟩
 let Q:{Q:Ideal (FC K L)//Q∈AOV K L}:=⟨q.asIdeal,hmem⟩
 have hplace:ML K L Q=q:=by
   apply HeightOneSpectrum.ext
   rfl
 have hvmap:BTM K L Q=v:=by
   apply Subtype.ext
   change (ML K L Q).valuation L=v.val
   rw [hplace]
   exact hq.symm
 apply hv
 rw [←hvmap]
 exact Finset.mem_image.mpr ⟨Q,Finset.mem_attach _ Q,rfl⟩
theorem EGM (W:Finset (Place_p19 K L)):
   (∑ v∈W,poleOrder_p19 K L v (RCN345.parameter_p19 K L))≤
     (Module.finrank (RatFunc K) L:ℤ):=by
 have htrim:
     (∑ v∈W,poleOrder_p19 K L v (RCN345.parameter_p19 K L))=
     ∑ v∈W ∩ CRE K L,
       poleOrder_p19 K L v (RCN345.parameter_p19 K L):=by
   symm
   apply Finset.sum_subset Finset.inter_subset_left
   intro v hvW hvnot
   apply CNV K L v
   intro hvI
   exact hvnot (Finset.mem_inter.mpr ⟨hvW,hvI⟩)
 calc
   _=∑ v∈W ∩ CRE K L,
       poleOrder_p19 K L v (RCN345.parameter_p19 K L):=htrim
   _≤ ∑ v∈CRE K L,
       poleOrder_p19 K L v (RCN345.parameter_p19 K L):=by
     apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
     intro v _ _
     exact GDA K L v _
   _=(Module.finrank (RatFunc K) L:ℤ):=CTR K L
end
end RCN346
end SubmissionLower
end ProximityPrize
end PackedLegacy_R2
section PackedLegacy_DG
namespace ProximityPrize
namespace SubmissionLower
namespace RCN026
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place_p19:=RCN345.ACR K L
def order_p19 (v:Place_p19 K L) (x:L):ℤ:= -(v.val x).log
def zeroOrder_p19 (v:Place_p19 K L) (x:L):ℤ:=max 0 (order_p19 K L v x)
theorem AUU (v:Place_p19 K L) (x:L):0≤zeroOrder_p19 K L v x:=
 le_max_left _ _
theorem EQG (v:Place_p19 K L) (x:L):
   zeroOrder_p19 K L v x-RCN346.poleOrder_p19 K L v x=order_p19 K L v x:=by
 unfold zeroOrder_p19 order_p19 RCN346.poleOrder_p19 RCN187.poleOrder
 omega
variable [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place_p19 K L):=Classical.decEq _
abbrev ET:=RCN349.FiniteNormalization K L
abbrev InfinityBase:=RCN349.InfinityBase K
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev FC:=RCN349.FC K L
variable (s:Finset (Polynomial K)) (hs:∀p∈s,Irreducible p∧p.Monic)
def finiteFiber_p19 (p:{p:Polynomial K//p∈s}):
   Finset (Ideal (ET K L)):=
 IsDedekindDomain.primesOverFinset
   (RCN366.primePlace K p.1 (hs p.1 p.2).1).asIdeal
   (ET K L)
abbrev FiniteIndex_p19:=
 Σ p:{p:Polynomial K//p∈s},
   {Q:Ideal (ET K L)//Q∈finiteFiber_p19 K L s hs p}
def finitePlace_p19 (i:FiniteIndex_p19 K L s hs):
   HeightOneSpectrum (ET K L):=
 RCN357.placeAbove (Polynomial K) (ET K L)
   (RCN366.primePlace K i.1.1 (hs i.1.1 i.1.2).1) i.2
theorem FDB:Function.Injective (finitePlace_p19 K L s hs):=by
 rintro ⟨p,P⟩ ⟨q,Q⟩ h
 have hI:P.1=Q.1:=congrArg HeightOneSpectrum.asIdeal h
 let pbase:=RCN366.primePlace K p.1 (hs p.1 p.2).1
 let qbase:=RCN366.primePlace K q.1 (hs q.1 q.2).1
 letI:P.1.LiesOver pbase.asIdeal:=
   ((IsDedekindDomain.mem_primesOverFinset_iff pbase.ne_bot
     (ET K L)).mp P.2).2
 letI:Q.1.LiesOver qbase.asIdeal:=
   ((IsDedekindDomain.mem_primesOverFinset_iff qbase.ne_bot
     (ET K L)).mp Q.2).2
 have hbase:pbase=qbase:=by
   apply HeightOneSpectrum.ext
   calc
     pbase.asIdeal=P.1.under (Polynomial K):=Ideal.over_def P.1 pbase.asIdeal
     _=Q.1.under (Polynomial K):=congrArg (Ideal.under (Polynomial K)) hI
     _=qbase.asIdeal:=(Ideal.over_def Q.1 qbase.asIdeal).symm
 have hpq:p=q:=Subtype.ext<|
   RCN366.primePlace_injective K p.1 q.1
     (hs p.1 p.2).1 (hs q.1 q.2).1 (hs p.1 p.2).2 (hs q.1 q.2).2 hbase
 subst q
 have hPQ:P=Q:=Subtype.ext hI
 cases hPQ
 rfl
abbrev EJR:=
 {Q:Ideal (FC K L)//Q∈RCN346.AOV K L}
abbrev FamilyIndex_p19:=FiniteIndex_p19 K L s hs ⊕ EJR K L
def familyChart_p19:FamilyIndex_p19 K L s hs→RCN345.ChartPlace_p19 K L:=
 Sum.elim (fun i↦Sum.inl (finitePlace_p19 K L s hs i))
   (fun Q↦Sum.inr (RCN346.ML K L Q))
def CTJ (i:FamilyIndex_p19 K L s hs):Place_p19 K L:=
 RCN345.chartMap_p19 K L (familyChart_p19 K L s hs i)
theorem EIL:Function.Injective (CTJ K L s hs):=by
 intro i j h
 have hc:=(RCN345.CMN K L).1 h
 cases i with
 | inl i=>
   cases j with
   | inl j=>
     exact congrArg Sum.inl (FDB K L s hs (Sum.inl.inj hc))
   | inr j=>cases hc
 | inr i=>
   cases j with
   | inl j=>cases hc
   | inr j=>
     have hI:i.1=j.1:=congrArg HeightOneSpectrum.asIdeal (Sum.inr.inj hc)
     exact congrArg Sum.inr (Subtype.ext hI)
theorem EJU (x:L):
   RCN349.ANO K L s hs x=
     ∑ i:FiniteIndex_p19 K L s hs,
       RCN357.fieldOrder (ET K L) L
         (finitePlace_p19 K L s hs i) x:=by
 rw [Fintype.sum_sigma]
 unfold RCN349.ANO
 simp only [Finset.attach_eq_univ]
 apply Finset.sum_congr rfl
 intro p _
 rw [RCN358.EBO K p.1 (hs p.1 p.2).1]
 simp only [Nat.cast_one,one_mul]
 apply Finset.sum_congr rfl
 intro Q _
 have hweight:=RCN358.ERU K L
   (finitePlace_p19 K L s hs ⟨p,Q⟩)
 change Q.1.inertiaDeg (Polynomial K)=1 at hweight
 rw [hweight]
 simp only [Nat.cast_one,one_mul]
 rfl
theorem EBM (x:L):
   RCN349.AHQ K L x=
     ∑ Q:EJR K L,
       RCN357.fieldOrder (FC K L) L
         (RCN346.ML K L Q) x:=by
 unfold RCN349.AHQ
 simp only [Finset.attach_eq_univ]
 apply Finset.sum_congr rfl
 intro Q _
 rw [RCN358.EPI K L Q,one_mul]
 rfl
theorem DGL (x:L):
   (∑ i:FamilyIndex_p19 K L s hs,order_p19 K L (CTJ K L s hs i) x)=
     RCN349.ANO K L s hs x+
       RCN349.AHQ K L x:=by
 rw [Fintype.sum_sum_type]
 change
   (∑ i:FiniteIndex_p19 K L s hs,
     RCN357.fieldOrder (ET K L) L
       (finitePlace_p19 K L s hs i) x)+
   (∑ Q:EJR K L,
     RCN357.fieldOrder (FC K L) L
       (RCN346.ML K L Q) x)=_
 rw [←EJU K L s hs x,←EBM K L x]
def familyValues_p19:Finset (Place_p19 K L):=
 Finset.univ.image (CTJ K L s hs)
theorem CCO (x:L):
   (∑ v∈familyValues_p19 K L s hs,order_p19 K L v x)=
     RCN349.ANO K L s hs x+
       RCN349.AHQ K L x:=by
 rw [familyValues_p19,Finset.sum_image
   (fun _ _ _ _ h↦EIL K L s hs h)]
 exact DGL K L s hs x
variable {s hs}
def placesFor_p19 (x:L) (hx:x≠0):Finset (Place_p19 K L):=
 familyValues_p19 K L (RCN349.DEX K L x hx)
   (RCN349.BRS K L x hx)
theorem DAL (x:L) (hx:x≠0):
   (∑ v∈placesFor_p19 K L x hx,order_p19 K L v x)=0:=by
 rw [placesFor_p19,CCO]
 exact RCN349.EGT K L x hx
theorem ALB (x:L) (hx:x≠0) (v:Place_p19 K L)
   (hv:order_p19 K L v x≠0):v∈placesFor_p19 K L x hx:=by
 obtain ⟨c,rfl⟩:=(RCN345.CMN K L).2 v
 let s:=RCN349.DEX K L x hx
 let hs:=RCN349.BRS K L x hx
 change RCN345.chartMap_p19 K L c∈familyValues_p19 K L s hs
 rcases c with q | q
 · have hq:RCN357.fieldOrder (ET K L) L q x≠0:=hv
   obtain ⟨p,hp,hirred,hQ⟩:=RCN349.FET K L x hx q hq
   let pindex:{p:Polynomial K//p∈s}:=⟨p,hp⟩
   let Q:{Q:Ideal (ET K L)//Q∈finiteFiber_p19 K L s hs pindex}:=
     ⟨q.asIdeal,hQ⟩
   let i:FamilyIndex_p19 K L s hs:=Sum.inl ⟨pindex,Q⟩
   have heq:CTJ K L s hs i=
       RCN345.chartMap_p19 K L (Sum.inl q):=by
     have hplace:finitePlace_p19 K L s hs ⟨pindex,Q⟩=q:=by
       apply HeightOneSpectrum.ext
       rfl
     change RCN345.chartMap_p19 K L
       (Sum.inl (finitePlace_p19 K L s hs ⟨pindex,Q⟩))=_
     rw [hplace]
   exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,heq⟩
 · have hQ:q.asIdeal∈RCN346.AOV K L:=
     (IsDedekindDomain.mem_primesOverFinset_iff
       (RCN349.ML K).ne_bot (FC K L)).mpr
       ⟨q.isPrime,RCN345.AHI K L q⟩
   let Q:EJR K L:=⟨q.asIdeal,hQ⟩
   let i:FamilyIndex_p19 K L s hs:=Sum.inr Q
   have heq:CTJ K L s hs i=
       RCN345.chartMap_p19 K L (Sum.inr q):=by
     have hplace:RCN346.ML K L Q=q:=by
       apply HeightOneSpectrum.ext
       rfl
     change RCN345.chartMap_p19 K L
       (Sum.inr (RCN346.ML K L Q))=_
     rw [hplace]
   exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,heq⟩
theorem AJO (x:L) (hx:x≠0):
   (∑ v∈placesFor_p19 K L x hx,zeroOrder_p19 K L v x)=
     ∑ v∈placesFor_p19 K L x hx,RCN346.poleOrder_p19 K L v x:=by
 apply sub_eq_zero.mp
 rw [←Finset.sum_sub_distrib]
 simp_rw [EQG]
 exact DAL K L x hx
theorem AUN (x:L) (hx:x≠0)
   (U:Finset (Place_p19 K L)) (hU:∀v∈U,1≤order_p19 K L v x):
   (U.card:ℤ)≤
     ∑ v∈placesFor_p19 K L x hx,RCN346.poleOrder_p19 K L v x:=by
 have hsub:U ⊆ placesFor_p19 K L x hx:=by
   intro v hv
   apply ALB K L x hx v
   have h:=hU v hv
   omega
 calc
   (U.card:ℤ)=∑ _v∈U,(1:ℤ):=by simp
   _≤ ∑ v∈U,zeroOrder_p19 K L v x:=by
     apply Finset.sum_le_sum
     intro v hv
     exact (hU v hv).trans (le_max_right _ _)
   _≤ ∑ v∈placesFor_p19 K L x hx,zeroOrder_p19 K L v x:=by
     apply Finset.sum_le_sum_of_subset_of_nonneg hsub
     intro v _ _
     exact AUU K L v x
   _=_:=AJO K L x hx
end
end RCN026
end SubmissionLower
end ProximityPrize
end PackedLegacy_DG
section PackedLegacy_H4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN017
open IsDedekindDomain
noncomputable section
section ActualPlaces
variable {K S L:Type*} [Field K] [CommRing S] [IsDedekindDomain S]
 [Algebra K S] [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]
@[simp] theorem pointPlace_asIdeal
   (hinj:Function.Injective (algebraMap (Polynomial K) S))
   (phi:S→ₐ[K] K):(pointPlace hinj phi).asIdeal=pointKernel phi:=rfl
end ActualPlaces
end
end RCN017
end SubmissionLower
end ProximityPrize
end PackedLegacy_H4
section PackedLegacy_R0
namespace ProximityPrize
namespace SubmissionLower
namespace RCN344
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
abbrev Place_p19:=RCN345.ACR K L
namespace SeparableCoordinate
variable [IsAlgClosed K]
theorem AMH (c:RCN344.SeparableCoordinate K L)
   (W:Finset (Place_p19 K L)):
   (∑ v∈W,RCN346.poleOrder_p19 K L v (RCN344.SeparableCoordinate.value K L c))≤
     (RCN344.SeparableCoordinate.degree K L c:ℤ):=by
 letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
 letI:Algebra (Polynomial K) L:=
   (c.embedding.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))).toAlgebra
 letI:IsScalarTower (Polynomial K) (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun a↦(c.embedding.commutes a).symm
 letI:IsScalarTower K (Polynomial K) L:=
   IsScalarTower.of_algebraMap_eq fun a↦by
     change algebraMap K L a=
       c.embedding (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) a))
     rw [←IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
     exact (c.embedding.commutes a).symm
 letI:FiniteDimensional (RatFunc K) L:=c.finite
 letI:Algebra.IsSeparable (RatFunc K) L:=c.separable
 exact RCN346.EGM K L W
end SeparableCoordinate
theorem NP (v:Place_p19 K L) (c:K):
   v.val (algebraMap K L c)≤1:=by
 letI:v.val.IsTrivialOn K:=v.property.2
 exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v.val c
variable [IsAlgClosed K]
theorem PY (c:Coordinate K L)
   (W:Finset (Place_p19 K L)):
   (∑ v∈W,RCN346.poleOrder_p19 K L v (RCN344.coordinateValue K L c))≤
     (RCN344.coordinateDegree K L c:ℤ):=by
 rcases c with a | c
 · have hz:∀v:Place_p19 K L,
       RCN346.poleOrder_p19 K L v (algebraMap K L a)=0:=
     fun v↦RCN346._Q11 K L v _
       (NP K L v a)
   simp only [RCN344.coordinateValue,RCN344.coordinateDegree,Sum.elim_inl,hz,Finset.sum_const_zero,
     Nat.cast_zero,le_refl]
 · exact RCN344.SeparableCoordinate.AMH K L c W
variable {σ:Type*} [Fintype σ]
theorem DFE (W:Finset (Place_p19 K L))
   (c:σ→Coordinate K L) (cap:σ→ℕ) (F:MvPolynomial σ K)
   (hcap:∀i,F.degreeOf i≤cap i):
   (∑ v∈W,RCN346.poleOrder_p19 K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦RCN344.coordinateValue K L (c i)) F))≤
     ∑ i,(cap i:ℤ)*(RCN344.coordinateDegree K L (c i):ℤ):=by
 have hlocal:=RCN187.weighted_poleOrder_eval_le_box
   W (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ a↦NP K L v a)
   (fun i↦RCN344.coordinateValue K L (c i)) cap F hcap
 simp only [Nat.cast_one,one_mul] at hlocal
 calc
   _≤ ∑ i,(cap i:ℤ)*
       ∑ v∈W,RCN346.poleOrder_p19 K L v (RCN344.coordinateValue K L (c i)):=hlocal
   _≤_:=by
     apply Finset.sum_le_sum
     intro i _
     exact mul_le_mul_of_nonneg_left
       (PY K L (c i) W) (Int.natCast_nonneg _)
section FixedSeparator
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place_p19 K L):=Classical.decEq _
theorem ELB (c:σ→Coordinate K L)
   (cap:σ→ℕ) (F:MvPolynomial σ K) (hcap:∀i,F.degreeOf i≤cap i)
   (hF:MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦RCN344.coordinateValue K L (c i)) F≠0)
   (U:Finset (Place_p19 K L))
   (hU:∀v∈U,1≤RCN026.order_p19 K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦RCN344.coordinateValue K L (c i)) F)):
   (U.card:ℤ)≤ ∑ i,(cap i:ℤ)*(RCN344.coordinateDegree K L (c i):ℤ):=by
 exact (RCN026.AUN K L _ hF U hU).trans
   (DFE K L _ c cap F hcap)
section AffineModel
variable (A:Type*) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
def modelPlace_p19 (φ:A→ₐ[K] K):Place_p19 K L:=
 RCN345.chartMap_p19 K L
   (Sum.inl (RCN000.actualPointPlace K A L φ))
theorem BQJ:Function.Injective (modelPlace_p19 K L A):=by
 intro φ ψ h
 have hchart:=(RCN345.CMN K L).1 h
 exact RCN000.actualPointPlace_injective K A L (Sum.inl.inj hchart)
theorem FKH (x:σ→A) (F:MvPolynomial σ K):
   algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F)=
     MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦algebraMap A L (x i)) F:=by
 have hhom:(algebraMap A L).comp (MvPolynomial.eval₂Hom (algebraMap K A) x)=
     MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦algebraMap A L (x i)):=by
   ext a
   · simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C]
     exact (IsScalarTower.algebraMap_apply K A L a).symm
   · simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X']
 exact DFunLike.congr_fun hhom F
theorem DNF
   (x:σ→A) (c:σ→Coordinate K L)
   (hc:∀i,RCN344.coordinateValue K L (c i)=algebraMap A L (x i))
   (cap:σ→ℕ) (F:MvPolynomial σ K) (hcap:∀i,F.degreeOf i≤cap i)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (S:Finset (A→ₐ[K] K))
   (hS:∀φ∈S,φ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   (S.card:ℤ)≤ ∑ i,(cap i:ℤ)*(RCN344.coordinateDegree K L (c i):ℤ):=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦RCN344.coordinateValue K L (c i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=by
   simp_rw [hc]
   exact (FKH K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦RCN344.coordinateValue K L (c i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace_p19 K L A)
 have hU:∀v∈U,1≤RCN026.order_p19 K L v
     (MvPolynomial.eval₂Hom (algebraMap K L) (fun i↦RCN344.coordinateValue K L (c i)) F):=by
   intro v hv
   obtain ⟨φ,hφ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact RCN000.actual_model_zero_order_ge_one K A L φ _ hF (hS φ hφ)
 have h:=ELB K L c cap F hcap hnonzero U hU
 have hcard:U.card=S.card:=Finset.card_image_of_injective _ (BQJ K L A)
 rwa [hcard] at h
end AffineModel
end FixedSeparator
end
end RCN344
end SubmissionLower
end ProximityPrize
end PackedLegacy_R0
section PackedLegacy_M
namespace ProximityPrize
namespace SubmissionLower
namespace RCN007
open scoped Classical BigOperators
open RCN002 RCN005 RCN006
noncomputable section
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
variable [IsAlgClosed K]
theorem CKX
   (hproj:RCN007.ProjectionsFiniteSeparable K P)
   (i₀:Fin 3) (hi₀:Transcendental K (coordinate K P i₀))
   (F:MvPolynomial (Fin 3) K) (hF:F∉P)
   (cap:Fin 3→ℕ) (hcap:∀i,F.degreeOf i≤cap i)
   (S:Finset (Fin 3→K))
   (hSP:∀v∈S,P≤RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀v∈S,MvPolynomial.aeval v F=0):
   (S.card:ℤ)≤ ∑ i,(cap i:ℤ)*(RCN007.actualCoordinateDegree K P i:ℤ):=by
 classical
 letI:Algebra (Polynomial K) (RCN002.CoordinateRing K P):=RCN006.quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (RCN002.CoordinateField K P):=RCN006.polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P i₀ hi₀
 letI:=RCN006.quotientBaseScalarTower K P i₀
 letI:=RCN006.polynomialBaseScalarTower K P i₀
 letI:=RCN006.quotientFractionScalarTower K P i₀
 letI:=RCN006.polynomialRationalScalarTower K P i₀ hi₀
 letI:=RCN005.rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P):=(hproj i₀ hi₀).1
 letI:Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=(hproj i₀ hi₀).2
 let c:=RCN007.coordinateData K P hproj
 have hc:∀i,RCN344.coordinateValue K (RCN002.CoordinateField K P) (c i)=
     algebraMap (RCN002.CoordinateRing K P) (RCN002.CoordinateField K P) (RCN006.quotientCoordinate K P i):=by
   intro i
   rw [RCN006.quotientCoordinate_fraction]
   exact RCN007.coordinateData_value K P hproj i
 let liftPoint:{v:Fin 3→K//v∈S}→(RCN002.CoordinateRing K P→ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w h
   have hvw:=RCN007.pointHom_injective K P h
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) hvw
 let points:=S.attach.image liftPoint
 have hpoints:∀φ∈points,φ (MvPolynomial.eval₂Hom
     (algebraMap K (RCN002.CoordinateRing K P)) (RCN006.quotientCoordinate K P) F)=0:=by
   intro φ hφ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hφ
   rw [RCN007.quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hcount:=RCN344.DNF
   K (RCN002.CoordinateField K P) (RCN002.CoordinateRing K P) (RCN006.quotientCoordinate K P)
   c hc cap F hcap (RCN007.quotient_eval_ne_zero_of_not_mem K P F hF) points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rw [hcard] at hcount
 simpa only [c,RCN007.coordinateData_degree] using hcount
theorem BMF
   (hproj:RCN007.ProjectionsFiniteSeparable K P)
   (hnonpoint:∀v:Fin 3→K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 3) K) (hF:F∉P)
   (cap:Fin 3→ℕ) (hcap:∀i,F.degreeOf i≤cap i)
   (S:Finset (Fin 3→K))
   (hSP:∀v∈S,P≤RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀v∈S,MvPolynomial.aeval v F=0):
   (S.card:ℤ)≤ ∑ i,(cap i:ℤ)*(RCN007.actualCoordinateDegree K P i:ℤ):=by
 obtain ⟨i,hi⟩:=RCN002.exists_transcendental_coordinate_of_ne_point_kernel K P hnonpoint
 exact CKX K P hproj i hi F hF cap hcap S hSP hSF
end
end RCN007
end SubmissionLower
end ProximityPrize
end PackedLegacy_M
end Compact_PackedLegacyCore0
section Compact_PackedLegacyCore1
section PackedLegacy_N4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN256
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]
def DVY (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X i
def XZ (i j z:ℕ):Fin 3→₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j+Finsupp.single 2 z
@[simp] theorem BIA (i j z:ℕ):
   XZ i j z 0=i:=by simp [XZ]
@[simp] theorem CMO (i j z:ℕ):
   XZ i j z 1=j:=by simp [XZ]
@[simp] theorem CMR (i j z:ℕ):
   XZ i j z 2=z:=by simp [XZ]
theorem DLO (d:Fin 3→₀ ℕ):
   XZ (d 0) (d 1) (d 2)=d:=by
 ext i
 fin_cases i<;>simp
abbrev BoxIndex (M L s:ℕ):=
 (i:Fin (min M L+1)) × (Fin (s+1) × Fin (L-i.val+1))
theorem EZX
   {n a b:ℕ} {i j:Fin n} {u:Fin a} {v:Fin b}
   (hab:a=b) (hij:i.val=j.val) (huv:u.val=v.val):
   HEq (i,u) (j,v):=by
 subst b
 have hi:i=j:=Fin.ext hij
 have hu:u=v:=Fin.ext huv
 cases hi
 cases hu
 rfl
def BHO (M L s:ℕ):
   boxExponents M L s ≃ BoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,by
       rcases d.property with ⟨hM,hL,hs⟩
       omega⟩,
     ⟨⟨d.val 1,by
         rcases d.property with ⟨hM,hL,hs⟩
         omega⟩,
       ⟨d.val 2,by
         change d.val 2<L-d.val 0+1
         rcases d.property with ⟨hM,hL,hs⟩
         omega⟩⟩⟩
 invFun q:=
   ⟨XZ q.1.val q.2.1.val q.2.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.1.isLt
     have hz:=q.2.2.isLt
     simp only [boxExponents,Set.mem_setOf_eq,BIA,
       CMO,CMR]
     omega⟩
 left_inv d:=Subtype.ext (DLO d.val)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨⟨j,hj⟩,⟨z,hz⟩⟩⟩
   simp
   apply EZX
   · simp [XZ]
   · rfl
   · rfl
instance FHH (M L s:ℕ):Fintype (boxExponents M L s):=
 Fintype.ofEquiv (BoxIndex M L s) (BHO M L s).symm
instance FER (M L s:ℕ):
   Module.Finite K (RCN256.coefficientBox K M L s):=
 Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boxExponents M L s))
end
end RCN256
end SubmissionLower
end ProximityPrize
end PackedLegacy_N4
section PackedLegacy_J
namespace ProximityPrize
namespace SubmissionLower
namespace RCN238
open scoped Classical BigOperators
open RCN002 RCN005 RCN007 RCN136 RCN231 RCN229 RCN313 RCN065 RCN319
open RCN319 renaming specialization → BM
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K→+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def DK (selected:K→Polynomial K) (γ:K):Fin 3→Ω:=
 fun i↦RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) i.succ
theorem EMD (selected:K→Polynomial K) (γ:K):
   DK φ selected γ (2:Fin 3)=(φ.comp Polynomial.C) γ:=rfl
theorem ABD (selected:K→Polynomial K):
   Function.Injective (DK φ selected):=by
 intro γ η h
 apply (φ.comp Polynomial.C).injective
 simpa only [EMD] using congrFun h (2:Fin 3)
def FK (F:MvPolynomial (Fin 4) K) (w:ℕ) (x u₀ u₁:K):
   MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (RCN313.agreementNumerator F w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁)
theorem AQG
   (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K)
   (p w:ℕ) [CharP Ω p] (hchar:w<p)
   (γ:K) (hdegree:(selected γ).natDegree≤w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0)
   (hregular:MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (x u₀ u₁:K):
   MvPolynomial.aeval (DK φ selected γ)
     (FK φ F w x u₀ u₁)=0 ↔
       (selected γ).eval x=u₀+γ*u₁:=by
 change MvPolynomial.eval (DK φ selected γ)
   (surfaceMap φ (RCN313.agreementNumerator F w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁))=0 ↔ _
 rw [RCN136.eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (DK φ selected γ)=
     RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i<;>rfl
 rw [hv]
 exact RCN229.factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F
   (selected γ) γ (φ Polynomial.X) hsolution hregular p w hchar hdegree x u₀ u₁
variable [IsAlgClosed Ω]
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
def BDR (cap:Fin 3→ℕ):ℕ:=
 ∑ j,cap j*RCN007.actualCoordinateDegree Ω P j
theorem ESC
   (hproj:RCN007.ProjectionsFiniteSeparable Ω P)
   (hnonpoint:∀v:Fin 3→Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w<p)
   (hdegree:∀γ∈Γ,(selected γ).natDegree≤w)
   (hsolution:∀γ∈Γ,RCN319.specialization K (selected γ) γ F=0)
   (hregular:∀γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀γ∈Γ,P≤RingHom.ker
     (MvPolynomial.aeval (DK φ selected γ)).toRingHom)
   (x u₀ u₁:K) (hproper:FK φ F w x u₀ u₁∉P)
   (cap:Fin 3→ℕ)
   (hcap:∀j,(FK φ F w x u₀ u₁).degreeOf j≤cap j):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card≤BDR P cap:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (DK φ selected)
 have hpointsP:∀v∈points,P≤RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint γ (Finset.mem_filter.mp hγ).1
 have hpointsF:∀v∈points,
     MvPolynomial.aeval v (FK φ F w x u₀ u₁)=0:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
   exact (AQG φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcount:=RCN007.BMF Ω P hproj hnonpoint
   (FK φ F w x u₀ u₁) hproper cap hcap points hpointsP hpointsF
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (ABD φ selected)
 rw [hcard] at hcount
 unfold BDR
 exact_mod_cast hcount
theorem CLK
   (hproj:RCN007.ProjectionsFiniteSeparable Ω P) (j:Fin 3)
   (hj:Transcendental Ω (coordinate Ω P j)):
   1≤RCN007.actualCoordinateDegree Ω P j:=by
 letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω P):=RCN005.rationalBaseAlgebra Ω P j hj
 letI:FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω P):=(hproj j hj).1
 rw [RCN007.actualCoordinateDegree_of_transcendental Ω P j hj]
 exact Module.finrank_pos
def BL (selected:K→Polynomial K) (Γ:Finset K) (w e:ℕ):Prop:=
 ∀P₀ P₁:Polynomial K,P₀.natDegree≤w→P₁.natDegree≤w→
   (Γ.filter (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)).card≤e+1
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem CQV
   (hproj:RCN007.ProjectionsFiniteSeparable Ω P)
   (hnonpoint:∀v:Fin 3→Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap φ F∈P)
   (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K→Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι→K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1≤w) (hchar:w<p)
   (hwa:w<a) (han:a≤nodes.card)
   (hdegree:∀γ∈Γ,(selected γ).natDegree≤w)
   (hsolution:∀γ∈Γ,RCN319.specialization K (selected γ) γ F=0)
   (hregular:∀γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀γ∈Γ,P≤RingHom.ker
     (MvPolynomial.aeval (DK φ selected γ)).toRingHom)
   (hagreement:∀γ∈Γ,
     a≤(nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:BL selected Γ w e)
   (cap:Fin 3→ℕ)
   (hcap:∀i∈nodes,∀j,
     (FK φ F w (x i) (u₀ i) (u₁ i)).degreeOf j≤cap j):
   Γ.card*(a-w)≤(nodes.card-w)*BDR P cap+
     (e+1)*(a-w)*RCN007.actualCoordinateDegree Ω P 2:=by
 classical
 let I:=RCN065.identityNodes φ P F nodes x u₀ u₁ w
 let relation:K→ι→Prop:=fun γ i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card≤w
 · have hfiber:∀i∈nodes \ I,(Γ.filter (fun γ↦relation γ i)).card≤BDR P cap:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:FK φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact ESC φ P hproj hnonpoint F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u₀ i) (u₁ i) hproper cap (hcap i hinodes)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w
     (BDR P cap) (RCN065.identityNodes_subset φ P F nodes x u₀ u₁ w) hI hwa han
     hagreement hfiber
   omega
 · have hc:w<I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀(t:{γ:K//γ∈Γ}) i,i∈I→
       (selected t.1).eval (x i)=u₀ i+t.1*u₁ i:=by
     intro t
     exact RCN065.selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P₀,P₁,h₀,h₁,_,hpencil⟩:=
     RCN065.exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
       (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
       (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card≤e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=RCN065.seed_transcendental_of_many_identities φ P F hF hH nodes x u₀ u₁ w hw
     hinj hc hnonpoint
   have hδ:=CLK P hproj (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w)≤
       (e+1)*(a-w)*RCN007.actualCoordinateDegree Ω P 2:=by
     calc
       _≤(e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _≤_:=by
         simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
end
end RCN238
end SubmissionLower
end ProximityPrize
end PackedLegacy_J
section PackedLegacy_DA
namespace ProximityPrize
namespace SubmissionLower
open Polynomial Polynomial.Bivariate
open scoped BigOperators
set_option linter.constructorNameAsVariable false
local instance concreteFieldChar:
   CharP ProximityPrize.Benchmark.IRSProfile.Field 2130706433:=
 charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem BPT
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hpos:0<R.natDegree) (hlt:R.natDegree<p):R.derivative≠0:=by
 intro hzero
 have hc:=congrArg (fun f:K[X]=>f.coeff (R.natDegree-1)) hzero
 rw [coeff_derivative] at hc
 have hsucc:R.natDegree-1+1=R.natDegree:=by omega
 rw [hsucc] at hc
 have hcastSucc:((R.natDegree-1:ℕ):K)+1=(R.natDegree:K):=by
   simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z:ℕ=>(z:K)) hsucc
 rw [hcastSucc,coeff_natDegree] at hc
 simp only [coeff_zero] at hc
 have hcast:(R.natDegree:K)≠0:=by
   intro hz
   have hdvd:p∣R.natDegree:=(CharP.cast_eq_zero_iff K p R.natDegree).mp hz
   exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd
 have hR:R≠0:=by
   intro hz
   simp [hz] at hpos
 exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hR) hcast) hc
theorem AVX
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hirr:Irreducible R) (hpos:0<R.natDegree) (hlt:R.natDegree<p):
   IsCoprime R R.derivative:=by
 have hdne:=BPT p R hpos hlt
 have hddeg:R.derivative.natDegree<R.natDegree:=
   natDegree_derivative_lt (ne_of_gt hpos)
 have hnotdvd:¬R∣R.derivative:=by
   intro hdvd
   have hle:=natDegree_le_of_dvd hdvd hdne
   omega
 by_contra hnot
 exact hnotdvd ((hirr.dvd_iff_not_isCoprime).2 hnot)
end SubmissionLower
end ProximityPrize
end PackedLegacy_DA
section PackedLegacy_G3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN360
noncomputable section
variable {K L:Type} [Field K] [Field L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
def bimap_p19 (f:K→+*L) (P:Polynomial (Polynomial K)):
   Polynomial (Polynomial L):=P.map (Polynomial.mapRingHom f)
theorem GHA (f:K→+*L)
   (P:Polynomial (Polynomial K)) (hP:P.IsPrimitive):
   (bimap_p19 f P).IsPrimitive:=by
 apply Polynomial.isPrimitive_of_contentIdeal_eq_top
 rw [bimap_p19,Polynomial.contentIdeal_map_eq_map_contentIdeal,
   (Polynomial.isPrimitive_iff_contentIdeal_eq_top P).mp hP,Ideal.map_top]
theorem EMX (f:K→+*L) (P:Polynomial (Polynomial K)):
   (bimap_p19 f P).natDegree≤P.natDegree:=
 Polynomial.natDegree_map_le
theorem EZC (f:K→+*L) (P:Polynomial (Polynomial K)):
   Polynomial.Bivariate.degreeX (bimap_p19 f P)≤Polynomial.Bivariate.degreeX P:=by
 classical
 unfold Polynomial.Bivariate.degreeX
 apply Finset.sup_le
 intro j _
 rw [show (bimap_p19 f P).coeff j=(P.coeff j).map f by simp [bimap_p19]]
 exact Polynomial.natDegree_map_le.trans
   (Polynomial.Bivariate.coeff_natDegree_le_degreeX P j)
theorem ART (f:K→+*L)
   (P:Polynomial (Polynomial K)) (x:L):
   (bimap_p19 f P).map (Polynomial.evalRingHom x)=
     P.map (Polynomial.eval₂RingHom f x):=by
 ext j
 simp [bimap_p19,Polynomial.eval_map]
theorem FMC (f:K→+*L)
   (P:Polynomial (Polynomial K)) (x y:K):
   ((bimap_p19 f P).map (Polynomial.evalRingHom (f x))).eval (f y)=
     f ((P.map (Polynomial.evalRingHom x)).eval y):=by
 have h:(bimap_p19 f P).map (Polynomial.evalRingHom (f x))=
     (P.map (Polynomial.evalRingHom x)).map f:=by
   ext j
   simp [bimap_p19,Polynomial.eval_map,Polynomial.eval₂_at_apply]
 rw [h,Polynomial.eval_map_apply]
theorem bimap_comp_p19 {M:Type} [Field M]
   (f:K→+*L) (g:L→+*M) (P:Polynomial (Polynomial K)):
   bimap_p19 g (bimap_p19 f P)=bimap_p19 (g.comp f) P:=by
 ext j i
 simp [bimap_p19]
theorem ERI (f:K→+*L)
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hres:Polynomial.resultant P Q m n≠0):
   Polynomial.resultant (bimap_p19 f P) (bimap_p19 f Q) m n≠0:=by
 unfold bimap_p19
 rw [Polynomial.resultant_map_map]
 intro hzero
 apply hres
 apply Polynomial.map_injective f f.injective
 simpa only [Polynomial.coe_mapRingHom,Polynomial.map_zero] using hzero
theorem ABJ (f:K→+*L)
   (P:Polynomial (Polynomial K)) (hP:P.IsPrimitive) (x:L):
   (bimap_p19 f P).map (Polynomial.evalRingHom x)≠0:=by
 classical
 exact RCN362.primitive_specialization_ne_zero
   (bimap_p19 f P) (GHA f P hP) x
theorem AXC (f:K→+*L)
   (P Q:Polynomial (Polynomial K)) (points:Finset (L × L))
   (hP:Irreducible P) (hdeg:0<P.natDegree) (hproper:¬P∣Q)
   (hroots:∀point∈points,
     ((bimap_p19 f P).map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     ((bimap_p19 f Q).map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card≤Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 have hcount:=RCN363.common_points_card_le_bidegree_bound
   (bimap_p19 f P) (bimap_p19 f Q) P.natDegree Q.natDegree points
   (EMX f P) (EMX f Q)
   (ERI f P Q P.natDegree Q.natDegree
     (RCN362.irreducible_resultant_ne_zero_of_not_dvd
       P Q hP hdeg hproper))
   (fun point _=>Or.inl (ABJ f P
     (hP.isPrimitive (Nat.ne_of_gt hdeg)) point.1)) hroots
 exact hcount.trans (Nat.add_le_add
   (Nat.mul_le_mul_left _ (EZC f P))
   (Nat.mul_le_mul_left _ (EZC f Q)))
end
end RCN360
end SubmissionLower
end ProximityPrize
end PackedLegacy_G3
section PackedLegacy_G6
namespace ProximityPrize
namespace SubmissionLower
namespace RCN364
noncomputable section
variable {K L:Type} [Field K] [Field L] [Algebra K L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
theorem WS
   (p:ℕ) [CharP K p] (f:Polynomial K) (x:L)
   (hf:f≠0) (hx:Polynomial.aeval x f=0) (hdegree:f.natDegree<p):
   IsIntegral K x∧IsSeparable K x:=by
 have hint:IsIntegral K x:=IsAlgebraic.isIntegral ⟨f,hf,hx⟩
 have hmin:(minpoly K x).natDegree≤f.natDegree:=
   Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hx) hf
 refine ⟨hint,?_⟩
 change (minpoly K x).Separable
 apply (Polynomial.separable_def _).mpr
 exact AVX p (minpoly K x)
   (minpoly.irreducible hint) (minpoly.natDegree_pos hint) (hmin.trans_lt hdegree)
theorem AVA
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPdegree:P.natDegree≤m) (hQdegree:Q.natDegree≤n)
   (hpositive:m≠0∨n≠0) (y r:L)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0):
   Polynomial.aeval y (Polynomial.resultant P Q m n)=0:=by
 obtain ⟨U,V,_,_,hidentity⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant
   P Q hPdegree hQdegree hpositive
 have heval:=congrArg
   (fun F:Polynomial (Polynomial K)=>
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r F) hidentity
 simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
   hP,hQ,zero_mul,zero_add] at heval
 exact heval.symm
theorem CXD (y r:L)
   (hy:IsSeparable K y) (hr:IsSeparable K r)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
   FiniteDimensional K L∧Algebra.IsSeparable K L:=by
 letI:FiniteDimensional K (IntermediateField.adjoin K ({y,r}:Set L)):=
   IntermediateField.finiteDimensional_adjoin_pair hy.isIntegral hr.isIntegral
 letI:Algebra.IsSeparable K (IntermediateField.adjoin K ({y,r}:Set L)):=
   IntermediateField.isSeparable_adjoin_pair_of_isSeparable K L hy hr
 letI:FiniteDimensional K (⊤:IntermediateField K L):=by
   rw [←hgenerate]
   infer_instance
 have hsepTop:Algebra.IsSeparable K (⊤:IntermediateField K L):=by
   rw [←hgenerate]
   infer_instance
 have hfinite:FiniteDimensional K L:=Module.Finite.of_surjective
   (IntermediateField.topEquiv (F:=K) (E:=L)).toLinearMap
   (IntermediateField.topEquiv (F:=K) (E:=L)).surjective
 exact ⟨hfinite,(IntermediateField.isSeparable_top (F:=K) (E:=L)).mp hsepTop⟩
theorem CKC
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0<P.natDegree)
   (hproper:¬P∣Q) (hRdegree:P.natDegree<p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree<p)
   (y r:L)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
   FiniteDimensional K L∧Algebra.IsSeparable K L:=by
 classical
 have hresne:=RCN362.irreducible_resultant_ne_zero_of_not_dvd
   P Q hirreducible hpositive hproper
 have hresroot:=AVA P Q
   P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive)) y r hP hQ
 obtain ⟨_,hySeparable⟩:=WS p
   (Polynomial.resultant P Q P.natDegree Q.natDegree) y hresne hresroot hresultantDegree
 let S:IntermediateField K L:=IntermediateField.adjoin K {y}
 let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K y⟩
 letI:DecidableEq S:=Classical.decEq S
 letI:CharP S p:=charP_of_injective_algebraMap (algebraMap K S).injective p
 let g:Polynomial K→+*S:=Polynomial.eval₂RingHom (algebraMap K S) yS
 let Py:Polynomial S:=P.map g
 have hPyne:Py≠0:=by
   have h:=RCN360.ABJ
     (algebraMap K S) P (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
   rw [RCN360.ART] at h
   exact h
 have hPydegree:Py.natDegree<p:=Polynomial.natDegree_map_le.trans_lt hRdegree
 have hcoefficient:(algebraMap S L).comp g=
     Polynomial.eval₂RingHom (algebraMap K L) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c))=
       Polynomial.eval₂ (algebraMap K L) y (Polynomial.C c)
     rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
     exact (IsScalarTower.algebraMap_apply K S L c).symm
   · change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X)=
       Polynomial.eval₂ (algebraMap K L) y Polynomial.X
     rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
     rfl
 have hPyroot:Polynomial.aeval r Py=0:=by
   change Polynomial.eval₂ (algebraMap S L) r (P.map g)=0
   rw [Polynomial.eval₂_map,hcoefficient]
   exact hP
 obtain ⟨_,hrSeparable⟩:=WS p
   Py r hPyne hPyroot hPydegree
 letI:Algebra.IsSeparable K S:=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).mpr hySeparable
 have hrOverK:IsSeparable K r:=
   IsSeparable.of_algebra_isSeparable_of_isSeparable K hrSeparable
 exact CXD y r hySeparable hrOverK hgenerate
end
end RCN364
end SubmissionLower
end ProximityPrize
end PackedLegacy_G6
section PackedLegacy_G4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN361
open RCN360
noncomputable section
section Evaluation
variable (K E:Type) [Field K] [Field E] [Algebra K E]
theorem planeEval_eq_p19 (y r:E) (P:Polynomial (Polynomial K)):
   planeEval K E y r P=
     ((bimap_p19 (algebraMap K E) P).map (Polynomial.evalRingHom y)).eval r:=by
 simp only [planeEval,RingHom.comp_apply,Polynomial.coe_mapRingHom,
   Polynomial.coe_evalRingHom]
 rw [ART]
variable (Ω:Type) [Field Ω] [Algebra K Ω]
theorem BPF (φ:E→ₐ[K] Ω) (y r:E)
   (P:Polynomial (Polynomial K)):
   φ (planeEval K E y r P)=planeEval K Ω (φ y) (φ r) P:=by
 rw [planeEval_eq_p19,planeEval_eq_p19]
 have h:=FMC φ.toRingHom
   (bimap_p19 (algebraMap K E) P) y r
 have hcomp:φ.toRingHom.comp (algebraMap K E)=algebraMap K Ω:=by
   ext a
   exact φ.commutes a
 rw [bimap_comp_p19,hcomp] at h
 exact h.symm
variable (E':Type) [Field E'] [Algebra K E']
theorem CKI
   (y r:E) (y' r':E') (φ:E→ₐ[K] Ω) (ψ:E' →ₐ[K] Ω)
   (hy:φ y=ψ y') (hr:φ r=ψ r'):
   RCN361.relationIdeal K E y r=RCN361.relationIdeal K E' y' r':=by
 apply Ideal.ext
 intro P
 change planeEval K E y r P=0 ↔ planeEval K E' y' r' P=0
 have heq:φ (planeEval K E y r P)=ψ (planeEval K E' y' r' P):=by
   rw [BPF,BPF,hy,hr]
 constructor
 · intro h
   apply ψ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq.symm
 · intro h
   apply φ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq
end Evaluation
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
 [FiniteDimensional K E] [Algebra.IsSeparable K E]
theorem EPY
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0<P.natDegree) (hproper:¬P∣Q)
   (y r:E) (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hPy:planeEval K E y r P=0) (hQy:planeEval K E y r Q=0):
   Module.finrank K E≤Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure E
 letI:Fintype (E→ₐ[K] Ω):=Fintype.ofFinite _
 let points:Finset (Ω × Ω):=Finset.univ.image (fun φ:E→ₐ[K] Ω=>(φ y,φ r))
 have hcard:points.card=Module.finrank K E:=by
   rw [Finset.card_image_of_injective _ (RCN361.embedding_pair_injective K E Ω y r hgen),
     Finset.card_univ,Fintype.card_eq_nat_card]
   exact Field.finSepDegree_eq_finrank_of_isSeparable K E
 rw [←hcard]
 apply AXC (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨φ,_,rfl⟩:=Finset.mem_image.mp hp
 constructor
 · rw [←planeEval_eq_p19]
   rw [←BPF K E Ω φ y r P,hPy,map_zero]
 · rw [←planeEval_eq_p19]
   rw [←BPF K E Ω φ y r Q,hQy,map_zero]
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
 {I:Type} [Fintype I] (E:I→Type)
 [∀i,Field (E i)] [∀i,Algebra K (E i)]
 [∀i,FiniteDimensional K (E i)] [∀i,Algebra.IsSeparable K (E i)]
theorem ECY
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0<P.natDegree) (hproper:¬P∣Q)
   (y r:∀i,E i)
   (hgen:∀i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i=>RCN361.relationIdeal K (E i) (y i) (r i)))
   (hPy:∀i,planeEval K (E i) (y i) (r i) P=0)
   (hQy:∀i,planeEval K (E i) (y i) (r i) Q=0):
   (∑ i,Module.finrank K (E i))≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure K
 letI:∀i,Fintype (E i→ₐ[K] Ω):=fun i=>Fintype.ofFinite _
 let pair:(Σ i,E i→ₐ[K] Ω)→Ω × Ω:=
   fun a=>(a.2 (y a.1),a.2 (r a.1))
 have hinj:Function.Injective pair:=by
   rintro ⟨i,φ⟩ ⟨j,ψ⟩ h
   have hij:i=j:=hkernels
     (CKI K (E i) Ω (E j)
       (y i) (r i) (y j) (r j) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h))
   subst j
   have heq:φ=ψ:=RCN361.algHom_eq_of_generating_pair K (E i) Ω
     (y i) (r i) (hgen i) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h)
   exact congrArg (Sigma.mk i) heq
 let points:Finset (Ω × Ω):=Finset.univ.image pair
 have hcard:points.card=∑ i,Module.finrank K (E i):=by
   rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_sigma]
   apply Finset.sum_congr rfl
   intro i _
   rw [Fintype.card_eq_nat_card,
     ←Field.finSepDegree_eq_of_isAlgClosed K (E i) Ω,
     Field.finSepDegree_eq_finrank_of_isSeparable]
 rw [←hcard]
 apply AXC (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨⟨i,φ⟩,_,rfl⟩:=Finset.mem_image.mp hp
 change
   ((bimap_p19 (algebraMap K Ω) P).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0∧
   ((bimap_p19 (algebraMap K Ω) Q).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0
 constructor
 · rw [←planeEval_eq_p19,←BPF K (E i) Ω φ (y i) (r i) P,hPy i,map_zero]
 · rw [←planeEval_eq_p19,←BPF K (E i) Ω φ (y i) (r i) Q,hQy i,map_zero]
end FiniteFamily
end
end RCN361
end SubmissionLower
end ProximityPrize
end PackedLegacy_G4
section PackedLegacy_W7
namespace ProximityPrize
namespace SubmissionLower
namespace RCN365
open RCN361
noncomputable section
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
theorem ASK
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0<P.natDegree)
   (hproper:¬P∣Q) (hRdegree:P.natDegree<p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree<p)
   (y r:E)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hP:planeEval K E y r P=0) (hQ:planeEval K E y r Q=0):
   FiniteDimensional K E∧Algebra.IsSeparable K E∧
     Module.finrank K E≤Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 have hPeval:Polynomial.eval₂
     (Polynomial.eval₂RingHom (algebraMap K E) y) r P=0:=by
   rw [←planeEval_eq_eval₂]
   exact hP
 have hQeval:Polynomial.eval₂
     (Polynomial.eval₂RingHom (algebraMap K E) y) r Q=0:=by
   rw [←planeEval_eq_eval₂]
   exact hQ
 have hfields:=RCN364.CKC
   p P Q hirreducible hpositive hproper hRdegree hresultantDegree y r hPeval hQeval hgenerate
 letI:FiniteDimensional K E:=hfields.1
 letI:Algebra.IsSeparable K E:=hfields.2
 exact ⟨hfields.1,hfields.2,
   RCN361.EPY K E P Q
     hirreducible hpositive hproper y r hgenerate hP hQ⟩
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
 {I:Type} [Fintype I] (E:I→Type)
 [∀i,Field (E i)] [∀i,Algebra K (E i)]
theorem BOW
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0<P.natDegree)
   (hproper:¬P∣Q) (hRdegree:P.natDegree<p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree<p)
   (y r:∀i,E i)
   (hgenerate:∀i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i=>RCN361.relationIdeal K (E i) (y i) (r i)))
   (hP:∀i,planeEval K (E i) (y i) (r i) P=0)
   (hQ:∀i,planeEval K (E i) (y i) (r i) Q=0):
   (∀i,FiniteDimensional K (E i)∧Algebra.IsSeparable K (E i))∧
     (∑ i,Module.finrank K (E i))≤
       Q.natDegree*Polynomial.Bivariate.degreeX P+
         P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 have hfields:∀i,FiniteDimensional K (E i)∧Algebra.IsSeparable K (E i):=by
   intro i
   have h:=ASK K (E i)
     p P Q hirreducible hpositive hproper hRdegree hresultantDegree
     (y i) (r i) (hgenerate i) (hP i) (hQ i)
   exact ⟨h.1,h.2.1⟩
 letI:∀i,FiniteDimensional K (E i):=fun i=>(hfields i).1
 letI:∀i,Algebra.IsSeparable K (E i):=fun i=>(hfields i).2
 exact ⟨hfields,
   RCN361.ECY K E P Q
     hirreducible hpositive hproper y r hgenerate hkernels hP hQ⟩
end FiniteFamily
end
end RCN365
end SubmissionLower
end ProximityPrize
end PackedLegacy_W7
section PackedLegacy_X4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN010
open RCN002 RCN005 RCN371 RCN011
open RCN371 renaming RationalPolynomials → KU
noncomputable section
variable (K:Type) [Field K]
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
theorem CON
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬G∣H)
   (hpositive:0<(planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree<p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree<p):
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P)∧
     Module.finrank (RatFunc K) (RCN002.CoordinateField K P)≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P (order 0) ht
 letI:CharP (RatFunc K) p:=
   charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
 have hirr:=RCN011.planeMap_irreducible_of_component
   (K:=K) (order:=order) (P:=P) (ht:=ht) G hG hGmem
 have hproperPlane:¬planeMap K order G∣planeMap K order H:=by
   intro h
   exact hproper ((RCN011.planeMap_dvd_iff_of_component
     (K:=K) (order:=order) (P:=P) (ht:=ht) G H hG hGmem).mp h)
 have hGroots:RCN361.planeEval (RatFunc K) (RCN002.CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order G)=0:=by
   change RCN011.actualPlaneEvaluation K order P ht (planeMap K order G)=0
   exact (RCN011.actualPlane_root_iff K order P ht G).mpr hGmem
 have hHroots:RCN361.planeEval (RatFunc K) (RCN002.CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order H)=0:=by
   change RCN011.actualPlaneEvaluation K order P ht (planeMap K order H)=0
   exact (RCN011.actualPlane_root_iff K order P ht H).mpr hHmem
 exact RCN365.ASK
   (RatFunc K) (RCN002.CoordinateField K P) p (planeMap K order G) (planeMap K order H)
   hirr hpositive hproperPlane hRdegree hresultantDegree
   (coordinate K P (order 2)) (coordinate K P (order 1))
   (RCN010.actual_generators K order P ht) hGroots hHroots
end Component
section FiniteFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I→Ideal (Original K)) [∀i,(P i).IsPrime]
theorem BXQ
   (ht:∀i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀i,G∈P i) (hHmem:∀i,H∈P i)
   (hproper:¬G∣H)
   (hpositive:0<(planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree<p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree<p):
   letI:∀i,Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=
     fun i=>RCN005.rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀i,FiniteDimensional (RatFunc K) (RCN002.CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (RCN002.CoordinateField K (P i)))≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀i,Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=
   fun i=>RCN005.rationalBaseAlgebra K (P i) (order 0) (ht i)
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   letI:CharP (RatFunc K) p:=
     charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
   have hirr:=RCN011.planeMap_irreducible_of_component
     (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G hG (hGmem i₀)
   have hproperPlane:¬planeMap K order G∣planeMap K order H:=by
     intro h
     exact hproper ((RCN011.planeMap_dvd_iff_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G H hG (hGmem i₀)).mp h)
   have hkernels:Function.Injective (fun i=>
       RCN361.relationIdeal (RatFunc K) (RCN002.CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))):=by
     change Function.Injective (fun i=>RCN011.actualRelationKernel K order (P i) (ht i))
     exact RCN011.actualRelationKernel_family_injective K order P ht hinj
   have hGroots:∀i,
       RCN361.planeEval (RatFunc K) (RCN002.CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order G)=0:=by
     intro i
     change RCN011.actualPlaneEvaluation K order (P i) (ht i) (planeMap K order G)=0
     exact (RCN011.actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
   have hHroots:∀i,
       RCN361.planeEval (RatFunc K) (RCN002.CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order H)=0:=by
     intro i
     change RCN011.actualPlaneEvaluation K order (P i) (ht i) (planeMap K order H)=0
     exact (RCN011.actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
   exact RCN365.BOW
     (RatFunc K) (fun i=>RCN002.CoordinateField K (P i)) p
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     hRdegree hresultantDegree
     (fun i=>coordinate K (P i) (order 2)) (fun i=>coordinate K (P i) (order 1))
     (fun i=>RCN010.actual_generators K order (P i) (ht i)) hkernels hGroots hHroots
 · letI:IsEmpty I:=⟨fun i=>hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end FiniteFamily
end
end RCN010
end SubmissionLower
end ProximityPrize
end PackedLegacy_X4
section PackedLegacy_G9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN004
open RCN002 RCN005 RCN371 RCN011 RCN009 RCN013 RCN010
open RCN371 renaming RationalPolynomials → KU
noncomputable section
variable (K:Type) [Field K]
def GUP (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (RCN002.CoordinateField K P)) (B:ℕ):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P)∧
   Module.finrank (RatFunc K) (RCN002.CoordinateField K P)≤B
def EIJ (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (RCN002.CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P)
def GYI {I:Type} [Fintype I] (P:I→Ideal (Original K))
   [∀i,(P i).IsPrime]
   (A:∀i,Algebra (RatFunc K) (RCN002.CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀i,FiniteDimensional (RatFunc K) (RCN002.CoordinateField K (P i))∧
   Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (RCN002.CoordinateField K (P i)))≤B
section Single
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
theorem AGY
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬G∣H)
   (h1:G.degreeOf (order 1)<p) (h2:G.degreeOf (order 2)<p)
   (hmixed:RCN013.originalMixedDegree K order G H<p):
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P)∧
     Module.finrank (RatFunc K) (RCN002.CoordinateField K P)≤RCN013.originalMixedDegree K order G H:=by
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
   RCN013.exists_positive_characteristic_order K order P G H p hG hGmem ht h1 h2 hmixed
 have ht':Transcendental K (coordinate K P (order' 0)):=by
   simpa only [hbase] using ht
 have hresult:
     letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P (order' 0) ht'
     FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P)∧
       Module.finrank (RatFunc K) (RCN002.CoordinateField K P)≤RCN013.originalMixedDegree K order' G H:=by
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P (order' 0) ht'
   obtain ⟨hfd,hsep,hbound⟩:=CON
     K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
   exact ⟨hfd,hsep,hbound.trans (RCN004.plane_budget_le_original K order' G H)⟩
 change GUP K P (RCN005.rationalBaseAlgebra K P (order' 0) ht')
   (RCN013.originalMixedDegree K order' G H) at hresult
 rw [RCN004.rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht,hbudget] at hresult
 exact hresult
end Single
section Family
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I→Ideal (Original K)) [∀i,(P i).IsPrime]
theorem BQE
   (ht:∀i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀i,G∈P i) (hHmem:∀i,H∈P i)
   (hproper:¬G∣H)
   (h1:G.degreeOf (order 1)<p) (h2:G.degreeOf (order 2)<p)
   (hmixed:RCN013.originalMixedDegree K order G H<p):
   letI:∀i,Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=
     fun i=>RCN005.rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀i,FiniteDimensional (RatFunc K) (RCN002.CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (RCN002.CoordinateField K (P i)))≤
       RCN013.originalMixedDegree K order G H:=by
 classical
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
     RCN013.exists_positive_characteristic_order K order (P i₀) G H p
       hG (hGmem i₀) (ht i₀) h1 h2 hmixed
   have ht':∀i,Transcendental K (coordinate K (P i) (order' 0)):=by
     intro i
     simpa only [hbase] using ht i
   have hresult:
       letI:∀i,Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=
         fun i=>RCN005.rationalBaseAlgebra K (P i) (order' 0) (ht' i)
       (∀i,FiniteDimensional (RatFunc K) (RCN002.CoordinateField K (P i))∧
         Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K (P i)))∧
         (∑ i,Module.finrank (RatFunc K) (RCN002.CoordinateField K (P i)))≤
           RCN013.originalMixedDegree K order' G H:=by
     letI:∀i,Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=
       fun i=>RCN005.rationalBaseAlgebra K (P i) (order' 0) (ht' i)
     obtain ⟨hfields,hbound⟩:=BXQ
       K order' P ht' hinj p G H hG hGmem hHmem hproper hpos houter hres
     exact ⟨hfields,hbound.trans (RCN004.plane_budget_le_original K order' G H)⟩
   have halg:(fun i=>RCN005.rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
       (fun i=>RCN005.rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
     funext i
     exact RCN004.rationalBaseAlgebra_congr K (P i) (order' 0) (order 0) hbase (ht' i) (ht i)
   change GYI K P (fun i=>RCN005.rationalBaseAlgebra K (P i) (order' 0) (ht' i))
     (RCN013.originalMixedDegree K order' G H) at hresult
   rw [halg,hbudget] at hresult
   exact hresult
 · letI:IsEmpty I:=⟨fun i=>hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end Family
theorem AAC
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬G∣H)
   (hdegree:∀j:Fin 3,G.degreeOf j<p)
   (hmixed:∀j k:Fin 3,j≠k→
     H.degreeOf j*G.degreeOf k+G.degreeOf j*H.degreeOf k<p):
   ∀(i:Fin 3) (hi:Transcendental K (coordinate K P i)),
     letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P i hi
     FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=by
 intro i hi
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hneq:order 1≠order 2:=by
   intro h
   have heq:=order.injective h
   exact (by decide:(1:Fin 3)≠2) heq
 have hbudget:RCN013.originalMixedDegree K order G H<p:=
   hmixed (order 1) (order 2) hneq
 have hresult:
     letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=by
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=RCN005.rationalBaseAlgebra K P (order 0) ht
   have h:=AGY K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hbudget
   exact ⟨h.1,h.2.1⟩
 change EIJ K P (RCN005.rationalBaseAlgebra K P (order 0) ht) at hresult
 rw [RCN004.rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
end
end RCN004
end SubmissionLower
end ProximityPrize
end PackedLegacy_G9
section PackedLegacy_AV
namespace ProximityPrize
namespace SubmissionLower
namespace RCN001
open RCN002 RCN005 RCN371 RCN007 RCN013 RCN004
open RCN371 renaming RationalPolynomials → KU
noncomputable section
variable (K:Type) [Field K]
section Family
variable {I:Type} [Fintype I] (P:I→Ideal (Original K)) [∀i,(P i).IsPrime]
theorem CLM
   (order:Fin 3 ≃ Fin 3) (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀i,G∈P i) (hHmem:∀i,H∈P i)
   (hproper:¬G∣H)
   (h1:G.degreeOf (order 1)<p) (h2:G.degreeOf (order 2)<p)
   (hmixed:RCN013.originalMixedDegree K order G H<p):
   (∑ i,RCN007.actualCoordinateDegree K (P i) (order 0))≤RCN013.originalMixedDegree K order G H:=by
 classical
 let s:Set I:={i | Transcendental K (coordinate K (P i) (order 0))}
 let D:s→ℕ:=fun i=>
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K (P i)):=
     RCN005.rationalBaseAlgebra K (P i) (order 0) i.2
   Module.finrank (RatFunc K) (RCN002.CoordinateField K (P i))
 have hinj':Function.Injective (fun i:s=>P i):=by
   intro i j h
   apply Subtype.ext
   exact hinj h
 have hbound:(∑ i:s,D i)≤RCN013.originalMixedDegree K order G H:=by
   have h:=BQE K order (fun i:s=>P i)
     (fun i=>i.2) hinj' p G H hG (fun i=>hGmem i) (fun i=>hHmem i)
     hproper h1 h2 hmixed
   exact h.2
 calc
   _=∑ i:s,D i:=by
     apply Finset.sum_congr_set s (fun i=>RCN007.actualCoordinateDegree K (P i) (order 0)) D
     · intro i hi
       exact RCN007.actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
     · intro i hi
       change¬Transcendental K (coordinate K (P i) (order 0)) at hi
       exact dif_neg hi
   _≤_:=hbound
end Family
theorem BLR
   {I:Type} [Fintype I] (P:I→Ideal (Original K)) [∀i,(P i).IsPrime]
   (hinj:Function.Injective P) (j:Fin 3) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀i,G∈P i) (hHmem:∀i,H∈P i)
   (hproper:¬G∣H) (hdegree:∀k:Fin 3,G.degreeOf k<p)
   (hmixed:RCN001.coordinateMixedDegree K G H j<p):
   (∑ i,RCN007.actualCoordinateDegree K (P i) j)≤RCN001.coordinateMixedDegree K G H j:=by
 have h:=CLM K P (Equiv.swap 0 j) hinj p G H
   hG hGmem hHmem hproper (hdegree ((Equiv.swap 0 j) 1))
     (hdegree ((Equiv.swap 0 j) 2)) hmixed
 simpa only [RCN001.coordinateMixedDegree,Equiv.swap_apply_left] using h
end
end RCN001
end SubmissionLower
end ProximityPrize
end PackedLegacy_AV
section PackedLegacy_F
namespace ProximityPrize
namespace SubmissionLower
namespace RCN243
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN319 RCN238 RCN264
open RCN319 renaming specialization → BM
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K→+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def CR (F:MvPolynomial (Fin 4) K):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)
theorem WQ (selected:K→Polynomial K) (γ:K)
   (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (DK φ selected γ) (surfaceMap φ Q)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) Q:=by
 rw [RCN136.eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (DK φ selected γ)=
     RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i<;>rfl
 rw [hv]
theorem KX
   (selected:K→Polynomial K) (Γ Δ:Finset K) (w e:ℕ)
   (hsub:Δ ⊆ Γ) (hno:BL selected Γ w e):
   BL selected Δ w e:=by
 intro P₀ P₁ h₀ h₁
 apply le_trans (Finset.card_le_card ?_) (hno P₀ P₁ h₀ h₁)
 intro γ hγ
 obtain ⟨hΔ,hp⟩:=Finset.mem_filter.mp hγ
 exact Finset.mem_filter.mpr ⟨hsub hΔ,hp⟩
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem CBX
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬G∣T)
   (selected:K→Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι→K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1≤w) (hchar:w<p)
   (hwa:w<a) (han:a≤nodes.card)
   (hGdegree:∀j:Fin 3,G.degreeOf j<p)
   (hcutDegree:∀j k:Fin 3,j≠k→
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k<p)
   (hdegree:∀γ∈Γ,(selected γ).natDegree≤w)
   (hsolution:∀γ∈Γ,RCN319.specialization K (selected γ) γ F=0)
   (hregular:∀γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀γ∈Γ,MvPolynomial.eval (DK φ selected γ) G=0)
   (hTpoint:∀γ∈Γ,MvPolynomial.eval (DK φ selected γ) T=0)
   (hagreement:∀γ∈Γ,
     a≤(nodes.filter (fun i=>(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:BL selected Γ w e)
   (cap budget:Fin 3→ℕ)
   (hcap:∀i∈nodes,∀j,
     (FK φ F w (x i) (u₀ i) (u₁ i)).degreeOf j≤cap j)
   (hbudget:∀i,
     (∑ C:RCN264.RegularComponent Ω G T (CR φ F),
       RCN007.actualCoordinateDegree Ω C.1 i)≤budget i):
   Γ.card*(a-w)≤(nodes.card-w)*(∑ i,cap i*budget i)+
     (e+1)*(a-w)*budget 2:=by
 classical
 let H:=CR φ F
 have hHp:∀γ∈Γ,MvPolynomial.eval (DK φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (DK φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [WQ]
   exact hregular γ hγ
 let degree:RCN264.RegularComponent Ω G T H→Fin 3→ℕ:=
   fun C i=>RCN007.actualCoordinateDegree Ω C.1 i
 have hcomponent:∀C:RCN264.RegularComponent Ω G T H,
     (RCN264.componentSeeds Ω G T H Γ (DK φ selected) C).card*(a-w)≤
       (nodes.card-w)*(∑ i,cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=RCN264.componentSeeds_subset Ω G T H Γ (DK φ selected) C
   have hgmem:=EN Ω G T H C
   have htmem:=GV Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:RCN007.ProjectionsFiniteSeparable Ω C.1:=
     AAC Ω C.1 p G T hG hgmem htmem
       hproper hGdegree hcutDegree
   have hcount:=CQV φ C.1 hproj
     (PU Ω G T H C) F hFmem
     (_Q6 Ω G T H C) selected
     (RCN264.componentSeeds Ω G T H Γ (DK φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ=>hdegree γ (hsub hγ))
     (fun γ hγ=>hsolution γ (hsub hγ))
     (fun γ hγ=>hregular γ (hsub hγ))
     (fun γ hγ=>RCN264.componentSeeds_on_prime Ω G T H Γ (DK φ selected) C γ hγ)
     (fun γ hγ=>hagreement γ (hsub hγ))
     (KX selected Γ _ w e hsub hnoPencil) cap hcap
   exact hcount
 exact AXW Ω G T H Γ (DK φ selected)
   hGpoint hTpoint hHp (a-w) (nodes.card-w) (e+1)
   cap budget degree hcomponent hbudget
theorem BOB
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (p:ℕ) [CharP Ω p] (hG:Irreducible G) (hproper:¬G∣T)
   (hGdegree:∀j:Fin 3,G.degreeOf j<p)
   (hcutDegree:∀j k:Fin 3,j≠k→
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k<p):
   ∀i,(∑ C:RCN264.RegularComponent Ω G T (CR φ F),
     RCN007.actualCoordinateDegree Ω C.1 i)≤RCN001.coordinateMixedDegree Ω G T i:=by
 intro i
 letI:∀C:RCN264.RegularComponent Ω G T (CR φ F),C.1.IsPrime:=
   fun C=>CYY Ω G T (CR φ F) C
 have hneq:(Equiv.swap (0:Fin 3) i) 1≠(Equiv.swap (0:Fin 3) i) 2:=
   (Equiv.swap (0:Fin 3) i).injective.ne (by decide)
 have hmixed:RCN001.coordinateMixedDegree Ω G T i<p:=
   hcutDegree ((Equiv.swap (0:Fin 3) i) 1) ((Equiv.swap (0:Fin 3) i) 2) hneq
 exact BLR Ω
   (fun C:RCN264.RegularComponent Ω G T (CR φ F)=>C.1)
   Subtype.val_injective i p G T hG
   (EN Ω G T (CR φ F))
   (GV Ω G T (CR φ F))
   hproper hGdegree hmixed
theorem COT
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬G∣T)
   (selected:K→Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι→K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1≤w) (hchar:w<p)
   (hwa:w<a) (han:a≤nodes.card)
   (hGdegree:∀j:Fin 3,G.degreeOf j<p)
   (hcutDegree:∀j k:Fin 3,j≠k→
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k<p)
   (hdegree:∀γ∈Γ,(selected γ).natDegree≤w)
   (hsolution:∀γ∈Γ,RCN319.specialization K (selected γ) γ F=0)
   (hregular:∀γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀γ∈Γ,MvPolynomial.eval (DK φ selected γ) G=0)
   (hTpoint:∀γ∈Γ,MvPolynomial.eval (DK φ selected γ) T=0)
   (hagreement:∀γ∈Γ,
     a≤(nodes.filter (fun i=>(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:BL selected Γ w e)
   (cap:Fin 3→ℕ)
   (hcap:∀i∈nodes,∀j,
     (FK φ F w (x i) (u₀ i) (u₁ i)).degreeOf j≤cap j):
   Γ.card*(a-w)≤
     (nodes.card-w)*(∑ i,cap i*RCN001.coordinateMixedDegree Ω G T i)+
     (e+1)*(a-w)*RCN001.coordinateMixedDegree Ω G T 2:=
 CBX φ F G T hG hdiv hproper selected Γ
   nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree hcutDegree
   hdegree hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
   (RCN001.coordinateMixedDegree Ω G T) hcap
   (BOB φ F G T p hG hproper hGdegree hcutDegree)
end
end RCN243
end SubmissionLower
end ProximityPrize
end PackedLegacy_F
section PackedLegacy_AK
namespace ProximityPrize
namespace SubmissionLower
namespace RCN318
open scoped BigOperators
open RCN223 RCN294
namespace TightParameters
def coefficients_p19 (P:RCN318.TightParameters):DegreeVector:=
 ⟨(P.n-P.w)*P.agreement.y,
   (P.n-P.w)*P.agreement.r,
   (P.n-P.w)*P.agreement.z+(P.errors+1)*P.errors⟩
end TightParameters
end RCN318
end SubmissionLower
end ProximityPrize
end PackedLegacy_AK
section PackedLegacy_N5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN260
open scoped BigOperators
open RCN318 RCN223 RCN294
open RCN318 renaming TightParameters → GH
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
structure DG where
 n:ℕ
 w:ℕ
 a:ℕ
 leftY:ℕ
 leftR:ℕ
 leftZ:ℕ
 rightY:ℕ
 rightR:ℕ
 rightZ:ℕ
 deriving DecidableEq
namespace DG
def errors (P:DG):ℕ:=P.n-P.a
def gap (P:DG):ℕ:=P.a-P.w
def KO (P:DG):RCN223.DegreeVector:=
 ⟨1+2*P.w*P.leftY,
   P.w*(2*P.leftR-1),
   2*P.w*P.leftZ+1⟩
def ESE (P:DG):RCN223.DegreeVector:=
 ⟨1+2*P.w*P.rightY,
   P.w*(2*P.rightR-1),
   2*P.w*P.rightZ+1⟩
def agreement (P:DG):RCN223.DegreeVector:=
 ⟨max P.KO.y P.ESE.y,
   max P.KO.r P.ESE.r,
   max P.KO.z P.ESE.z⟩
def mixedCost (P:DG):RCN223.DegreeVector:=
 ⟨P.leftR*P.rightZ+P.leftZ*P.rightR,
   P.leftY*P.rightZ+P.leftZ*P.rightY,
   P.leftY*P.rightR+P.leftR*P.rightY⟩
end DG
end RCN260
end SubmissionLower
end ProximityPrize
end PackedLegacy_N5
section PackedLegacy_EK
namespace ProximityPrize
namespace SubmissionLower
namespace RCN135
open RCN077 RCN269 RCN233 RCN231 RCN229 RCN139 RCN313 RCN319
open RCN319 renaming specialization → BM
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable (K:Type*) [Field K]
@[simp] theorem initialPoint_X (P:Polynomial K) (γ:K):
   initialPoint K P γ 0=RCN135.initialCoordinate K:=rfl
@[simp] theorem initialPoint_Z (P:Polynomial K) (γ:K):
   initialPoint K P γ 3=RCN135.coefficientEmbedding K γ:=rfl
end
end RCN135
end SubmissionLower
end ProximityPrize
end PackedLegacy_EK
section PackedLegacy_Y4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN068
open scoped Classical
open RCN051 RCN313 RCN136 RCN174 RCN231 RCN238
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def HasCaps_p19 (Q:MvPolynomial (Fin 3) Ω) (v:DegreeVector):Prop:=
 ∀i,Q.degreeOf i≤capAt v i
variable (φ:Polynomial K→+*Ω)
def GAG (F:MvPolynomial (Fin 4) K) (w:ℕ):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (numerator K F (w+1))
theorem BHT
   (F:MvPolynomial (Fin 4) K) (ell s L:ℕ) (hs:1≤s)
   (hY:F.degreeOf 1≤ell) (hR:F.degreeOf 2≤s) (hZ:F.degreeOf 3≤L)
   (w:ℕ) (c:ℕ→K) (x u₀ u₁:K):
   HasCaps_p19 (surfaceMap φ (RCN313.agreementNumerator F w c x u₀ u₁))
     (RCN068.agreementCaps ell s L w):=by
 obtain ⟨hy,hr,hz⟩:=RCN313.agreementNumerator_degree_bounds F ell s L hs hY hR hZ w c x u₀ u₁
 intro i
 fin_cases i
 · exact (RCN136.surfaceMap_degreeOf_le φ _ 0).trans hy
 · exact (RCN136.surfaceMap_degreeOf_le φ _ 1).trans hr
 · exact (RCN136.surfaceMap_degreeOf_le φ _ 2).trans hz
theorem ETM
   (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree≤w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (DK φ selected γ) (GAG φ F w)=0:=by
 change MvPolynomial.eval (DK φ selected γ)
   (surfaceMap φ (numerator K F (w+1)))=0
 rw [RCN136.eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (DK φ selected γ)=
     RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i<;>rfl
 rw [hv]
 exact RCN231.polynomialPoint_numerator_zero (φ.comp Polynomial.C) F (selected γ) γ
   (φ Polynomial.X) hsolution (w+1) (Nat.lt_succ_of_le hdegree)
section MixedGates
variable (G T:MvPolynomial (Fin 3) Ω) (g t:DegreeVector)
theorem FAX (hG:HasCaps_p19 G g) (hT:HasCaps_p19 T t) (j k:Fin 3):
   T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k≤
     capAt t j*capAt g k+capAt g j*capAt t k:=
 Nat.add_le_add (Nat.mul_le_mul (hT j) (hG k)) (Nat.mul_le_mul (hG j) (hT k))
theorem ENJ (p:ℕ)
   (hY:mixed g t unitY<p) (hR:mixed g t unitR<p) (hZ:mixed g t unitZ<p):
   ∀j k:Fin 3,j≠k→
     capAt t j*capAt g k+capAt g j*capAt t k<p:=by
 intro j k hne
 fin_cases j<;>fin_cases k
 all_goals try exact (hne rfl).elim
 all_goals first
   | simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
   | simpa [capAt,mixed,unitR,Nat.mul_comm,Nat.add_comm] using hR
   | simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem APW (p:ℕ)
   (hG:HasCaps_p19 G g) (hT:HasCaps_p19 T t)
   (hg:∀j,capAt g j<p)
   (hY:mixed g t unitY<p) (hR:mixed g t unitR<p) (hZ:mixed g t unitZ<p):
   (∀j,G.degreeOf j<p)∧
     ∀j k:Fin 3,j≠k→
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k<p:=by
 refine ⟨fun j↦(hG j).trans_lt (hg j),?_⟩
 intro j k hjk
 exact (FAX G T g t hG hT j k).trans_lt
   (ENJ g t p hY hR hZ j k hjk)
end MixedGates
end
end RCN068
end SubmissionLower
end ProximityPrize
end PackedLegacy_Y4
section PackedLegacy_BV
namespace ProximityPrize
namespace SubmissionLower
namespace RCN170
open scoped Classical BigOperators
open RCN051 RCN068 RCN169 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem XH
   (selected:K→Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) selected γ)
     (surfaceMap (RCN135.polynomialEmbedding K) F)=
       RCN135.polynomialEmbedding K (RCN319.specialization K (selected γ) γ F):=by
 rw [WQ]
 exact RCN135.evaluation_at_initialPoint K (selected γ) γ F
end
end RCN170
end SubmissionLower
end ProximityPrize
end PackedLegacy_BV
section PackedLegacy_DB
namespace ProximityPrize
namespace SubmissionLower
open Polynomial Polynomial.Bivariate Matrix
open scoped BigOperators
variable {F:Type} [Field F]
theorem CRX
   {ι:Type} [Fintype ι] [DecidableEq ι]
   (M:Matrix ι ι F[X]) {N:ℕ}
   (h:∀σ:Equiv.Perm ι,(∏ i:ι,M (σ i) i).natDegree≤N):
   M.det.natDegree≤N:=by
 classical
 rw [Matrix.det_apply']
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro σ _
 exact (Polynomial.natDegree_C_mul_le
   ((Equiv.Perm.sign σ:ℤ):F) (∏ i:ι,M (σ i) i)).trans (h σ)
theorem BNX
   (B H:F[X][Y]) (n m:ℕ):
   (Polynomial.resultant B H n m).natDegree≤
     m*totalDegree B+n*totalDegree H-m*n:=by
 classical
 let M:Matrix (Fin (n+m)) (Fin (n+m)) F[X]:=
   Polynomial.sylvester B H n m
 rw [Polynomial.resultant]
 change M.det.natDegree≤_
 apply CRX (M:=M)
 intro σ
 by_cases hzero:∃i:Fin (n+m),M (σ i) i=0
 · rcases hzero with ⟨i,hi⟩
   have hprod:(∏ i:Fin (n+m),M (σ i) i)=0:=
     Finset.prod_eq_zero (Finset.mem_univ i) hi
   simp [hprod]
 · have hne (i:Fin (n+m)):M (σ i) i≠0:=by
     intro hi
     exact hzero ⟨i,hi⟩
   let lidx:Fin n→ℕ:=fun j=>
     ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)
   let ridx:Fin m→ℕ:=fun j=>
     ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)
   let ldeg:Fin n→ℕ:=fun j=>
     (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree
   let rdeg:Fin m→ℕ:=fun j=>
     (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree
   have hleft_Icc (j:Fin n):
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+m)
         then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.castAdd m j) (by simp [hentry,hc])
   have hright_Icc (j:Fin m):
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+n)
         then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.natAdd n j) (by simp [hentry,hc])
   have hleft (j:Fin n):lidx j+ldeg j≤totalDegree H:=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
           if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+m)
           then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hleft_Icc j)]
     have hcoeff:H.coeff (lidx j)≠0:=by
       have hh:=hne (Fin.castAdd m j)
       rw [hentry] at hh
       simpa only [lidx] using hh
     have hsupp:lidx j∈H.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:ldeg j=(H.coeff (lidx j)).natDegree:=by
       dsimp [ldeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le H hsupp
   have hright (j:Fin m):ridx j+rdeg j≤totalDegree B:=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
           if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+n)
           then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hright_Icc j)]
     have hcoeff:B.coeff (ridx j)≠0:=by
       have hh:=hne (Fin.natAdd n j)
       rw [hentry] at hh
       simpa only [ridx] using hh
     have hsupp:ridx j∈B.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:rdeg j=(B.coeff (ridx j)).natDegree:=by
       dsimp [rdeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le B hsupp
   have hleft_sum:
       (∑ j:Fin n,(lidx j+ldeg j))≤n*totalDegree H:=by
     calc
       _≤ ∑ _j:Fin n,totalDegree H:=
         Finset.sum_le_sum (fun j _=>hleft j)
       _=n*totalDegree H:=by simp
   have hright_sum:
       (∑ j:Fin m,(ridx j+rdeg j))≤m*totalDegree B:=by
     calc
       _≤ ∑ _j:Fin m,totalDegree B:=
         Finset.sum_le_sum (fun j _=>hright j)
       _=m*totalDegree B:=by simp
   have hidxsum:
       (∑ j:Fin n,lidx j)+(∑ j:Fin m,ridx j)=m*n:=by
     have hleft_row (j:Fin n):
         ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)=(j:ℕ)+lidx j:=by
       dsimp [lidx]
       have hle:=(Set.mem_Icc.mp (hleft_Icc j)).1
       omega
     have hright_row (j:Fin m):
         ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)=(j:ℕ)+ridx j:=by
       dsimp [ridx]
       have hle:=(Set.mem_Icc.mp (hright_Icc j)).1
       omega
     have hsum_left_rows:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin n,lidx j):=by
       calc
         _=∑ j:Fin n,((j:ℕ)+lidx j):=
           Finset.sum_congr rfl (fun j _=>hleft_row j)
         _=_:=Finset.sum_add_distrib
     have hsum_right_rows:
         (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin m,(j:ℕ))+(∑ j:Fin m,ridx j):=by
       calc
         _=∑ j:Fin m,((j:ℕ)+ridx j):=
           Finset.sum_congr rfl (fun j _=>hright_row j)
         _=_:=Finset.sum_add_distrib
     have hperm_sum:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           ∑ i:Fin (n+m),(i:ℕ):=by
       simpa using (Equiv.sum_comp σ (fun i:Fin (n+m)=>(i:ℕ)))
     have hrows_split:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ)):=by
       simpa using (Fin.sum_univ_add
         (fun i:Fin (n+m)=>((σ i:Fin (n+m)):ℕ)))
     have hcols_split:
         (∑ i:Fin (n+m),(i:ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin m,(n+(j:ℕ))):=by
       simpa using (Fin.sum_univ_add (fun i:Fin (n+m)=>(i:ℕ)))
     have hright_cols:
         (∑ j:Fin m,(n+(j:ℕ)))=
           m*n+∑ j:Fin m,(j:ℕ):=by
       simp [Finset.sum_add_distrib,Finset.sum_const]
     have hmain:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+
             (m*n+∑ j:Fin m,(j:ℕ)):=by
       rw [←hrows_split,hperm_sum,hcols_split,hright_cols]
     omega
   have hsum:
       ((∑ j:Fin n,lidx j)+(∑ j:Fin n,ldeg j))+
           ((∑ j:Fin m,ridx j)+(∑ j:Fin m,rdeg j))≤
         n*totalDegree H+m*totalDegree B:=by
     simpa only [Finset.sum_add_distrib] using Nat.add_le_add hleft_sum hright_sum
   have hdeg_parts:
       (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j)≤
         m*totalDegree B+n*totalDegree H-m*n:=by
     omega
   have hsum_deg_split:
       (∑ i:Fin (n+m),(M (σ i) i).natDegree)=
         (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=by
     simpa only [ldeg,rdeg] using
       (Fin.sum_univ_add (fun i:Fin (n+m)=>(M (σ i) i).natDegree))
   calc
     (∏ i:Fin (n+m),M (σ i) i).natDegree≤
         ∑ i:Fin (n+m),(M (σ i) i).natDegree:=by
       simpa using Polynomial.natDegree_prod_le Finset.univ
         (fun i:Fin (n+m)=>M (σ i) i)
     _=(∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=hsum_deg_split
     _≤_:=hdeg_parts
end SubmissionLower
end ProximityPrize
end PackedLegacy_DB
section PackedLegacy_AY
namespace ProximityPrize
namespace SubmissionLower
namespace RCN012
open Polynomial Polynomial.Bivariate RCN002 RCN005 RCN371 RCN011 RCN009 RCN013
open RCN371 renaming RationalPolynomials → KU
noncomputable section
variable {A:Type} [Field A]
variable (K:Type) [Field K]
theorem BQF
   (B H:A[X][Y]) (n mCap totalB totalH cap:ℕ)
   (hHne:H≠0) (hBouter:B.natDegree≤n)
   (hHouter:H.natDegree≤mCap)
   (hBtotal:totalDegree B≤totalB)
   (hHtotal:totalDegree H≤totalH)
   (hbudget:∀m,m≤mCap→
     m*totalB+n*totalH-m*n≤cap):
   (Polynomial.resultant B H).natDegree≤cap:=by
 by_cases hres:Polynomial.resultant B H=0
 · simp [hres]
 · have hfixed:=BNX
     B H n H.natDegree
   have hdegreeCap:
       H.natDegree*totalDegree B+n*totalDegree H-H.natDegree*n≤
         H.natDegree*totalB+n*totalH-H.natDegree*n:=by
     exact Nat.sub_le_sub_right
       (Nat.add_le_add (Nat.mul_le_mul_left H.natDegree hBtotal)
         (Nat.mul_le_mul_left n hHtotal)) _
   have hfixedCap:
       (Polynomial.resultant B H n H.natDegree).natDegree≤cap:=
     hfixed.trans (hdegreeCap.trans (hbudget H.natDegree hHouter))
   have hcoeff:H.coeff H.natDegree≠0:=by
     rw [Polynomial.coeff_natDegree]
     exact Polynomial.leadingCoeff_ne_zero.mpr hHne
   let factor:A[X]:=
     (-1)^(H.natDegree*(n-B.natDegree))*
       H.coeff H.natDegree^(n-B.natDegree)
   have hfactor:factor≠0:=by
     apply _root_.mul_ne_zero
     · exact pow_ne_zero _ (by norm_num)
     · exact pow_ne_zero _ hcoeff
   have hpad:=Polynomial.resultant_add_left_deg
     (f:=B) (g:=H) (m:=B.natDegree)
     (k:=n-B.natDegree) (n:=H.natDegree) le_rfl
   have hsum:B.natDegree+(n-B.natDegree)=n:=
     Nat.add_sub_of_le hBouter
   rw [hsum] at hpad
   change Polynomial.resultant B H n H.natDegree=
     factor*Polynomial.resultant B H at hpad
   calc
     (Polynomial.resultant B H).natDegree≤
         (factor*Polynomial.resultant B H).natDegree:=by
       rw [Polynomial.natDegree_mul hfactor hres]
       omega
     _=(Polynomial.resultant B H n H.natDegree).natDegree:=by rw [hpad]
     _≤cap:=hfixedCap
theorem XY
   (order:Fin 3 ≃ Fin 3) (G T:Original K)
   (n mCap totalG totalT cap:ℕ) (hTne:T≠0)
   (hGouter:(planeMap K order G).natDegree≤n)
   (hTouter:(planeMap K order T).natDegree≤mCap)
   (hGsupport:∀d∈(rationalMap K order G).support,
     d 0+d 1≤totalG)
   (hTsupport:∀d∈(rationalMap K order T).support,
     d 0+d 1≤totalT)
   (hbudget:∀m,m≤mCap→
     m*totalG+n*totalT-m*n≤cap):
   (Polynomial.resultant (planeMap K order G)
     (planeMap K order T)).natDegree≤cap:=by
 apply BQF
   (planeMap K order G) (planeMap K order T)
     n mCap totalG totalT cap
 · intro hzero
   apply hTne
   apply RCN011.planeMap_injective K order
   simpa only [map_zero] using hzero
 · exact hGouter
 · exact hTouter
 · exact RCN012.planeMap_totalDegree_le_of_rational_support
     K order G totalG hGsupport
 · exact RCN012.planeMap_totalDegree_le_of_rational_support
     K order T totalT hTsupport
 · exact hbudget
end
end RCN012
end SubmissionLower
end ProximityPrize
end PackedLegacy_AY
section PackedLegacy_Y
namespace ProximityPrize
namespace SubmissionLower
namespace RCN003
open RCN002 RCN005 RCN371 RCN011 RCN009 RCN013 RCN010 RCN004 RCN007 RCN001
open RCN371 renaming RationalPolynomials → KU
open RCN012
noncomputable section
variable (K:Type) [Field K]
def EIJ (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (RCN002.CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P)
theorem RH
   (P:Ideal (Original K)) [P.IsPrime] (i:Fin 3)
   (hi:Transcendental K (coordinate K P i))
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P)
   (hproper:¬G∣H) (hdegree:∀j:Fin 3,G.degreeOf j<p)
   (hmixed:RCN001.coordinateMixedDegree K G H i<p):
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
     RCN005.rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=by
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hresult:
     letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
       RCN005.rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=by
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
     RCN005.rationalBaseAlgebra K P (order 0) ht
   have h:=AGY K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hmixed
   exact ⟨h.1,h.2.1⟩
 change EIJ K P (RCN005.rationalBaseAlgebra K P (order 0) ht) at hresult
 change EIJ K P (RCN005.rationalBaseAlgebra K P i hi)
 rw [RCN004.rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
end
end RCN003
end SubmissionLower
end ProximityPrize
end PackedLegacy_Y
section PackedLegacy_Z9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN222
open scoped Classical BigOperators
open RCN051 RCN068 RCN135 RCN136 RCN138 RCN137 RCN267 RCN081 RCN238 RCN243 RCN231 RCN174 RCN319
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
noncomputable section
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
theorem DRT (selected:K→Polynomial K) (γ:K):
   DK (RCN135.polynomialEmbedding K) selected γ=
     fun i:Fin 3=>initialPoint K (selected γ) γ i.succ:=rfl
theorem UM
   (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K) (γ:K):
   MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) selected γ)
     (surfaceMap (RCN135.polynomialEmbedding K) F)=
       RCN135.polynomialEmbedding K (RCN319.specialization K (selected γ) γ F):=by
 rw [DRT]
 simpa only [RCN138.canonical_geometricSurfaceMap] using
   RCN138.eval_at_actual_generic_initial_point K (selected γ) γ F
def KK (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K)
   (Γ:Finset K) (g:RCN222.GeometricFactor K F):Finset K:=by
 classical
 exact Γ.filter (fun γ=>
   MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) selected γ) g.1=0)
theorem WK
   (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K)
   (Γ:Finset K) (g:RCN222.GeometricFactor K F):KK K F selected Γ g ⊆ Γ:=by
 classical
 exact Finset.filter_subset _ _
theorem AAD
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (selected:K→Polynomial K) (Γ:Finset K)
   (hsolutions:∀γ∈Γ,RCN319.specialization K (selected γ) γ F=0):
   Γ.card≤ ∑ g:RCN222.GeometricFactor K F,(KK K F selected Γ g).card:=by
 classical
 have hcover:Γ ⊆ Finset.univ.biUnion (KK K F selected Γ):=by
   intro γ hγ
   have hz:MvPolynomial.eval (DK (RCN135.polynomialEmbedding K) selected γ)
       (surfaceMap (RCN135.polynomialEmbedding K) F)=0:=by
     rw [UM,hsolutions γ hγ,map_zero]
   obtain ⟨g,hg,hzg⟩:=RCN137.exists_surfaceFactor_zero (RCN135.polynomialEmbedding K)
     (RCN135.polynomialEmbedding_injective K) F hF
     (DK (RCN135.polynomialEmbedding K) selected γ) hz
   exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
     Finset.mem_filter.mpr ⟨hγ,hzg⟩⟩
 exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
end
end RCN222
end SubmissionLower
end ProximityPrize
end PackedLegacy_Z9
section PackedLegacy_DW
namespace ProximityPrize
namespace SubmissionLower
namespace RCN052
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001
open RCN318 renaming TightParameters → GH
open RCN082 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
open RCN222 renaming GeometricFactor → EX
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def OX (P:DG)
   (F:MvPolynomial (Fin 4) K):RCN223.DegreeVector:=
 ⟨F.degreeOf 2*P.rightZ+F.degreeOf 3*P.rightR,
   F.degreeOf 1*P.rightZ+F.degreeOf 3*P.rightY,
   F.degreeOf 1*P.rightR+F.degreeOf 2*P.rightY⟩
def regularCapAt (v:RCN223.DegreeVector):Fin 3→ℕ:=
 ![v.y,v.r,v.z]
theorem ABX
   (P:DG) (F T:MvPolynomial (Fin 4) K) (hF:F≠0)
   (hTY:T.degreeOf 1≤P.rightY) (hTR:T.degreeOf 2≤P.rightR)
   (hTZ:T.degreeOf 3≤P.rightZ) (i:Fin 3):
   (∑ g:RCN222.GeometricFactor K F,
     RCN001.coordinateMixedDegree (GenericField K) g.1
       (surfaceMap (RCN135.polynomialEmbedding K) T) i)≤
     regularCapAt (OX P F) i:=by
 classical
 have hsum (j:Fin 3):
     (∑ g:RCN222.GeometricFactor K F,g.1.degreeOf j)≤F.degreeOf j.succ:=
   RCN222.geometricFactor_sum_degree_le K F hF j
 have hsum0:(∑ g:RCN222.GeometricFactor K F,g.1.degreeOf 0)≤F.degreeOf 1:=by
   simpa using hsum 0
 have hsum1:(∑ g:RCN222.GeometricFactor K F,g.1.degreeOf 1)≤F.degreeOf 2:=by
   simpa using hsum 1
 have hsum2:(∑ g:RCN222.GeometricFactor K F,g.1.degreeOf 2)≤F.degreeOf 3:=by
   have h:=hsum 2
   rw [show (2:Fin 3).succ=(3:Fin 4) by decide] at h
   exact h
 have hT0:(surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 0≤P.rightY:=
   (RCN136.surfaceMap_degreeOf_le (RCN135.polynomialEmbedding K) T 0).trans hTY
 have hT1:(surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 1≤P.rightR:=
   (RCN136.surfaceMap_degreeOf_le (RCN135.polynomialEmbedding K) T 1).trans hTR
 have hT2:(surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 2≤P.rightZ:=
   (RCN136.surfaceMap_degreeOf_le (RCN135.polynomialEmbedding K) T 2).trans hTZ
 have hi:i=0∨i=1∨i=2:=by omega
 rcases hi with rfl | rfl | rfl
 · change (∑ geom:RCN222.GeometricFactor K F,
       ((surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 1*geom.1.degreeOf 2+
         geom.1.degreeOf 1*(surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 2))≤
       F.degreeOf 2*P.rightZ+F.degreeOf 3*P.rightR
   rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT1 hsum2)
       (Nat.mul_le_mul hsum1 hT2)
 · change (∑ geom:RCN222.GeometricFactor K F,
       ((surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 0*geom.1.degreeOf 2+
         geom.1.degreeOf 0*(surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 2))≤
       F.degreeOf 1*P.rightZ+F.degreeOf 3*P.rightY
   rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT0 hsum2)
       (Nat.mul_le_mul hsum0 hT2)
 · simp only [RCN001.coordinateMixedDegree_two,
     regularCapAt,OX,Matrix.cons_val_two]
   change (∑ geom:RCN222.GeometricFactor K F,
       ((surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 0*geom.1.degreeOf 1+
         geom.1.degreeOf 0*(surfaceMap (RCN135.polynomialEmbedding K) T).degreeOf 1))≤
       F.degreeOf 1*P.rightR+F.degreeOf 2*P.rightY
   rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT0 hsum1)
       (Nat.mul_le_mul hsum0 hT1)
end
end RCN052
end SubmissionLower
end ProximityPrize
end PackedLegacy_DW
section PackedLegacy_Z4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN140
open scoped Classical BigOperators
open RCN223 RCN286 RCN167 RCN174 RCN319 RCN081 RCN266 RCN291 RCN238
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def regularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K→Polynomial K) (Gamma:Finset K)
   (F:RCN266.RegularIndex Q):Finset K:=
 Gamma.filter (fun gamma↦RCN286.RegularSolution F.1 (selected gamma) gamma)
theorem ACS (Q:MvPolynomial (Fin 4) K)
   (selected:K→Polynomial K) (Gamma:Finset K)
   (F:RCN266.RegularIndex Q):
   regularSeeds Q selected Gamma F ⊆ Gamma:=
 Finset.filter_subset _ _
end
end RCN140
end SubmissionLower
end ProximityPrize
end PackedLegacy_Z4
section PackedLegacy_BC
namespace ProximityPrize
namespace SubmissionLower
namespace RCN119
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]
def DVY (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X i
def ERA (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0-MvPolynomial.X 1 else MvPolynomial.X i
def shiftPlus_p19:Poly K→ₐ[K] Poly K:=MvPolynomial.aeval (DVY K)
def shiftMinus_p19:Poly K→ₐ[K] Poly K:=MvPolynomial.aeval (ERA K)
theorem EIS:
   (shiftMinus_p19 K).comp (shiftPlus_p19 K)=AlgHom.id K (Poly K):=by
 ext i
 fin_cases i<;>simp [shiftPlus_p19,shiftMinus_p19,DVY,ERA]
@[simp] theorem FDZ (f:Poly K):
   shiftMinus_p19 K (shiftPlus_p19 K f)=f:=
 DFunLike.congr_fun (EIS K) f
@[simp] theorem shiftPlus_slopeDifference_p19:
   shiftPlus_p19 K (RCN119.slopeDifference K)=MvPolynomial.X 0:=by
 simp [RCN119.slopeDifference,shiftPlus_p19,DVY]
@[simp] theorem FRG:
   shiftMinus_p19 K (MvPolynomial.X 0)=RCN119.slopeDifference K:=by
 simp [shiftMinus_p19,ERA,RCN119.slopeDifference]
def contactJet_p19 (h:ℕ):Poly K→ₗ[K] Poly K:=
 (RCN119.monomialRemainder K (Finsupp.single 0 h)).comp (shiftPlus_p19 K).toLinearMap
def XZ (i j z:ℕ):Fin 3→₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j+Finsupp.single 2 z
@[simp] theorem BIA (i j z:ℕ):
   XZ i j z 0=i:=by simp [XZ]
@[simp] theorem CMO (i j z:ℕ):
   XZ i j z 1=j:=by simp [XZ]
@[simp] theorem CMR (i j z:ℕ):
   XZ i j z 2=z:=by simp [XZ]
theorem DLO (d:Fin 3→₀ ℕ):
   XZ (d 0) (d 1) (d 2)=d:=by
 ext i
 fin_cases i<;>simp
theorem EWN
   {n:ℕ} {a b:Fin n→ℕ}
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
def BHO (M L s:ℕ):
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
       change d.val 2<L+1-d.val 0-d.val 1
       omega⟩⟩⟩
 invFun q:=
   ⟨XZ q.1.val q.2.1.val q.2.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.1.isLt
     have hz:=q.2.2.isLt
     simp only [boxExponents,Set.mem_setOf_eq,BIA,
       CMO,CMR]
     omega⟩
 left_inv d:=Subtype.ext (DLO d.val)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨⟨j,hj⟩,⟨z,hz⟩⟩⟩
   apply Sigma.ext
   · apply Fin.ext
     exact BIA i j z
   · dsimp only
     apply @EWN (s+1)
       (fun k↦L+1-(XZ i j z) 0-k.val)
       (fun k↦L+1-i-k.val) _ _ _ _
     · funext k
       simp only [BIA]
     · exact CMO i j z
     · exact CMR i j z
instance FHH (M L s:ℕ):Fintype (boxExponents M L s):=
 Fintype.ofEquiv (BoxIndex M L s) (BHO M L s).symm
def blockJet_p19 (M L s h:ℕ):RCN119.coefficientBox K M L s→ₗ[K] Poly K:=
 (contactJet_p19 K h).comp (RCN119.coefficientBox K M L s).subtype
end
end RCN119
end SubmissionLower
end ProximityPrize
end PackedLegacy_BC
section PackedLegacy_C1
namespace ProximityPrize
namespace SubmissionLower
namespace RCN100
open RCN119 ProximityPrize.Benchmark
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
@[simp] theorem ECW (D w L s:ℕ):
   reconstruct K D w L s (0:RCN100.CoefficientIndex D w L s→K)=0:=by
 simp [reconstruct]
abbrev LocalTarget_p19 (m L s:ℕ):=
 (r:Fin m)→LinearMap.range
   (blockJet_p19 K (min r.val L) L s (m-r.val))
abbrev GlobalTarget_p19 (I:Type*) (m L s:ℕ):=I→LocalTarget_p19 K m L s
def AMB {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I→K):
   (RCN100.CoefficientIndex D w L s→K)→ₗ[K] GlobalTarget_p19 K I m L s:=
 LinearMap.pi fun i=>LinearMap.pi fun r=>
   (blockJet_p19 K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val)
end
end RCN100
end SubmissionLower
end ProximityPrize
end PackedLegacy_C1
section PackedLegacy_X3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN372
open scoped Classical BigOperators
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3_p19 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def shearImage (a:K) (i:Fin 3):Poly3_p19 K:=
 ![MvPolynomial.X 0,
   MvPolynomial.X 1-MvPolynomial.C a*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def unshearImage (a:K) (i:Fin 3):Poly3_p19 K:=
 ![MvPolynomial.X 0,
   MvPolynomial.X 1+MvPolynomial.C a*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def shearAlgHom (a:K):Poly3_p19 K→ₐ[K] Poly3_p19 K:=
 MvPolynomial.aeval (shearImage a)
def DUM (a:K):Poly3_p19 K→ₐ[K] Poly3_p19 K:=
 MvPolynomial.aeval (unshearImage a)
theorem FNV (a:K):
   (DUM a).comp (shearAlgHom a)=AlgHom.id K (Poly3_p19 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i<;>simp [shearImage,unshearImage,shearAlgHom,DUM]<;>ring
theorem FMX (a:K):
   (shearAlgHom a).comp (DUM a)=AlgHom.id K (Poly3_p19 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i<;>simp [shearImage,unshearImage,shearAlgHom,DUM]<;>ring
def shearEquiv (a:K):Poly3_p19 K ≃ₐ[K] Poly3_p19 K:=
 AlgEquiv.ofAlgHom (shearAlgHom a) (DUM a)
   (FMX a) (FNV a)
@[simp] theorem shearEquiv_apply (a:K) (F:Poly3_p19 K):
   shearEquiv a F=shearAlgHom a F:=rfl
section WeightedDegree
def weightEmbed_p19 (weights:Fin 3→ℕ):(Fin 3→₀ ℕ)→+(Fin 4→₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i<;>simp [Finsupp.add_apply,map_add]
theorem CVF (weights:Fin 3→ℕ) (d:Fin 3→₀ ℕ) (i:Fin 3):
   weightEmbed_p19 weights d i.castSucc=d i:=by
 fin_cases i<;>simp [weightEmbed_p19]
theorem EDV (weights:Fin 3→ℕ) (d:Fin 3→₀ ℕ):
   weightEmbed_p19 weights d (3:Fin 4)=Finsupp.weight weights d:=by
 simp [weightEmbed_p19]
theorem AJC (weights:Fin 3→ℕ):
   Function.Injective (weightEmbed_p19 weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun b:Fin 4→₀ ℕ↦b i.castSucc) h
 simpa only [CVF] using hi
def weightedLift_p19 (weights:Fin 3→ℕ):Poly3_p19 K→+*MvPolynomial (Fin 4) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed_p19 weights)
theorem CVA (weights:Fin 3→ℕ) (F:Poly3_p19 K):
   (weightedLift_p19 weights F).support=F.support.image (weightEmbed_p19 weights):=by
 change (Finsupp.mapDomain (weightEmbed_p19 weights) (AddMonoidAlgebra.coeff F)).support=
   Finset.image (weightEmbed_p19 weights) (AddMonoidAlgebra.coeff F).support
 exact Finsupp.mapDomain_support_of_injective (AJC weights) _
theorem KD (weights:Fin 3→ℕ) (F:Poly3_p19 K):
   (weightedLift_p19 weights F).degreeOf (3:Fin 4)=
     MvPolynomial.weightedTotalDegree weights F:=by
 change (weightedLift_p19 weights F).degreeOf (3:Fin 4)=
   F.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,CVA,Finset.sup_image]
 apply congrArg (fun f:(Fin 3→₀ ℕ)→ℕ↦F.support.sup f)
 funext d
 exact EDV weights d
def wt_p19 (weights:Fin 3→ℕ) (F:Poly3_p19 K):ℕ:=
 MvPolynomial.weightedTotalDegree weights F
theorem wt_mul_le_p19 (weights:Fin 3→ℕ) (F G:Poly3_p19 K):
   wt_p19 weights (F*G)≤wt_p19 weights F+wt_p19 weights G:=by
 unfold wt_p19
 rw [←KD,map_mul]
 simpa only [KD] using
   MvPolynomial.degreeOf_mul_le (3:Fin 4)
     (weightedLift_p19 weights F) (weightedLift_p19 weights G)
theorem wt_sub_le_p19 (weights:Fin 3→ℕ) (F G:Poly3_p19 K):
   wt_p19 weights (F-G)≤max (wt_p19 weights F) (wt_p19 weights G):=by
 unfold wt_p19
 rw [←KD,map_sub]
 simpa only [KD] using
   MvPolynomial.degreeOf_sub_le (3:Fin 4)
     (weightedLift_p19 weights F) (weightedLift_p19 weights G)
theorem wt_pow_le_p19 (weights:Fin 3→ℕ) (F:Poly3_p19 K) (n:ℕ):
   wt_p19 weights (F^n)≤n*wt_p19 weights F:=by
 unfold wt_p19
 rw [←KD,map_pow]
 simpa only [KD] using
   MvPolynomial.degreeOf_pow_le (3:Fin 4) (weightedLift_p19 weights F) n
theorem wt_C_p19 (weights:Fin 3→ℕ) (c:K):
   wt_p19 weights (MvPolynomial.C c:Poly3_p19 K)=0:=by
 unfold wt_p19 MvPolynomial.weightedTotalDegree
 simp
theorem wt_X_p19 (weights:Fin 3→ℕ) (i:Fin 3):
   wt_p19 weights (MvPolynomial.X i:Poly3_p19 K)=weights i:=by
 unfold wt_p19 MvPolynomial.weightedTotalDegree
 simp [MvPolynomial.support_X,Finsupp.weight_single]
theorem FCX {ι:Type*} [DecidableEq ι]
   (weights:Fin 3→ℕ) (I:Finset ι) (f:ι→Poly3_p19 K):
   wt_p19 weights (∏ i∈I,f i)≤ ∑ i∈I,wt_p19 weights (f i):=by
 induction I using Finset.induction_on with
 | empty=>simp [wt_p19,MvPolynomial.weightedTotalDegree]
 | @insert i I hi ih=>
     simp only [Finset.prod_insert hi,Finset.sum_insert hi]
     exact (wt_mul_le_p19 weights (f i) (∏ j∈I,f j)).trans
       (Nat.add_le_add le_rfl ih)
theorem CLG {ι:Type*} [DecidableEq ι]
   (weights:Fin 3→ℕ) (I:Finset ι) (f:ι→Poly3_p19 K) (cap:ℕ)
   (hf:∀i∈I,wt_p19 weights (f i)≤cap):
   wt_p19 weights (∑ i∈I,f i)≤cap:=by
 unfold wt_p19
 rw [←KD,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (3:Fin 4) I
   (fun i↦weightedLift_p19 weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [KD]
 exact hf i hi
theorem weight_fin3_p19 (weights:Fin 3→ℕ) (d:Fin 3→₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i<;>simp
 rw [hd,map_add,map_add]
 simp [Finsupp.weight_single,Nat.mul_comm]
end WeightedDegree
end
end RCN372
end SubmissionLower
end ProximityPrize
end PackedLegacy_X3
section PackedLegacy_Z3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN125
open scoped Classical BigOperators
open RCN095 RCN372 RCN003 RCN002 RCN011 RCN371 RCN012 RCN013
open RCN095 renaming PolynomialInFlag → BI
open RCN371 renaming RationalPolynomials → KU
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3_p19 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def flagImage_p19 (lam μ ν:K) (i:Fin 3):Poly3_p19 K:=
 ![MvPolynomial.X 0-MvPolynomial.C lam*MvPolynomial.X 2,
   MvPolynomial.X 1-
     (MvPolynomial.C μ*MvPolynomial.X 0-
       MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2),
   MvPolynomial.X 2] i
def unflagImage_p19 (lam μ ν:K) (i:Fin 3):Poly3_p19 K:=
 ![MvPolynomial.X 0+MvPolynomial.C lam*MvPolynomial.X 2,
   MvPolynomial.X 1+MvPolynomial.C μ*MvPolynomial.X 0+
     MvPolynomial.C ν*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def flagAlgHom_p19 (lam μ ν:K):Poly3_p19 K→ₐ[K] Poly3_p19 K:=
 MvPolynomial.aeval (flagImage_p19 lam μ ν)
def unflagAlgHom_p19 (lam μ ν:K):Poly3_p19 K→ₐ[K] Poly3_p19 K:=
 MvPolynomial.aeval (unflagImage_p19 lam μ ν)
@[simp] theorem flagAlgHom_X_p19 (lam μ ν:K) (i:Fin 3):
   flagAlgHom_p19 lam μ ν (MvPolynomial.X i)=flagImage_p19 lam μ ν i:=by
 simp [flagAlgHom_p19]
theorem GDN (lam μ ν:K):
   (unflagAlgHom_p19 lam μ ν).comp (flagAlgHom_p19 lam μ ν)=
     AlgHom.id K (Poly3_p19 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i<;>
   simp [flagImage_p19,unflagImage_p19,flagAlgHom_p19,unflagAlgHom_p19]<;>ring
theorem GCG (lam μ ν:K):
   (flagAlgHom_p19 lam μ ν).comp (unflagAlgHom_p19 lam μ ν)=
     AlgHom.id K (Poly3_p19 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i<;>
   simp [flagImage_p19,unflagImage_p19,flagAlgHom_p19,unflagAlgHom_p19]<;>ring
def flagEquiv_p19 (lam μ ν:K):Poly3_p19 K ≃ₐ[K] Poly3_p19 K:=
 AlgEquiv.ofAlgHom (flagAlgHom_p19 lam μ ν) (unflagAlgHom_p19 lam μ ν)
   (GCG lam μ ν) (GDN lam μ ν)
@[simp] theorem EKI (lam μ ν:K) (F:Poly3_p19 K):
   flagEquiv_p19 lam μ ν F=flagAlgHom_p19 lam μ ν F:=rfl
theorem ARZ (lam μ ν:K) (F:Poly3_p19 K):
   Irreducible (flagAlgHom_p19 lam μ ν F) ↔ Irreducible F:=by
 simpa only [EKI] using
   (MulEquiv.irreducible_iff (flagEquiv_p19 lam μ ν))
theorem flag_dvd_iff_p19 (lam μ ν:K) (F G:Poly3_p19 K):
   flagAlgHom_p19 lam μ ν F∣flagAlgHom_p19 lam μ ν G ↔ F∣G:=by
 simpa only [EKI] using
   (map_dvd_iff (flagEquiv_p19 lam μ ν))
theorem flag_ne_zero_p19 (lam μ ν:K) {F:Poly3_p19 K} (hF:F≠0):
   flagAlgHom_p19 lam μ ν F≠0:=
 (flagEquiv_p19 lam μ ν).injective.ne hF
theorem eval₂Hom_flag_p19
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3_p19 K) (u v z:A) (lam μ ν:K):
   MvPolynomial.eval₂Hom (algebraMap K A) ![u,v,z]
       (flagAlgHom_p19 lam μ ν F)=
     MvPolynomial.eval₂Hom (algebraMap K A)
       ![u-algebraMap K A lam*z,
         v-algebraMap K A μ*u+
           algebraMap K A (μ*lam-ν)*z,
         z] F:=by
 have hhom:
     (MvPolynomial.eval₂Hom (algebraMap K A) ![u,v,z]).comp
         (flagAlgHom_p19 lam μ ν).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K A)
         ![u-algebraMap K A lam*z,
           v-algebraMap K A μ*u+
             algebraMap K A (μ*lam-ν)*z,
           z]:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp [RingHom.comp_apply,flagAlgHom_p19]
   · intro i
     fin_cases i<;>
       simp [RingHom.comp_apply,flagAlgHom_p19,flagImage_p19]<;>ring
 exact RingHom.congr_fun hhom F
theorem eval₂Hom_flag_at_affine_p19
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3_p19 K) (y s z:A) (lam μ ν:K):
   MvPolynomial.eval₂Hom (algebraMap K A)
       ![y+algebraMap K A lam*z,
         s+algebraMap K A μ*y+algebraMap K A ν*z,
         z] (flagAlgHom_p19 lam μ ν F)=
     MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z] F:=by
 rw [eval₂Hom_flag_p19]
 congr 2
 funext i
 fin_cases i<;>simp<;>ring
def ABT (weights:Fin 3→ℕ):Fin 3→ℕ:=
 ![max (weights 0) (weights 2),
   max (weights 1) (max (weights 0) (weights 2)),
   weights 2]
theorem GGW (weights:Fin 3→ℕ) (lam μ ν:K) (i:Fin 3):
   wt_p19 weights (flagImage_p19 lam μ ν i)≤ABT weights i:=by
 fin_cases i
 · dsimp [flagImage_p19,ABT]
   have hm:=wt_mul_le_p19 weights (MvPolynomial.C lam:Poly3_p19 K)
     (MvPolynomial.X 2)
   rw [wt_C_p19,Nat.zero_add,wt_X_p19] at hm
   exact (wt_sub_le_p19 weights (MvPolynomial.X 0)
     (MvPolynomial.C lam*MvPolynomial.X 2)).trans
       (max_le_max (by rw [wt_X_p19]) hm)
 · dsimp [flagImage_p19,ABT]
   have hμ:=wt_mul_le_p19 weights (MvPolynomial.C μ:Poly3_p19 K)
     (MvPolynomial.X 0)
   have hν:=wt_mul_le_p19 weights (MvPolynomial.C (μ*lam-ν):Poly3_p19 K)
     (MvPolynomial.X 2)
   rw [wt_C_p19,Nat.zero_add,wt_X_p19] at hμ hν
   have hinner:=wt_sub_le_p19 weights
     (MvPolynomial.C μ*MvPolynomial.X 0)
     (MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2)
   have houter:=wt_sub_le_p19 weights (MvPolynomial.X 1)
     (MvPolynomial.C μ*MvPolynomial.X 0-
       MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2)
   exact houter.trans (max_le_max (by rw [wt_X_p19])
     (hinner.trans (max_le_max hμ hν)))
 · simp [flagImage_p19,ABT,wt_X_p19]
theorem EBP
   (weights:Fin 3→ℕ) (lam μ ν:K) (d:Fin 3→₀ ℕ):
   wt_p19 weights (∏ i∈d.support,flagImage_p19 lam μ ν i^d i)≤
     Finsupp.weight (ABT weights) d:=by
 apply (FCX weights d.support
   (fun i↦flagImage_p19 lam μ ν i^d i)).trans
 calc
   (∑ i∈d.support,wt_p19 weights (flagImage_p19 lam μ ν i^d i))≤
       ∑ i∈d.support,d i*ABT weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le_p19 weights (flagImage_p19 lam μ ν i) (d i)).trans
       (Nat.mul_le_mul_left _ (GGW weights lam μ ν i))
   _=Finsupp.weight (ABT weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem BXL
   (weights:Fin 3→ℕ) (lam μ ν:K) (F:Poly3_p19 K):
   wt_p19 weights (flagAlgHom_p19 lam μ ν F)≤wt_p19 (ABT weights) F:=by
 change wt_p19 weights
     (MvPolynomial.eval₂ MvPolynomial.C (flagImage_p19 lam μ ν) F)≤_
 rw [MvPolynomial.eval₂_eq]
 apply CLG
 intro d hd
 have hprod:=EBP weights lam μ ν d
 have hcoeff:wt_p19 weights (MvPolynomial.C (F.coeff d):Poly3_p19 K)=0:=
   wt_C_p19 weights _
 have hmul:=wt_mul_le_p19 weights (MvPolynomial.C (F.coeff d):Poly3_p19 K)
   (∏ i∈d.support,flagImage_p19 lam μ ν i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree (ABT weights) hd))
def sWeight_p19:Fin 3→ℕ:=![0,1,0]
def ysWeight_p19:Fin 3→ℕ:=![1,1,0]
def totalWeight_p19:Fin 3→ℕ:=![1,1,1]
@[simp] theorem flagPullWeights_sWeight_p19:ABT sWeight_p19=sWeight_p19:=by
 funext i
 fin_cases i<;>simp [ABT,sWeight_p19]
@[simp] theorem flagPullWeights_ysWeight_p19:ABT ysWeight_p19=ysWeight_p19:=by
 funext i
 fin_cases i<;>simp [ABT,ysWeight_p19]
@[simp] theorem flagPullWeights_totalWeight_p19:
   ABT totalWeight_p19=totalWeight_p19:=by
 funext i
 fin_cases i<;>simp [ABT,totalWeight_p19]
def BI (p:FlagDegree) (F:Poly3_p19 K):Prop:=
 ∀d∈F.support,InFlag p d
theorem DWH {p:FlagDegree} {F:Poly3_p19 K}
   (hF:BI p F):wt_p19 sWeight_p19 F≤p.all:=by
 unfold wt_p19 MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).1
 simpa [sWeight_p19,weight_fin3_p19] using h
theorem DNV {p:FlagDegree} {F:Poly3_p19 K}
   (hF:BI p F):wt_p19 ysWeight_p19 F≤p.yz+p.all:=by
 unfold wt_p19 MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).2.1
 simpa [ysWeight_p19,weight_fin3_p19,Nat.add_comm] using h
theorem COV {p:FlagDegree} {F:Poly3_p19 K}
   (hF:BI p F):
   wt_p19 totalWeight_p19 F≤p.zOnly+p.yz+p.all:=by
 unfold wt_p19 MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).2.2
 simpa [totalWeight_p19,weight_fin3_p19,Nat.add_comm,Nat.add_left_comm,
   Nat.add_assoc] using h
theorem ECL
   (p:FlagDegree) (F:Poly3_p19 K) (lam μ ν:K)
   (hF:BI p F):
   BI p (flagAlgHom_p19 lam μ ν F):=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight_p19 hd
 have hys:=MvPolynomial.le_weightedTotalDegree ysWeight_p19 hd
 have htot:=MvPolynomial.le_weightedTotalDegree totalWeight_p19 hd
 have hsw:=(BXL sWeight_p19 lam μ ν F).trans
   (by simpa using DWH hF)
 have hysw:=(BXL ysWeight_p19 lam μ ν F).trans
   (by simpa using DNV hF)
 have htotw:=(BXL totalWeight_p19 lam μ ν F).trans
   (by simpa using COV hF)
 refine ⟨?_,?_,?_⟩
 · have:=hs.trans hsw
   simpa [sWeight_p19,weight_fin3_p19] using this
 · have:=hys.trans hysw
   simpa [ysWeight_p19,weight_fin3_p19,Nat.add_comm] using this
 · have:=htot.trans htotw
   simpa [totalWeight_p19,weight_fin3_p19,Nat.add_comm,Nat.add_left_comm,
     Nat.add_assoc] using this
def uOrder_p19:Fin 3 ≃ Fin 3:=Equiv.refl _
def vOrder_p19:Fin 3 ≃ Fin 3:=Equiv.swap 0 1
def zOrder_p19:Fin 3 ≃ Fin 3:=Equiv.swap 0 2
end
end RCN125
end SubmissionLower
end ProximityPrize
end PackedLegacy_Z3
section PackedLegacy_B9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN094
open scoped Classical BigOperators
open RCN095 RCN372
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def BTY (aY v bY aS bS cS:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.C aY+MvPolynomial.C v*MvPolynomial.X 0+
     MvPolynomial.C bY*MvPolynomial.X 2,
   MvPolynomial.C aS+MvPolynomial.C v*MvPolynomial.X 1+
     MvPolynomial.C bS*MvPolynomial.X 0+
     MvPolynomial.C cS*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def CNK (aY v bY aS bS cS:K) (i:Fin 3):Poly3 K:=
 let y:=MvPolynomial.C v⁻¹*
   (MvPolynomial.X 0-MvPolynomial.C aY-
     MvPolynomial.C bY*MvPolynomial.X 2)
 ![y,
   MvPolynomial.C v⁻¹*
     (MvPolynomial.X 1-MvPolynomial.C aS-
       MvPolynomial.C bS*y-MvPolynomial.C cS*MvPolynomial.X 2),
   MvPolynomial.X 2] i
def YD (aY v bY aS bS cS:K):Poly3 K→ₐ[K] Poly3 K:=
 MvPolynomial.aeval (BTY aY v bY aS bS cS)
def BBH (aY v bY aS bS cS:K):Poly3 K→ₐ[K] Poly3 K:=
 MvPolynomial.aeval (CNK aY v bY aS bS cS)
theorem EWE
   (aY v bY aS bS cS:K) (hv:v≠0):
   (BBH aY v bY aS bS cS).comp
       (YD aY v bY aS bS cS)=
     AlgHom.id K (Poly3 K):=by
 have hvC:(MvPolynomial.C v:Poly3 K)*MvPolynomial.C v⁻¹=1:=by
   rw [←map_mul]
   simp [hv]
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · simp [BTY,CNK,YD,BBH]
   linear_combination
     (MvPolynomial.X 0-MvPolynomial.C bY*MvPolynomial.X 2-
       MvPolynomial.C aY)*hvC
 · simp [BTY,CNK,YD,BBH]
   linear_combination
     (MvPolynomial.X 1-MvPolynomial.C cS*MvPolynomial.X 2-
       (MvPolynomial.C aS+MvPolynomial.C v⁻¹*MvPolynomial.C bS*
         (MvPolynomial.X 0-MvPolynomial.C aY-
           MvPolynomial.C bY*MvPolynomial.X 2)))*hvC
 · simp [BTY,CNK,YD,BBH]
theorem EVC
   (aY v bY aS bS cS:K) (hv:v≠0):
   (YD aY v bY aS bS cS).comp
       (BBH aY v bY aS bS cS)=
     AlgHom.id K (Poly3 K):=by
 have hvC:(MvPolynomial.C v⁻¹:Poly3 K)*MvPolynomial.C v=1:=by
   rw [←map_mul]
   simp [hv]
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · simp [BTY,CNK,YD,BBH]
   linear_combination MvPolynomial.X 0*hvC
 · simp [BTY,CNK,YD,BBH]
   linear_combination
     (MvPolynomial.X 1-
       MvPolynomial.C v⁻¹*MvPolynomial.C bS*MvPolynomial.X 0)*hvC
 · simp [BTY,CNK,YD,BBH]
def DFU (aY v bY aS bS cS:K) (hv:v≠0):
   Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom
   (YD aY v bY aS bS cS)
   (BBH aY v bY aS bS cS)
   (EVC aY v bY aS bS cS hv)
   (EWE aY v bY aS bS cS hv)
@[simp] theorem residualEquiv_apply
   (aY v bY aS bS cS:K) (hv:v≠0) (F:Poly3 K):
   DFU aY v bY aS bS cS hv F=
     YD aY v bY aS bS cS F:=rfl
theorem eval₂Hom_residual
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (y s z:A) (aY v bY aS bS cS:K):
   MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z]
       (YD aY v bY aS bS cS F)=
     MvPolynomial.eval₂Hom (algebraMap K A)
       ![algebraMap K A aY+algebraMap K A v*y+
           algebraMap K A bY*z,
         algebraMap K A aS+algebraMap K A v*s+
           algebraMap K A bS*y+algebraMap K A cS*z,
         z] F:=by
 have hhom:
     (MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z]).comp
         (YD aY v bY aS bS cS).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K A)
         ![algebraMap K A aY+algebraMap K A v*y+
             algebraMap K A bY*z,
           algebraMap K A aS+algebraMap K A v*s+
             algebraMap K A bS*y+algebraMap K A cS*z,
           z]:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp [RingHom.comp_apply,YD]
   · intro i
     fin_cases i<;>
       simp [RingHom.comp_apply,YD,BTY]<;>ring
 exact RingHom.congr_fun hhom F
end
end RCN094
end SubmissionLower
end ProximityPrize
end PackedLegacy_B9
section PackedLegacy_BQ
namespace ProximityPrize
namespace SubmissionLower
namespace RCN163
open scoped Classical
open RCN094 RCN238 RCN125 RCN372
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
local instance:DecidableEq Omega:=Classical.decEq Omega
@[simp] theorem polynomial_eval₂_comp_C_X_p19
   (phi:Polynomial K→+*Omega) (P:Polynomial K):
   P.eval₂ (phi.comp Polynomial.C) (phi Polynomial.X)=phi P:=by
 change (Polynomial.eval₂RingHom (phi.comp Polynomial.C)
   (phi Polynomial.X)) P=phi P
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [RingHom.comp_apply]
 · simp
end
end RCN163
end SubmissionLower
end ProximityPrize
end PackedLegacy_BQ
section PackedLegacy_B
namespace ProximityPrize
namespace SubmissionLower
namespace RCN159
open scoped Classical
open RCN136 RCN231 RCN319 RCN313 RCN065 RCN238 RCN163 RCN156 RCN275 RCN234 RCN094 RCN095 RCN125
open RCN319 renaming specialization → BM
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
abbrev Poly3_p19 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4_p19 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure FH
   (phi:Polynomial K→+*Omega) (Gamma:Finset K) (x:Iota→K)
   (p e:ℕ) [CharP Omega p] (flag:FlagDegree) (d:ℕ)
   (support:RCN275.ResidualSupportParameters:=
     RCN275.ResidualSupportParameters.acceptedSupport) where
 nodes:Finset Iota
 u0:Iota→K
 u1:Iota→K
 selected:K→Polynomial K
 F:Poly4_p19 K
 G:Poly3_p19 Omega
 MW:Irreducible G
 RR:G∣surfaceMap phi F
 y_dependent:0<G.degreeOf 1
 BLO:¬G∣surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)
 flag_support:RCN095.PolynomialInFlag flag G
 AFS:wt RCN156.residualSWeights F≤support.s
 ACG:wt RCN156.residualYSWeights F≤support.ys
 UT:wt RCN156.residualTotalWeights F≤support.total
 x_injective:Set.InjOn x nodes
 degree_le:∀gamma∈Gamma,(selected gamma).natDegree≤d
 solution:∀gamma∈Gamma,
   RCN319.specialization K (selected gamma) gamma F=0
 regular:∀gamma∈Gamma,
   MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (RCN231.polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
       (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0
 on_component:∀gamma∈Gamma,
   MvPolynomial.eval (DK phi selected gamma) G=0
 BNN:BL selected Gamma d e
 WG:d<p
namespace FH
variable {phi:Polynomial K→+*Omega} {Gamma:Finset K} {x:Iota→K}
 {p e:ℕ} [CharP Omega p] {flag:FlagDegree} {d:ℕ}
 {support:RCN275.ResidualSupportParameters}
def AUY (S:FH phi Gamma x p e flag d support):
   Ideal (Poly3_p19 Omega):=Ideal.span {S.G}
def identities (S:FH phi Gamma x p e flag d support):Finset Iota:=
 RCN065.identityNodes phi S.AUY S.F S.nodes x S.u0 S.u1 d
def Agrees (S:FH phi Gamma x p e flag d support)
   (gamma:K) (i:Iota):Prop:=
 (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i
local instance (S:FH phi Gamma x p e flag d support):
   ∀gamma i,Decidable (S.Agrees gamma i):=fun _ _↦Classical.propDecidable _
def AJW (S:FH phi Gamma x p e flag d support)
   (gamma:K):Finset Iota:=
 S.nodes.filter (S.Agrees gamma)
theorem DNW
   (S:FH phi Gamma x p e flag d support):S.AUY.IsPrime:=by
 exact Ideal.isPrime_span_singleton_of_prime S.MW.prime
theorem CQP
   (S:FH phi Gamma x p e flag d support):
   surfaceMap phi S.F∈S.AUY:=by
 exact Ideal.mem_span_singleton.mpr S.RR
theorem DET
   (S:FH phi Gamma x p e flag d support):
   surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) S.F)∉
     S.AUY:=by
 intro h
 exact S.BLO (Ideal.mem_span_singleton.mp h)
theorem FDL
   (S:FH phi Gamma x p e flag d support)
   {gamma:K} (hgamma:gamma∈Gamma):
   S.AUY≤RingHom.ker
     (MvPolynomial.aeval (DK phi S.selected gamma)).toRingHom:=by
 change Ideal.span {S.G}≤
   RingHom.ker
     (MvPolynomial.aeval (DK phi S.selected gamma)).toRingHom
 rw [Ideal.span_le]
 intro Q hQ
 simp only [Set.mem_singleton_iff] at hQ
 subst Q
 exact S.on_component gamma hgamma
end FH
end
end RCN159
end SubmissionLower
end ProximityPrize
end PackedLegacy_B
section PackedLegacy_D8
namespace ProximityPrize
namespace SubmissionLower
namespace RCN221
open scoped Classical BigOperators
open RCN223 RCN135 RCN136 RCN138 RCN137 RCN267 RCN081 RCN238 RCN231 RCN174 RCN319 RCN243 RCN222 RCN266 RCN159 RCN156 RCN275 RCN234 RCN095
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
open RCN222 renaming GeometricFactor → EX
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def FBB {F:MvPolynomial (Fin 4) K}
   (g:RCN222.GeometricFactor K F):FlagDegree:=
 ⟨g.1.degreeOf (2:Fin 3),g.1.degreeOf (0:Fin 3),
   g.1.degreeOf (1:Fin 3)⟩
theorem EGC {F:MvPolynomial (Fin 4) K}
   (g:RCN222.GeometricFactor K F):RCN095.PolynomialInFlag (FBB K g) g.1:=by
 intro d hd
 have h0:=MvPolynomial.monomial_le_degreeOf (0:Fin 3) hd
 have h1:=MvPolynomial.monomial_le_degreeOf (1:Fin 3) hd
 have h2:=MvPolynomial.monomial_le_degreeOf (2:Fin 3) hd
 change d 1≤g.1.degreeOf 1∧
   d 0+d 1≤g.1.degreeOf 0+g.1.degreeOf 1∧
   d 0+d 1+d 2≤
     g.1.degreeOf 2+g.1.degreeOf 0+g.1.degreeOf 1
 omega
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
def AIT
   (support:RCN275.ResidualSupportParameters)
   {pchar errorCap degree:ℕ} [CharP K pchar]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0<F.degreeOf (2:Fin 4))
   (hRsmall:F.degreeOf (2:Fin 4)<pchar)
   (hsupport:RCN275.ResidualSupportData support F)
   (selected:K→Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota→K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀gamma∈Gamma,(selected gamma).natDegree≤degree)
   (hsolutions:∀gamma∈Gamma,
     RCN319.specialization K (selected gamma) gamma F=0)
   (hregular:∀gamma∈Gamma,
     RCN319.specialization K (selected gamma) gamma
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:BL selected Gamma degree errorCap)
   (hdegreeChar:degree<pchar)
   (g:RCN222.GeometricFactor K F):
   letI:CharP (GenericField K) pchar:=RCN135.genericField_charP K pchar
   FH (RCN135.polynomialEmbedding K)
     (KK K F selected Gamma g) x pchar errorCap
     (FBB K g) degree support:=by
 classical
 letI:CharP (GenericField K) pchar:=RCN135.genericField_charP K pchar
 have hgspec:=RCN137.surfaceFactors_spec (RCN135.polynomialEmbedding K) F g.1 g.2
 have hgirred:=hgspec.1
 have hgdiv:=hgspec.2
 have hgate:=RCN267.geometric_factor_regular_gate K (GenericField K) F hF pchar
   hRpos hRsmall g.1 hgirred
   (by simpa only [RCN138.canonical_geometricSurfaceMap] using hgdiv)
 have hsub:=WK K F selected Gamma g
 exact {
   nodes:=nodes
   u0:=u0
   u1:=u1
   selected:=selected
   F:=F
   G:=g.1
   MW:=hgirred
   RR:=hgdiv
   y_dependent:=hgate.1
   BLO:=by
     simpa only [RCN138.canonical_geometricSurfaceMap] using hgate.2.2.2.2
   flag_support:=EGC K g
   AFS:=hsupport.s_weight
   ACG:=hsupport.ys_weight
   UT:=hsupport.total_weight
   x_injective:=hinj
   degree_le:=fun gamma hgamma↦hdegree gamma (hsub hgamma)
   solution:=fun gamma hgamma↦hsolutions gamma (hsub hgamma)
   regular:=fun gamma hgamma↦
     RCN222.selectedPoint_regular_of_specialization K F selected gamma
       (hregular gamma (hsub hgamma))
   on_component:=fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2
   BNN:=KX selected Gamma _ degree errorCap
     hsub hnoPencil
   WG:=hdegreeChar
 }
end
end RCN221
end SubmissionLower
end ProximityPrize
end PackedLegacy_D8
end Compact_PackedLegacyCore1
section Compact_PackedLegacyCore2
section PackedLegacy_BG
namespace ProximityPrize
namespace SubmissionLower
namespace RCN130
open scoped Classical BigOperators
open RCN081 RCN136 RCN135 RCN137 RCN222 RCN266 RCN167 RCN156 RCN095
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN222 renaming GeometricFactor → EX
open RCN095 renaming PolynomialInFlag → BI
open RCN125 (sWeight_p19 ysWeight_p19 totalWeight_p19)
open RCN071 RCN234 RCN275 RCN159
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K L:Type} [Field K] [Field L]
theorem DSZ (G:MvPolynomial (Fin 3) L):
   MvPolynomial.weightedTotalDegree sWeight_p19 G≤
       MvPolynomial.weightedTotalDegree ysWeight_p19 G∧
     MvPolynomial.weightedTotalDegree ysWeight_p19 G≤
       MvPolynomial.weightedTotalDegree totalWeight_p19 G:=by
 constructor
 · unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro d hd
   exact (show Finsupp.weight sWeight_p19 d≤Finsupp.weight ysWeight_p19 d by
     rw [RCN372.weight_fin3_p19,RCN372.weight_fin3_p19]
     simp [sWeight_p19,ysWeight_p19]).trans (Finset.le_sup hd)
 · unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro d hd
   exact (show Finsupp.weight ysWeight_p19 d≤Finsupp.weight totalWeight_p19 d by
     rw [RCN372.weight_fin3_p19,RCN372.weight_fin3_p19]
     simp [ysWeight_p19,totalWeight_p19]).trans (Finset.le_sup hd)
def SA (G:MvPolynomial (Fin 3) L):FlagDegree:=
 flagFromCaps (MvPolynomial.weightedTotalDegree totalWeight_p19 G)
   (MvPolynomial.weightedTotalDegree ysWeight_p19 G)
   (MvPolynomial.weightedTotalDegree sWeight_p19 G)
abbrev CO (K:Type) [Field K]
   {F:MvPolynomial (Fin 4) K} (g:RCN222.GeometricFactor K F):=
 SA g.1
theorem AHR (G:MvPolynomial (Fin 3) L):
   (SA G).all=MvPolynomial.weightedTotalDegree sWeight_p19 G∧
     (SA G).yz+(SA G).all=
       MvPolynomial.weightedTotalDegree ysWeight_p19 G∧
     (SA G).zOnly+(SA G).yz+
       (SA G).all=MvPolynomial.weightedTotalDegree totalWeight_p19 G:=
 RCN130.flagFromCaps_cumulative _ _ _ (DSZ G).1
   (DSZ G).2
theorem AES (G:MvPolynomial (Fin 3) L):
   RCN095.PolynomialInFlag (SA G) G:=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight_p19 hd
 have hm:=MvPolynomial.le_weightedTotalDegree ysWeight_p19 hd
 have ht:=MvPolynomial.le_weightedTotalDegree totalWeight_p19 hd
 rw [RCN372.weight_fin3_p19] at hs hm ht
 simp [sWeight_p19,ysWeight_p19,totalWeight_p19] at hs hm ht
 have hc:=AHR G
 change d 1≤(SA G).all∧
   d 0+d 1≤(SA G).yz+(SA G).all∧
   d 0+d 1+d 2≤(SA G).zOnly+
     (SA G).yz+(SA G).all
 rw [hc.2.2,hc.2.1,hc.1]
 exact ⟨hs,hm,ht⟩
theorem CBQ (phi:Polynomial K→+*L)
   (F:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree sWeight_p19 (surfaceMap phi F)≤
       wt RCN156.residualSWeights F∧
     MvPolynomial.weightedTotalDegree ysWeight_p19 (surfaceMap phi F)≤
       wt RCN156.residualYSWeights F∧
     MvPolynomial.weightedTotalDegree totalWeight_p19 (surfaceMap phi F)≤
       wt RCN156.residualTotalWeights F:=by
 refine ⟨?_,?_,?_⟩
 all_goals
   unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro e he
   obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (RCN136.support_surfaceMap_subset phi F he)
   rw [RCN372.weight_fin3_p19]
 · have h:=MvPolynomial.le_weightedTotalDegree RCN156.residualSWeights hd
   rw [weight_fin4] at h
   simpa [wt,sWeight_p19,RCN156.residualSWeights,Finsupp.tail_apply] using h
 · have h:=MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hd
   rw [weight_fin4] at h
   simpa [wt,ysWeight_p19,RCN156.residualYSWeights,Finsupp.tail_apply] using h
 · have h:=MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights hd
   rw [weight_fin4] at h
   simpa [wt,totalWeight_p19,RCN156.residualTotalWeights,Finsupp.tail_apply] using h
theorem VD (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∑ g:RCN222.GeometricFactor K F,(CO K g).all)≤
       (RCN130.originalCumulativeFlag F).all∧
     (∑ g:RCN222.GeometricFactor K F,((CO K g).yz+
       (CO K g).all))≤
       (RCN130.originalCumulativeFlag F).yz+(RCN130.originalCumulativeFlag F).all∧
     (∑ g:RCN222.GeometricFactor K F,((CO K g).zOnly+
       (CO K g).yz+(CO K g).all))≤
       (RCN130.originalCumulativeFlag F).zOnly+(RCN130.originalCumulativeFlag F).yz+
         (RCN130.originalCumulativeFlag F).all:=by
 let phi:=RCN135.polynomialEmbedding K
 have hSF:=RCN136.surfaceMap_ne_zero phi (RCN135.polynomialEmbedding_injective K) F hF
 have hp:=RCN137.normalizedFactorSet_product_dvd (surfaceMap phi F) hSF
 have hs:=RCN071.sum_weightedTotalDegree_le_of_prod_dvd_fin3 sWeight_p19
   (RCN137.surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have hm:=RCN071.sum_weightedTotalDegree_le_of_prod_dvd_fin3 ysWeight_p19
   (RCN137.surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have ht:=RCN071.sum_weightedTotalDegree_le_of_prod_dvd_fin3 totalWeight_p19
   (RCN137.surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have hmap:=CBQ phi F
 have hc:=RCN130.originalCumulativeFlag_cumulative F
 refine ⟨?_,?_,?_⟩
 · rw [Finset.sum_congr rfl (fun g _↦(AHR g.1).1),
     Finset.sum_coe_sort,hc.1]
   exact hs.trans hmap.1
 · rw [Finset.sum_congr rfl (fun g _↦(AHR g.1).2.1),
     Finset.sum_coe_sort,hc.2.1]
   exact hm.trans hmap.2.1
 · rw [Finset.sum_congr rfl (fun g _↦(AHR g.1).2.2),
     Finset.sum_coe_sort,hc.2.2]
   exact ht.trans hmap.2.2
theorem AER
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   {P:RCN275.ResidualSupportParameters} (H:RCN275.ResidualSupportData P F)
   (g:RCN222.GeometricFactor K F):
   (CO K g).all≤P.s∧
     (CO K g).yz+(CO K g).all≤P.ys∧
     (CO K g).zOnly+(CO K g).yz+
       (CO K g).all≤P.total:=by
 have hb:=VD F hF
 have hc:=RCN130.originalCumulativeFlag_cumulative F
 rw [hc.2.2,hc.2.1,hc.1] at hb
 refine ⟨?_,?_,?_⟩
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.1.trans H.s_weight)
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.2.1.trans H.ys_weight)
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.2.2.trans H.total_weight)
def BJP {Iota:Type} {phi:Polynomial K→+*L}
   {Gamma:Finset K} {x:Iota→K} {p e d:ℕ} [CharP L p]
   {oldFlag newFlag:FlagDegree} {support:RCN275.ResidualSupportParameters}
   (S:FH phi Gamma x p e oldFlag d support)
   (hflag:RCN095.PolynomialInFlag newFlag S.G):
   FH phi Gamma x p e newFlag d support:=
 {S with flag_support:=hflag}
end
end RCN130
end SubmissionLower
end ProximityPrize
end PackedLegacy_BG
section PackedLegacy_L1
namespace ProximityPrize
namespace SubmissionLower
namespace RCN180
open scoped BigOperators
open RCN100 RCN081 RCN234 RCN156
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
noncomputable section
variable {K:Type*} [Field K]
def CMS (D w L s:ℕ):
   (RCN100.CoefficientIndex D w L s→K)→ₗ[K]
     RCN100.globalCoefficientBox K D w L s:=
 LinearMap.codRestrict (RCN100.globalCoefficientBox K D w L s)
   (RCN180.reconstructLinear (K:=K) D w L s)
   (RCN100.reconstruct_mem_globalCoefficientBox K D w L s)
theorem BVS (D w L s:ℕ):
   Function.Surjective (CMS (K:=K) D w L s):=by
 intro Q
 refine ⟨encodeBox Q,?_⟩
 apply Subtype.ext
 exact RCN180.reconstruct_encodeBox Q
instance EGE (D w L s:ℕ):
   Module.Finite K (RCN100.globalCoefficientBox K D w L s):=
 Module.Finite.of_surjective (CMS (K:=K) D w L s)
   (BVS (K:=K) D w L s)
section IJ
open RCN119
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
variable {I:Type*} [Fintype I]
abbrev IJ (D w L s m:ℕ)
   (nodes u₀ u₁:I→K):=
 LinearMap.ker (AMB K D w L s m nodes u₀ u₁)
def LZ (D w L s m:ℕ)
   (nodes u₀ u₁:I→K):
   IJ (K:=K) D w L s m nodes u₀ u₁→ₗ[K] Poly4 K:=
 (RCN180.reconstructLinear (K:=K) D w L s).comp
   (IJ (K:=K) D w L s m nodes u₀ u₁).subtype
@[simp] theorem SE (D w L s m:ℕ)
   (nodes u₀ u₁:I→K)
   (v:IJ (K:=K) D w L s m nodes u₀ u₁):
   LZ (K:=K) D w L s m nodes u₀ u₁ v=
     reconstruct K D w L s v.1:=rfl
end IJ
end
end RCN180
end SubmissionLower
end ProximityPrize
end PackedLegacy_L1
section PackedLegacy_ContactOrderBridge
namespace ProximityPrize
namespace SubmissionLower
namespace BY
open scoped BigOperators Pointwise
open RCN081 RCN119 RCN100 RCN122
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN122 renaming specialization → BM
noncomputable section
section KernelBridge
variable (K:Type*) [Field K]
@[simp] theorem shiftPlus_X_bridge (i:Fin 3):
    shiftPlus_p19 K (MvPolynomial.X i)=
      ![MvPolynomial.X 0+MvPolynomial.X 1,MvPolynomial.X 1,MvPolynomial.X 2] i:=by
  fin_cases i<;>simp [shiftPlus_p19]<;>rfl
end KernelBridge
end
end BY
end SubmissionLower
end ProximityPrize
end PackedLegacy_ContactOrderBridge
section PackedLegacy_CH
namespace ProximityPrize
namespace SubmissionLower
namespace RCN324
open IsLocalRing
variable {K R:Type*} [CommRing K] [CommRing R] [Algebra K R]
theorem EGU:∀{n p:ℕ},p.Prime→(p∣n.factorial ↔ p≤n)
 | 0,_,hp=>iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
 | n+1,p,hp=>by
     rw [Nat.factorial_succ,hp.dvd_mul,EGU hp]
     exact ⟨fun h=>h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
       fun h=>(_root_.lt_or_eq_of_le h).elim
         (Or.inr ∘ Nat.le_of_lt_succ) fun h=>Or.inl<| by rw [h]⟩
section DVR
variable [IsDomain R] [IsDiscreteValuationRing R]
theorem CUH
   (D:Derivation K R R) (pi u:R) (mu r p:ℕ)
   [CharP R p] (hp:p.Prime) (hmu:mu<p) (hr:r≤mu)
   (hpi:Irreducible pi) (hu:IsUnit u) (htrans:IsUnit (D pi)):
   IsDiscreteValuationRing.addVal R ((D:R→R)^[r] (pi^mu*u))=mu-r:=by
 obtain ⟨error,herror⟩:=RCN324.iterate_pow_mul_expansion D pi u mu r hr
 have hdescDvd:mu.descFactorial r∣mu.factorial:=by
   refine ⟨(mu-r).factorial,?_⟩
   rw [mul_comm,Nat.factorial_mul_descFactorial hr]
 have hnot:¬p∣mu.descFactorial r:=by
   intro hd
   have hpf:p∣mu.factorial:=hd.trans hdescDvd
   rw [EGU hp] at hpf
   omega
 have hc:IsUnit (mu.descFactorial r:R):=
   (CharP.isUnit_natCast_iff hp).2 hnot
 have hlead:IsUnit ((mu.descFactorial r:R)*u*(D pi)^r):=
   (hc.mul hu).mul (htrans.pow r)
 let lead:R:=(mu.descFactorial r:R)*u*(D pi)^r
 have hpiError:¬IsUnit (pi*error):=
   not_isUnit_of_not_isUnit_dvd hpi.not_isUnit (dvd_mul_right pi error)
 have hbracket:IsUnit (lead+pi*error):=
   RCN324.isUnit_add_of_isUnit_of_not_isUnit hlead hpiError
 have hfactor:
     (D:R→R)^[r] (pi^mu*u)=pi^(mu-r)*(lead+pi*error):=by
   rw [herror]
   simp only [lead]
   ring
 rw [hfactor,IsDiscreteValuationRing.addVal_mul,
   IsDiscreteValuationRing.addVal_pow,
   IsDiscreteValuationRing.addVal_uniformizer hpi,
   IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hbracket]
 simp
end DVR
end RCN324
end SubmissionLower
end ProximityPrize
end PackedLegacy_CH
section PackedLegacy_BF
namespace ProximityPrize
namespace SubmissionLower
namespace RCN128
open ProximityPrize.Benchmark RCN050 RCN174 RCN319 RCN238 RCN223
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN319 renaming specialization → BM
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
theorem FJ:
   CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
end
end RCN128
end SubmissionLower
end ProximityPrize
end PackedLegacy_BF
section PackedLegacy_AF
namespace ProximityPrize
namespace SubmissionLower
namespace RCN287
open scoped Classical BigOperators
open RCN081 RCN313 RCN136 RCN234 RCN179 RCN095 RCN275 RCN156 RCN174 RCN238 RCN266 RCN159 RCN318
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
open RCN095 renaming PolynomialInFlag → BI
open RCN174 renaming CoefficientIndex → ED, globalCoefficientBox → BA
open RCN318 renaming TightParameters → GH
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Omega:Type} [Field K] [Field Omega]
theorem DTP
   {P:RCN275.ResidualSupportParameters} {F:MvPolynomial (Fin 4) K}
   (H:RCN275.ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ→K) (x u0 u1:K):
   (RCN313.agreementNumerator F d coeffs x u0 u1).degreeOf (2:Fin 4)≤
       d*(2*P.s-1)∧
     wt RCN156.residualYSWeights (RCN313.agreementNumerator F d coeffs x u0 u1)≤
       1+d*(2*P.ys-2)∧
     wt RCN156.residualTotalWeights (RCN313.agreementNumerator F d coeffs x u0 u1)≤
       1+d*(2*P.total-2):=by
 obtain ⟨hY,hR,hZ⟩:=H.coordinate_bounds
 refine ⟨(RCN313.agreementNumerator_degree_bounds F P.ys P.s P.total
   P.one_le_s hY hR hZ d coeffs x u0 u1).2.1,?_,?_⟩
 · have h:=RCN179.agreementNumerator_wt_le_equal_weight RCN156.residualYSWeights rfl
     F P.ys (by change 1≤1;norm_num)
     (by change 1≤P.ys;exact P.one_le_s.trans P.s_le_ys)
     (by change 2*1≤P.ys;simpa using P.two_le_ys)
     (by change 1≤1;norm_num) H.ys_weight d coeffs x u0 u1
   have hcoeff:2*(P.ys-1)=2*P.ys-2:=by omega
   apply h.trans_eq
   change max 1 0+d*(2*(P.ys-1))=
     1+d*(2*P.ys-2)
   rw [hcoeff]
   norm_num
 · have htotalTwo:2≤P.total:=P.two_le_ys.trans P.ys_le_total
   have honeTotal:1≤P.total:=
     P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
   have h:=RCN179.agreementNumerator_wt_le_equal_weight RCN156.residualTotalWeights rfl
     F P.total (by change 1≤1;norm_num)
     (by change 1≤P.total;exact honeTotal)
     (by change 2*1≤P.total;simpa using htotalTwo)
     (by change 1≤1;norm_num) H.total_weight d coeffs x u0 u1
   have hcoeff:2*(P.total-1)=2*P.total-2:=by omega
   apply h.trans_eq
   change max 1 1+d*(2*(P.total-1))=
     1+d*(2*P.total-2)
   rw [hcoeff]
   norm_num
theorem ANZ
   {P:RCN275.ResidualSupportParameters} (hsy:P.s<P.ys)
   (phi:Polynomial K→+*Omega) {F:MvPolynomial (Fin 4) K}
   (H:RCN275.ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ→K) (x u0 u1:K):
   RCN095.PolynomialInFlag (RCN287.sharpResidualAgreementFlag P d)
     (surfaceMap phi (RCN313.agreementNumerator F d coeffs x u0 u1)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (RCN136.support_surfaceMap_subset phi (RCN313.agreementNumerator F d coeffs x u0 u1) he)
 obtain ⟨hR,hYS,hTotal⟩:=DTP H
   d coeffs x u0 u1
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS:=
   (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hq).trans hYS
 have hqTotal:=
   (MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0*0+q 1*1+q 2*1+q 3*0≤
   1+d*(2*P.ys-2) at hqYS
 change q 0*0+q 1*1+q 2*1+q 3*1≤
   1+d*(2*P.total-2) at hqTotal
 norm_num at hqYS hqTotal
 have hqR':q 2≤(RCN287.sharpResidualAgreementFlag P d).all:=by
   change q 2≤(2*P.s-1)*d
   rw [Nat.mul_comm]
   exact hqR
 change q 2≤(RCN287.sharpResidualAgreementFlag P d).all∧
   q 1+q 2≤(RCN287.sharpResidualAgreementFlag P d).yz+
     (RCN287.sharpResidualAgreementFlag P d).all∧
   q 1+q 2+q 3≤(RCN287.sharpResidualAgreementFlag P d).zOnly+
     (RCN287.sharpResidualAgreementFlag P d).yz+
     (RCN287.sharpResidualAgreementFlag P d).all
 refine ⟨hqR',?_,?_⟩
 · rw [RCN287.sharpResidualAgreementFlag_ys P hsy]
   exact hqYS
 · rw [RCN287.sharpResidualAgreementFlag_total P hsy]
   exact hqTotal
end
end RCN287
end SubmissionLower
end ProximityPrize
end PackedLegacy_AF
section PackedLegacy_N6
namespace ProximityPrize
namespace SubmissionLower
namespace RCN261
open RCN290 RCN293 RCN081
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
noncomputable section
variable {K:Type*} [Field K]
theorem BTT (P:MvPolynomial (Fin 4) K) (n:ℕ):
   RCN293.liftedCoefficient P n=0 ↔ (collectR K P).coeff n=0:=by
 change RCN293.embedCoefficients K ((collectR K P).coeff n)=0 ↔ _
 rw [← map_zero (RCN293.embedCoefficients K),RCN261.embedCoefficients_injective.eq_iff]
theorem AVJ (P:MvPolynomial (Fin 4) K)
   (n:ℕ) (hP:P.degreeOf 2<n):RCN293.liftedCoefficient P n=0:=by
 apply (BTT P n).mpr
 exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [RCN290.collectR_natDegree])
theorem DRJ {σ:Type*}
   (P:MvPolynomial (Option σ) K) (i:σ) (n:ℕ):
   (MvPolynomial.optionEquivLeft K σ (MvPolynomial.pderiv (some i) P)).coeff n=
     MvPolynomial.pderiv i ((MvPolynomial.optionEquivLeft K σ P).coeff n):=by
 classical
 ext e
 rw [MvPolynomial.optionEquivLeft_coeff_coeff,MvPolynomial.coeff_pderiv,
   MvPolynomial.coeff_pderiv,MvPolynomial.optionEquivLeft_coeff_coeff]
 have he:e.optionElim n+Finsupp.single (some i) 1=
     (e+Finsupp.single i 1).optionElim n:=by
   ext j
   cases j with
   | none=>simp
   | some j=>
       simp only [Finsupp.add_apply,Finsupp.optionElim_apply_some]
       rw [Finsupp.single_apply_left
         (show Function.Injective (some:σ→Option σ) from fun _ _ h=>Option.some.inj h)]
 rw [he,Finsupp.optionElim_apply_some]
theorem BRH (P:MvPolynomial (Fin 4) K)
   (i:Fin 4) (hi:i ≠ 2) (n:ℕ):
   RCN293.liftedCoefficient (MvPolynomial.pderiv i P) n=
     MvPolynomial.pderiv i (RCN293.liftedCoefficient P n):=by
 have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i=some ⟨i,hi⟩:=by
   simp [Equiv.optionSubtypeNe_symm_apply,hi]
 have hrename:
     MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm
       (MvPolynomial.pderiv i P)=
     MvPolynomial.pderiv (some (⟨i,hi⟩:RCN290.RemainingCoordinates))
       (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm P):=by
   rw [← MvPolynomial.pderiv_rename
     (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective i P,hindex]
 have hc:(collectR K (MvPolynomial.pderiv i P)).coeff n=
     MvPolynomial.pderiv (⟨i,hi⟩:RCN290.RemainingCoordinates) ((collectR K P).coeff n):=by
   change (MvPolynomial.optionEquivLeft K RCN290.RemainingCoordinates
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm
       (MvPolynomial.pderiv i P))).coeff n=_
   rw [hrename,DRJ]
   rfl
 unfold RCN293.liftedCoefficient
 rw [hc,RCN293.embedCoefficients_eq_rename,RCN293.embedCoefficients_eq_rename]
 exact (MvPolynomial.pderiv_rename Subtype.val_injective
   (⟨i,hi⟩:RCN290.RemainingCoordinates) ((collectR K P).coeff n)).symm
theorem DPW (P:MvPolynomial (Fin 4) K) (t:ℕ)
   (ht:0<t) (hP:P.degreeOf 2≤t) (hzero:RCN293.liftedCoefficient P t=0):
   P.degreeOf 2≤t-1:=by
 rw [← RCN290.collectR_natDegree]
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 by_cases heq:n=t
 · subst n
   exact (BTT P t).mp hzero
 · exact Polynomial.coeff_eq_zero_of_natDegree_lt
     (by rw [RCN290.collectR_natDegree];omega)
theorem EVY (W F q:MvPolynomial (Fin 4) K) (t s k:ℕ)
   (ht:0<t) (hW:W.degreeOf 2≤t) (hF:F.degreeOf 2≤s)
   (hq:q.degreeOf 2=0) (hks:k+s=t)
   (hcoeff:RCN293.liftedCoefficient W t=q*RCN293.liftedCoefficient F s):
   (W-q*MvPolynomial.X (2:Fin 4)^k*F).degreeOf 2≤t-1:=by
 have hR:((MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K)^k).degreeOf 2≤k:=by
   simpa using MvPolynomial.degreeOf_pow_le (2:Fin 4)
     (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) k
 have hqR:(q*MvPolynomial.X (2:Fin 4)^k).degreeOf 2≤k:=by
   have h:=MvPolynomial.degreeOf_mul_le (2:Fin 4) q
     ((MvPolynomial.X (2:Fin 4))^k)
   omega
 have hprod:(q*MvPolynomial.X (2:Fin 4)^k*F).degreeOf 2≤t:=by
   have h:=RCN313.degree_mul_bound (2:Fin 4) hqR hF
   omega
 apply DPW _ t ht
   (RCN313.degree_sub_bound (2:Fin 4) hW hprod)
 rw [RCN261.liftedCoefficient_sub,← hks,
   RCN261.liftedCoefficient_mul_top _ F k s hqR hF,
   RCN261.liftedCoefficient_mul_degree_zero_left _ _ k hq,
   RCN261.liftedCoefficient_X_R_pow,mul_one,hks,hcoeff,sub_self]
end
end RCN261
end SubmissionLower
end ProximityPrize
end PackedLegacy_N6
section PackedLegacy_N8
namespace ProximityPrize
namespace SubmissionLower
namespace RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN261
noncomputable section
set_option maxHeartbeats 800000
variable {K:Type*} [Field K]
theorem EDP (F:Poly K) (s:ℕ)
   (hF:F.degreeOf (2:Fin 4)≤s):
   RCN293.liftedCoefficient (polyG K F) (s+1)=
     -MvPolynomial.pderiv (1:Fin 4) (RCN293.liftedCoefficient F s):=by
 have hPX:=RCN313.pderiv_degree_bound (0:Fin 4) (2:Fin 4) F s hF
 have hx:RCN293.liftedCoefficient (MvPolynomial.pderiv (0:Fin 4) F) (s+1)=0:=
   AVJ _ _ (by omega)
 simp only [polyG,RCN261.liftedCoefficient_neg,RCN261.liftedCoefficient_add,hx,zero_add,
   RCN261.liftedCoefficient_X_R_mul,BRH F 1 (by decide) s]
theorem BOX (F P:Poly K) (a s:ℕ)
   (hs:1≤s) (hF:F.degreeOf (2:Fin 4)≤s)
   (hP:P.degreeOf (2:Fin 4)≤a):
   RCN293.liftedCoefficient (RCN262.vectorNumerator F P) (a+s)=
     (s:Poly K)*RCN293.liftedCoefficient F s*
         MvPolynomial.pderiv (1:Fin 4) (RCN293.liftedCoefficient P a)-
       (a:Poly K)*MvPolynomial.pderiv (1:Fin 4) (RCN293.liftedCoefficient F s)*
         RCN293.liftedCoefficient P a:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4)≤1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4)≤s-1:=
   RCN313.pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4)≤s+1:=
   RCN313.polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hPX:=RCN313.pderiv_degree_bound (0:Fin 4) (2:Fin 4) P a hP
 have hPY:=RCN313.pderiv_degree_bound (1:Fin 4) (2:Fin 4) P a hP
 have hPR:=RCN313.pderiv_same_degree_bound (2:Fin 4) P a hP
 have hcR:RCN293.liftedCoefficient R 1=1:=by
   simpa only [R,pow_one] using RCN261.liftedCoefficient_X_R_pow (K:=K) 1
 have hcH:RCN293.liftedCoefficient H (s-1)=(s:Poly K)*RCN293.liftedCoefficient F s:=
   RCN262.liftedCoefficient_polyH_top F s hs
 have hRH:(R*H).degreeOf (2:Fin 4)≤s:=by
   have h:=RCN313.degree_mul_bound (2:Fin 4) hR hH
   omega
 have hcRH:RCN293.liftedCoefficient (R*H) s=(s:Poly K)*RCN293.liftedCoefficient F s:=by
   have h:=RCN261.liftedCoefficient_mul_top R H 1 (s-1) hR hH
   rw [show 1+(s-1)=s by omega,hcR,hcH,one_mul] at h
   exact h
 have hx:RCN293.liftedCoefficient (H*MvPolynomial.pderiv (0:Fin 4) P) (a+s)=0:=by
   apply AVJ
   have h:=RCN313.degree_mul_bound (2:Fin 4) hH hPX
   omega
 have hy:RCN293.liftedCoefficient (R*H*MvPolynomial.pderiv (1:Fin 4) P) (a+s)=
     (s:Poly K)*RCN293.liftedCoefficient F s*
       MvPolynomial.pderiv (1:Fin 4) (RCN293.liftedCoefficient P a):=by
   have h:=RCN261.liftedCoefficient_mul_top (R*H) (MvPolynomial.pderiv (1:Fin 4) P)
     s a hRH hPY
   rw [hcRH,BRH P 1 (by decide) a] at h
   simpa only [Nat.add_comm] using h
 have hr:RCN293.liftedCoefficient (G*MvPolynomial.pderiv (2:Fin 4) P) (a+s)=
     -(a:Poly K)*MvPolynomial.pderiv (1:Fin 4) (RCN293.liftedCoefficient F s)*
       RCN293.liftedCoefficient P a:=by
   by_cases ha:a=0
   · have hz:=RCN313.pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) P (by simpa [ha] using hP)
     simp [ha,hz]
   · have hapos:0<a:=Nat.pos_of_ne_zero ha
     have h:=RCN261.liftedCoefficient_mul_top G (MvPolynomial.pderiv (2:Fin 4) P)
       (s+1) (a-1) hG hPR
     rw [show s+1+(a-1)=a+s by omega,
       EDP F s hF,
       RCN261.liftedCoefficient_pderiv_R_top P a hapos,map_natCast] at h
     rw [h]
     ring
 change RCN293.liftedCoefficient (H*MvPolynomial.pderiv (0:Fin 4) P+
   R*H*MvPolynomial.pderiv (1:Fin 4) P+
     G*MvPolynomial.pderiv (2:Fin 4) P) (a+s)=_
 rw [RCN261.liftedCoefficient_add,RCN261.liftedCoefficient_add,hx,hy,hr]
 ring
theorem DFB (F:Poly K) (s:ℕ)
   (hs:1≤s) (hF:F.degreeOf (2:Fin 4)≤s):
   RCN293.liftedCoefficient (RCN262.vectorNumerator F (polyH K F)) (2*s-1)=
     (s:Poly K)*RCN293.liftedCoefficient F s*
       MvPolynomial.pderiv (1:Fin 4) (RCN293.liftedCoefficient F s):=by
 have hH:=RCN313.pderiv_same_degree_bound (2:Fin 4) F s hF
 have h:=BOX F (polyH K F) (s-1) s hs hF hH
 rw [show s-1+s=2*s-1 by omega,
   RCN262.liftedCoefficient_polyH_top F s hs] at h
 rw [h,MvPolynomial.pderiv_mul]
 simp only [Derivation.map_natCast,zero_mul,mul_zero,add_zero,zero_add]
 rw [Nat.cast_sub hs]
 simp only [Nat.cast_one]
 ring
theorem DWI (F P:Poly K) (a s b:ℕ)
   (hs:1≤s) (hF:F.degreeOf (2:Fin 4)≤s)
   (hP:P.degreeOf (2:Fin 4)≤a):
   RCN293.liftedCoefficient (RCN313.numeratorStep K F b P) (a+(2*s-1))=
     RCN293.liftedCoefficient F s*((s:Poly K)*
       ((s:Poly K)*RCN293.liftedCoefficient F s*
           MvPolynomial.pderiv (1:Fin 4) (RCN293.liftedCoefficient P a)-
         ((a+2*b:ℕ):Poly K)*
           MvPolynomial.pderiv (1:Fin 4) (RCN293.liftedCoefficient F s)*
             RCN293.liftedCoefficient P a)):=by
 have hH:=RCN313.pderiv_same_degree_bound (2:Fin 4) F s hF
 have hV:=RCN262.vectorNumerator_R_degree_bound F P a s hs hF hP
 have hVH:(RCN262.vectorNumerator F (polyH K F)).degreeOf (2:Fin 4)≤2*s-1:=by
   have h:=RCN262.vectorNumerator_R_degree_bound F (polyH K F) (s-1) s hs hF hH
   omega
 have hfirst:=RCN261.liftedCoefficient_mul_top (polyH K F) (RCN262.vectorNumerator F P)
   (s-1) (a+s) hH hV
 rw [show s-1+(a+s)=a+(2*s-1) by omega,
   RCN262.liftedCoefficient_polyH_top F s hs,
   BOX F P a s hs hF hP] at hfirst
 have hlast:=RCN261.liftedCoefficient_mul_top P (RCN262.vectorNumerator F (polyH K F))
   a (2*s-1) hP hVH
 rw [DFB F s hs hF] at hlast
 rw [RCN262.numeratorStep_eq_vector,RCN261.liftedCoefficient_sub,hfirst]
 rw [show ((2*b:ℕ):Poly K)*P*RCN262.vectorNumerator F (polyH K F)=
   ((2*b:ℕ):Poly K)*(P*RCN262.vectorNumerator F (polyH K F)) by ring,
   RCN261.liftedCoefficient_natCast_mul,hlast]
 push_cast
 ring
theorem EEN (F P:Poly K) (s b:ℕ)
   (hs:1≤s) (hF:F.degreeOf (2:Fin 4)≤s)
   (hP:P.degreeOf (2:Fin 4)≤2*b*(s-1)):
   (reducedStep F P s b).degreeOf (2:Fin 4)≤2*(b+1)*(s-1):=by
 let a:=2*b*(s-1)
 let t:=a+(2*s-1)
 have ht:0<t:=by dsimp [t];omega
 have hW:=RCN313.numeratorStep_R_degree_bound F P b a s hs hF hP
 have hcoeff:RCN293.liftedCoefficient (RCN313.numeratorStep K F b P) t=
     excessFactor F P s b*RCN293.liftedCoefficient F s:=by
   rw [DWI F P a s b hs hF hP]
   dsimp [excessFactor,a]
   ring
 have hks:(2*b+1)*(s-1)+s=t:=by
   dsimp [t,a]
   have hsi:s=(s-1)+1:=by omega
   conv_lhs=>rhs;rw [hsi]
   have ht':2*s-1=2*(s-1)+1:=by omega
   rw [ht']
   ring
 have h:=EVY (RCN313.numeratorStep K F b P) F (excessFactor F P s b)
   t s ((2*b+1)*(s-1)) ht hW hF (RCN262.excessFactor_R_degree F P s b) hks hcoeff
 have heq:t-1=2*(b+1)*(s-1):=by
   dsimp [t,a]
   have ht':2*s-1=2*(s-1)+1:=by omega
   rw [ht',← Nat.add_assoc,Nat.add_sub_cancel]
   ring
 simpa only [reducedStep,RCN262.reductionMultiplier,heq] using h
theorem DMS (F:Poly K) (s:ℕ)
   (hs:1≤s) (hF:F.degreeOf (2:Fin 4)≤s) (b:ℕ):
   (RCN262.reducedNumerator F s b).degreeOf (2:Fin 4)≤2*b*(s-1):=by
 induction b with
 | zero=>simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4) ≠ 1)]
 | succ b ih=>exact EEN F (RCN262.reducedNumerator F s b) s b hs hF ih
theorem BYV (F:Poly K) (s:ℕ)
   (hs:1≤s) (hF:F.degreeOf (2:Fin 4)≤s)
   (w j:ℕ) (hj:j≤w) (c:ℕ→K) (x:K):
   (RCN262.reducedCommonNumeratorTerm F s w c x j).degreeOf (2:Fin 4)≤2*w*(s-1):=by
 have hN:=DMS F s hs hF j
 have hCN:(MvPolynomial.C (c j)*RCN262.reducedNumerator F s j).degreeOf (2:Fin 4)≤
     2*j*(s-1):=
   (MvPolynomial.degreeOf_C_mul_le (RCN262.reducedNumerator F s j) (2:Fin 4) (c j)).trans hN
 have hH:=RCN313.pderiv_same_degree_bound (2:Fin 4) F s hF
 have hHP:=RCN313.degree_pow_bound (2:Fin 4) (2*(w-j)) hH
 have hXP:((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly K)^j).degreeOf
     (2:Fin 4)≤0:=by
   simpa only [Nat.mul_zero] using
     RCN313.degree_pow_bound (2:Fin 4) j (RCN313.shiftedX_degree_bound (2:Fin 4) (by decide) x)
 have h:=RCN313.degree_mul_bound (2:Fin 4) (RCN313.degree_mul_bound (2:Fin 4) hCN hHP) hXP
 apply h.trans
 have hw:j+(w-j)=w:=by omega
 calc
   2*j*(s-1)+2*(w-j)*(s-1)+0=
       2*(j+(w-j))*(s-1):=by ring
   _≤2*w*(s-1):=by simp only [hw,le_refl]
theorem BOF (F:Poly K) (s:ℕ)
   (hs:1≤s) (hF:F.degreeOf (2:Fin 4)≤s)
   (w:ℕ) (c:ℕ→K) (x:K):
   (RCN262.reducedClearedTaylorNumerator F s w c x).degreeOf (2:Fin 4)≤2*w*(s-1):=by
 apply RCN313.degree_sum_bound (2:Fin 4)
 intro j hj
 exact BYV F s hs hF w j
   (by have h:=Finset.mem_range.mp hj;omega) c x
theorem BZL (F:Poly K) (s:ℕ)
   (hs:1≤s) (hF:F.degreeOf (2:Fin 4)≤s)
   (w:ℕ) (c:ℕ→K) (x u₀ u₁:K):
   (RCN262.reducedAgreementNumerator F s w c x u₀ u₁).degreeOf (2:Fin 4)≤2*w*(s-1):=by
 apply RCN313.degree_sub_bound (2:Fin 4)
 · exact BOF F s hs hF w c x
 · have hA:=RCN313.affineSeedPolynomial_degree_bound (2:Fin 4) 0
     (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4) ≠ 3)]) u₀ u₁
   have hH:=RCN313.pderiv_same_degree_bound (2:Fin 4) F s hF
   simpa only [polyH,Nat.zero_add] using
     RCN313.degree_mul_bound (2:Fin 4) hA (RCN313.degree_pow_bound (2:Fin 4) (2*w) hH)
end
end RCN262
end SubmissionLower
end ProximityPrize
end PackedLegacy_N8
section PackedLegacy_Z5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN162
open scoped Classical
open RCN094
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def ALL
   (aY v bY aS bS cS:K) (q:Fin 3→K):Fin 3→K:=
 ![aY+v*q 0+bY*q 2,
   aS+v*q 1+bS*q 0+cS*q 2,
   q 2]
theorem FOB
   (aY v bY aS bS cS:K) (hv:v≠0)
   (q:Fin 3→K) (F:Poly3 K):
   MvPolynomial.eval q
       (DFU aY v bY aS bS cS hv F)=
     MvPolynomial.eval (ALL aY v bY aS bS cS q) F:=by
 change MvPolynomial.eval₂Hom (RingHom.id K) q
     (YD aY v bY aS bS cS F)=
   MvPolynomial.eval₂Hom (RingHom.id K)
     (ALL aY v bY aS bS cS q) F
 have hq:q=![q 0,q 1,q 2]:=by
   funext i
   fin_cases i<;>rfl
 have hforward:
     ALL aY v bY aS bS cS q=
       ![aY+v*q 0+bY*q 2,
         aS+v*q 1+bS*q 0+cS*q 2,
         q 2]:=by
   funext i
   fin_cases i<;>simp [ALL]
 calc
   _=MvPolynomial.eval₂Hom (RingHom.id K) ![q 0,q 1,q 2]
         (YD aY v bY aS bS cS F):=by rw [←hq]
   _=MvPolynomial.eval₂Hom (RingHom.id K)
         ![aY+v*q 0+bY*q 2,
           aS+v*q 1+bS*q 0+cS*q 2,
           q 2] F:=by
     simpa only [Algebra.algebraMap_self,RingHom.id_apply] using
       (eval₂Hom_residual F (q 0) (q 1) (q 2) aY v bY aS bS cS)
   _=_:=by rw [hforward]
theorem DNQ
   (aY v bY aS bS cS:K) (hv:v≠0)
   (q:Fin 3→K):
   (RingHom.ker (MvPolynomial.aeval q).toRingHom).comap
       (DFU aY v bY aS bS cS hv).toRingEquiv.toRingHom=
     RingHom.ker
       (MvPolynomial.aeval
         (ALL aY v bY aS bS cS q)).toRingHom:=by
 ext F
 simp only [Ideal.mem_comap,RingHom.mem_ker]
 change MvPolynomial.eval q
     (DFU aY v bY aS bS cS hv F)=0 ↔
   MvPolynomial.eval (ALL aY v bY aS bS cS q) F=0
 rw [FOB]
structure AIQ (G T H:Poly3 K) where
 ideal:Ideal (Poly3 K)
 isPrime:ideal.IsPrime
 G_mem:G∈ideal
 T_mem:T∈ideal
 H_not_mem:H∉ideal
 ne_point:∀q:Fin 3→K,
   ideal≠RingHom.ker (MvPolynomial.aeval q).toRingHom
def AIQ.FVV
   {G T H:Poly3 K} (D:AIQ G T H)
   (c:K) (hc:c≠0):
   AIQ G T (MvPolynomial.C c*H):=by
 have hu:IsUnit (MvPolynomial.C c:Poly3 K):=
   (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
 refine {
   ideal:=D.ideal
   isPrime:=D.isPrime
   G_mem:=D.G_mem
   T_mem:=D.T_mem
   H_not_mem:=?_
   ne_point:=D.ne_point
 }
 intro hmem
 exact D.H_not_mem ((D.ideal.unit_mul_mem_iff_mem hu).mp hmem)
@[simp] theorem AIQ.mulRegularityUnit_ideal
   {G T H:Poly3 K} (D:AIQ G T H)
   (c:K) (hc:c≠0):
   (D.FVV c hc).ideal=D.ideal:=rfl
def AIQ.mapResidual
   {G T H:Poly3 K} (D:AIQ G T H)
   (aY v bY aS bS cS:K) (hv:v≠0):
   AIQ
     (YD aY v bY aS bS cS G)
     (YD aY v bY aS bS cS T)
     (YD aY v bY aS bS cS H):=by
 let E:=DFU aY v bY aS bS cS hv
 let Pnext:Ideal (Poly3 K):=D.ideal.map E.toRingEquiv.toRingHom
 letI:D.ideal.IsPrime:=D.isPrime
 haveI:Pnext.IsPrime:=Ideal.map_isPrime_of_equiv E.toRingEquiv
 refine {
   ideal:=Pnext
   isPrime:=inferInstance
   G_mem:=?_
   T_mem:=?_
   H_not_mem:=?_
   ne_point:=?_
 }
 · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.G_mem
 · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.T_mem
 · intro hmem
   exact D.H_not_mem
     ((Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
       (I:=D.ideal) (x:=H)).mp hmem)
 · intro q heq
   apply D.ne_point (ALL aY v bY aS bS cS q)
   have hback:Pnext.comap E.toRingEquiv.toRingHom=D.ideal:=by
     ext F
     exact Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
       (I:=D.ideal) (x:=F)
   rw [←hback,heq,
     DNQ aY v bY aS bS cS hv q]
@[simp] theorem AIQ.mapResidual_ideal
   {G T H:Poly3 K} (D:AIQ G T H)
   (aY v bY aS bS cS:K) (hv:v≠0):
   (D.mapResidual aY v bY aS bS cS hv).ideal=
     D.ideal.map
       (DFU aY v bY aS bS cS hv).toRingEquiv.toRingHom:=rfl
end
end RCN162
end SubmissionLower
end ProximityPrize
end PackedLegacy_Z5
section PackedLegacy_AE
namespace ProximityPrize
namespace SubmissionLower
namespace RCN272
open scoped Classical BigOperators
open RCN002 RCN007 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065
open RCN319 renaming specialization → BM
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K→+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def CMV
   (P:Ideal (MvPolynomial (Fin 3) Ω))
   (A:MvPolynomial (Fin 3) Ω) (cost:ℕ):Prop:=
 ∀points:Finset (Fin 3→Ω),
   (∀v∈points,P≤RingHom.ker (MvPolynomial.aeval v).toRingHom)→
   (∀v∈points,MvPolynomial.aeval v A=0)→
   points.card≤cost
end
end RCN272
end SubmissionLower
end ProximityPrize
end PackedLegacy_AE
section PackedLegacy_BR
namespace ProximityPrize
namespace SubmissionLower
namespace RCN165
open scoped Classical
open RCN095 RCN094 RCN162 RCN272
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3_p19 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
structure BIR
   (P:Ideal (Poly3_p19 K)) (cost:FlagDegree→ℕ) where
 zero_le:∀(r:FlagDegree) (A:Poly3_p19 K),
   RCN095.PolynomialInFlag r A→A∉P→CMV P A (cost r)
end
end RCN165
end SubmissionLower
end ProximityPrize
end PackedLegacy_BR
section PackedLegacy_BE
namespace ProximityPrize
namespace SubmissionLower
namespace RCN123
open scoped Classical
open RCN095 RCN125 RCN371 RCN011 RCN009 RCN012
open RCN095 renaming PolynomialInFlag → BI
open RCN371 renaming RationalPolynomials → KU
noncomputable section
variable {K:Type} [Field K]
structure ESO (p:FlagDegree) (F:Poly3 K):Prop where
 uOuter:(planeMap K uOrder_p19 F).natDegree≤p.all
 uTotal:∀d∈(rationalMap K uOrder_p19 F).support,
   d 0+d 1≤p.zOnly+p.yz+p.all
 vOuter:(planeMap K vOrder_p19 F).natDegree≤p.yz+p.all
 vTotal:∀d∈(rationalMap K vOrder_p19 F).support,
   d 0+d 1≤p.zOnly+p.yz+p.all
 zOuter:(planeMap K zOrder_p19 F).natDegree≤p.all
 zTotal:∀d∈(rationalMap K zOrder_p19 F).support,
   d 0+d 1≤p.yz+p.all
theorem FOP
   {p:FlagDegree} {F:Poly3 K}
   (hF:RCN125.BI p F):
   F.degreeOf 1≤p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (hF d hd).1
theorem GVU
   {p:FlagDegree} {F:Poly3 K}
   (hF:RCN125.BI p F):
   F.degreeOf 0≤p.yz+p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (Nat.le_add_right (d 0) (d 1)).trans (hF d hd).2.1
theorem EBN
   (p:FlagDegree) (F:Poly3 K)
   (hF:RCN125.BI p F):
   ESO p F:=by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · exact (RCN009.planeMap_natDegree_le K uOrder_p19 F).trans
     (by simpa [uOrder_p19] using FOP hF)
 · apply RCN012.rationalMap_joint_support_of_original K uOrder_p19 F _
   intro d hd
   have h:=(hF d hd).2.2
   have h':d 1+d 2≤p.zOnly+p.yz+p.all:=by omega
   simpa [uOrder_p19] using h'
 · exact (RCN009.planeMap_natDegree_le K vOrder_p19 F).trans
     (by simpa [vOrder_p19,Equiv.swap_apply_def] using GVU hF)
 · apply RCN012.rationalMap_joint_support_of_original K vOrder_p19 F _
   intro d hd
   have h:=(hF d hd).2.2
   have h':d 0+d 2≤p.zOnly+p.yz+p.all:=by omega
   simpa [vOrder_p19,Equiv.swap_apply_def] using h'
 · exact (RCN009.planeMap_natDegree_le K zOrder_p19 F).trans
     (by simpa [zOrder_p19,Equiv.swap_apply_def] using FOP hF)
 · apply RCN012.rationalMap_joint_support_of_original K zOrder_p19 F _
   intro d hd
   have h:=(hF d hd).2.1
   simpa [zOrder_p19,Equiv.swap_apply_def,Nat.add_comm] using h
theorem LQ
   (p:FlagDegree) (F:Poly3 K) (lam mu nu:K)
   (hF:F.support ⊆ flagSupport p):
   ESO p (flagAlgHom_p19 lam mu nu F):=by
 apply EBN
 apply ECL p F lam mu nu
 intro d hd
 exact (RCN095.mem_flagSupport_iff p d).mp (hF hd)
end
end RCN123
end SubmissionLower
end ProximityPrize
end PackedLegacy_BE
section PackedLegacy_I
namespace ProximityPrize
namespace SubmissionLower
namespace RCN237
open scoped Classical BigOperators
open RCN264 RCN095 RCN121 RCN165 RCN156 RCN275
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure FE (p q:FlagDegree) where
 zCost:RCN264.RegularComponent Omega G T H→ℕ
 yzCost:RCN264.RegularComponent Omega G T H→ℕ
 allCost:RCN264.RegularComponent Omega G T H→ℕ
 primeBudget:∀C:RCN264.RegularComponent Omega G T H,
   BIR C.1 (fun r↦
     r.zOnly*zCost C+r.yz*yzCost C+r.all*allCost C)
 sum_zCost_le:(∑ C:RCN264.RegularComponent Omega G T H,zCost C)≤
   flagMixed p q unitZFlag
 BMO:(∑ C:RCN264.RegularComponent Omega G T H,yzCost C)≤
   flagMixed p q unitYZFlag
 BBW:(∑ C:RCN264.RegularComponent Omega G T H,allCost C)≤
   flagMixed p q unitAllFlag
def FE.weightedCost
   {p q:FlagDegree} (B:FE (G:=G) (T:=T) (H:=H) p q)
   (r:FlagDegree) (C:RCN264.RegularComponent Omega G T H):ℕ:=
 r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C
theorem FE.DGB
   {p q:FlagDegree} (B:FE (G:=G) (T:=T) (H:=H) p q)
   (r:FlagDegree):
   (∑ C:RCN264.RegularComponent Omega G T H,B.weightedCost r C)≤
     flagMixed p q r:=by
 calc
   (∑ C:RCN264.RegularComponent Omega G T H,B.weightedCost r C)=
       r.zOnly*(∑ C:RCN264.RegularComponent Omega G T H,B.zCost C)+
       r.yz*(∑ C:RCN264.RegularComponent Omega G T H,B.yzCost C)+
       r.all*(∑ C:RCN264.RegularComponent Omega G T H,B.allCost C):=by
     simp only [FE.weightedCost,
       Finset.sum_add_distrib,Finset.mul_sum]
   _≤r.zOnly*flagMixed p q unitZFlag+
       r.yz*flagMixed p q unitYZFlag+
       r.all*flagMixed p q unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_left r.zOnly B.sum_zCost_le)
         (Nat.mul_le_mul_left r.yz B.BMO))
       (Nat.mul_le_mul_left r.all B.BBW)
   _=flagMixed p q r:=(RCN121.flagMixed_projection_decomposition p q r).symm
end
end RCN237
end SubmissionLower
end ProximityPrize
end PackedLegacy_I
section PackedLegacy_B1
namespace ProximityPrize
namespace SubmissionLower
namespace RCN066
open scoped Classical BigOperators
open RCN072 RCN264 RCN095 RCN272 RCN165 RCN237
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
variable {K:Type} [Field K]
theorem VB {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T-T'):
   RCN264.regularComponents K G T H=RCN264.regularComponents K G T' H:=by
 classical
 ext P
 simp only [RCN264.regularComponents_def,Finset.mem_filter,RCN072.mem_componentFamily,
   RCN066.cutIdeal_eq_of_dvd_sub h]
def JA {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T-T'):
   RCN264.RegularComponent K G T H ≃ RCN264.RegularComponent K G T' H:=
 Equiv.subtypeEquivRight (fun P=>by rw [VB h])
@[simp] theorem regularComponentEquiv_val {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T-T') (C:RCN264.RegularComponent K G T H):
   (JA h C).1=C.1:=Equiv.subtypeEquivRight_apply_coe _ _
@[simp] theorem DQF {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T-T') (C:RCN264.RegularComponent K G T' H):
   ((JA h).symm C).1=C.1:=Equiv.subtypeEquivRight_symm_apply_coe _ _
end
end RCN066
end SubmissionLower
end ProximityPrize
end PackedLegacy_B1
section PackedLegacy_E5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN263
open RCN136 RCN231 RCN313 RCN238 RCN156 RCN234 RCN095 RCN275 RCN262 RCN066
open RCN095 renaming PolynomialInFlag → BI
open RCN262 renaming pderiv_eq_zero_of_wt_lt → BBG
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
theorem CWR
   (phi:Polynomial K→+*Omega) (P:RCN275.ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:RCN275.ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ→K) (x u0 u1:K):
   RCN095.PolynomialInFlag (RCN263.reducedResidualAgreementFlag P d)
     (surfaceMap phi
       (RCN262.reducedAgreementNumerator F P.s d coeffs x u0 u1)):=by
 have hR:=BZL F P.s P.one_le_s
   H.coordinate_bounds.2.1 d coeffs x u0 u1
 have hYS:=RCN262.reducedAgreementNumerator_wt_le RCN156.residualYSWeights rfl rfl rfl
   F P.s P.ys P.one_le_s P.two_le_ys H.ys_weight d coeffs x u0 u1
 have hTotal:=RCN262.reducedAgreementNumerator_wt_le RCN156.residualTotalWeights rfl rfl rfl
   F P.s P.total P.one_le_s (P.two_le_ys.trans P.ys_le_total)
   H.total_weight d coeffs x u0 u1
 rw [show RCN156.residualYSWeights 3=0 from rfl] at hYS
 rw [show RCN156.residualTotalWeights 3=1 from rfl] at hTotal
 norm_num at hYS hTotal
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (RCN136.support_surfaceMap_subset phi
     (RCN262.reducedAgreementNumerator F P.s d coeffs x u0 u1) he)
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS:=
   (MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hq).trans hYS
 have hqTotal:=
   (MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0*0+q 1*1+q 2*1+q 3*0≤_ at hqYS
 change q 0*0+q 1*1+q 2*1+q 3*1≤_ at hqTotal
 norm_num at hqYS hqTotal
 change q 2≤(RCN263.reducedResidualAgreementFlag P d).all∧
   q 1+q 2≤(RCN263.reducedResidualAgreementFlag P d).yz+
     (RCN263.reducedResidualAgreementFlag P d).all∧
   q 1+q 2+q 3≤(RCN263.reducedResidualAgreementFlag P d).zOnly+
     (RCN263.reducedResidualAgreementFlag P d).yz+
     (RCN263.reducedResidualAgreementFlag P d).all
 refine ⟨?_,?_,?_⟩
 · change q 2≤(2*P.s-2)*d
   have hs:2*(P.s-1)=2*P.s-2:=by omega
   have heq:2*d*(P.s-1)=(2*P.s-2)*d:=by
     rw [← hs]
     ring
   rw [heq] at hqR
   exact hqR
 · rw [RCN263.reducedResidualAgreementFlag_ys]
   have hs:2*(P.ys-1)=2*P.ys-2:=by omega
   have heq:2*d*(P.ys-1)=d*(2*P.ys-2):=by
     rw [← hs]
     ring
   rw [heq] at hqYS
   exact hqYS
 · rw [RCN263.reducedResidualAgreementFlag_total]
   have hs:2*(P.total-1)=2*P.total-2:=by
     have:=P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
     omega
   have heq:2*d*(P.total-1)=d*(2*P.total-2):=by
     rw [← hs]
     ring
   rw [heq] at hqTotal
   exact hqTotal
end
end RCN263
end SubmissionLower
end ProximityPrize
end PackedLegacy_E5
section PackedLegacy_DZ
namespace ProximityPrize
namespace SubmissionLower
namespace RCN057
open RCN313 RCN055 RCN056 RCN234
noncomputable section
variable {K:Type*} [Field K]
theorem BBG (weights:Fin 4→ℕ) (P:Poly K) (i:Fin 4)
   (hP:wt weights P<weights i):MvPolynomial.pderiv i P=0:=by
 apply MvPolynomial.support_eq_empty.mp
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro d hd
 have hh:=MvPolynomial.le_weightedTotalDegree weights (RCN313.support_before_pderiv i P d hd)
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 change Finsupp.weight weights d+weights i≤wt weights P at hh
 omega
namespace WeightBound
variable {w:Fin 4→ℕ} {P Q:Poly K} {a b:ℤ}
theorem pderiv_p19 (hP:WeightBound w P a) (i:Fin 4):
   WeightBound w (MvPolynomial.pderiv i P) (a-w i):=by
 by_cases hz:MvPolynomial.pderiv i P=0
 · exact Or.inl hz
 rcases hP with rfl | hp
 · exact (hz (map_zero _)).elim
 right
 have hi:w i≤wt w P:=by
   by_contra hh
   exact hz (BBG w P i (by omega))
 have hd:=wt_pderiv_le w P i (wt w P) le_rfl
 have hsum:wt w (MvPolynomial.pderiv i P)+w i≤wt w P:=by omega
 have hsum':(wt w (MvPolynomial.pderiv i P):ℤ)+w i≤wt w P:=by
   exact_mod_cast hsum
 linarith
theorem horizontal_p19 (hP:WeightBound w P a) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t≤1):
   WeightBound w (RCN055.horizontalDerivation P) (a+1-t):=by
 have hx:=hP.pderiv_p19 (0:Fin 4)
 have hy:=hP.pderiv_p19 (1:Fin 4)
 have hr:WeightBound w (MvPolynomial.X (2:Fin 4):Poly K) 1:=
   Or.inr (by simp only [wt_X,hR,Nat.cast_one,le_refl])
 simp only [hX,Nat.cast_zero,sub_zero] at hx
 rw [hY] at hy
 have hxy:WeightBound w (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) P)
     (a+1-t):=by convert hr.mul hy using 1;ring
 have ht':(t:ℤ)≤1:=by exact_mod_cast ht
 simpa only [RCN055.horizontalDerivation,Derivation.add_apply,Derivation.smul_apply,
   smul_eq_mul] using (hx.mono (by linarith)).add hxy
end WeightBound
end
end RCN057
end SubmissionLower
end ProximityPrize
end PackedLegacy_DZ
section PackedLegacy_D2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN207
open scoped Classical BigOperators Pointwise
open RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
variable {K:Type*} [Field K]
local notation "Poly" =>MvPolynomial (Fin 3) K
theorem flag_eq_p19 {p q:FlagDegree} (hx:p.zOnly=q.zOnly)
   (hy:p.yz=q.yz) (hz:p.all=q.all):p=q:=by
 cases p;cases q;simp_all
theorem FHG {p:FlagDegree} {A:Poly} (hA:RCN095.PolynomialInFlag p A) (k:ℕ):
   RCN095.PolynomialInFlag (k • p) (A^k):=by
 induction k with
 | zero=>simpa using inFlag_const (0 • p) (1:K)
 | succ k ih=>
   have heq:(k+1) • p=k • p+p:=by
     apply flag_eq_p19<;>simp only [nsmul_zOnly,nsmul_yz,nsmul_all,
       add_zOnly,add_yz,add_all]<;>ring
   rw [pow_succ,heq]
   exact RCN207.inFlag_mul_poly ih hA
theorem FGX (k:ℕ) (B:Fin (k+1)→Poly) (Q U:Poly) (t:K)
   (c:Fin (k+1)→FlagDegree) (P:FlagDegree)
   (hB:∀j,RCN095.PolynomialInFlag (c j) (B j))
   (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:RCN095.PolynomialInFlag unitYZFlag U)
   (hc:∀j,c j+(k-j.val) • unitYZFlag+j.val • (2 • unitAllFlag)=P):
   RCN095.PolynomialInFlag P (RCN207.eliminatedCut k B Q U t):=by
 unfold RCN207.eliminatedCut filteredCut
 apply RCN207.inFlag_sum_poly
 intro j _
 rw [←hc j]
 exact RCN207.inFlag_mul_poly (RCN207.inFlag_mul_poly (hB j) (FHG hU _))
   (FHG (RCN207.inFlag_sub_poly (inFlag_const _ _) hQ) _)
theorem ENX (a b s k:ℕ) (C:FlagDegree)
   (B:Fin (k+1)→Poly) (Q U:Poly) (t:K)
   (c:Fin (k+1)→FlagDegree)
   (hB:∀j,RCN095.PolynomialInFlag (c j) (B j))
   (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:RCN095.PolynomialInFlag unitYZFlag U)
   (hc:∀j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   RCN095.PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩:FlagDegree)) (RCN207.eliminatedCut k B Q U t):=by
 apply FGX k B Q U t c _ hB hQ hU
 intro j
 have hx:=congrArg FlagDegree.zOnly (hc j)
 have hy:=congrArg FlagDegree.yz (hc j)
 have hz:=congrArg FlagDegree.all (hc j)
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 apply flag_eq_p19
 all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,
   nsmul_all,unitYZFlag,unitAllFlag] at*
 all_goals nlinarith
theorem FCY (a b s:ℕ) (H G Q U:Poly) (t:K)
   (hH:RCN095.PolynomialInFlag ⟨a,b+1,s+1⟩ H)
   (hG:RCN095.PolynomialInFlag ⟨a,b,s+3⟩ G)
   (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:RCN095.PolynomialInFlag unitYZFlag U):
   RCN095.PolynomialInFlag ⟨a,b+1,s+3⟩ (RCN207.movingEquation H G Q U t):=by
 apply RCN207.inFlag_sub_poly
 · have hc:(⟨a,b+1,s+1⟩:FlagDegree)+2 • unitAllFlag=⟨a,b+1,s+3⟩:=by
     apply flag_eq_p19
     all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,
       nsmul_yz,nsmul_all,unitAllFlag]
     omega
   rw [←hc]
   exact RCN207.inFlag_mul_poly hH (RCN207.inFlag_sub_poly (inFlag_const _ _) hQ)
 · have hc:unitYZFlag+(⟨a,b,s+3⟩:FlagDegree)=⟨a,b+1,s+3⟩:=by
     apply flag_eq_p19<;>simp only [add_zOnly,add_yz,add_all,unitYZFlag]<;>omega
   rw [←hc]
   exact RCN207.inFlag_mul_poly hU hG
end
end RCN207
end SubmissionLower
end ProximityPrize
end PackedLegacy_D2
section PackedLegacy_BZ
namespace ProximityPrize
namespace SubmissionLower
namespace RCN184
open scoped Classical BigOperators WithZero
open RCN187 RCN133 RCN295
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
 [DecidableEq σ] [Algebra K L]
theorem exp_sum_p19 (s:Finset σ) (z:σ→ℤ):
   WithZero.exp (∑ i∈s,z i)=∏ i∈s,WithZero.exp (z i):=by
 classical
 induction s using Finset.induction_on with
 | empty=>simp
 | @insert i s hi ih=>simp [hi,ih,WithZero.exp_add]
theorem CXH
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ→L) (d:σ→₀ ℕ)
   (hlive:∀i,d i≠0→x i≠0):
   v (MvPolynomial.eval₂Hom (algebraMap K L) x
       (MvPolynomial.monomial d (1:K)))=
     WithZero.exp (RCN295.exponentValuationWeight v x d):=by
 classical
 rw [MvPolynomial.eval₂Hom_monomial,
   Finsupp.prod_fintype _ _ (fun _↦pow_zero _),map_mul,map_prod]
 simp only [map_one,one_mul,map_pow]
 rw [show WithZero.exp (RCN295.exponentValuationWeight v x d)=
     ∏ i,WithZero.exp ((d i:ℤ)*(v (x i)).log) by
   unfold RCN295.exponentValuationWeight
   simpa only using exp_sum_p19 (Finset.univ:Finset σ)
     (fun i↦(d i:ℤ)*(v (x i)).log)]
 apply Finset.prod_congr rfl
 intro i _
 by_cases hd:d i=0
 · simp [hd]
 · have hvx:v (x i)≠0:=
     (Valuation.ne_zero_iff v).mpr (hlive i hd)
   rw [show ((d i:ℤ)*(v (x i)).log)=
       d i • (v (x i)).log by simp,
     WithZero.exp_nsmul,WithZero.exp_log hvx]
theorem AIL
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ→L) (E:Finset (σ→₀ ℕ))
   (hdown:RCN295.ExponentSetDownwardClosed E) (hzero:0∈E):
   ∃c:E→K,
     v (RCN184.coefficientEvaluation x E c)=
       WithZero.exp (RCN295.exponentSetPoleWeight v x E):=by
 obtain ⟨d,hd,hmax⟩:=RCN184.exists_mem_exponentPoleWeight_eq v x E hzero
 let e:σ→₀ ℕ:=RCN184.livePoleTruncation v x d
 have he:e∈E:=hdown d hd e (RCN184.livePoleTruncation_le v x d)
 let esub:E:=⟨e,he⟩
 refine ⟨RCN184.deltaCoefficient E esub,?_⟩
 rw [RCN184.coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
   RCN184.polynomialOfSupport_deltaCoefficient]
 rw [CXH v x e
   (RCN184.livePoleTruncation_coordinate_ne_zero v x d)]
 rw [RCN184.exponentValuationWeight_livePoleTruncation,hmax]
end
end RCN184
end SubmissionLower
end ProximityPrize
end PackedLegacy_BZ
section PackedLegacy_GA
namespace ProximityPrize
namespace SubmissionLower
namespace RCN296
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN344 RCN002 RCN005 RCN006 RCN007
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place_p19 K L):=Classical.decEq _
variable (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
theorem CIW
   (x:σ→A) (E:Finset (σ→₀ ℕ))
   (F:MvPolynomial σ K) (hFE:F.support ⊆ E)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (q:ℕ)
   (hpole:∀W:Finset (Place_p19 K L),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val
       (fun i↦algebraMap A L (x i)) E)≤(q:ℤ))
   (S:Finset (A→ₐ[K] K))
   (hS:∀ψ∈S,ψ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   S.card≤q:=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=
   (FKH K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace_p19 K L A)
 have hU:∀v∈U,1≤RCN026.order_p19 K L v
     (MvPolynomial.eval₂Hom (algebraMap K L)
       (fun i↦algebraMap A L (x i)) F):=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact RCN000.actual_model_zero_order_ge_one
     K A L ψ _ hF (hS ψ hψ)
 let W:=RCN026.placesFor_p19 K L _ hnonzero
 have hcount:=RCN026.AUN
   K L _ hnonzero U hU
 have hsupport:=RCN295.weighted_poleOrder_eval_le_exponentSet W
   (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ c↦NP K L v c)
   (fun i↦algebraMap A L (x i)) E F hFE
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (BQJ K L A)
 have hq:(S.card:ℤ)≤q:=by
   calc
     (S.card:ℤ)=(U.card:ℤ):=by rw [hcard]
     _≤ ∑ v∈W,RCN346.poleOrder_p19 K L v
         (MvPolynomial.eval₂Hom (algebraMap K L)
           (fun i↦algebraMap A L (x i)) F):=hcount
     _≤ ∑ v∈W,RCN295.exponentSetPoleWeight v.val
         (fun i↦algebraMap A L (x i)) E:=by
       simpa only [RCN346.poleOrder_p19,Nat.cast_one,one_mul] using hsupport
     _≤(q:ℤ):=hpole W
 exact_mod_cast hq
end
end RCN296
end SubmissionLower
end ProximityPrize
end PackedLegacy_GA
section PackedLegacy_O4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN273
open scoped Classical BigOperators WithZero
open RCN002 RCN007 RCN264 RCN243 RCN295 RCN296 RCN272 RCN344
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
structure EDO
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3→₀ ℕ)) (separator:Fin 3) (wholeCost:ℕ) where
 cost:RCN264.RegularComponent Ω G T H→ℕ
 DCG:∀C:RCN264.RegularComponent Ω G T H,
   Transcendental Ω (coordinate Ω C.1 separator)
 pole_le:∀C:RCN264.RegularComponent Ω G T H,
   let htr:=DCG C
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     RCN005.rationalBaseAlgebra Ω C.1 separator htr
   ∀W:Finset (Place_p19 Ω (RCN002.CoordinateField Ω C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Ω C.1) E)≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RCN264.RegularComponent Ω G T H,cost C)≤wholeCost
end
end RCN273
end SubmissionLower
end ProximityPrize
end PackedLegacy_O4
section PackedLegacy_GU
namespace ProximityPrize
namespace SubmissionLower
namespace RCN323
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN002 RCN005 RCN006 RCN007
open RCN344 RCN264 RCN273
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place_p19 K L):=Classical.decEq _
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
theorem NR
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (F:MvPolynomial (Fin 3) Ω) (hF:F∉P):
   MvPolynomial.eval₂Hom (algebraMap Ω (RCN002.CoordinateField Ω P))
     (coordinate Ω P) F≠0:=by
 intro hz
 apply hF
 rw [←RCN002.aeval_coordinate_ker Ω P]
 exact hz
structure BXS
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3→₀ ℕ)) (separator:Fin 3) (wholeCost:ℕ)
   (hseparator:∀C:RCN264.RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀C:RCN264.RegularComponent Ω G T H,
     RCN007.ProjectionsFiniteSeparable Ω C.1) where
 polynomial:MvPolynomial (Fin 3) Ω
 support_subset:polynomial.support ⊆ E
 proper:∀C:RCN264.RegularComponent Ω G T H,polynomial∉C.1
 cost:RCN264.RegularComponent Ω G T H→ℕ
 exact_pole:∀C:RCN264.RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (RCN002.CoordinateRing Ω C.1):=
     RCN006.quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (RCN002.CoordinateField Ω C.1):=
     RCN006.polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     RCN005.rationalBaseAlgebra Ω C.1 separator htr
   letI:=RCN006.quotientBaseScalarTower Ω C.1 separator
   letI:=RCN006.polynomialBaseScalarTower Ω C.1 separator
   letI:=RCN006.quotientFractionScalarTower Ω C.1 separator
   letI:=RCN006.polynomialRationalScalarTower Ω C.1 separator htr
   letI:=RCN005.rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (hproj C separator htr).2
   ∀v:Place_p19 Ω (RCN002.CoordinateField Ω C.1),
     RCN187.poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Ω (RCN002.CoordinateField Ω C.1))
           (coordinate Ω C.1) polynomial)=
       RCN295.exponentSetPoleWeight v.val (coordinate Ω C.1) E
 cycle_le:∀C:RCN264.RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (RCN002.CoordinateRing Ω C.1):=
     RCN006.quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (RCN002.CoordinateField Ω C.1):=
     RCN006.polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     RCN005.rationalBaseAlgebra Ω C.1 separator htr
   letI:=RCN006.quotientBaseScalarTower Ω C.1 separator
   letI:=RCN006.polynomialBaseScalarTower Ω C.1 separator
   letI:=RCN006.quotientFractionScalarTower Ω C.1 separator
   letI:=RCN006.polynomialRationalScalarTower Ω C.1 separator htr
   letI:=RCN005.rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (RCN002.CoordinateField Ω C.1))
     (coordinate Ω C.1) polynomial
   let hb:b≠0:=NR C.1 polynomial (proper C)
   (∑ v∈RCN026.placesFor_p19 Ω (RCN002.CoordinateField Ω C.1) b hb,
     RCN346.poleOrder_p19 Ω (RCN002.CoordinateField Ω C.1) v b)≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RCN264.RegularComponent Ω G T H,cost C)≤wholeCost
end
end RCN323
end SubmissionLower
end ProximityPrize
end PackedLegacy_GU
section PackedLegacy_B4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN075
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN187 RCN133 RCN184 RCN295 RCN002 RCN005 RCN006 RCN007
open RCN344 RCN264 RCN273 RCN323
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
def AJQ
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀C:RCN264.RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀C:RCN264.RegularComponent Ω G T H,
     RCN007.ProjectionsFiniteSeparable Ω C.1)
   (C:RCN264.RegularComponent Ω G T H):
   Finset (Place_p19 Ω (RCN002.CoordinateField Ω C.1)):=by
 classical
 let htr:=hseparator C
 letI:Algebra (Polynomial Ω) (RCN002.CoordinateRing Ω C.1):=
   RCN006.quotientPolynomialAlgebra Ω C.1 separator
 letI:Algebra (Polynomial Ω) (RCN002.CoordinateField Ω C.1):=
   RCN006.polynomialBaseAlgebra Ω C.1 separator
 letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
   RCN005.rationalBaseAlgebra Ω C.1 separator htr
 letI:=RCN006.quotientBaseScalarTower Ω C.1 separator
 letI:=RCN006.polynomialBaseScalarTower Ω C.1 separator
 letI:=RCN006.quotientFractionScalarTower Ω C.1 separator
 letI:=RCN006.polynomialRationalScalarTower Ω C.1 separator htr
 letI:=RCN005.rationalBaseScalarTower Ω C.1 separator htr
 letI:FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
   (hproj C separator htr).1
 letI:Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
   (hproj C separator htr).2
 exact Finset.univ.biUnion (fun i:Fin 3↦
   if hi:coordinate Ω C.1 i≠0 then
     RCN026.placesFor_p19 Ω (RCN002.CoordinateField Ω C.1)
       (coordinate Ω C.1 i) hi
   else ∅)
structure KV
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3→₀ ℕ)) (separator:Fin 3)
   (hseparator:∀C:RCN264.RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀C:RCN264.RegularComponent Ω G T H,
     RCN007.ProjectionsFiniteSeparable Ω C.1) where
 polynomial:MvPolynomial (Fin 3) Ω
 support_subset:polynomial.support ⊆ E
 proper:∀C:RCN264.RegularComponent Ω G T H,polynomial∉C.1
 exact_pole:∀C:RCN264.RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (RCN002.CoordinateRing Ω C.1):=
     RCN006.quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (RCN002.CoordinateField Ω C.1):=
     RCN006.polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     RCN005.rationalBaseAlgebra Ω C.1 separator htr
   letI:=RCN006.quotientBaseScalarTower Ω C.1 separator
   letI:=RCN006.polynomialBaseScalarTower Ω C.1 separator
   letI:=RCN006.quotientFractionScalarTower Ω C.1 separator
   letI:=RCN006.polynomialRationalScalarTower Ω C.1 separator htr
   letI:=RCN005.rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (hproj C separator htr).2
   ∀v:Place_p19 Ω (RCN002.CoordinateField Ω C.1),
     poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Ω (RCN002.CoordinateField Ω C.1))
           (coordinate Ω C.1) polynomial)=
       RCN295.exponentSetPoleWeight v.val (coordinate Ω C.1) E
end
end RCN075
end SubmissionLower
end ProximityPrize
end PackedLegacy_B4
section PackedLegacy_X
namespace ProximityPrize
namespace SubmissionLower
namespace RCN341
open scoped Classical
open RCN002 RCN005 RCN006 RCN007
open RCN344 RCN264 RCN295 RCN296
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
theorem AEK
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (D:RCN341.SeparableLiteralCoordinate P)
   (E:Finset (Fin 3→₀ ℕ)) (q:ℕ)
   (hpole:
     letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega P):=
       RCN005.rationalBaseAlgebra Omega P D.index D.transcendental
     ∀W:Finset (Place_p19 Omega (RCN002.CoordinateField Omega P)),
       (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega P) E)≤
         (q:ℤ))
   (F:MvPolynomial (Fin 3) Omega) (hFE:F.support ⊆ E) (hF:F∉P)
   (S:Finset (Fin 3→Omega))
   (hSP:∀v∈S,P≤RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀v∈S,MvPolynomial.aeval v F=0):
   S.card≤q:=by
 classical
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (RCN002.CoordinateRing Omega P):=
   RCN006.quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (RCN002.CoordinateField Omega P):=
   RCN006.polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega P):=
   RCN005.rationalBaseAlgebra Omega P i0 htr
 letI:=RCN006.quotientBaseScalarTower Omega P i0
 letI:=RCN006.polynomialBaseScalarTower Omega P i0
 letI:=RCN006.quotientFractionScalarTower Omega P i0
 letI:=RCN006.polynomialRationalScalarTower Omega P i0 htr
 letI:=RCN005.rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega P):=
   D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega P):=
   D.separable
 let liftPoint:{v:Fin 3→Omega//v∈S}→
     (RCN002.CoordinateRing Omega P→ₐ[Omega] Omega):=
   fun v↦pointHom Omega P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   have h:=RCN007.pointHom_injective Omega P hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn Omega P↦z.val) h
 let points:=S.attach.image liftPoint
 have hpoints:∀psi∈points,psi (MvPolynomial.eval₂Hom
     (algebraMap Omega (RCN002.CoordinateRing Omega P))
     (RCN006.quotientCoordinate Omega P) F)=0:=by
   intro psi hpsi
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hpsi
   rw [RCN007.quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hpole':∀W:Finset (Place_p19 Omega (RCN002.CoordinateField Omega P)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val
       (fun i↦algebraMap (RCN002.CoordinateRing Omega P) (RCN002.CoordinateField Omega P)
         (RCN006.quotientCoordinate Omega P i)) E)≤(q:ℤ):=by
   intro W
   simpa only [RCN006.quotientCoordinate_fraction] using hpole W
 have hcount:=CIW
   (K:=Omega) (L:=RCN002.CoordinateField Omega P) (σ:=Fin 3)
   (RCN002.CoordinateRing Omega P) (RCN006.quotientCoordinate Omega P) E F hFE
   (RCN007.quotient_eval_ne_zero_of_not_mem Omega P F hF) q hpole' points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
end
end RCN341
end SubmissionLower
end ProximityPrize
end PackedLegacy_X
section PackedLegacy_P
namespace ProximityPrize
namespace SubmissionLower
namespace RCN114
open scoped Classical BigOperators WithZero
open RCN187 RCN295 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
variable {L:Type*} [Field L]
theorem ACW
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3→L)
   (p:FlagDegree) (i:Fin 3)
   (hi:Finsupp.single i 1∈flagSupport p):
   poleOrder v (x i)≤RCN295.exponentSetPoleWeight v x (flagSupport p):=by
 rw [←RCN114.exponentPoleWeight_single v x i]
 unfold RCN295.exponentSetPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
   ⟨Finsupp.single i 1,hi,rfl⟩)
theorem UC
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3→L):
   RCN295.exponentSetPoleWeight v x (flagSupport unitZFlag)=poleOrder v (x 2):=by
 apply le_antisymm
 · simpa [unitZFlag] using RCN114.exponentSetPoleWeight_flagSupport_le v x unitZFlag
 · apply ACW v x unitZFlag 2
   rw [RCN095.mem_flagSupport_iff]
   simp [InFlag,unitZFlag]
theorem QD
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3→L):
   RCN295.exponentSetPoleWeight v x (flagSupport unitYZFlag)=
     max (poleOrder v (x 0)) (poleOrder v (x 2)):=by
 apply le_antisymm
 · simpa [unitYZFlag] using RCN114.exponentSetPoleWeight_flagSupport_le v x unitYZFlag
 · apply max_le
   · apply ACW v x unitYZFlag 0
     rw [RCN095.mem_flagSupport_iff]
     simp [InFlag,unitYZFlag]
   · apply ACW v x unitYZFlag 2
     rw [RCN095.mem_flagSupport_iff]
     simp [InFlag,unitYZFlag]
theorem SF
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3→L):
   RCN295.exponentSetPoleWeight v x (flagSupport unitAllFlag)=
     max (poleOrder v (x 1))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 apply le_antisymm
 · simpa [unitAllFlag] using RCN114.exponentSetPoleWeight_flagSupport_le v x unitAllFlag
 · apply max_le
   · apply ACW v x unitAllFlag 1
     rw [RCN095.mem_flagSupport_iff]
     simp [InFlag,unitAllFlag]
   · apply max_le
     · apply ACW v x unitAllFlag 0
       rw [RCN095.mem_flagSupport_iff]
       simp [InFlag,unitAllFlag]
     · apply ACW v x unitAllFlag 2
       rw [RCN095.mem_flagSupport_iff]
       simp [InFlag,unitAllFlag]
theorem AEI
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3→L)
   (p:FlagDegree):
   RCN295.exponentSetPoleWeight v x (flagSupport p)≤
     (p.zOnly:ℤ)*RCN295.exponentSetPoleWeight v x (flagSupport unitZFlag)+
     (p.yz:ℤ)*RCN295.exponentSetPoleWeight v x (flagSupport unitYZFlag)+
     (p.all:ℤ)*RCN295.exponentSetPoleWeight v x (flagSupport unitAllFlag):=by
 rw [UC,QD,
   SF]
 exact RCN114.exponentSetPoleWeight_flagSupport_le v x p
end
end RCN114
end SubmissionLower
end ProximityPrize
end PackedLegacy_P
section PackedLegacy_Q8
namespace ProximityPrize
namespace SubmissionLower
namespace RCN340
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005 RCN006
open RCN344 RCN264 RCN095 RCN114 RCN295 RCN341 RCN237 RCN165
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def UJ
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:RCN341.SeparableLiteralCoordinate P)
   (E:Finset (Fin 3→₀ ℕ)) (cost:ℕ):Prop:=
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (RCN002.CoordinateRing Omega P):=
   RCN006.quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (RCN002.CoordinateField Omega P):=
   RCN006.polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega P):=
   RCN005.rationalBaseAlgebra Omega P i0 htr
 letI:=RCN006.quotientBaseScalarTower Omega P i0
 letI:=RCN006.polynomialBaseScalarTower Omega P i0
 letI:=RCN006.quotientFractionScalarTower Omega P i0
 letI:=RCN006.polynomialRationalScalarTower Omega P i0 htr
 letI:=RCN005.rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega P):=
   D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega P):=
   D.separable
 ∀W:Finset (Place_p19 Omega (RCN002.CoordinateField Omega P)),
   (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega P) E)≤
     (cost:ℤ)
structure QZ
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 zCost:RCN264.RegularComponent Omega G T H→ℕ
 yzCost:RCN264.RegularComponent Omega G T H→ℕ
 allCost:RCN264.RegularComponent Omega G T H→ℕ
 zPole:∀C:RCN264.RegularComponent Omega G T H,
   UJ (base C) (flagSupport unitZFlag) (zCost C)
 yzPole:∀C:RCN264.RegularComponent Omega G T H,
   UJ (base C) (flagSupport unitYZFlag) (yzCost C)
 allPole:∀C:RCN264.RegularComponent Omega G T H,
   UJ (base C) (flagSupport unitAllFlag) (allCost C)
 sum_zCost_le:(∑ C:RCN264.RegularComponent Omega G T H,zCost C)≤
   flagMixed p q unitZFlag
 BMO:(∑ C:RCN264.RegularComponent Omega G T H,yzCost C)≤
   flagMixed p q unitYZFlag
 BBW:(∑ C:RCN264.RegularComponent Omega G T H,allCost C)≤
   flagMixed p q unitAllFlag
def QZ.toFE
   {base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (U:QZ base p q):
   FE (G:=G) (T:=T) (H:=H) p q where
 zCost:=U.zCost
 yzCost:=U.yzCost
 allCost:=U.allCost
 sum_zCost_le:=U.sum_zCost_le
 BMO:=U.BMO
 BBW:=U.BBW
 primeBudget:=by
   intro C
   refine ⟨?_⟩
   intro r A hA hproper points hpointsP hpointsA
   let D:=base C
   let i0:=D.index
   let htr:=D.transcendental
   letI:Algebra (Polynomial Omega) (RCN002.CoordinateRing Omega C.1):=
     RCN006.quotientPolynomialAlgebra Omega C.1 i0
   letI:Algebra (Polynomial Omega) (RCN002.CoordinateField Omega C.1):=
     RCN006.polynomialBaseAlgebra Omega C.1 i0
   letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     RCN005.rationalBaseAlgebra Omega C.1 i0 htr
   letI:=RCN006.quotientBaseScalarTower Omega C.1 i0
   letI:=RCN006.polynomialBaseScalarTower Omega C.1 i0
   letI:=RCN006.quotientFractionScalarTower Omega C.1 i0
   letI:=RCN006.polynomialRationalScalarTower Omega C.1 i0 htr
   letI:=RCN005.rationalBaseScalarTower Omega C.1 i0 htr
   letI:FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     D.finite
   letI:Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     D.separable
   have hz:=U.zPole C
   have hyz:=U.yzPole C
   have hall:=U.allPole C
   change∀W:Finset (Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitZFlag))≤(U.zCost C:ℤ) at hz
   change∀W:Finset (Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitYZFlag))≤(U.yzCost C:ℤ) at hyz
   change∀W:Finset (Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitAllFlag))≤(U.allCost C:ℤ) at hall
   have hpole:∀W:Finset (Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
       (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport r))≤
       ((r.zOnly*U.zCost C+r.yz*U.yzCost C+
         r.all*U.allCost C:ℕ):ℤ):=by
     intro W
     calc
       (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
           (flagSupport r))≤
           ∑ v∈W,
             ((r.zOnly:ℤ)*RCN295.exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitZFlag)+
              (r.yz:ℤ)*RCN295.exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitYZFlag)+
              (r.all:ℤ)*RCN295.exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitAllFlag)):=by
         apply Finset.sum_le_sum
         intro v _
         exact AEI v.val
           (coordinate Omega C.1) r
       _=(r.zOnly:ℤ)*
             (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitZFlag))+
           (r.yz:ℤ)*
             (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitYZFlag))+
           (r.all:ℤ)*
             (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitAllFlag)):=by
         simp only [Finset.sum_add_distrib,Finset.mul_sum]
       _≤(r.zOnly:ℤ)*(U.zCost C:ℤ)+
           (r.yz:ℤ)*(U.yzCost C:ℤ)+
           (r.all:ℤ)*(U.allCost C:ℤ):=by
         exact add_le_add
           (add_le_add
             (mul_le_mul_of_nonneg_left (hz W) (by positivity))
             (mul_le_mul_of_nonneg_left (hyz W) (by positivity)))
           (mul_le_mul_of_nonneg_left (hall W) (by positivity))
       _=((r.zOnly*U.zCost C+r.yz*U.yzCost C+
           r.all*U.allCost C:ℕ):ℤ):=by
         push_cast
         ring
   exact AEK C.1 D
     (flagSupport r)
     (r.zOnly*U.zCost C+r.yz*U.yzCost C+r.all*U.allCost C)
     hpole A ((RCN095.support_subset_flagSupport_iff r A).2 hA) hproper
     points hpointsP hpointsA
end
end RCN340
end SubmissionLower
end ProximityPrize
end PackedLegacy_Q8
section PackedLegacy_DE
namespace ProximityPrize
namespace SubmissionLower
namespace RCN024
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
section FiniteWithoutSeparability
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀]
theorem BAC
   (P Q:Polynomial (Polynomial K₀))
   (hirreducible:Irreducible P) (hpositive:0<P.natDegree)
   (hproper:¬P∣Q) (y r:E₀)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r Q=0)
   (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
   FiniteDimensional K₀ E₀:=by
 classical
 have hresne:=RCN362.irreducible_resultant_ne_zero_of_not_dvd
   P Q hirreducible hpositive hproper
 have hresroot:=RCN364.AVA P Q
   P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive))
     y r hP hQ
 have hyIntegral:IsIntegral K₀ y:=
   IsAlgebraic.isIntegral ⟨Polynomial.resultant P Q P.natDegree Q.natDegree,
     hresne,hresroot⟩
 let S:IntermediateField K₀ E₀:=IntermediateField.adjoin K₀ {y}
 let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K₀ y⟩
 let g:Polynomial K₀→+*S:=Polynomial.eval₂RingHom (algebraMap K₀ S) yS
 let Py:Polynomial S:=P.map g
 have hPyne:Py≠0:=by
   have h:=RCN360.ABJ
     (algebraMap K₀ S) P
     (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
   rw [RCN360.ART] at h
   exact h
 have hcoefficient:(algebraMap S E₀).comp g=
     Polynomial.eval₂RingHom (algebraMap K₀ E₀) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap S E₀
         (Polynomial.eval₂ (algebraMap K₀ S) yS (Polynomial.C c))=
       Polynomial.eval₂ (algebraMap K₀ E₀) y (Polynomial.C c)
     rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
     exact (IsScalarTower.algebraMap_apply K₀ S E₀ c).symm
   · change algebraMap S E₀
         (Polynomial.eval₂ (algebraMap K₀ S) yS Polynomial.X)=
       Polynomial.eval₂ (algebraMap K₀ E₀) y Polynomial.X
     rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
     rfl
 have hPyroot:Polynomial.aeval r Py=0:=by
   change Polynomial.eval₂ (algebraMap S E₀) r (P.map g)=0
   rw [Polynomial.eval₂_map,hcoefficient]
   exact hP
 have hrIntegralS:IsIntegral S r:=
   IsAlgebraic.isIntegral ⟨Py,hPyne,hPyroot⟩
 letI:FiniteDimensional K₀ S:=
   IntermediateField.adjoin.finiteDimensional hyIntegral
 letI:Algebra.IsIntegral K₀ S:=Algebra.IsIntegral.of_finite K₀ S
 have hrIntegral:IsIntegral K₀ r:=isIntegral_trans r hrIntegralS
 exact RCN024.finiteDimensional_of_integral_generating_pair y r hyIntegral hrIntegral hgen
end FiniteWithoutSeparability
end
end RCN024
end SubmissionLower
end ProximityPrize
end PackedLegacy_DE
section PackedLegacy_DF
namespace ProximityPrize
namespace SubmissionLower
namespace RCN025
open scoped Classical BigOperators
open RCN024
noncomputable section
section FinitePlaneFamily
variable {K:Type} [Field K] [DecidableEq K]
 {I:Type*} [Fintype I]
 (E:I→Type) [∀i,Field (E i)] [∀i,Algebra K (E i)]
 [∀i,FiniteDimensional K (E i)]
theorem BHK
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hpositive:0<P.natDegree)
   (hproper:¬P∣Q)
   (y r:∀i,E i)
   (hgen:∀i,IntermediateField.adjoin K
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i=>
     RCN361.relationIdeal K (E i) (y i) (r i)))
   (hProot:∀i,RCN361.planeEval K (E i)
     (y i) (r i) P=0)
   (hQroot:∀i,RCN361.planeEval K (E i)
     (y i) (r i) Q=0):
   (∑ i,Module.finrank K (E i))≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 have hspecial:∀f∈
     (Finset.univ.image (fun i=>minpoly K (y i))),
       P.map (AdjoinRoot.mk f)≠0:=by
   intro f hf
   obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
   letI:Fact (Irreducible (minpoly K (y i))):=
     ⟨minpoly.irreducible (IsIntegral.of_finite K (y i))⟩
   have hcoeff:Polynomial.eval₂RingHom
       (algebraMap K (AdjoinRoot (minpoly K (y i))))
         (AdjoinRoot.root (minpoly K (y i)))=
       AdjoinRoot.mk (minpoly K (y i)):=by
     apply Polynomial.ringHom_ext
     · intro c
       simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
         AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
     · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
         AdjoinRoot.mk_X]
   have h:=RCN360.ABJ
     (algebraMap K (AdjoinRoot (minpoly K (y i)))) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive))
     (AdjoinRoot.root (minpoly K (y i)))
   rw [RCN360.ART,hcoeff] at h
   exact h
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 exact (RCN025.sum_finrank_le_resultant_of_relationIdeal_injective
   (K:=K) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
     hkernels hProot hQroot hspecial hresultant).trans
       (bivariate_resultant_natDegree_le
         (F:=K) P Q P.natDegree Q.natDegree)
end FinitePlaneFamily
end
end RCN025
end SubmissionLower
end ProximityPrize
end PackedLegacy_DF
section PackedLegacy_X7
namespace ProximityPrize
namespace SubmissionLower
namespace RCN021
open scoped Classical BigOperators
open RCN371 RCN011 RCN009 RCN013 RCN024 RCN025 RCN022
open RCN371 renaming RationalPolynomials → KU
noncomputable section
set_option maxHeartbeats 1000000
variable (K:Type) [Field K]
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance:IsLocalization (RCN371.coefficientDenominators K)
   (RCN371.RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
section FixedFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (E:I→Type)
 [∀i,Field (E i)] [∀i,Algebra K (E i)]
 (e:∀i,Original K→ₐ[K] E i)
theorem EOC
   (ht:∀i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀i,
     letI:Algebra (RatFunc K) (E i):=
       (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀i,e i G=0) (hHroot:∀i,e i H=0)
   (hproper:¬G∣H) (hpositive:0<(planeMap K order G).natDegree):
   letI:∀i,Algebra (RatFunc K) (E i):=fun i↦
     (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
   (∀i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i))≤
       (planeMap K order H).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀i,Algebra (RatFunc K) (E i):=fun i↦
   (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     RCN021.planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((RCN021.planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hGroots:∀i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change RCN021.planeEvaluation K (E i) order (e i) (ht i) (planeMap K order G)=0
     rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change RCN021.planeEvaluation K (E i) order (e i) (ht i) (planeMap K order H)=0
     rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
     exact hHroot i
   have hfinite:∀i,FiniteDimensional (RatFunc K) (E i):=by
     intro i
     have hGeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hGroots i
     have hHeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hHroots i
     exact BAC (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
       hGeval hHeval (hgen i)
   letI:∀i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change RCN021.relationKernel K (E i) order (e i) (ht i)=
       RCN021.relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [RCN021.relationKernel_contract] using hc
   exact ⟨hfinite,
     BHK
       (K:=RatFunc K) (I:=I) E
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (fun i↦e i (MvPolynomial.X (order 2)))
       (fun i↦e i (MvPolynomial.X (order 1))) hgen
       hrelation hGroots hHroots⟩
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end FixedFamily
end
end RCN021
end SubmissionLower
end ProximityPrize
end PackedLegacy_X7
section PackedLegacy_EE
namespace ProximityPrize
namespace SubmissionLower
namespace RCN124
open scoped Classical BigOperators
open RCN371 RCN011 RCN009 RCN013 RCN024 RCN025 RCN022 RCN021 RCN012
open RCN371 renaming RationalPolynomials → KU
noncomputable section
theorem AEL
   {F:Type} [Field F] {I:Type*} [Fintype I]
   (E:I→Type) [∀i,Field (E i)] [∀i,Algebra F (E i)]
   [∀i,FiniteDimensional F (E i)]
   (P Q:Polynomial (Polynomial F))
   (hP:Irreducible P) (hpositive:0<P.natDegree)
   (hproper:¬P∣Q)
   (y r:∀i,E i)
   (hgen:∀i,IntermediateField.adjoin F
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦
     RCN361.relationIdeal F (E i) (y i) (r i)))
   (hProot:∀i,RCN361.planeEval F (E i)
     (y i) (r i) P=0)
   (hQroot:∀i,RCN361.planeEval F (E i)
     (y i) (r i) Q=0):
   (∑ i,Module.finrank F (E i))≤
     (Polynomial.resultant P Q).natDegree:=by
 classical
 letI:DecidableEq F:=Classical.decEq F
 have hspecial:∀f∈
     (Finset.univ.image (fun i↦minpoly F (y i))),
       P.map (AdjoinRoot.mk f)≠0:=by
   intro f hf
   obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
   letI:Fact (Irreducible (minpoly F (y i))):=
     ⟨minpoly.irreducible (IsIntegral.of_finite F (y i))⟩
   have hcoeff:Polynomial.eval₂RingHom
       (algebraMap F (AdjoinRoot (minpoly F (y i))))
         (AdjoinRoot.root (minpoly F (y i)))=
       AdjoinRoot.mk (minpoly F (y i)):=by
     apply Polynomial.ringHom_ext
     · intro c
       simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
         AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
     · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
         AdjoinRoot.mk_X]
   have h:=RCN360.ABJ
     (algebraMap F (AdjoinRoot (minpoly F (y i)))) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive))
     (AdjoinRoot.root (minpoly F (y i)))
   rw [RCN360.ART,hcoeff] at h
   exact h
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 simpa only using
   (RCN025.sum_finrank_le_resultant_of_relationIdeal_injective
     (K:=F) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
       hkernels hProot hQroot hspecial hresultant)
variable (K:Type) [Field K]
theorem CXF
   (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
   (E:I→Type)
   [∀i,Field (E i)] [∀i,Algebra K (E i)]
   (e:∀i,Original K→ₐ[K] E i)
   (ht:∀i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀i,
     letI:Algebra (RatFunc K) (E i):=
       (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
         (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀i,e i G=0) (hHroot:∀i,e i H=0)
   (hproper:¬G∣H) (hpositive:0<(planeMap K order G).natDegree)
   (n mCap totalG totalH cap:ℕ) (hHne:H≠0)
   (hGouter:(planeMap K order G).natDegree≤n)
   (hHouter:(planeMap K order H).natDegree≤mCap)
   (hGsupport:∀d∈(rationalMap K order G).support,
     d 0+d 1≤totalG)
   (hHsupport:∀d∈(rationalMap K order H).support,
     d 0+d 1≤totalH)
   (hbudget:∀m,m≤mCap→
     m*totalG+n*totalH-m*n≤cap):
   letI:∀i,Algebra (RatFunc K) (E i):=fun i↦
     (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
       (ht i)).toRingHom.toAlgebra
   (∀i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i))≤cap:=by
 classical
 letI:∀i,Algebra (RatFunc K) (E i):=fun i↦
   (RCN022.elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
     (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     RCN021.planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((RCN021.planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hbase:=EOC K order E e ht hgen hkernels
     G H hG hGroot hHroot hproper hpositive
   have hfinite:∀i,FiniteDimensional (RatFunc K) (E i):=hbase.1
   letI:∀i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hGroots:∀i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change RCN021.planeEvaluation K (E i) order (e i) (ht i)
       (planeMap K order G)=0
     rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change RCN021.planeEvaluation K (E i) order (e i) (ht i)
       (planeMap K order H)=0
     rw [←RingHom.comp_apply,RCN021.planeEvaluation_comp_planeMap]
     exact hHroot i
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change RCN021.relationKernel K (E i) order (e i) (ht i)=
       RCN021.relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [RCN021.relationKernel_contract] using hc
   refine ⟨hfinite,?_⟩
   exact (AEL E
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     (fun i↦e i (MvPolynomial.X (order 2)))
     (fun i↦e i (MvPolynomial.X (order 1))) hgen hrelation
     hGroots hHroots).trans
       (XY K order G H
         n mCap totalG totalH cap hHne hGouter hHouter
         hGsupport hHsupport hbudget)
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end
end RCN124
end SubmissionLower
end ProximityPrize
end PackedLegacy_EE
section PackedLegacy_Y7
namespace ProximityPrize
namespace SubmissionLower
namespace RCN093
open scoped Classical BigOperators
open RCN002 RCN005 RCN022 RCN011 RCN371
open RCN371 renaming RationalPolynomials → KU
open RCN125 RCN124
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem ACO (lam μ ν:K)
   (F:MvPolynomial (Fin 3) K):
   RCN093.flagEvaluation K P lam μ ν (flagAlgHom_p19 lam μ ν F)=
     RCN002.coordinateEvaluation K P F:=by
 change MvPolynomial.eval₂Hom (algebraMap K (RCN002.CoordinateField K P))
     ![coordinate K P 0+lam • coordinate K P 2,
       coordinate K P 1+μ • coordinate K P 0+ν • coordinate K P 2,
       coordinate K P 2] (flagAlgHom_p19 lam μ ν F)=_
 rw [show lam • coordinate K P 2=
     algebraMap K (RCN002.CoordinateField K P) lam*coordinate K P 2 by
       simp [Algebra.smul_def],
   show μ • coordinate K P 0=
     algebraMap K (RCN002.CoordinateField K P) μ*coordinate K P 0 by
       simp [Algebra.smul_def],
   show ν • coordinate K P 2=
     algebraMap K (RCN002.CoordinateField K P) ν*coordinate K P 2 by
       simp [Algebra.smul_def],
   eval₂Hom_flag_at_affine_p19]
 rw [RCN002.coordinateEvaluation_eq_aeval]
 have hx:(![coordinate K P 0,coordinate K P 1,coordinate K P 2]:
     Fin 3→RCN002.CoordinateField K P)=coordinate K P:=by
   funext i
   fin_cases i<;>rfl
 rw [hx]
 exact (MvPolynomial.aeval_eq_eval₂Hom (coordinate K P) F).symm
theorem AEE (lam μ ν:K):
   (RingHom.ker (RCN093.flagEvaluation K P lam μ ν).toRingHom).comap
       (flagAlgHom_p19 lam μ ν).toRingHom=P:=by
 rw [RingHom.comap_ker]
 have hcomp:(RCN093.flagEvaluation K P lam μ ν).comp (flagAlgHom_p19 lam μ ν)=
     RCN002.coordinateEvaluation K P:=by
   apply AlgHom.ext
   intro F
   exact ACO K P lam μ ν F
 have hring:=congrArg
   (fun f:MvPolynomial (Fin 3) K→ₐ[K] RCN002.CoordinateField K P↦
     f.toRingHom) hcomp
 rw [show (RCN093.flagEvaluation K P lam μ ν).toRingHom.comp
     (flagAlgHom_p19 lam μ ν).toRingHom=
     (RCN002.coordinateEvaluation K P).toRingHom from hring,
   RCN002.coordinateEvaluation_ker]
theorem CFB
   [Algebra (RatFunc K) (RCN002.CoordinateField K P)]
   [IsScalarTower K (RatFunc K) (RCN002.CoordinateField K P)]
   (lam μ ν:K)
   (L:IntermediateField (RatFunc K) (RCN002.CoordinateField K P))
   (hU:affineU K P lam∈L) (hV:affineV K P μ ν∈L)
   (hZ:coordinate K P 2∈L):L=⊤:=by
 have hlam:algebraMap K (RCN002.CoordinateField K P) lam∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) lam)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (RCN002.CoordinateField K P)] using h
 have hμ:algebraMap K (RCN002.CoordinateField K P) μ∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) μ)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (RCN002.CoordinateField K P)] using h
 have hν:algebraMap K (RCN002.CoordinateField K P) ν∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) ν)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (RCN002.CoordinateField K P)] using h
 have hY:coordinate K P 0∈L:=by
   have h:=L.sub_mem hU (L.mul_mem hlam hZ)
   simpa only [affineU,Algebra.smul_def,add_sub_cancel_right] using h
 have hS:coordinate K P 1∈L:=by
   have h:=L.sub_mem hV
     (L.add_mem (L.mul_mem hμ hY) (L.mul_mem hν hZ))
   have heq:affineV K P μ ν-
       (algebraMap K (RCN002.CoordinateField K P) μ*coordinate K P 0+
         algebraMap K (RCN002.CoordinateField K P) ν*coordinate K P 2)=
       coordinate K P 1:=by
     simp only [affineV,Algebra.smul_def]
     ring
   rwa [heq] at h
 have hcoords:Set.range (coordinate K P) ⊆ L.restrictScalars K:=by
   rintro x ⟨i,rfl⟩
   fin_cases i
   · exact hY
   · exact hS
   · exact hZ
 have htop:L.restrictScalars K=⊤:=by
   apply top_unique
   rw [←RCN002.adjoin_coordinates_eq_top K P]
   exact IntermediateField.adjoin_le_iff.mpr hcoords
 exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
theorem BUX (lam μ ν:K)
   (hU:Transcendental K (affineU K P lam)):
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
     (RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineU K P lam)
       hU).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P 2,affineV K P μ ν}:
       Set (RCN002.CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
   (RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineU K P lam)
     hU).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (RCN002.CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineU K P lam)
       hU).commutes c).symm
 let L:IntermediateField (RatFunc K) (RCN002.CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {coordinate K P 2,affineV K P μ ν}
 have hZ:coordinate K P 2∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hV:affineV K P μ ν∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hUmem:affineU K P lam∈L:=by
   change RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineU K P lam) hU
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [RCN022.elementEmbedding_variable] at hbase
 exact CFB K P lam μ ν L hUmem hV hZ
theorem BTS (lam μ ν:K)
   (hV:Transcendental K (affineV K P μ ν)):
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
     (RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineV K P μ ν)
       hV).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P 2,affineU K P lam}:
       Set (RCN002.CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
   (RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineV K P μ ν)
     hV).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (RCN002.CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineV K P μ ν)
       hV).commutes c).symm
 let L:IntermediateField (RatFunc K) (RCN002.CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {coordinate K P 2,affineU K P lam}
 have hZ:coordinate K P 2∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hU:affineU K P lam∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hVmem:affineV K P μ ν∈L:=by
   change RCN022.elementEmbedding K (RCN002.CoordinateField K P) (affineV K P μ ν) hV
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [RCN022.elementEmbedding_variable] at hbase
 exact CFB K P lam μ ν L hU hVmem hZ
theorem BKE (lam μ ν:K)
   (hZ:Transcendental K (coordinate K P 2)):
   letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
     (RCN022.elementEmbedding K (RCN002.CoordinateField K P) (coordinate K P 2)
       hZ).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({affineU K P lam,affineV K P μ ν}:
       Set (RCN002.CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
   (RCN022.elementEmbedding K (RCN002.CoordinateField K P) (coordinate K P 2)
     hZ).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (RCN002.CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((RCN022.elementEmbedding K (RCN002.CoordinateField K P) (coordinate K P 2)
       hZ).commutes c).symm
 let L:IntermediateField (RatFunc K) (RCN002.CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {affineU K P lam,affineV K P μ ν}
 have hU:affineU K P lam∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hV:affineV K P μ ν∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hZmem:coordinate K P 2∈L:=by
   change RCN022.elementEmbedding K (RCN002.CoordinateField K P) (coordinate K P 2) hZ
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [RCN022.elementEmbedding_variable] at hbase
 exact CFB K P lam μ ν L hU hV hZmem
section Family
variable {I:Type} [Fintype I]
 (Q:I→Ideal (MvPolynomial (Fin 3) K)) [∀i,(Q i).IsPrime]
theorem AVC
   (hinj:Function.Injective Q) (lam μ ν:K):
   Function.Injective (fun i↦
     RingHom.ker (RCN093.flagEvaluation K (Q i) lam μ ν).toRingHom):=by
 intro i j hij
 apply hinj
 have hc:=congrArg (Ideal.comap (flagAlgHom_p19 lam μ ν).toRingHom) hij
 simpa only [AEE] using hc
theorem RG
   (hinj:Function.Injective Q) (lam μ ν:K)
   (order:Fin 3 ≃ Fin 3)
   (ht:∀i,Transcendental K
     (RCN093.flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0))))
   (hgen:∀i,
     letI:Algebra (RatFunc K) (RCN002.CoordinateField K (Q i)):=
       (RCN022.elementEmbedding K (RCN002.CoordinateField K (Q i))
         (RCN093.flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0)))
         (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({RCN093.flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 2)),
         RCN093.flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 1))}:
         Set (RCN002.CoordinateField K (Q i)))=⊤)
   (G H:MvPolynomial (Fin 3) K) (hG:Irreducible G)
   (hGmem:∀i,G∈Q i) (hHmem:∀i,H∈Q i)
   (hproper:¬G∣H)
   (hpositive:0<
     (planeMap K order (flagAlgHom_p19 lam μ ν G)).natDegree)
   (n mCap totalG totalH cap:ℕ) (hHne:H≠0)
   (hGouter:(planeMap K order
     (flagAlgHom_p19 lam μ ν G)).natDegree≤n)
   (hHouter:(planeMap K order
     (flagAlgHom_p19 lam μ ν H)).natDegree≤mCap)
   (hGsupport:∀d∈(rationalMap K order
     (flagAlgHom_p19 lam μ ν G)).support,d 0+d 1≤totalG)
   (hHsupport:∀d∈(rationalMap K order
     (flagAlgHom_p19 lam μ ν H)).support,d 0+d 1≤totalH)
   (hbudget:∀m,m≤mCap→
     m*totalG+n*totalH-m*n≤cap):
   letI:∀i,Algebra (RatFunc K) (RCN002.CoordinateField K (Q i)):=
     fun i↦(RCN022.elementEmbedding K (RCN002.CoordinateField K (Q i))
       (RCN093.flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0)))
       (ht i)).toRingHom.toAlgebra
   (∀i,FiniteDimensional (RatFunc K) (RCN002.CoordinateField K (Q i)))∧
     (∑ i,Module.finrank (RatFunc K) (RCN002.CoordinateField K (Q i)))≤cap:=by
 let e:∀i,MvPolynomial (Fin 3) K→ₐ[K] RCN002.CoordinateField K (Q i):=
   fun i↦RCN093.flagEvaluation K (Q i) lam μ ν
 have hGroot:∀i,e i (flagAlgHom_p19 lam μ ν G)=0:=by
   intro i
   rw [show e i (flagAlgHom_p19 lam μ ν G)=RCN002.coordinateEvaluation K (Q i) G
     from ACO K (Q i) lam μ ν G]
   change G∈RingHom.ker (RCN002.coordinateEvaluation K (Q i)).toRingHom
   rw [RCN002.coordinateEvaluation_ker]
   exact hGmem i
 have hHroot:∀i,e i (flagAlgHom_p19 lam μ ν H)=0:=by
   intro i
   rw [show e i (flagAlgHom_p19 lam μ ν H)=RCN002.coordinateEvaluation K (Q i) H
     from ACO K (Q i) lam μ ν H]
   change H∈RingHom.ker (RCN002.coordinateEvaluation K (Q i)).toRingHom
   rw [RCN002.coordinateEvaluation_ker]
   exact hHmem i
 exact CXF K order
   (fun i↦RCN002.CoordinateField K (Q i)) e ht hgen
   (AVC K Q hinj lam μ ν)
   (flagAlgHom_p19 lam μ ν G) (flagAlgHom_p19 lam μ ν H)
   ((ARZ lam μ ν G).mpr hG)
   hGroot hHroot (by simpa only [flag_dvd_iff_p19] using hproper) hpositive
   n mCap totalG totalH cap (flag_ne_zero_p19 lam μ ν hHne)
   hGouter hHouter hGsupport hHsupport hbudget
end Family
end
end RCN093
end SubmissionLower
end ProximityPrize
end PackedLegacy_Y7
section PackedLegacy_BB
namespace ProximityPrize
namespace SubmissionLower
namespace RCN118
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005 RCN006 RCN007
open RCN344 RCN264 RCN272 RCN273
open RCN323 RCN075 RCN095 RCN114 RCN187 RCN295
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
structure AUI
   {G T H:MvPolynomial (Fin 3) Ω}
   (p:FlagDegree) (separator:Fin 3)
   (hseparator:∀C:RCN264.RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀C:RCN264.RegularComponent Ω G T H,
     RCN007.ProjectionsFiniteSeparable Ω C.1)
   (B:KV G T H (flagSupport p) separator
     hseparator hproj)
   (zCap yzCap allCap:ℕ) where
 zCost:RCN264.RegularComponent Ω G T H→ℕ
 yzCost:RCN264.RegularComponent Ω G T H→ℕ
 allCost:RCN264.RegularComponent Ω G T H→ℕ
 cycle_le:∀C:RCN264.RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (RCN002.CoordinateRing Ω C.1):=
     RCN006.quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (RCN002.CoordinateField Ω C.1):=
     RCN006.polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     RCN005.rationalBaseAlgebra Ω C.1 separator htr
   letI:=RCN006.quotientBaseScalarTower Ω C.1 separator
   letI:=RCN006.polynomialBaseScalarTower Ω C.1 separator
   letI:=RCN006.quotientFractionScalarTower Ω C.1 separator
   letI:=RCN006.polynomialRationalScalarTower Ω C.1 separator htr
   letI:=RCN005.rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (RCN002.CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   let hb:b≠0:=NR
     C.1 B.polynomial (B.proper C)
   (∑ v∈RCN026.placesFor_p19 Ω
       (RCN002.CoordinateField Ω C.1) b hb,
     RCN346.poleOrder_p19 Ω (RCN002.CoordinateField Ω C.1) v b)≤
       ((p.zOnly*zCost C+p.yz*yzCost C+
         p.all*allCost C:ℕ):ℤ)
 sum_zCost_le:(∑ C:RCN264.RegularComponent Ω G T H,zCost C)≤zCap
 BMO:(∑ C:RCN264.RegularComponent Ω G T H,yzCost C)≤yzCap
 BBW:(∑ C:RCN264.RegularComponent Ω G T H,allCost C)≤allCap
end
end RCN118
end SubmissionLower
end ProximityPrize
end PackedLegacy_BB
section PackedLegacy_Y8
namespace ProximityPrize
namespace SubmissionLower
namespace RCN097
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain RCN022 RCN351 RCN344 RCN295 RCN075 RCN002 RCN005 RCN007 RCN264 RCN093
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem ANP
   {K L:Type*} [Field K] [Field L] [Algebra K L]
   (v:RCN345.ACR K L)
   (r z:L):
   ∀{a b:K},
     v.val (r+a • z)<max (v.val r) (v.val z)→
     v.val (r+b • z)<max (v.val r) (v.val z)→a=b:=by
 intro a b ha hb
 by_contra hab
 have hab0:a-b≠0:=sub_ne_zero.mpr hab
 letI:v.val.IsTrivialOn K:=v.property.2
 have hdiff:v.val ((r+a • z)-(r+b • z))<
     max (v.val r) (v.val z):=v.val.map_sub_lt ha hb
 have hvaldiff:v.val ((r+a • z)-(r+b • z))=v.val z:=by
   rw [show (r+a • z)-(r+b • z)=(a-b) • z by module,
     Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one (a-b) hab0,one_mul]
 rw [hvaldiff] at hdiff
 have hzr:v.val z<v.val r:=by
   simpa only [lt_max_iff,lt_self_iff_false,or_false] using hdiff
 have hmax:max (v.val r) (v.val z)=v.val r:=max_eq_left hzr.le
 have ha0:a≠0:=by
   intro ha0
   rw [ha0,zero_smul,add_zero,hmax] at ha
   exact (lt_irrefl _ ha).elim
 have haz:v.val (a • z)=v.val z:=by
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 have hsum:v.val (r+a • z)=v.val r:=by
   apply v.val.map_add_eq_of_lt_left
   rwa [haz]
 rw [hsum,hmax] at ha
 exact (lt_irrefl _ ha).elim
section RegularComponents
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
 {G T H:MvPolynomial (Fin 3) Ω}
structure UZ
   (hseparator:∀C:RCN264.RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 2))
   (hproj:∀C:RCN264.RegularComponent Ω G T H,
     RCN007.ProjectionsFiniteSeparable Ω C.1) where
 lam:Ω
 lam_ne:lam≠0
 hU:∀C:RCN264.RegularComponent Ω G T H,
   Transcendental Ω (affineU Ω C.1 lam)
 finiteU:∀C:RCN264.RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω C.1)
       (affineU Ω C.1 lam) (hU C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω C.1)
 separableU:∀C:RCN264.RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω C.1)
       (affineU Ω C.1 lam) (hU C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω C.1)
 exactU:∀C:RCN264.RegularComponent Ω G T H,
   ∀v∈AJQ hseparator hproj C,
     v.val (affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 0))
         (v.val (coordinate Ω C.1 2))
 mu:Ω
 mu_ne:mu≠0
 hV:∀C:RCN264.RegularComponent Ω G T H,
   Transcendental Ω
     (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
 finiteV:∀C:RCN264.RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω C.1)
       (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
       (hV C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Ω) (RCN002.CoordinateField Ω C.1)
 separableV:∀C:RCN264.RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (RCN002.CoordinateField Ω C.1):=
     (RCN022.elementEmbedding Ω (RCN002.CoordinateField Ω C.1)
       (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
       (hV C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (RCN002.CoordinateField Ω C.1)
 exactV:∀C:RCN264.RegularComponent Ω G T H,
   ∀v∈AJQ hseparator hproj C,
     v.val (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 1))
         (v.val (affineU Ω C.1 lam))
end RegularComponents
end
end RCN097
end SubmissionLower
end ProximityPrize
end PackedLegacy_Y8
section PackedLegacy_DN
namespace ProximityPrize
namespace SubmissionLower
namespace RCN035
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential RCN344 RCN369 RCN370 RCN351
open RCN022 RCN097
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
 {I:Type*} [Fintype I]
 (E:I→Type*) [∀i,Field (E i)] [∀i,Algebra K (E i)]
 (r z:∀i,E i)
variable (W:∀i,
 Finset (RCN345.ACR K (E i)))
theorem RQ
   (S:Set K) (hS:S.Infinite)
   (base:∀i,RCN344.SeparableCoordinate K (E i))
   (hactive:∀i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃a:K,a∈S∧a≠0∧∀i,
     ∃ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (RCN022.elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (RCN022.elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 let J:=I ⊕ Sigma fun i:I=>{v//v∈W i}
 let Bad:J→K→Prop
   | Sum.inl i,a=>D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr iv,a=>iv.2.1.val (r iv.1+a • z iv.1)<
       max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀j {a b},Bad j a→Bad j b→a=b:=by
   intro j a b ha hb
   rcases j with i | ⟨i,v⟩
   · by_cases hdz:D K (E i) (z i)=0
     · have hdr:D K (E i) (r i)≠0:=
         (hactive i).resolve_right (fun hn=>hn hdz)
       change D K (E i) (r i)+a • D K (E i) (z i)=0 at ha
       exfalso
       apply hdr
       simpa only [hdz,smul_zero,add_zero] using ha
     · exact RCN351.shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
         hdz ha hb
   · exact ANP v.1 (r i) (z i) ha hb
 obtain ⟨a,haS,ha0,havoid⟩:=
   RCN097.exists_nonzero_avoiding_finite_subsingleton_in S hS Bad hsingle
 refine ⟨a,haS,ha0,fun i=> ?_⟩
 have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
   exact havoid (Sum.inl i)
 have hD:D K (E i) (r i+a • z i)≠0:=by
   rw [map_add,(D K (E i)).map_smul]
   exact hdiff
 obtain ⟨ht,hfinite,hsep⟩:=
   RCN035.element_transcendental_finite_separable_of_differential_ne_zero
     K (E i) (base i) (r i+a • z i) hD
 refine ⟨ht,hfinite,hsep,?_⟩
 intro v hv
 have hnotlt:=havoid (Sum.inr ⟨i,⟨v,hv⟩⟩)
 have hupper:=v.val.map_add (r i) (a • z i)
 have haz:v.val (a • z i)=v.val (z i):=by
   letI:v.val.IsTrivialOn K:=v.property.2
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 rw [haz] at hupper
 exact le_antisymm hupper (le_of_not_gt hnotlt)
theorem AFY
   (base:∀i,RCN344.SeparableCoordinate K (E i))
   (hactive:∀i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃a:K,a≠0∧∀i,
     ∃ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (RCN022.elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (RCN022.elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 obtain ⟨a,-,h⟩:=RQ E r z W
   Set.univ Set.infinite_univ base hactive
 exact ⟨a,h⟩
theorem WV
   (S:Set K) (hS:S.Infinite)
   (Extra:K→Prop)
   (hextra:∀{a b},Extra a→Extra b→a=b)
   (base:∀i,RCN344.SeparableCoordinate K (E i))
   (hactive:∀i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃a:K,a∈S∧a≠0∧¬Extra a∧∀i,
     ∃ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (RCN022.elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (RCN022.elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 let J:=Unit ⊕ (I ⊕ Sigma fun i:I=>{v//v∈W i})
 let Bad:J→K→Prop
   | Sum.inl _,a=>Extra a
   | Sum.inr (Sum.inl i),a=>
       D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr (Sum.inr iv),a=>iv.2.1.val (r iv.1+a • z iv.1)<
       max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀j {a b},Bad j a→Bad j b→a=b:=by
   intro j a b ha hb
   rcases j with _ | i | ⟨i,v⟩
   · exact hextra ha hb
   · by_cases hdz:D K (E i) (z i)=0
     · have hdr:D K (E i) (r i)≠0:=
         (hactive i).resolve_right (fun hn=>hn hdz)
       change D K (E i) (r i)+a • D K (E i) (z i)=0 at ha
       exfalso
       apply hdr
       simpa only [hdz,smul_zero,add_zero] using ha
     · exact RCN351.shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
         hdz ha hb
   · exact ANP v.1 (r i) (z i) ha hb
 obtain ⟨a,haS,ha0,havoid⟩:=
   RCN097.exists_nonzero_avoiding_finite_subsingleton_in S hS Bad hsingle
 refine ⟨a,haS,ha0,havoid (Sum.inl ()),fun i=> ?_⟩
 have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
   exact havoid (Sum.inr (Sum.inl i))
 have hD:D K (E i) (r i+a • z i)≠0:=by
   rw [map_add,(D K (E i)).map_smul]
   exact hdiff
 obtain ⟨ht,hfinite,hsep⟩:=
   RCN035.element_transcendental_finite_separable_of_differential_ne_zero
     K (E i) (base i) (r i+a • z i) hD
 refine ⟨ht,hfinite,hsep,?_⟩
 intro v hv
 have hnotlt:=havoid (Sum.inr (Sum.inr ⟨i,⟨v,hv⟩⟩))
 have hupper:=v.val.map_add (r i) (a • z i)
 have haz:v.val (a • z i)=v.val (z i):=by
   letI:v.val.IsTrivialOn K:=v.property.2
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 rw [haz] at hupper
 exact le_antisymm hupper (le_of_not_gt hnotlt)
theorem YC
   (Extra:K→Prop)
   (hextra:∀{a b},Extra a→Extra b→a=b)
   (base:∀i,RCN344.SeparableCoordinate K (E i))
   (hactive:∀i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃a:K,a≠0∧¬Extra a∧∀i,
     ∃ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (RCN022.elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (RCN022.elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 obtain ⟨a,-,h⟩:=WV E r z W
   Set.univ Set.infinite_univ Extra hextra base hactive
 exact ⟨a,h⟩
end FiniteFamily
end
end RCN035
end SubmissionLower
end ProximityPrize
end PackedLegacy_DN
section PackedLegacy_A3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN046
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN264 RCN095 RCN341 RCN340 RCN237 RCN295 RCN042
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure EE
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 zProjection:∀C:RCN264.RegularComponent Omega G T H,
   Coordinate Omega (RCN002.CoordinateField Omega C.1)
 yzProjection:∀C:RCN264.RegularComponent Omega G T H,
   Coordinate Omega (RCN002.CoordinateField Omega C.1)
 NV:∀C:RCN264.RegularComponent Omega G T H,
   Coordinate Omega (RCN002.CoordinateField Omega C.1)
 zValue:∀C:RCN264.RegularComponent Omega G T H,
   RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (zProjection C)=
     coordinate Omega C.1 2
 ACE:∀C:RCN264.RegularComponent Omega G T H,
   Transcendental Omega
     (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (NV C))
 zPole_eq:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
   RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitZFlag)=
     RCN346.poleOrder_p19 Omega (RCN002.CoordinateField Omega C.1) v
       (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (zProjection C))
 yzPole_eq:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
   RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitYZFlag)=
     RCN346.poleOrder_p19 Omega (RCN002.CoordinateField Omega C.1) v
       (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (yzProjection C))
 allPole_eq:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
   RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitAllFlag)=
     RCN346.poleOrder_p19 Omega (RCN002.CoordinateField Omega C.1) v
       (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (NV C))
 ARJ:
   (∑ C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (zProjection C))≤
     flagMixed p q unitZFlag
 ALE:
   (∑ C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (yzProjection C))≤
     flagMixed p q unitYZFlag
 AQB:
   (∑ C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (NV C))≤
     flagMixed p q unitAllFlag
def EE.toQZ
   {base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:EE base p q):
   QZ base p q where
 zCost:=fun C=>RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
   (P.zProjection C)
 yzCost:=fun C=>RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
   (P.yzProjection C)
 allCost:=fun C=>RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
   (P.NV C)
 sum_zCost_le:=P.ARJ
 BMO:=P.ALE
 BBW:=P.AQB
 zPole:=by
   intro C
   unfold UJ
   dsimp only
   intro W
   calc
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitZFlag))=
         ∑ v∈W,RCN346.poleOrder_p19 Omega
           (RCN002.CoordinateField Omega C.1) v
           (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1)
             (P.zProjection C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.zPole_eq C v
     _≤(RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
         (P.zProjection C):ℤ):=
       PY Omega
         (RCN002.CoordinateField Omega C.1) (P.zProjection C) W
 yzPole:=by
   intro C
   unfold UJ
   dsimp only
   intro W
   calc
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitYZFlag))=
         ∑ v∈W,RCN346.poleOrder_p19 Omega
           (RCN002.CoordinateField Omega C.1) v
           (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1)
             (P.yzProjection C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.yzPole_eq C v
     _≤(RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
         (P.yzProjection C):ℤ):=
       PY Omega
         (RCN002.CoordinateField Omega C.1) (P.yzProjection C) W
 allPole:=by
   intro C
   unfold UJ
   dsimp only
   intro W
   calc
     (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitAllFlag))=
         ∑ v∈W,RCN346.poleOrder_p19 Omega
           (RCN002.CoordinateField Omega C.1) v
           (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1)
             (P.NV C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.allPole_eq C v
     _≤(RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
         (P.NV C):ℤ):=
       PY Omega
         (RCN002.CoordinateField Omega C.1) (P.NV C) W
def EE.toFE
   {base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:EE base p q):
   FE (G:=G) (T:=T) (H:=H) p q:=
 P.toQZ.toFE
theorem EE.one_le_zDegree_of_transcendental
   {base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:EE base p q)
   (C:RCN264.RegularComponent Omega G T H)
   (hZ:Transcendental Omega (coordinate Omega C.1 2)):
   1≤RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
     (P.zProjection C):=by
 apply RCN042.one_le_coordinateDegree_of_transcendental_value
 rwa [P.zValue C]
theorem EE.one_le_toPrimeFlagBudgetFamily_zCost
   {base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:EE base p q)
   (C:RCN264.RegularComponent Omega G T H)
   (hZ:Transcendental Omega (coordinate Omega C.1 2)):
   1≤P.toFE.zCost C:=
 P.one_le_zDegree_of_transcendental C hZ
end
end RCN046
end SubmissionLower
end ProximityPrize
end PackedLegacy_A3
section PackedLegacy_DS
namespace ProximityPrize
namespace SubmissionLower
namespace RCN044
open scoped Classical WithZero
open IsDedekindDomain RCN187 RCN002 RCN005 RCN006
open RCN344 RCN341
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
def OW
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:RCN341.SeparableLiteralCoordinate P):
   Finset (Place_p19 Omega (RCN002.CoordinateField Omega P)):=by
 classical
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (RCN002.CoordinateRing Omega P):=
   RCN006.quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (RCN002.CoordinateField Omega P):=
   RCN006.polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega P):=
   RCN005.rationalBaseAlgebra Omega P i0 htr
 letI:=RCN006.quotientBaseScalarTower Omega P i0
 letI:=RCN006.polynomialBaseScalarTower Omega P i0
 letI:=RCN006.quotientFractionScalarTower Omega P i0
 letI:=RCN006.polynomialRationalScalarTower Omega P i0 htr
 letI:=RCN005.rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega P):=D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega P):=D.separable
 exact Finset.univ.biUnion (fun i:Fin 3=>
   if hi:coordinate Omega P i≠0 then
     RCN026.placesFor_p19 Omega (RCN002.CoordinateField Omega P)
       (coordinate Omega P i) hi
   else ∅)
theorem DW
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:RCN341.SeparableLiteralCoordinate P)
   (v:Place_p19 Omega (RCN002.CoordinateField Omega P))
   (hv:v∉OW D) (i:Fin 3):
   poleOrder v.val (coordinate Omega P i)=0:=by
 classical
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (RCN002.CoordinateRing Omega P):=
   RCN006.quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (RCN002.CoordinateField Omega P):=
   RCN006.polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega P):=
   RCN005.rationalBaseAlgebra Omega P i0 htr
 letI:=RCN006.quotientBaseScalarTower Omega P i0
 letI:=RCN006.polynomialBaseScalarTower Omega P i0
 letI:=RCN006.quotientFractionScalarTower Omega P i0
 letI:=RCN006.polynomialRationalScalarTower Omega P i0 htr
 letI:=RCN005.rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega P):=D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega P):=D.separable
 by_cases hi:coordinate Omega P i=0
 · simp [hi,poleOrder]
 · have hnot:v∉RCN026.placesFor_p19 Omega
       (RCN002.CoordinateField Omega P) (coordinate Omega P i) hi:=by
     intro hmem
     apply hv
     unfold OW
     apply Finset.mem_biUnion.mpr
     exact ⟨i,Finset.mem_univ _,by simp [hi,hmem]⟩
   have horder:RCN026.order_p19 Omega (RCN002.CoordinateField Omega P) v
       (coordinate Omega P i)=0:=by
     by_contra hne
     exact hnot (RCN026.ALB Omega
       (RCN002.CoordinateField Omega P) (coordinate Omega P i) hi v hne)
   unfold RCN026.order_p19 at horder
   unfold poleOrder
   have hlog:(v.val (coordinate Omega P i)).log=0:=by omega
   rw [hlog]
   simp
end
end RCN044
end SubmissionLower
end ProximityPrize
end PackedLegacy_DS
section PackedLegacy_ED
namespace ProximityPrize
namespace SubmissionLower
namespace RCN115
open scoped Classical BigOperators
open IsDedekindDomain RCN002 RCN005 RCN006 RCN007
open RCN344 RCN264 RCN075 RCN323 RCN118 RCN093 RCN125 RCN371 RCN011 RCN022
open RCN371 renaming RationalPolynomials → KU
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
structure AGX
   {G T H:MvPolynomial (Fin 3) Omega}
   (E:Finset (Fin 3→₀ ℕ)) (separator:Fin 3)
   (hseparator:∀C:RCN264.RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator))
   (hproj:∀C:RCN264.RegularComponent Omega G T H,
     RCN007.ProjectionsFiniteSeparable Omega C.1)
   (B:KV G T H E separator hseparator hproj) where
 parameter:∀C:RCN264.RegularComponent Omega G T H,
   RCN344.SeparableCoordinate Omega (RCN002.CoordinateField Omega C.1)
 pole_eq:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (RCN002.CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   RCN346.poleOrder_p19 Omega (RCN002.CoordinateField Omega C.1) v b=
     RCN346.poleOrder_p19 Omega (RCN002.CoordinateField Omega C.1) v
       (RCN344.SeparableCoordinate.value Omega (RCN002.CoordinateField Omega C.1)
         (parameter C))
def AGX.cost
   {G T H:MvPolynomial (Fin 3) Omega}
   {E:Finset (Fin 3→₀ ℕ)} {separator:Fin 3}
   {hseparator:∀C:RCN264.RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator)}
   {hproj:∀C:RCN264.RegularComponent Omega G T H,
     RCN007.ProjectionsFiniteSeparable Omega C.1}
   {B:KV G T H E separator hseparator hproj}
   (P:AGX E separator hseparator hproj B)
   (C:RCN264.RegularComponent Omega G T H):ℕ:=
 RCN344.SeparableCoordinate.degree Omega (RCN002.CoordinateField Omega C.1) (P.parameter C)
end
end RCN115
end SubmissionLower
end ProximityPrize
end PackedLegacy_ED
section PackedLegacy_Z0
namespace ProximityPrize
namespace SubmissionLower
namespace RCN116
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005 RCN006 RCN007
open RCN344 RCN264 RCN187 RCN075 RCN295 RCN095 RCN114 RCN125 RCN093 RCN097 RCN099 RCN115 RCN118 RCN123 RCN272 RCN371 RCN011 RCN022
open RCN095 renaming PolynomialInFlag → BI
open RCN371 renaming RationalPolynomials → KU
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable {hseparator:∀C:RCN264.RegularComponent Omega G T H,
 Transcendental Omega (coordinate Omega C.1 2)}
variable {hproj:∀C:RCN264.RegularComponent Omega G T H,
 RCN007.ProjectionsFiniteSeparable Omega C.1}
structure ENR
   (D:UZ hseparator hproj)
   (G:MvPolynomial (Fin 3) Omega):Prop where
 u:0<(planeMap Omega uOrder_p19
   (flagAlgHom_p19 D.lam D.mu (D.mu*D.lam) G)).natDegree
 v:0<(planeMap Omega vOrder_p19
   (flagAlgHom_p19 D.lam D.mu (D.mu*D.lam) G)).natDegree
 z:0<(planeMap Omega zOrder_p19
   (flagAlgHom_p19 D.lam D.mu (D.mu*D.lam) G)).natDegree
end
end RCN116
end SubmissionLower
end ProximityPrize
end PackedLegacy_Z0
section PackedLegacy_X9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN037
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044 RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370 RCN351
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
theorem AQU
   {L:Type*} [Field L] [Algebra Omega L]
   (v:RCN346.Place_p19 Omega L) (x:L)
   (hx:IsAlgebraic Omega x):
   RCN187.poleOrder v.val x=0:=by
 obtain ⟨a,rfl⟩:=RCN370.eq_algebraMap_of_isAlgebraic Omega L x hx
 exact RCN346._Q11 Omega L v _
   (NP Omega L v a)
structure AOH
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hY:∀C:RCN264.RegularComponent Omega G T H,RCN037.LiteralProjectionGate C 0)
   (hZ:∀C:RCN264.RegularComponent Omega G T H,RCN037.LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0) where
 lam:Omega
 lam_ne:lam≠0
 mu:Omega
 mu_ne:mu≠0
 uProjection:∀C:RCN264.RegularComponent Omega G T H,
   Coordinate Omega (RCN002.CoordinateField Omega C.1)
 NV:∀C:RCN264.RegularComponent Omega G T H,
   Coordinate Omega (RCN002.CoordinateField Omega C.1)
 uGate:∀C:RCN264.RegularComponent Omega G T H,
   ∀htr:Transcendental Omega (affineU Omega C.1 lam),
     (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
         (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1))∧
     (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
         (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1))
 GN:∀C:RCN264.RegularComponent Omega G T H,
   Transcendental Omega (affineV Omega C.1 mu (mu*lam))
 allFinite:∀C:RCN264.RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (GN C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1)
 allSeparable:∀C:RCN264.RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (GN C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1)
 uValue:∀C:RCN264.RegularComponent Omega G T H,
   RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (uProjection C)=
     affineU Omega C.1 lam
 allValue:∀C:RCN264.RegularComponent Omega G T H,
   RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (NV C)=
     affineV Omega C.1 mu (mu*lam)
 ACE:∀C:RCN264.RegularComponent Omega G T H,
   Transcendental Omega
     (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (NV C))
 uPole:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (uProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
       (RCN187.poleOrder v.val (coordinate Omega C.1 2))
 allPole:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (NV C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
       (max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)))
 directional:MvPolynomial.pderiv (0:Fin 3) G-
   MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0
theorem ALD
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hY:∀C:RCN264.RegularComponent Omega G T H,RCN037.LiteralProjectionGate C 0)
   (hZ:∀C:RCN264.RegularComponent Omega G T H,RCN037.LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   Nonempty (AOH base hY hZ hSderiv):=by
 classical
 let ActiveU:={C:RCN264.RegularComponent Omega G T H//
   D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0}
 let EU:ActiveU→Type:=fun C=>RCN002.CoordinateField Omega C.1.1
 let rY:∀C:ActiveU,EU C:=fun C=>coordinate Omega C.1.1 0
 let z:∀C:ActiveU,EU C:=fun C=>coordinate Omega C.1.1 2
 let WU:∀C:ActiveU,Finset (Place_p19 Omega (EU C)):=
   fun C=>OW (base C.1)
 let baseU:∀C:ActiveU,RCN344.SeparableCoordinate Omega (EU C):=
   fun C=>RCN042.literalToSeparableCoordinate (base C.1)
 obtain ⟨lam,hlam0,hlam⟩:=
   AFY EU rY z WU
     baseU (fun C=>C.2)
 let U:∀C:RCN264.RegularComponent Omega G T H,
     RCN002.CoordinateField Omega C.1:=
   fun C=>affineU Omega C.1 lam
 have hUgate:∀C:RCN264.RegularComponent Omega G T H,
     ∀htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1))∧
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1)):=by
   intro C htr
   by_cases hactive:
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     obtain ⟨hs,hfinite,hsep,_⟩:=hlam CU
     have hp:htr=hs:=Subsingleton.elim _ _
     cases hp
     exact ⟨hfinite,hsep⟩
   · have hzero:=not_or.mp hactive
     have hYalg:IsAlgebraic Omega (coordinate Omega C.1 0):=by
       apply not_not.mp
       intro hy
       exact (RCN042.differential_ne_zero_of_gate _ hy (hY C hy))
         (not_ne_iff.mp hzero.1)
     have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=by
       apply not_not.mp
       intro hz
       exact (RCN042.differential_ne_zero_of_gate _ hz (hZ C hz))
         (not_ne_iff.mp hzero.2)
     exact (htr (hYalg.add (hZalg.smul lam))).elim
 let uProjection:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=
   fun C=>RCN042.coordinateOfGate (U C) (hUgate C)
 have huValue:∀C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (uProjection C)=U C:=
   fun C=>RCN042.coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)):=by
   intro C v
   by_cases hactive:
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     by_cases hv:v∈OW (base C)
     · exact RCN099.poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
         simpa only [WU,rY,z,U,affineU] using
           (hlam CU).choose_spec.2.2 v hv)
     · have h0:=DW
           (base C) v hv 0
       have h2:=DW
           (base C) v hv 2
       have h0le:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ h0
       have h2le:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ h2
       letI:v.val.IsTrivialOn Omega:=v.property.2
       have hscalar:v.val (lam • coordinate Omega C.1 2)=
           v.val (coordinate Omega C.1 2):=by
         rw [Algebra.smul_def,map_mul,
           Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
       have hUle:v.val (U C)≤1:=by
         exact (v.val.map_add _ _).trans
           (by rw [hscalar];exact max_le h0le h2le)
       have hU0:RCN187.poleOrder v.val (U C)=0:=
         RCN346._Q11 Omega
           (RCN002.CoordinateField Omega C.1) v _ hUle
       rw [hU0,h0,h2]
       simp
   · have hzero:=not_or.mp hactive
     have hYalg:IsAlgebraic Omega (coordinate Omega C.1 0):=by
       apply not_not.mp
       intro hy
       exact (RCN042.differential_ne_zero_of_gate _ hy (hY C hy))
         (not_ne_iff.mp hzero.1)
     have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=by
       apply not_not.mp
       intro hz
       exact (RCN042.differential_ne_zero_of_gate _ hz (hZ C hz))
         (not_ne_iff.mp hzero.2)
     have hUalg:IsAlgebraic Omega (U C):=hYalg.add (hZalg.smul lam)
     rw [AQU v _ hUalg,
       AQU v _ hYalg,
       AQU v _ hZalg]
     simp
 have hactiveV:∀C:RCN264.RegularComponent Omega G T H,
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 1)≠0∨
       D Omega (RCN002.CoordinateField Omega C.1) (U C)≠0:=by
   intro C
   by_cases hactive:
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     obtain ⟨hs,hfinite,hsep,_⟩:=hlam CU
     exact Or.inr (RCN042.differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
   · have hzero:=not_or.mp hactive
     have hb:=RCN037.base_differential_ne_zero (base C)
     generalize hidx:(base C).index=i at hb
     fin_cases i
     · exact (hb (not_ne_iff.mp hzero.1)).elim
     · exact Or.inl hb
     · exact (hb (not_ne_iff.mp hzero.2)).elim
 let EC:RCN264.RegularComponent Omega G T H→Type:=
   fun C=>RCN002.CoordinateField Omega C.1
 let rS:∀C,EC C:=fun C=>coordinate Omega C.1 1
 let W:∀C,Finset (Place_p19 Omega (EC C)):=
   fun C=>OW (base C)
 let baseC:∀C,RCN344.SeparableCoordinate Omega (EC C):=
   fun C=>RCN042.literalToSeparableCoordinate (base C)
 let Extra:Omega→Prop:=fun mu=>
   MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G=0
 have hextra:∀{a b},Extra a→Extra b→a=b:=by
   exact RCN096.directional_bad_coefficient_subsingleton G hSderiv
 obtain ⟨mu,hmu0,hmudir,hmu⟩:=
   YC
     EC rS U W Extra hextra baseC hactiveV
 let V:∀C:RCN264.RegularComponent Omega G T H,
     RCN002.CoordinateField Omega C.1:=
   fun C=>coordinate Omega C.1 1+mu • U C
 let hV:∀C:RCN264.RegularComponent Omega G T H,
     Transcendental Omega (V C):=fun C=>(hmu C).choose
 let vProjection:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=fun C=>Sum.inr {
   embedding:=RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (vProjection C)=V C:=by
   intro C
   exact RCN022.elementEmbedding_variable Omega (RCN002.CoordinateField Omega C.1) (V C) (hV C)
 have hvPole:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈OW (base C)
   · exact RCN099.poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=DW
         (base C) v hv 1
     have hY:=DW
         (base C) v hv 0
     have hZ:=DW
         (base C) v hv 2
     have hU:RCN187.poleOrder v.val (U C)=0:=by
       rw [huPole C v,hY,hZ]
       simp
     have hSle:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ hS
     have hUle:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ hU
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (mu • U C)=v.val (U C):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one mu hmu0,one_mul]
     have hVle:v.val (V C)≤1:=
       (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le hSle hUle)
     have hV0:RCN187.poleOrder v.val (V C)=0:=
       RCN346._Q11 Omega
         (RCN002.CoordinateField Omega C.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀C:RCN264.RegularComponent Omega G T H,
     Transcendental Omega (affineV Omega C.1 mu (mu*lam)):=fun C=>by
   rw [show affineV Omega C.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:RCN264.RegularComponent Omega G T H):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
         (affineV Omega C.1 mu (mu*lam)) (hVAff C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1) (V C) (hV C):=
   RCN116.elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])
 refine ⟨{
   lam:=lam
   lam_ne:=hlam0
   mu:=mu
   mu_ne:=hmu0
   uProjection:=uProjection
   NV:=vProjection
   uGate:=hUgate
   GN:=hVAff
   allFinite:=?_
   allSeparable:=?_
   uValue:=huValue
   allValue:=?_
   ACE:=?_
   uPole:=?_
   allPole:=?_
   directional:=hmudir}⟩
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.1
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.2.1
 · intro C
   rw [hvValue C]
   simp only [V,U,affineU,affineV]
   simp only [smul_add,smul_smul,add_assoc]
 · intro C
   rw [hvValue C]
   exact hV C
 · intro C v
   rw [huValue C]
   exact huPole C v
 · intro C v
   rw [hvValue C,hvPole C v,huPole C v]
end
end RCN037
end SubmissionLower
end ProximityPrize
end PackedLegacy_X9
section PackedLegacy_BA
namespace ProximityPrize
namespace SubmissionLower
namespace RCN117
open scoped Classical
open RCN267 RCN125 RCN097 RCN116 RCN011
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
theorem EZW (lam mu nu:K) (F:Poly3 K):
   MvPolynomial.pderiv (1:Fin 3) (flagAlgHom_p19 lam mu nu F)=
     flagAlgHom_p19 lam mu nu (MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a=>simp
 | add P Q hP hQ=>simp [hP,hQ]
 | mul_X P i hP=>
     fin_cases i<;>
       simp [flagImage_p19,hP,MvPolynomial.pderiv_mul,
         Derivation.leibniz]<;>ring
theorem DTK (lam mu:K) (F:Poly3 K):
   MvPolynomial.pderiv (0:Fin 3)
       (flagAlgHom_p19 lam mu (mu*lam) F)=
     flagAlgHom_p19 lam mu (mu*lam)
       (MvPolynomial.pderiv (0:Fin 3) F-
         MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a=>simp
 | add P Q hP hQ=>
     simp [hP,hQ,mul_add,sub_eq_add_neg]<;>ring
 | mul_X P i hP=>
     fin_cases i<;>
       simp [flagImage_p19,hP,MvPolynomial.pderiv_mul,
         Derivation.leibniz]<;>ring
theorem MV
   (lam mu:K) (G:Poly3 K)
   (hderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   0<(planeMap K uOrder_p19
         (flagAlgHom_p19 lam mu (mu*lam) G)).natDegree∧
     0<(planeMap K zOrder_p19
         (flagAlgHom_p19 lam mu (mu*lam) G)).natDegree:=by
 have hflag:MvPolynomial.pderiv (1:Fin 3)
     (flagAlgHom_p19 lam mu (mu*lam) G)≠0:=by
   rw [EZW]
   exact (flagEquiv_p19 lam mu (mu*lam)).injective.ne hderiv
 constructor
 · apply RCN117.planeMap_natDegree_pos_of_pderiv_ne_zero uOrder_p19
   simpa [uOrder_p19] using hflag
 · apply RCN117.planeMap_natDegree_pos_of_pderiv_ne_zero zOrder_p19
   simpa [zOrder_p19,Equiv.swap_apply_def] using hflag
section Characteristic
variable (p:ℕ) [CharP K p]
theorem XD
   (lam mu:K) (G:Poly3 K)
   (hdirectional:MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0):
   0<(planeMap K vOrder_p19
       (flagAlgHom_p19 lam mu (mu*lam) G)).natDegree:=by
 apply RCN117.planeMap_natDegree_pos_of_pderiv_ne_zero vOrder_p19
 simpa [vOrder_p19,Equiv.swap_apply_def,
   DTK] using
   (flagEquiv_p19 lam mu (mu*lam)).injective.ne hdirectional
end Characteristic
end
end RCN117
end SubmissionLower
end ProximityPrize
end PackedLegacy_BA
section PackedLegacy_Y0
namespace ProximityPrize
namespace SubmissionLower
namespace RCN039
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN046 RCN037 RCN095 RCN114 RCN093 RCN123 RCN121 RCN117 RCN116 RCN125 RCN022
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def AUZ
   (p q:FlagDegree)
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hY:∀C:RCN264.RegularComponent Omega G T H,
     RCN037.LiteralProjectionGate C 0)
   (hZ:∀C:RCN264.RegularComponent Omega G T H,
     RCN037.LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AOH base hY hZ hSderiv)
   (hG:Irreducible G) (hproper:¬G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   EE base p q:=by
 classical
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let zProj:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=fun C=>
   RCN042.coordinateOfGate (coordinate Omega C.1 2) (hZ C)
 let uProj:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=fun C=>
   RCN042.coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)
 let vProj:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=fun C=>Sum.inr {
   embedding:=RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.GN C)
   finite:=D.allFinite C
   separable:=D.allSeparable C}
 let gCaps:=LQ p G lam mu nu hGsupport
 let tCaps:=LQ q T lam mu nu hTsupport
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let sZ:={C:RCN264.RegularComponent Omega G T H//
   Transcendental Omega (coordinate Omega C.1 2)}
 have hinjZ:Function.Injective (fun C:sZ=>C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htZ:∀C:sZ,
     Transcendental Omega
       (RCN093.flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (zOrder_p19 0))):=by
   intro C
   simpa [zOrder_p19,Equiv.swap_apply_def,lam,mu,nu] using C.2
 have hembZ (C:sZ):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder_p19 0))) (htZ C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (coordinate Omega C.1.1 2) C.2:=
   RCN116.elementEmbedding_congr (htZ C) C.2
     (by simp [zOrder_p19,Equiv.swap_apply_def,lam,mu,nu])
 have hgenZ:∀C:sZ,
     letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
       (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder_p19 0))) (htZ C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder_p19 2)),
         RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder_p19 1))}:
         Set (RCN002.CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembZ C]
   simpa [zOrder_p19,Equiv.swap_apply_def,lam,mu,nu] using
     BKE Omega C.1.1 lam mu nu C.2
 have hfamilyZ:=RG
   (K:=Omega) (Q:=fun C:sZ=>C.1.1) hinjZ lam mu nu zOrder_p19
   htZ hgenZ G T hG
   (fun C=>EN Omega G T H C.1)
   (fun C=>GV Omega G T H C.1)
   hproper
   (MV D.lam D.mu G hSderiv).2
   p.all q.all (p.yz+p.all) (q.yz+q.all)
   (flagMixed p q unitZFlag) hTne
   (by simpa only [gCaps] using gCaps.zOuter)
   (by simpa only [tCaps] using tCaps.zOuter)
   (by simpa only [gCaps] using gCaps.zTotal)
   (by simpa only [tCaps] using tCaps.zTotal)
   (RCN121.z_flag_trapezoid_budget p q)
 have hsumZ:
     (∑ C:RCN264.RegularComponent Omega G T H,
       RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (zProj C))≤
       flagMixed p q unitZFlag:=by
   have hsplit:=RCN042.sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RCN264.RegularComponent Omega G T H=>RCN002.CoordinateField Omega C.1)
     (x:=fun C=>coordinate Omega C.1 2) hZ
   change (∑ C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
       (RCN042.coordinateOfGate (coordinate Omega C.1 2) (hZ C)))≤_
   rw [hsplit]
   calc
     (∑ C:sZ,
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
         (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
           (coordinate Omega C.1.1 2) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1)))=
         ∑ C:sZ,
           (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
             (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
               (RCN093.flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (zOrder_p19 0))) (htZ C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembZ C]
     _≤_:=hfamilyZ.2
 let sU:={C:RCN264.RegularComponent Omega G T H//
   Transcendental Omega (affineU Omega C.1 D.lam)}
 have hinjU:Function.Injective (fun C:sU=>C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htU:∀C:sU,
     Transcendental Omega
       (RCN093.flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (uOrder_p19 0))):=by
   intro C
   simpa [uOrder_p19,lam,mu,nu] using C.2
 have hembU (C:sU):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder_p19 0))) (htU C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (affineU Omega C.1.1 D.lam) C.2:=
   RCN116.elementEmbedding_congr (htU C) C.2
     (by simp [uOrder_p19,lam,mu,nu])
 have hgenU:∀C:sU,
     letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
       (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder_p19 0))) (htU C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder_p19 2)),
         RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder_p19 1))}:
         Set (RCN002.CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembU C]
   simpa [uOrder_p19,lam,mu,nu] using
     BUX Omega C.1.1 lam mu nu C.2
 have hfamilyU:=RG
   (K:=Omega) (Q:=fun C:sU=>C.1.1) hinjU lam mu nu uOrder_p19
   htU hgenU G T hG
   (fun C=>EN Omega G T H C.1)
   (fun C=>GV Omega G T H C.1)
   hproper
   (MV D.lam D.mu G hSderiv).1
   p.all q.all (p.zOnly+p.yz+p.all)
   (q.zOnly+q.yz+q.all) (flagMixed p q unitYZFlag) hTne
   (by simpa only [gCaps] using gCaps.uOuter)
   (by simpa only [tCaps] using tCaps.uOuter)
   (by simpa only [gCaps] using gCaps.uTotal)
   (by simpa only [tCaps] using tCaps.uTotal)
   (RCN121.u_flag_trapezoid_budget p q)
 have hsumU:
     (∑ C:RCN264.RegularComponent Omega G T H,
       RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (uProj C))≤
       flagMixed p q unitYZFlag:=by
   have hsplit:=RCN042.sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RCN264.RegularComponent Omega G T H=>RCN002.CoordinateField Omega C.1)
     (x:=fun C=>affineU Omega C.1 D.lam) D.uGate
   change (∑ C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
       (RCN042.coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)))≤_
   rw [hsplit]
   calc
     (∑ C:sU,
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
         (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
           (affineU Omega C.1.1 D.lam) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1)))=
         ∑ C:sU,
           (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
             (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
               (RCN093.flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (uOrder_p19 0))) (htU C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembU C]
     _≤_:=hfamilyU.2
 let htV:∀C:RCN264.RegularComponent Omega G T H,
     Transcendental Omega
       (RCN093.flagEvaluation Omega C.1 lam mu nu
         (MvPolynomial.X (vOrder_p19 0))):=by
   intro C
   simpa [vOrder_p19,Equiv.swap_apply_def,lam,mu,nu] using
     D.GN C
 have hembV (C:RCN264.RegularComponent Omega G T H):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
         (RCN093.flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder_p19 0))) (htV C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam))
           (D.GN C):=
   RCN116.elementEmbedding_congr (htV C) (D.GN C)
     (by simp [vOrder_p19,Equiv.swap_apply_def,lam,mu,nu])
 have hgenV:∀C:RCN264.RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
       (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
         (RCN093.flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder_p19 0))) (htV C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({RCN093.flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder_p19 2)),
         RCN093.flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder_p19 1))}:
         Set (RCN002.CoordinateField Omega C.1))=⊤:=by
   intro C
   rw [hembV C]
   simpa [vOrder_p19,Equiv.swap_apply_def,lam,mu,nu] using
     BTS Omega C.1 lam mu nu (D.GN C)
 have hinjV:Function.Injective
     (fun C:RCN264.RegularComponent Omega G T H=>C.1):=by
   intro C E hCE
   exact Subtype.ext hCE
 have hfamilyV:=RG
   (K:=Omega) (Q:=fun C:RCN264.RegularComponent Omega G T H=>C.1)
   hinjV lam mu nu vOrder_p19 htV hgenV G T hG
   (fun C=>EN Omega G T H C)
   (fun C=>GV Omega G T H C)
   hproper
   (XD D.lam D.mu G D.directional)
   (p.yz+p.all) (q.yz+q.all)
   (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
   (flagMixed p q unitAllFlag) hTne
   (by simpa only [gCaps] using gCaps.vOuter)
   (by simpa only [tCaps] using tCaps.vOuter)
   (by simpa only [gCaps] using gCaps.vTotal)
   (by simpa only [tCaps] using tCaps.vTotal)
   (RCN121.v_flag_trapezoid_budget p q)
 have hsumV:
     (∑ C:RCN264.RegularComponent Omega G T H,
       RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (vProj C))≤
       flagMixed p q unitAllFlag:=by
   calc
     _=∑ C:RCN264.RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
             (affineV Omega C.1 D.mu (D.mu*D.lam))
               (D.GN C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rfl
     _=∑ C:RCN264.RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
             (RCN093.flagEvaluation Omega C.1 lam mu nu
               (MvPolynomial.X (vOrder_p19 0))) (htV C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembV C]
     _≤_:=hfamilyV.2
 have hvValue (C:RCN264.RegularComponent Omega G T H):
     RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (vProj C)=
       affineV Omega C.1 D.mu (D.mu*D.lam):=by
   dsimp only [vProj,RCN344.coordinateValue,RCN344.SeparableCoordinate.value,Sum.elim_inr]
   exact RCN022.elementEmbedding_variable Omega (RCN002.CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.GN C)
 refine {
   zProjection:=zProj
   yzProjection:=uProj
   NV:=vProj
   zValue:=?_
   ACE:=?_
   zPole_eq:=?_
   yzPole_eq:=?_
   allPole_eq:=?_
   ARJ:=hsumZ
   ALE:=hsumU
   AQB:=hsumV}
 · intro C
   exact RCN042.coordinateOfGate_value _ _
 · intro C
   rw [hvValue C]
   exact D.GN C
 · intro C v
   rw [UC]
   change _=RCN187.poleOrder v.val _
   simp only [zProj]
   exact congrArg (RCN187.poleOrder v.val) (RCN042.coordinateOfGate_value _ _).symm
 · intro C v
   rw [QD]
   change _=RCN187.poleOrder v.val _
   rw [RCN042.coordinateOfGate_value]
   rw [←D.uValue C]
   exact (D.uPole C v).symm
 · intro C v
   rw [SF]
   change _=RCN187.poleOrder v.val _
   rw [hvValue C,←D.allValue C]
   exact (D.allPole C v).symm
theorem ACA
   (p q:FlagDegree)
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hY:∀C:RCN264.RegularComponent Omega G T H,
     RCN037.LiteralProjectionGate C 0)
   (hZ:∀C:RCN264.RegularComponent Omega G T H,
     RCN037.LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (EE base p q):=by
 obtain ⟨D⟩:=ALD base hY hZ hSderiv
 exact ⟨AUZ p q base hY hZ hSderiv D
   hG hproper hGsupport hTsupport⟩
end
end RCN039
end SubmissionLower
end ProximityPrize
end PackedLegacy_Y0
section PackedLegacy_Y5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN084
open scoped Classical BigOperators
open RCN095 RCN121 RCN071 RCN137 RCN264 RCN341 RCN037 RCN039 RCN046 RCN237 RCN002 RCN005 RCN003 RCN001
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K]
local notation "Poly" =>MvPolynomial (Fin 3) K
variable [IsAlgClosed K]
theorem AAU (F N A R:Poly) (hF:F≠0)
   (v:Fin 3→K) (hvF:MvPolynomial.eval v F=0)
   (hvA:MvPolynomial.eval v A=0) (hvR:MvPolynomial.eval v R≠0)
   (hvD:MvPolynomial.eval v (MvPolynomial.pderiv (1:Fin 3) F)≠0)
   (hi:RCN084.IsolatedPoint F N A v):
   ∃g:↥(RCN084.activeFactors F N),MvPolynomial.eval v g.1=0:=by
 obtain ⟨g,hg,hgv⟩:=RCN137.exists_normalizedFactorSet_zero (MvPolynomial.eval v) F hF hvF
 have hs:=RCN137.normalizedFactorSet_spec F g hg
 have hproper:¬g∣N:=by
   intro hgN
   obtain ⟨D,hD⟩:=AZA K g A R v hgv hvA hvR
   have hmem:=EN K g A R D
   exact hi D.1 inferInstance (PU K g A R D) hD
     (D.1.mem_of_dvd hs.2 hmem) (D.1.mem_of_dvd hgN hmem)
     (GV K g A R D)
 have hderiv:MvPolynomial.pderiv (1:Fin 3) g≠0:=by
   intro hz
   obtain ⟨b,hb⟩:=hs.2
   apply hvD
   rw [hb,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hz,map_zero,hgv]
   ring
 exact ⟨⟨g,Finset.mem_filter.mpr ⟨hg,hproper,hderiv⟩⟩,hgv⟩
theorem AOE (F N R:Poly) (hF:F≠0)
   (p q:FlagDegree) (hFp:RCN095.PolynomialInFlag p F) (hNq:RCN095.PolynomialInFlag q N)
   (c:ℕ) [CharP K c] (hdeg:p.zOnly+p.yz+p.all<c)
   (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c):
   ∃base:∀g:↥(RCN084.activeFactors F N),∀C:RCN264.RegularComponent K g.1 N R,
       RCN341.SeparableLiteralCoordinate C.1,
     (∀g:↥(RCN084.activeFactors F N),∀C:RCN264.RegularComponent K g.1 N R,RCN037.LiteralProjectionGate C 0)∧
     (∀g:↥(RCN084.activeFactors F N),∀C:RCN264.RegularComponent K g.1 N R,RCN037.LiteralProjectionGate C 2):=by
 have hgate (g:↥(RCN084.activeFactors F N)) (C:RCN264.RegularComponent K g.1 N R)
     (i:Fin 3) (hi:Transcendental K (coordinate K C.1 i)):
     letI:Algebra (RatFunc K) (RCN002.CoordinateField K C.1):=RCN005.rationalBaseAlgebra K C.1 i hi
     FiniteDimensional (RatFunc K) (RCN002.CoordinateField K C.1)∧
       Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K C.1):=by
   have hg:=RCN084.activeFactors_spec F N g
   have hgdeg (j:Fin 3):g.1.degreeOf j≤p.zOnly+p.yz+p.all:=
     (RCN137.coordinate_degree_le_of_dvd j g.1 F hg.2.1 hF).trans (RCN084.degreeOf_le_flag_total F p hFp j)
   have hNdeg (j:Fin 3):=RCN084.degreeOf_le_flag_total N q hNq j
   apply RH K C.1 i hi c g.1 N
     hg.1 (EN K _ _ _ C) (GV K _ _ _ C)
     hg.2.2.1 (fun j↦(hgdeg j).trans_lt hdeg)
   have hprod (u v:Fin 3):N.degreeOf u*g.1.degreeOf v+g.1.degreeOf u*N.degreeOf v≤
       2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all):=by
     calc
       _≤(q.zOnly+q.yz+q.all)*(p.zOnly+p.yz+p.all)+
           (p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all):=
         Nat.add_le_add (Nat.mul_le_mul (hNdeg u) (hgdeg v))
           (Nat.mul_le_mul (hgdeg u) (hNdeg v))
       _=_:=by ring
   have hi3:i=0∨i=1∨i=2:=by omega
   rcases hi3 with rfl | rfl | rfl
   · rw [RCN001.coordinateMixedDegree_zero];exact (hprod 1 2).trans_lt hmix
   · rw [RCN001.coordinateMixedDegree_one];exact (hprod 0 2).trans_lt hmix
   · rw [RCN001.coordinateMixedDegree_two];exact (hprod 0 1).trans_lt hmix
 refine ⟨fun g C↦Classical.choice (RCN341.exists_separableLiteralCoordinate_of_YZ_gates C.1
   (PU K _ _ _ C) (hgate g C 0) (hgate g C 2)),?_,?_⟩
 · exact fun g C↦hgate g C 0
 · exact fun g C↦hgate g C 2
end
end RCN084
end SubmissionLower
end ProximityPrize
end PackedLegacy_Y5
section PackedLegacy_L2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN181
open scoped BigOperators
open Set UniqueFactorizationMonoid RCN100 RCN180 RCN137
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K:Type*} [Field K]
local instance:StrongNormalizationMonoid (Koala6831Intrinsic.Carrier K):=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid (Koala6831Intrinsic.Carrier K):=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid (Koala6831Intrinsic.Carrier K)
def SY {D w L s:ℕ}
   (V:Submodule K (RCN100.CoefficientIndex D w L s→K)):
   V→ₗ[K] Koala6831Intrinsic.Carrier K:=
 (RCN180.reconstructLinear (K:=K) D w L s).comp V.subtype
end
end RCN181
end SubmissionLower
end ProximityPrize
end PackedLegacy_L2
section PackedLegacy_L4
namespace ProximityPrize
namespace SubmissionLower
namespace RCN183
open scoped BigOperators
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN130 RCN234 RCN156 RCN081
open RCN100 renaming CoefficientIndex → ED, coefficientCount → AW, globalCoefficientBox → BA, reconstruct_injective → ABR
open RCN119 renaming coefficientBox → IN, coefficientBoxFinite → FER, monomialRemainder → DUF, slopeDifference → IA
open Koala6831Intrinsic renaming Carrier → Poly4
open RCN081 renaming degree_weightedLift → KD, support_weightedLift → CVA, weightEmbed_castSucc → CVF, weightEmbed_injective → AJC, weightEmbed_last → EDV, weightedLift_injective → CCQ
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:StrongNormalizationMonoid GlobalPoly:=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid GlobalPoly
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
@[simp] theorem AHO
   {D L s:ℕ}
   (V:Submodule IRSProfile.Field
     (RCN100.CoefficientIndex D 131071 L s→IRSProfile.Field)) (v:V):
   SY V v=
     reconstruct IRSProfile.Field D 131071 L s v.1:=rfl
end
end RCN183
end SubmissionLower
end ProximityPrize
end PackedLegacy_L4
section PackedLegacy_Y6
namespace ProximityPrize
namespace SubmissionLower
namespace RCN086
open scoped Classical BigOperators
open RCN313 RCN136 RCN238 RCN053 RCN054 RCN095 RCN207 RCN234 RCN198
open RCN054 renaming coefficientFlag → LJ
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 35000
variable {K Ω:Type} [Field K] [Field Ω]
theorem CJY (φ:Polynomial K→+*Ω)
   (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree≤w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (DK φ selected γ) (RCN086.globalTailCut φ F (w+1))=0:=by
 rw [RCN086.globalTailCut_eq,map_mul]
 have hzero:=RCN068.ETM φ F selected γ w hdegree hsolution
 change MvPolynomial.aeval _ (surfaceMap φ (numerator K F (w+1)))=0 at hzero
 rw [hzero,zero_mul]
end
end RCN086
end SubmissionLower
end ProximityPrize
end PackedLegacy_Y6
section PackedLegacy_FD
namespace ProximityPrize
namespace SubmissionLower
namespace RCN212
open scoped Classical BigOperators WithZero
open RCN133 RCN184 RCN295 RCN095 RCN187
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 1000000
def MS:Finset (Fin 4→₀ ℕ):=
 RCN212.quadraticSupport.image liftExponent ∪ RCN212.linearSupport.image RCN212.shiftExponent
theorem BJI (d:Fin 4→₀ ℕ):
   d∈MS ↔ d 0+d 1+d 2+d 3≤2∧d 3≤1∧d 1+2*d 3≤2:=by
 classical
 constructor
 · intro hd
   rcases Finset.mem_union.mp hd with hd | hd
   · obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hd
     have he:=(RCN095.mem_flagSupport_iff _ _).mp he
     simp only [InFlag,nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag] at he
     simp [liftExponent]
     omega
   · obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hd
     have he:=(RCN095.mem_flagSupport_iff _ _).mp he
     simp only [InFlag,unitYZFlag] at he
     simp [RCN212.shiftExponent,liftExponent]
     omega
 · rintro ⟨ht,hw,hr⟩
   let e:=RCN095.exponentOfTriple (d 0,d 1,d 2)
   have heq0:e 0=d 0∧e 1=d 1∧e 2=d 2:=by simp [e,RCN095.exponentOfTriple]
   have hdw:d 3=0∨d 3=1:=by omega
   rcases hdw with hdw | hdw
   · apply Finset.mem_union_left
     refine Finset.mem_image.mpr ⟨e,?_,?_⟩
     · rw [RCN095.mem_flagSupport_iff]
       simp [InFlag,unitAllFlag,heq0.1,heq0.2.1,heq0.2.2]
       omega
     · ext i;fin_cases i<;>simp [liftExponent,heq0.1,heq0.2.1,heq0.2.2,hdw]
   · apply Finset.mem_union_right
     refine Finset.mem_image.mpr ⟨e,?_,?_⟩
     · rw [RCN095.mem_flagSupport_iff]
       simp [InFlag,unitYZFlag,heq0.1,heq0.2.1,heq0.2.2]
       omega
     · ext i;fin_cases i<;>simp [RCN212.shiftExponent,liftExponent,heq0.1,heq0.2.1,heq0.2.2,hdw]
theorem DXD:RCN295.ExponentSetDownwardClosed MS:=by
 intro d hd e he
 rw [BJI] at hd ⊢
 have h0:=he 0;have h1:=he 1;have h2:=he 2;have h3:=he 3
 omega
theorem EYD:(0:Fin 4→₀ ℕ)∈MS:=by
 simp [BJI]
def BWM (d:RCN212.quadraticSupport):MS:=
 ⟨liftExponent d.1,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d.1,d.2,rfl⟩)⟩
def linearIndex_p19 (d:RCN212.linearSupport):MS:=
 ⟨RCN212.shiftExponent d.1,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d.1,d.2,rfl⟩)⟩
theorem EPF:Function.Injective BWM:=
 fun _ _ h↦Subtype.ext (RCN212.liftExponent_injective (congrArg Subtype.val h))
theorem DST:Function.Injective linearIndex_p19:=
 fun _ _ h↦Subtype.ext (RCN212.shiftExponent_injective (congrArg Subtype.val h))
def supportIndex_p19:RCN212.quadraticSupport ⊕ RCN212.linearSupport→MS:=
 Sum.elim BWM linearIndex_p19
theorem EVE:Function.Bijective supportIndex_p19:=by
 constructor
 · intro d e h
   cases d with
   | inl d=>
     cases e with
     | inl e=>exact congrArg Sum.inl (EPF h)
     | inr e=>
                have hh:=DFunLike.congr_fun (congrArg Subtype.val h) 3
                simp [supportIndex_p19,BWM,linearIndex_p19,liftExponent,RCN212.shiftExponent] at hh
   | inr d=>
     cases e with
     | inl e=>
                have hh:=DFunLike.congr_fun (congrArg Subtype.val h) 3
                simp [supportIndex_p19,BWM,linearIndex_p19,liftExponent,RCN212.shiftExponent] at hh
     | inr e=>exact congrArg Sum.inr (DST h)
 · intro d
   rcases Finset.mem_union.mp d.2 with hd | hd
   · obtain ⟨e,he,h⟩:=Finset.mem_image.mp hd
     exact ⟨Sum.inl ⟨e,he⟩,Subtype.ext h⟩
   · obtain ⟨e,he,h⟩:=Finset.mem_image.mp hd
     exact ⟨Sum.inr ⟨e,he⟩,Subtype.ext h⟩
variable {K L:Type*} [Field K] [Field L] [Algebra K L]
def restrictQ_p19:(MS→K)→ₗ[K] (RCN212.quadraticSupport→K):=
 LinearMap.funLeft K K BWM
def restrictU_p19:(MS→K)→ₗ[K] (RCN212.linearSupport→K):=
 LinearMap.funLeft K K linearIndex_p19
theorem DZV:Function.Surjective (restrictU_p19 (K:=K)):=
 LinearMap.funLeft_surjective_of_injective K K _ DST
def BIK (c:MS→K):=RCN133.polynomialOfSupport RCN212.quadraticSupport (restrictQ_p19 c)
def CKK (c:MS→K):=RCN133.polynomialOfSupport RCN212.linearSupport (restrictU_p19 c)
theorem CQA (c:MS→K):
   RCN095.PolynomialInFlag (2 • unitAllFlag) (BIK c):=
 (RCN095.support_subset_flagSupport_iff _ _).mp (RCN133.support_polynomialOfSupport_subset _ _)
theorem DHT (c:MS→K):
   RCN095.PolynomialInFlag unitYZFlag (CKK c):=
 (RCN095.support_subset_flagSupport_iff _ _).mp (RCN133.support_polynomialOfSupport_subset _ _)
theorem DAQ (x:Fin 3→L) (w:L) (c:MS→K):
   RCN184.coefficientEvaluation (RCN212.movingCoordinates x w) MS c=
     MvPolynomial.eval₂Hom (algebraMap K L) x (BIK c)+
     MvPolynomial.eval₂Hom (algebraMap K L) x (CKK c)*w:=by
 let e:=Equiv.ofBijective supportIndex_p19 EVE
 change MvPolynomial.eval₂Hom _ _ (RCN133.polynomialOfSupport _ _)=_
 simp only [RCN133.polynomialOfSupport,map_sum]
 rw [←e.sum_comp]
 simp only [Fintype.sum_sum_type,e,Equiv.ofBijective_apply,supportIndex_p19,Sum.elim_inl,
   Sum.elim_inr,BWM,linearIndex_p19]
 simp only [RCN212.evaluation_lift,RCN212.evaluation_shift]
 simp [BIK,CKK,RCN133.polynomialOfSupport,map_sum,
   Finset.sum_mul,restrictQ_p19,restrictU_p19,LinearMap.funLeft,BWM,linearIndex_p19]
theorem GSH (i:Fin 3):Finsupp.single i.castSucc 1∈MS:=by
 fin_cases i<;>simp [BJI]
theorem DXP (x:Fin 3→L) (w:L) (i:Fin 3):
   ∃c:MS→K,
     RCN184.coefficientEvaluation (RCN212.movingCoordinates x w) MS c=x i:=by
 refine ⟨RCN184.deltaCoefficient MS ⟨Finsupp.single i.castSucc 1,GSH i⟩,?_⟩
 change MvPolynomial.eval₂Hom _ _ (RCN133.polynomialOfSupport _ _)=_
 rw [RCN184.polynomialOfSupport_deltaCoefficient]
 fin_cases i<;>simp [MvPolynomial.eval₂Hom_monomial,RCN212.movingCoordinates]
theorem AZV (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3→L) (w:L):
   RCN295.exponentSetPoleWeight v (RCN212.movingCoordinates x w) MS=
     max (2*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))+poleOrder v w):=by
 let q:Fin 4→ℤ:=fun i↦poleOrder v (RCN212.movingCoordinates x w i)
 let a:=max (q 1) (max (q 0) (q 2))
 let b:=max (q 0) (q 2)
 have hq:∀i,0≤q i:=fun i↦le_max_left _ _
 have ha0:q 0≤a:=(le_max_left _ _).trans (le_max_right _ _)
 have ha1:q 1≤a:=le_max_left _ _
 have ha2:q 2≤a:=(le_max_right _ _).trans (le_max_right _ _)
 have hb0:q 0≤b:=le_max_left _ _
 have hb2:q 2≤b:=le_max_right _ _
 have ha:0≤a:=(hq 1).trans ha1
 change RCN295.exponentSetPoleWeight v (RCN212.movingCoordinates x w) MS=max (2*a) (b+q 3)
 have hweight (d:Fin 4→₀ ℕ):RCN295.exponentPoleWeight v (RCN212.movingCoordinates x w) d=
     (d 0:ℤ)*q 0+(d 1:ℤ)*q 1+(d 2:ℤ)*q 2+(d 3:ℤ)*q 3:=by
   simp [RCN295.exponentPoleWeight,Fin.sum_univ_four,q]
 apply le_antisymm
 · unfold RCN295.exponentSetPoleWeight
   apply Finset.max'_le
   intro z hz
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact (by omega:0≤2*a).trans (le_max_left _ _)
   obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   rcases (BJI d).mp hd with ⟨ht,hw,hr⟩
   rw [hweight]
   have hdw:d 3=0∨d 3=1:=by omega
   rcases hdw with hdw | hdw
   · have ht':(d 0:ℤ)+d 1+d 2≤2:=by exact_mod_cast (by omega:d 0+d 1+d 2≤2)
     have h0:=mul_le_mul_of_nonneg_left ha0 (Int.natCast_nonneg (d 0))
     have h1:=mul_le_mul_of_nonneg_left ha1 (Int.natCast_nonneg (d 1))
     have h2:=mul_le_mul_of_nonneg_left ha2 (Int.natCast_nonneg (d 2))
     simp only [hdw,Nat.cast_zero,zero_mul,add_zero]
     apply le_trans _ (le_max_left _ _)
     nlinarith
   · have hd1:d 1=0:=by omega
     have ht':(d 0:ℤ)+d 2≤1:=by exact_mod_cast (by omega:d 0+d 2≤1)
     have hb:0≤b:=(hq 0).trans hb0
     have h0:=mul_le_mul_of_nonneg_left hb0 (Int.natCast_nonneg (d 0))
     have h2:=mul_le_mul_of_nonneg_left hb2 (Int.natCast_nonneg (d 2))
     simp only [hdw,hd1,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero]
     apply le_trans _ (le_max_right _ _)
     nlinarith
 · have hmem (d:Fin 4→₀ ℕ) (hd:d∈MS):
       RCN295.exponentPoleWeight v (RCN212.movingCoordinates x w) d≤
         RCN295.exponentSetPoleWeight v (RCN212.movingCoordinates x w) MS:=by
     apply Finset.le_max'
     exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
   have hs (i:Fin 3):2*q i.castSucc≤RCN295.exponentSetPoleWeight v (RCN212.movingCoordinates x w) MS:=by
     have hm:Finsupp.single i.castSucc 2∈MS:=by fin_cases i<;>simp [BJI]
     have hh:=hmem _ hm
     fin_cases i<;>simpa [hweight] using hh
   have hw (i:Fin 3) (hi:i=0∨i=2):q i.castSucc+q 3≤
       RCN295.exponentSetPoleWeight v (RCN212.movingCoordinates x w) MS:=by
     have hm:Finsupp.single i.castSucc 1+Finsupp.single 3 1∈MS:=by
       rcases hi with rfl | rfl<;>simp [BJI]
     have hh:=hmem _ hm
     rcases hi with rfl | rfl<;>simpa [hweight] using hh
   have hs0:=hs 0;have hs1:=hs 1;have hs2:=hs 2
   have hw0:=hw 0 (Or.inl rfl);have hw2:=hw 2 (Or.inr rfl)
   dsimp [a,b] at*
   omega
end
end RCN212
end SubmissionLower
end ProximityPrize
end PackedLegacy_FD
section PackedLegacy_A9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN064
open scoped Classical BigOperators WithZero
open RCN212 RCN184 RCN133 RCN295 RCN095 RCN114 RCN187 RCN344 RCN002 RCN005 RCN006 RCN341 RCN044 RCN037 RCN207 RCN208 RCN264 RCN042 RCN035 RCN022
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
theorem FDJ {K L σ:Type*} [Field K] [Field L]
   [Algebra K L] [Fintype σ] [DecidableEq σ]
   (v:RCN345.ACR K L) (x:σ→L)
   (E:Finset (σ→₀ ℕ)) (c:E→K)
   (hc:c∉RCN184.cancellationSubmodule v.val (NP K L v) x E):
   v.val (RCN184.coefficientEvaluation x E c)=WithZero.exp (RCN295.exponentSetPoleWeight v.val x E):=by
 apply le_antisymm
 · exact RCN295.valuation_eval_le_exp_exponentSet v.val (algebraMap K L)
     (NP K L v) x E _ (RCN133.support_polynomialOfSupport_subset _ _)
 · exact le_of_not_gt hc
theorem CQD {K I:Type*} [Field K] [Infinite K] [Finite I]
   (L:I→Type*) [∀i,Field (L i)] [∀i,Algebra K (L i)]
   (x:∀i,Fin 3→L i) (w:∀i,L i) (index:I→Fin 3)
   (hd:∀i,KaehlerDifferential.D K (L i) (x i (index i))≠0)
   (V:∀i,Finset (RCN345.ACR K (L i))):
   ∃c:MS→K,∀i,
     RCN184.coefficientEvaluation (x i) RCN212.linearSupport (restrictU_p19 c)≠0∧
     KaehlerDifferential.D K (L i)
       (RCN184.coefficientEvaluation (RCN212.movingCoordinates (x i) (w i)) MS c)≠0∧
     ∀v∈V i,
       v.val (RCN184.coefficientEvaluation (RCN212.movingCoordinates (x i) (w i)) MS c)=
         WithZero.exp (max (2*max (poleOrder v.val (x i 1))
           (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))))
           (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))+poleOrder v.val (w i)))∧
       v.val (RCN184.coefficientEvaluation (x i) RCN212.linearSupport (restrictU_p19 c))=
         WithZero.exp (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))):=by
 classical
 let evJ i:=RCN184.coefficientEvaluation (K:=K) (RCN212.movingCoordinates (x i) (w i)) MS
 let evU i:=(RCN184.coefficientEvaluation (K:=K) (x i) RCN212.linearSupport).comp restrictU_p19
 let Extra:=I × Bool
 let Pole:=Sigma fun i:I↦{v//v∈V i} × Bool
 let bad:Extra ⊕ Pole→Submodule K (MS→K)
   | Sum.inl (i,false)=>LinearMap.ker (evU i)
   | Sum.inl (i,true)=>LinearMap.ker ((KaehlerDifferential.D K (L i)).toLinearMap.comp (evJ i))
   | Sum.inr ⟨i,v,false⟩=>(RCN184.cancellationSubmodule v.1.val
       (NP K (L i) v.1) (x i) RCN212.linearSupport).comap restrictU_p19
   | Sum.inr ⟨i,v,true⟩=>RCN184.cancellationSubmodule v.1.val
       (NP K (L i) v.1) (RCN212.movingCoordinates (x i) (w i)) MS
 have hbad:∀j,bad j≠⊤:=by
   rintro (⟨i,b⟩ | ⟨i,v,b⟩)
   · cases b
     · obtain ⟨c,hc⟩:=DZV (K:=K)
         (RCN184.deltaCoefficient RCN212.linearSupport ⟨0,RCN095.zero_mem_flagSupport _⟩)
       have hone:evU i c=1:=by
         change RCN184.coefficientEvaluation (x i) RCN212.linearSupport (restrictU_p19 c)=1
         rw [hc]
         change MvPolynomial.eval₂Hom _ _ (RCN133.polynomialOfSupport _ _)=_
         rw [RCN184.polynomialOfSupport_deltaCoefficient]
         simp
       intro ht
       have hz:evU i c=0:=LinearMap.mem_ker.mp (by change c∈bad (Sum.inl (i,false));rw [ht];trivial)
       exact one_ne_zero (hone.symm.trans hz)
     · obtain ⟨c,hc⟩:=DXP (K:=K) (x i) (w i) (index i)
       intro ht
       have hz:KaehlerDifferential.D K (L i) (evJ i c)=0:=
         LinearMap.mem_ker.mp (by change c∈bad (Sum.inl (i,true));rw [ht];trivial)
       exact hd i (hc ▸ hz)
   · cases b
     · obtain ⟨d,hd⟩:=AIL (K:=K)
         v.1.val (x i) RCN212.linearSupport (RCN095.flagSupport_downwardClosed _) (RCN095.zero_mem_flagSupport _)
       obtain ⟨c,hc⟩:=DZV (K:=K) d
       intro ht
       have hm:c∈bad (Sum.inr ⟨i,v,false⟩):=by rw [ht];trivial
       change v.1.val (RCN184.coefficientEvaluation (x i) RCN212.linearSupport (restrictU_p19 c))<_ at hm
       rw [hc,hd] at hm
       exact lt_irrefl _ hm
     · obtain ⟨c,hc⟩:=AIL (K:=K)
         v.1.val (RCN212.movingCoordinates (x i) (w i)) MS
         DXD EYD
       exact RCN184.cancellationSubmodule_ne_top_of_exact _ _ _ _ c hc
 obtain ⟨c,hc⟩:=RCN133.exists_avoiding_finite_proper_submodules bad hbad
 refine ⟨c,fun i↦⟨?_,?_,?_⟩⟩
 · exact hc (Sum.inl (i,false))
 · exact hc (Sum.inl (i,true))
 · intro v hv
   have hj:=FDJ v (RCN212.movingCoordinates (x i) (w i)) MS c
     (hc (Sum.inr ⟨i,⟨v,hv⟩,true⟩))
   have hu:=FDJ v (x i) RCN212.linearSupport (restrictU_p19 c)
     (hc (Sum.inr ⟨i,⟨v,hv⟩,false⟩))
   rw [AZV] at hj
   rw [QD] at hu
   exact ⟨hj,hu⟩
variable {K:Type} [Field K] [IsAlgClosed K]
def ALT {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:RCN341.SeparableLiteralCoordinate P) (w:RCN002.CoordinateField K P):
   Finset (Place_p19 K (RCN002.CoordinateField K P)):=by
 letI:=RCN006.polynomialBaseAlgebra K P D.index
 letI:=RCN005.rationalBaseAlgebra K P D.index D.transcendental
 letI:=RCN006.polynomialBaseScalarTower K P D.index
 letI:=RCN006.polynomialRationalScalarTower K P D.index D.transcendental
 letI:=RCN005.rationalBaseScalarTower K P D.index D.transcendental
 letI:FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P):=D.finite
 letI:Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=D.separable
 exact OW D ∪ if hw:w≠0 then
   RCN026.placesFor_p19 K (RCN002.CoordinateField K P) w hw else ∅
theorem CAX {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:RCN341.SeparableLiteralCoordinate P) (w:RCN002.CoordinateField K P)
   (v:Place_p19 K (RCN002.CoordinateField K P)) (hv:v∉ALT D w):
   (∀i,poleOrder v.val (coordinate K P i)=0)∧poleOrder v.val w=0:=by
 letI:=RCN006.polynomialBaseAlgebra K P D.index
 letI:=RCN005.rationalBaseAlgebra K P D.index D.transcendental
 letI:=RCN006.polynomialBaseScalarTower K P D.index
 letI:=RCN006.polynomialRationalScalarTower K P D.index D.transcendental
 letI:=RCN005.rationalBaseScalarTower K P D.index D.transcendental
 letI:FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P):=D.finite
 letI:Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=D.separable
 constructor
 · exact DW D v
     (fun h↦hv (Finset.mem_union_left _ h))
 · by_cases hw:w=0
   · simp [hw,poleOrder]
   have horder:RCN026.order_p19 K (RCN002.CoordinateField K P) v w=0:=by
     by_contra hn
     apply hv
     apply Finset.mem_union_right
     simp only [dif_pos hw]
     exact RCN026.ALB K (RCN002.CoordinateField K P) w hw v hn
   simp only [RCN026.order_p19] at horder
   simp [poleOrder,show (v.val w).log=0 by omega]
def KS (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G:MvPolynomial (Fin 3) K) (v:Place_p19 K (RCN002.CoordinateField K P)):ℤ:=
 max (2*max (poleOrder v.val (coordinate K P 1))
   (max (poleOrder v.val (coordinate K P 0)) (poleOrder v.val (coordinate K P 2))))
   (max (poleOrder v.val (coordinate K P 0)) (poleOrder v.val (coordinate K P 2))+
     poleOrder v.val (movingRatio P H G))
end
end RCN064
end SubmissionLower
end ProximityPrize
end PackedLegacy_A9
section PackedLegacy_O3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN271
open scoped Classical
open RCN272 RCN094 RCN162 RCN165
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Ring3_p19 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def ABY (P:Ideal (Ring3_p19 K)) (H A:Ring3_p19 K)
   (cost:ℕ):Prop:=
 ∀points:Finset (Fin 3→K),
   (∀v∈points,P≤RingHom.ker (MvPolynomial.aeval v).toRingHom)→
   (∀v∈points,MvPolynomial.aeval v H≠0)→
   (∀v∈points,MvPolynomial.aeval v A=0)→points.card≤cost
section Selected
open RCN136 RCN231 RCN319 RCN238 RCN243
open RCN319 renaming specialization → BM
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem BMQ
   (φ:Polynomial K→+*Ω) (P:Ideal (Ring3_p19 Ω))
   (F:MvPolynomial (Fin 4) K) (selected:K→Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w<p)
   (hdegree:∀γ∈Γ,(selected γ).natDegree≤w)
   (hsolution:∀γ∈Γ,RCN319.specialization K (selected γ) γ F=0)
   (hregular:∀γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀γ∈Γ,P≤RingHom.ker
     (MvPolynomial.aeval (DK φ selected γ)).toRingHom)
   (x u₀ u₁:K) (cost:ℕ)
   (hzero:ABY P (CR φ F)
     (FK φ F w x u₀ u₁) cost):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card≤cost:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (DK φ selected)
 have hcount:points.card≤cost:=by
   apply hzero points
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     exact hpoint γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     change MvPolynomial.eval (DK φ selected γ)
       (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
     rw [WQ]
     exact hregular γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
     exact (AQG φ F selected p w hchar γ
       (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (ABD φ selected)
 rwa [hcard] at hcount
end Selected
end
end RCN271
end SubmissionLower
end ProximityPrize
end PackedLegacy_O3
section PackedLegacy_E3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN257
open scoped Classical BigOperators WithZero
open RCN344 RCN000 RCN002 RCN005 RCN006 RCN007 RCN271 RCN341
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
 (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
local instance:DecidableEq K:=Classical.decEq K
theorem EGJ (ψ:A→ₐ[K] K) (h:A) (hψ:ψ h≠0):
   (modelPlace_p19 K L A ψ).val (algebraMap A L h)=1:=by
 apply le_antisymm
 · exact RCN000.actual_model_value_le_one K A L ψ h
 · apply le_of_not_gt
   intro hlt
   exact hψ ((RCN000.actual_model_value_lt_one_iff K A L ψ h).mp hlt)
theorem DEE
   (ψ:A→ₐ[K] K) (a h:A) (k:ℕ) (ha:a≠0)
   (hzero:ψ a=0) (hregular:ψ h≠0):
   1≤RCN026.order_p19 K L (modelPlace_p19 K L A ψ)
     (algebraMap A L a/(algebraMap A L h)^k):=by
 have hv:=EGJ K L A ψ h hregular
 change 1≤-((modelPlace_p19 K L A ψ).val
   (algebraMap A L a/(algebraMap A L h)^k)).log
 simp only [map_div₀,map_pow,hv,one_pow,div_one]
 exact RCN000.actual_model_zero_order_ge_one K A L ψ a ha hzero
theorem CKW
   (a h:A) (k cost:ℕ) (ha:a≠0) (hh:h≠0)
   (hpole:∀W:Finset (Place_p19 K L),
     (∑ v∈W,RCN346.poleOrder_p19 K L v
       (algebraMap A L a/(algebraMap A L h)^k))≤(cost:ℤ))
   (S:Finset (A→ₐ[K] K))
   (hzero:∀ψ∈S,ψ a=0) (hregular:∀ψ∈S,ψ h≠0):
   S.card≤cost:=by
 classical
 let f:L:=algebraMap A L a/(algebraMap A L h)^k
 have hfa:algebraMap A L a≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne ha
 have hfh:algebraMap A L h≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne hh
 have hf:f≠0:=div_ne_zero hfa (pow_ne_zero k hfh)
 let U:=S.image (modelPlace_p19 K L A)
 have hU:∀v∈U,1≤RCN026.order_p19 K L v f:=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   exact DEE K L A ψ a h k ha
     (hzero ψ hψ) (hregular ψ hψ)
 have hcount:=RCN026.AUN K L f hf U hU
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (BQJ K L A)
 have hb:(S.card:ℤ)≤cost:=by
   rw [←hcard]
   exact hcount.trans (hpole _)
 exact_mod_cast hb
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem AIR
   (base:RCN341.SeparableLiteralCoordinate P)
   (H F:MvPolynomial (Fin 3) K) (k cost:ℕ) (hF:F∉P) (hH:H∉P)
   (hpole:
     letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
       RCN005.rationalBaseAlgebra K P base.index base.transcendental
     ∀W:Finset (Place_p19 K (RCN002.CoordinateField K P)),
       (∑ v∈W,RCN346.poleOrder_p19 K (RCN002.CoordinateField K P) v
         (MvPolynomial.aeval (coordinate K P) F/
           (MvPolynomial.aeval (coordinate K P) H)^k))≤(cost:ℤ)):
   ABY P H F cost:=by
 classical
 let i₀:=base.index
 let hi₀:=base.transcendental
 letI:Algebra (Polynomial K) (RCN002.CoordinateRing K P):=
   RCN006.quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (RCN002.CoordinateField K P):=
   RCN006.polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (RCN002.CoordinateField K P):=
   RCN005.rationalBaseAlgebra K P i₀ hi₀
 letI:=RCN006.quotientBaseScalarTower K P i₀
 letI:=RCN006.polynomialBaseScalarTower K P i₀
 letI:=RCN006.quotientFractionScalarTower K P i₀
 letI:=RCN006.polynomialRationalScalarTower K P i₀ hi₀
 letI:=RCN005.rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (RCN002.CoordinateField K P):=base.finite
 letI:Algebra.IsSeparable (RatFunc K) (RCN002.CoordinateField K P):=base.separable
 intro S hSP hSH hSF
 let liftPoint:{v:Fin 3→K//v∈S}→(RCN002.CoordinateRing K P→ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) (RCN007.pointHom_injective K P hvw)
 let points:=S.attach.image liftPoint
 have hzero:∀ψ∈points,ψ (Ideal.Quotient.mk P F)=0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSF v.1 v.2
 have hregular:∀ψ∈points,ψ (Ideal.Quotient.mk P H)≠0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSH v.1 v.2
 have hFq:Ideal.Quotient.mk P F≠0:=
   fun hz↦hF (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hHq:Ideal.Quotient.mk P H≠0:=
   fun hz↦hH (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hcount:=CKW K (RCN002.CoordinateField K P)
   (RCN002.CoordinateRing K P) (Ideal.Quotient.mk P F) (Ideal.Quotient.mk P H)
   k cost hFq hHq (by simpa only [RCN257.quotient_fraction_eq_field_eval] using hpole)
   points hzero hregular
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
end ActualCurve
end
end RCN257
end SubmissionLower
end ProximityPrize
end PackedLegacy_E3
end Compact_PackedLegacyCore2
section Compact_PackedLegacy
section PackedLegacy_M3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN199
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN341 RCN095 RCN114 RCN295 RCN187 RCN207 RCN064 RCN204 RCN271 RCN257
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K:Type} [Field K]
local notation "Poly" =>MvPolynomial (Fin 3) K
structure RD (P:Ideal Poly) [P.IsPrime] (H G:Poly) where
 zCost:ℕ
 yzCost:ℕ
 allCost:ℕ
 movingCost:ℕ
 zPole:∀W:Finset (Place_p19 K (RCN002.CoordinateField K P)),
   (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitZFlag))≤(zCost:ℤ)
 yzPole:∀W:Finset (Place_p19 K (RCN002.CoordinateField K P)),
   (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitYZFlag))≤(yzCost:ℤ)
 allPole:∀W:Finset (Place_p19 K (RCN002.CoordinateField K P)),
   (∑ v∈W,RCN295.exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitAllFlag))≤(allCost:ℤ)
 movingPole:∀W:Finset (Place_p19 K (RCN002.CoordinateField K P)),
   (∑ v∈W,KS P H G v)≤(movingCost:ℤ)
namespace RD
variable {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
 {H G:MvPolynomial (Fin 3) K}
def weightedCost (budget:RD P H G) (r:FlagDegree):ℕ:=
 r.zOnly*budget.zCost+r.yz*budget.yzCost+r.all*budget.allCost
theorem CUE (budget:RD P H G) (r:FlagDegree)
   (W:Finset (Place_p19 K (RCN002.CoordinateField K P))):
   (∑ v∈W,flagPole v.val (coordinate K P) r)≤(budget.weightedCost r:ℤ):=by
 have hz:=budget.zPole W
 have hy:=budget.yzPole W
 have ha:=budget.allPole W
 simp only [UC] at hz
 simp only [QD] at hy
 simp only [SF] at ha
 have h:=add_le_add (add_le_add
   (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
   (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
   (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
 simpa only [flagPole,Finset.sum_add_distrib,←Finset.mul_sum,
   weightedCost,Nat.cast_add,Nat.cast_mul] using h
end RD
end
end RCN199
end SubmissionLower
end ProximityPrize
end PackedLegacy_M3
section PackedLegacy_M6
namespace ProximityPrize
namespace SubmissionLower
namespace RCN202
open scoped Classical BigOperators
open RCN002 RCN072 RCN264 RCN207 RCN208 RCN134 RCN084 RCN095 RCN341 RCN037 RCN076
open RCN084 renaming activeFactors → HR, activeFactors_spec → OJ
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
local notation "Poly" =>MvPolynomial (Fin 3) K
local notation "PE" =>MvPolynomial (Fin 3) E
theorem EDS
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1)→Poly)
   (C:RCN264.RegularComponent K F (filteredCut k B H G) H)
   [Algebra (RatFunc K) (RCN002.CoordinateField K C.1)]
   [IsScalarTower K (RatFunc K) (RCN002.CoordinateField K C.1)]
   [FiniteDimensional (RatFunc K) (RCN002.CoordinateField K C.1)]
   (hj:algebraMap (RatFunc K) (RCN002.CoordinateField K C.1) (RCN202.rationalVariable K)=
     movingValue C.1 H G Q U)
   (D:Ideal PE) [D.IsPrime]
   (hnonpoint:∀v:Fin 3→E,D≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hF:RCN208.scalarPolynomialMap K E F∈D)
   (hN:RCN207.movingEquation (RCN208.scalarPolynomialMap K E H) (RCN208.scalarPolynomialMap K E G)
     (RCN208.scalarPolynomialMap K E Q) (RCN208.scalarPolynomialMap K E U)
     (algebraMap (RatFunc K) E (RCN202.rationalVariable K))∈D)
   (hH:RCN208.scalarPolynomialMap K E H∉D) (hU:RCN208.scalarPolynomialMap K E U∉D)
   (hbelow:D.comap (RCN208.scalarPolynomialMap K E)≤C.1):
   RCN207.eliminatedCut k (fun j↦RCN208.scalarPolynomialMap K E (B j))
     (RCN208.scalarPolynomialMap K E Q) (RCN208.scalarPolynomialMap K E U)
     (algebraMap (RatFunc K) E (RCN202.rationalVariable K))∉D:=by
 intro hA
 let mu:=RCN208.scalarPolynomialMap K E
 let t:=algebraMap (RatFunc K) E (RCN202.rationalVariable K)
 let evD:=RCN002.coordinateEvaluation E D
 let ev:=evD.toRingHom.comp mu
 have hTor:mu (filteredCut k B H G)∈D:=by
   rw [RCN207.map_filteredCut]
   exact RCN207.original_mem_of_eliminated_mem D k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hA hU
 have hcut:cutIdeal K F (filteredCut k B H G)≤D.comap mu:=by
   apply Ideal.span_le.mpr
   intro A hA
   rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hA) with rfl | rfl
   · exact hF
   · exact hTor
 have hmin:=(RCN072.mem_componentFamily K F (filteredCut k B H G) C.1).mp
   (AAS K _ _ _ C)
 have hcontract:D.comap mu=C.1:=
   le_antisymm hbelow (hmin.2 ⟨inferInstance,hcut⟩ hbelow)
 have hker:RingHom.ker ev=C.1:=by
   rw [show RingHom.ker ev=(RingHom.ker evD.toRingHom).comap mu from rfl,
     RCN002.coordinateEvaluation_ker E D]
   exact hcontract
 let phi:=RCN208.coordinateFieldMap C.1 ev hker
 have hphi (A:Poly):phi (RCN002.coordinateEvaluation K C.1 A)=ev A:=
   RCN208.coordinateFieldMap_eval _ _ _ A
 have hscalar (c:K):phi (algebraMap K (RCN002.CoordinateField K C.1) c)=
     algebraMap E (RCN002.CoordinateField E D) (algebraMap K E c):=by
   simpa [ev,mu,RCN208.scalarPolynomialMap] using hphi (MvPolynomial.C c)
 have hHne:ev H≠0:=by
   intro hz
   have:mu H∈RingHom.ker evD.toRingHom:=hz
   rw [RCN002.coordinateEvaluation_ker E D] at this
   exact hH this
 have hNzero:evD (RCN207.movingEquation (mu H) (mu G) (mu Q) (mu U) t)=0:=by
   apply RingHom.mem_ker.mp
   change _∈RingHom.ker (RCN002.coordinateEvaluation E D).toRingHom
   rwa [RCN002.coordinateEvaluation_ker E D]
 have hrel:ev H*(algebraMap E (RCN002.CoordinateField E D) t-ev Q)=ev U*ev G:=by
   have hconst:evD (MvPolynomial.C t)=algebraMap E (RCN002.CoordinateField E D) t:=evD.commutes t
   apply sub_eq_zero.mp
   simpa only [RCN207.movingEquation,map_sub,map_mul,hconst,
     ev,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hNzero
 have hjmap:phi (movingValue C.1 H G Q U)=algebraMap E (RCN002.CoordinateField E D) t:=by
   unfold movingValue
   rw [map_add,map_div₀,map_mul,hphi Q,hphi U,hphi G,hphi H]
   have hd:ev U*ev G/ev H=algebraMap E (RCN002.CoordinateField E D) t-ev Q:=by
     apply (div_eq_iff hHne).mpr
     simpa only [mul_comm] using hrel.symm
   rw [hd];ring
 have hdiag:(algebraMap E (RCN002.CoordinateField E D)).comp (algebraMap (RatFunc K) E)=
     phi.comp (algebraMap (RatFunc K) (RCN002.CoordinateField K C.1)):=by
   apply IsFractionRing.ringHom_ext (A:=Polynomial K)
   intro p
   have hp:((algebraMap E (RCN002.CoordinateField E D)).comp (algebraMap (RatFunc K) E)).comp
       (algebraMap (Polynomial K) (RatFunc K))=
       (phi.comp (algebraMap (RatFunc K) (RCN002.CoordinateField K C.1))).comp
         (algebraMap (Polynomial K) (RatFunc K)):=by
     apply Polynomial.ringHom_ext
     · intro c
       change algebraMap E (RCN002.CoordinateField E D)
         (algebraMap (RatFunc K) E (algebraMap K (RatFunc K) c))=
         phi (algebraMap (RatFunc K) (RCN002.CoordinateField K C.1) (algebraMap K (RatFunc K) c))
       rw [←IsScalarTower.algebraMap_apply K (RatFunc K) E,
         ←IsScalarTower.algebraMap_apply K (RatFunc K) (RCN002.CoordinateField K C.1),hscalar]
     · change algebraMap E (RCN002.CoordinateField E D) t=
         phi (algebraMap (RatFunc K) (RCN002.CoordinateField K C.1) (RCN202.rationalVariable K))
       rw [hj];exact hjmap.symm
   exact RingHom.congr_fun hp p
 have halg:∀i,IsAlgebraic E (coordinate E D i):=by
   intro i
   have hint:=IsIntegral.map_of_comp_eq (algebraMap (RatFunc K) E) phi hdiag
     (IsIntegral.of_finite (RatFunc K) (coordinate K C.1 i))
   have hcoord:phi (coordinate K C.1 i)=coordinate E D i:=by
     simpa only [coordinate,ev,evD,RingHom.comp_apply,mu,RCN208.scalarPolynomialMap,
       MvPolynomial.map_X,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hphi (MvPolynomial.X i)
   rw [hcoord] at hint
   exact hint.isAlgebraic
 obtain ⟨v,hv⟩:=RCN002.eq_point_kernel_of_coordinates_algebraic E D halg
 exact hnonpoint v hv
theorem VX
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1)→Poly)
   (C:RCN264.RegularComponent K F (filteredCut k B H G) H)
   [Algebra (RatFunc K) (RCN002.CoordinateField K C.1)]
   [IsScalarTower K (RatFunc K) (RCN002.CoordinateField K C.1)]
   [FiniteDimensional (RatFunc K) (RCN002.CoordinateField K C.1)]
   (hj:algebraMap (RatFunc K) (RCN002.CoordinateField K C.1) (RCN202.rationalVariable K)=
     movingValue C.1 H G Q U) (hU:U∉C.1)
   (f:RCN002.CoordinateField K C.1→ₐ[RatFunc K] E):
   let mu:=RCN208.scalarPolynomialMap K E
   let t:=algebraMap (RatFunc K) E (RCN202.rationalVariable K)
   let v:=RCN134.embeddingPoint C.1 (f.restrictScalars K)
   let N:=RCN207.movingEquation (mu H) (mu G) (mu Q) (mu U) t
   let A:=RCN207.eliminatedCut k (fun j↦mu (B j)) (mu Q) (mu U) t
   MvPolynomial.eval v (mu F)=0∧MvPolynomial.eval v N=0∧
     MvPolynomial.aeval v A=0∧MvPolynomial.eval v (mu H*mu U)≠0∧
     RCN084.IsolatedPoint (mu F) N A v:=by
 dsimp only
 let mu:=RCN208.scalarPolynomialMap K E
 let t:=algebraMap (RatFunc K) E (RCN202.rationalVariable K)
 let v:=RCN134.embeddingPoint C.1 (f.restrictScalars K)
 let ev:=MvPolynomial.eval v
 have hev (A:Poly):ev (mu A)=f (RCN002.coordinateEvaluation K C.1 A):=by
   have h:=AlgHom.congr_fun (RCN134.embeddingPoint_aeval C.1 (f.restrictScalars K)) A
   change MvPolynomial.eval v (MvPolynomial.map (algebraMap K E) A)=_
   rw [MvPolynomial.eval_map]
   exact h
 have hz (A:Poly) (hA:A∈C.1):ev (mu A)=0:=by
   rw [hev]
   have ha:RCN002.coordinateEvaluation K C.1 A=0:=by
     apply RingHom.mem_ker.mp
     change A∈RingHom.ker (RCN002.coordinateEvaluation K C.1).toRingHom
     rwa [RCN002.coordinateEvaluation_ker K C.1]
   rw [ha,map_zero]
 have hne (A:Poly) (hA:A∉C.1):ev (mu A)≠0:=by
   rw [hev]
   exact fun h↦hA (by
     rw [←RCN002.coordinateEvaluation_ker K C.1]
     exact (map_eq_zero_iff f f.injective).mp h)
 have hHne:=hne H (_Q6 K _ _ _ C)
 have hUne:=hne U hU
 have hjval:ev (mu Q)+ev (mu U)*ev (mu G)/ev (mu H)=t:=by
   simp only [hev]
   have h:=f.commutes (RCN202.rationalVariable K)
   rw [hj] at h
   simpa only [movingValue,map_add,map_div₀,map_mul] using h
 have hN:ev (RCN207.movingEquation (mu H) (mu G) (mu Q) (mu U) t)=0:=by
   have hevC:ev (MvPolynomial.C t)=t:=by simp [ev]
   simp only [RCN207.movingEquation,map_sub,map_mul,hevC]
   have h:=(div_eq_iff hHne).mp (show ev (mu U)*ev (mu G)/ev (mu H)=t-ev (mu Q) by
     linear_combination hjval)
   linear_combination-h
 have hA:ev (RCN207.eliminatedCut k (fun j↦mu (B j)) (mu Q) (mu U) t)=0:=by
   apply (RCN207.eliminatedCut_zero_iff ev k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hHne hUne).mpr
   rw [←RCN207.map_filteredCut]
   exact hz _ (GV K _ _ _ C)
 refine ⟨hz F (EN K _ _ _ C),hN,hA,?_,?_⟩
 · simpa only [map_mul] using mul_ne_zero hHne hUne
 · intro D hD hn hp hDF hDN
   letI:=hD
   apply EDS F H G Q U k B C hj D hn hDF hDN
   · exact fun h↦hHne (hp h)
   · exact fun h↦hUne (hp h)
   · exact RCN208.comap_le_of_embedding_point C.1 (f.restrictScalars K) D hp
theorem DSK (a b s k:ℕ) (C:FlagDegree)
   (H G Q U:Poly) (B:Fin (k+1)→Poly) (c:Fin (k+1)→FlagDegree)
   (hH:RCN095.PolynomialInFlag ⟨a,b+1,s+1⟩ H) (hG:RCN095.PolynomialInFlag ⟨a,b,s+3⟩ G)
   (hQ:RCN095.PolynomialInFlag (2 • unitAllFlag) Q) (hU:RCN095.PolynomialInFlag unitYZFlag U)
   (hB:∀j,RCN095.PolynomialInFlag (c j) (B j))
   (hc:∀j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   RCN095.PolynomialInFlag ⟨a,b+1,s+3⟩ (RCN202.fiberEquation (E:=E) H G Q U)∧
   RCN095.PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩:FlagDegree)) (fiberCut (E:=E) k B Q U):=by
 constructor
 · exact FCY a b s _ _ _ _ _
     (inFlag_map (algebraMap K E) hH) (inFlag_map (algebraMap K E) hG)
     (inFlag_map (algebraMap K E) hQ) (inFlag_map (algebraMap K E) hU)
 · exact ENX a b s k C _ _ _ _ c
     (fun j↦inFlag_map (algebraMap K E) (hB j))
     (inFlag_map (algebraMap K E) hQ) (inFlag_map (algebraMap K E) hU) hc
end
end RCN202
end SubmissionLower
end ProximityPrize
end PackedLegacy_M6
section PackedLegacy_M5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN201
open scoped Classical
open RCN198 RCN136 RCN313 RCN095 RCN234 RCN156 RCN057 RCN055
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 3000000
variable {K Ω:Type} [Field K] [Field Ω]
theorem mapped_flag_p19 (φ:Polynomial K→+*Ω)
   (Q:MvPolynomial (Fin 4) K) (a b s:ℕ)
   (hR:wt RCN156.residualSWeights Q≤s)
   (hM:wt RCN156.residualYSWeights Q≤b+s)
   (hT:wt RCN156.residualTotalWeights Q≤a+b+s):
   RCN095.PolynomialInFlag ⟨a,b,s⟩ (surfaceMap φ Q):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp (RCN136.support_surfaceMap_subset φ Q he)
 have hr:=(MvPolynomial.le_weightedTotalDegree RCN156.residualSWeights hq).trans hR
 have hm:=(MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hq).trans hM
 have ht:=(MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights hq).trans hT
 simp [RCN081.weight_fin4,RCN156.residualSWeights] at hr
 simp [RCN081.weight_fin4,RCN156.residualYSWeights] at hm
 simp [RCN081.weight_fin4,RCN156.residualTotalWeights] at ht
 exact ⟨hr,hm,ht⟩
theorem G_weight_p19 (w:Fin 4→ℕ) (t:ℕ)
   (h0:w 0=0) (h1:w 1=t) (h2:w 2=1) (ht:t≤1)
   (F:MvPolynomial (Fin 4) K) (C:ℕ)
   (hC:1≤C) (hF:wt w F≤C):wt w (polyG K F)≤C+1-t:=by
 have hf:WeightBound w F (C:ℤ):=Or.inr (by exact_mod_cast hF)
 have hg:WeightBound w (polyG K F) ((C:ℤ)+1-t):=by
   simpa only [polyG,RCN055.horizontalDerivation,Derivation.add_apply,
     Derivation.smul_apply,smul_eq_mul] using (hf.horizontal t h0 h1 h2 ht).neg
 rcases hg with hz | hb
 · simp [hz,wt,MvPolynomial.weightedTotalDegree]
 · have htc:t≤C+1:=by omega
   have hb':(wt w (polyG K F):ℤ)≤((C+1-t:ℕ):ℤ):=by
     rw [Nat.cast_sub htc]
     push_cast
     exact hb
   exact_mod_cast hb'
theorem DGW (φ:Polynomial K→+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2≤s+2)
   (hYR:wt ![0,1,1,0] F≤b+s+3)
   (hAll:wt ![0,1,1,1] F≤a+b+s+3):
   RCN095.PolynomialInFlag ⟨a,b+1,s+1⟩ (surfaceMap φ (polyH K F))∧
   RCN095.PolynomialInFlag ⟨a,b,s+3⟩ (surfaceMap φ (polyG K F)):=by
 have hS:=support_data a b s F hR hYR hAll
 have hr:=hS.s_weight
 have hm:=hS.ys_weight
 have ha:=hS.total_weight
 change wt RCN156.residualSWeights F≤s+2 at hr
 change wt RCN156.residualYSWeights F≤b+s+3 at hm
 change wt RCN156.residualTotalWeights F≤a+b+s+3 at ha
 constructor
 · apply mapped_flag_p19 φ (polyH K F) a (b+1) (s+1)
   · simpa [RCN156.residualSWeights] using wt_polyH_le RCN156.residualSWeights F (s+2) hr
   · have h:=wt_polyH_le RCN156.residualYSWeights F (b+s+3) hm
     change wt RCN156.residualYSWeights (polyH K F)≤b+s+3-1 at h
     omega
   · have h:=wt_polyH_le RCN156.residualTotalWeights F (a+b+s+3) ha
     change wt RCN156.residualTotalWeights (polyH K F)≤a+b+s+3-1 at h
     omega
 · apply mapped_flag_p19 φ (polyG K F) a b (s+3)
   · simpa using G_weight_p19 RCN156.residualSWeights 0 rfl rfl rfl (by omega) F
       (s+2) (by omega) hr
   · simpa [Nat.add_assoc] using G_weight_p19 RCN156.residualYSWeights 1 rfl rfl rfl (by omega) F
       (b+s+3) (by omega) hm
   · have h:=G_weight_p19 RCN156.residualTotalWeights 1 rfl rfl rfl (by omega) F
       (a+b+s+3) (by omega) ha
     omega
end
end RCN201
end SubmissionLower
end ProximityPrize
end PackedLegacy_M5
section PackedLegacy_ET
namespace ProximityPrize
namespace SubmissionLower
namespace RCN151
open scoped Classical
open RCN136 RCN231 RCN319 RCN313 RCN065 RCN238 RCN163 RCN156 RCN275 RCN234 RCN094 RCN095 RCN125 RCN162
open RCN319 renaming specialization → BM
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure BOH
   (phi:Polynomial K→+*Omega) (Gamma:Finset K) (x:Iota→K)
   (p e:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree) (d:ℕ)
   (support:RCN275.ResidualSupportParameters:=
     RCN275.ResidualSupportParameters.acceptedSupport) where
 nodes:Finset Iota
 u0:Iota→K
 u1:Iota→K
 selected:K→Polynomial K
 F:Poly4 K
 G:Poly3 Omega
 T:Poly3 Omega
 primeData:AIQ G T
   (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))
 RR:G∣surfaceMap phi F
 G_flag_support:RCN095.PolynomialInFlag surfaceFlag G
 T_flag_support:RCN095.PolynomialInFlag cutFlag T
 AFS:wt RCN156.residualSWeights F≤support.s
 ACG:wt RCN156.residualYSWeights F≤support.ys
 UT:wt RCN156.residualTotalWeights F≤support.total
 x_injective:Set.InjOn x nodes
 degree_le:∀gamma∈Gamma,(selected gamma).natDegree≤d
 solution:∀gamma∈Gamma,
   RCN319.specialization K (selected gamma) gamma F=0
 regular:∀gamma∈Gamma,
   MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (RCN231.polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
       (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0
 on_prime:∀gamma∈Gamma,primeData.ideal≤RingHom.ker
   (MvPolynomial.aeval (DK phi selected gamma)).toRingHom
 BNN:BL selected Gamma d e
 WG:d<p
namespace BOH
variable {phi:Polynomial K→+*Omega} {Gamma:Finset K}
 {x:Iota→K} {p e:ℕ} [CharP Omega p]
 {surfaceFlag cutFlag:FlagDegree} {d:ℕ}
 {support:RCN275.ResidualSupportParameters}
def Agrees
   (S:BOH phi Gamma x p e surfaceFlag cutFlag d support)
   (gamma:K) (i:Iota):Prop:=
 (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i
end BOH
end
end RCN151
end SubmissionLower
end ProximityPrize
end PackedLegacy_ET
section PackedLegacy_DP
namespace ProximityPrize
namespace SubmissionLower
namespace RCN038
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044 RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370 RCN351
open RCN037
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure JO
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hactive:∀C:RCN264.RegularComponent Omega G T H,
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0) where
 lam:Omega
 lam_ne:lam≠0
 mu:Omega
 mu_ne:mu≠0
 uProjection:∀C:RCN264.RegularComponent Omega G T H,
   Coordinate Omega (RCN002.CoordinateField Omega C.1)
 NV:∀C:RCN264.RegularComponent Omega G T H,
   Coordinate Omega (RCN002.CoordinateField Omega C.1)
 uGate:∀C:RCN264.RegularComponent Omega G T H,
   ∀htr:Transcendental Omega (affineU Omega C.1 lam),
     (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
         (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1))∧
     (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
         (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1))
 ZG:∀C:RCN264.RegularComponent Omega G T H,
   Transcendental Omega (affineU Omega C.1 lam)
 GN:∀C:RCN264.RegularComponent Omega G T H,
   Transcendental Omega (affineV Omega C.1 mu (mu*lam))
 allFinite:∀C:RCN264.RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (GN C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1)
 allSeparable:∀C:RCN264.RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
     (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (GN C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1)
 uValue:∀C:RCN264.RegularComponent Omega G T H,
   RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (uProjection C)=
     affineU Omega C.1 lam
 allValue:∀C:RCN264.RegularComponent Omega G T H,
   RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (NV C)=
     affineV Omega C.1 mu (mu*lam)
 ACE:∀C:RCN264.RegularComponent Omega G T H,
   Transcendental Omega
     (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (NV C))
 uPole:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (uProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
       (RCN187.poleOrder v.val (coordinate Omega C.1 2))
 allPole:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (NV C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
       (max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)))
 directional:MvPolynomial.pderiv (0:Fin 3) G-
   MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0
theorem ACK
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hactive:∀C:RCN264.RegularComponent Omega G T H,
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (S:Set Omega) (hS:S.Infinite):
   ∃D:JO base hactive hSderiv,D.lam∈S∧D.mu∈S:=by
 classical
 let E:RCN264.RegularComponent Omega G T H→Type:=
   fun C=>RCN002.CoordinateField Omega C.1
 let rY:∀C,E C:=fun C=>coordinate Omega C.1 0
 let z:∀C,E C:=fun C=>coordinate Omega C.1 2
 let W:∀C,Finset (Place_p19 Omega (E C)):=
   fun C=>OW (base C)
 let baseC:∀C,RCN344.SeparableCoordinate Omega (E C):=
   fun C=>RCN042.literalToSeparableCoordinate (base C)
 obtain ⟨lam,hlamS,hlam0,hlam⟩:=
   RQ E rY z W
     S hS baseC hactive
 let U:∀C:RCN264.RegularComponent Omega G T H,
     RCN002.CoordinateField Omega C.1:=fun C=>affineU Omega C.1 lam
 have hUgate:∀C:RCN264.RegularComponent Omega G T H,
     ∀htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega C.1))∧
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega C.1)):=by
   intro C htr
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   have hp:htr=hs:=Subsingleton.elim _ _
   cases hp
   exact ⟨hfinite,hsep⟩
 let uProjection:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=
   fun C=>RCN042.coordinateOfGate (U C) (hUgate C)
 have huValue:∀C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (uProjection C)=U C:=
   fun C=>RCN042.coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)):=by
   intro C v
   by_cases hv:v∈OW (base C)
   · exact RCN099.poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rY,z,U,affineU] using
         (hlam C).choose_spec.2.2 v hv)
   · have h0:=DW
         (base C) v hv 0
     have h2:=DW
         (base C) v hv 2
     have h0le:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ h0
     have h2le:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ h2
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (lam • coordinate Omega C.1 2)=
         v.val (coordinate Omega C.1 2):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
     have hUle:v.val (U C)≤1:=by
       exact (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le h0le h2le)
     have hU0:RCN187.poleOrder v.val (U C)=0:=
       RCN346._Q11 Omega
         (RCN002.CoordinateField Omega C.1) v _ hUle
     rw [hU0,h0,h2]
     simp
 have hactiveV:∀C:RCN264.RegularComponent Omega G T H,
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 1)≠0∨
       D Omega (RCN002.CoordinateField Omega C.1) (U C)≠0:=by
   intro C
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   exact Or.inr (RCN042.differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
 let rS:∀C,E C:=fun C=>coordinate Omega C.1 1
 let Extra:Omega→Prop:=fun mu=>
   MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G=0
 have hextra:∀{a b},Extra a→Extra b→a=b:=by
   exact RCN096.directional_bad_coefficient_subsingleton G hSderiv
 obtain ⟨mu,hmuS,hmu0,hmudir,hmu⟩:=
   WV
     E rS U W S hS Extra hextra baseC hactiveV
 let V:∀C:RCN264.RegularComponent Omega G T H,
     RCN002.CoordinateField Omega C.1:=
   fun C=>coordinate Omega C.1 1+mu • U C
 let hV:∀C:RCN264.RegularComponent Omega G T H,
     Transcendental Omega (V C):=fun C=>(hmu C).choose
 let vProjection:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=fun C=>Sum.inr {
   embedding:=RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (vProjection C)=V C:=by
   intro C
   exact RCN022.elementEmbedding_variable Omega (RCN002.CoordinateField Omega C.1) (V C) (hV C)
 have hvPole:∀(C:RCN264.RegularComponent Omega G T H)
     (v:Place_p19 Omega (RCN002.CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈OW (base C)
   · exact RCN099.poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=DW
         (base C) v hv 1
     have hY:=DW
         (base C) v hv 0
     have hZ:=DW
         (base C) v hv 2
     have hU:RCN187.poleOrder v.val (U C)=0:=by
       rw [huPole C v,hY,hZ]
       simp
     have hSle:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ hS
     have hUle:=RCN099.valuation_le_one_of_poleOrder_eq_zero v.val _ hU
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (mu • U C)=v.val (U C):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one mu hmu0,one_mul]
     have hVle:v.val (V C)≤1:=
       (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le hSle hUle)
     have hV0:RCN187.poleOrder v.val (V C)=0:=
       RCN346._Q11 Omega
         (RCN002.CoordinateField Omega C.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀C:RCN264.RegularComponent Omega G T H,
     Transcendental Omega (affineV Omega C.1 mu (mu*lam)):=fun C=>by
   rw [show affineV Omega C.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:RCN264.RegularComponent Omega G T H):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
         (affineV Omega C.1 mu (mu*lam)) (hVAff C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1) (V C) (hV C):=
   RCN116.elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])
 refine ⟨{
   lam:=lam
   lam_ne:=hlam0
   mu:=mu
   mu_ne:=hmu0
   uProjection:=uProjection
   NV:=vProjection
   uGate:=hUgate
   ZG:=fun C=>(hlam C).choose
   GN:=hVAff
   allFinite:=?_
   allSeparable:=?_
   uValue:=huValue
   allValue:=?_
   ACE:=?_
   uPole:=?_
   allPole:=?_
   directional:=hmudir},hlamS,hmuS⟩
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.1
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.2.1
 · intro C
   rw [hvValue C]
   simp only [V,U,affineU,affineV]
   simp only [smul_add,smul_smul,add_assoc]
 · intro C
   rw [hvValue C]
   exact hV C
 · intro C v
   rw [huValue C]
   exact huPole C v
 · intro C v
   rw [hvValue C,hvPole C v,huPole C v]
theorem AFF
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hactive:∀C:RCN264.RegularComponent Omega G T H,
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   Nonempty (JO base hactive hSderiv):=
 ⟨(ACK base hactive hSderiv
   Set.univ Set.infinite_univ).choose⟩
end
end RCN038
end SubmissionLower
end ProximityPrize
end PackedLegacy_DP
section PackedLegacy_A2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN040
open scoped Classical BigOperators WithZero
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN046 RCN037 RCN038 RCN095 RCN114 RCN093 RCN123 RCN121 RCN117 RCN116 RCN125 RCN022
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def ALJ
   (p q:FlagDegree)
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hactive:∀C:RCN264.RegularComponent Omega G T H,
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀C:RCN264.RegularComponent Omega G T H,
     RCN037.LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:JO base hactive hSderiv)
   (hG:Irreducible G) (hproper:¬G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   EE base p q:=by
 classical
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let zProj:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=fun C=>
   RCN042.coordinateOfGate (coordinate Omega C.1 2) (hZ C)
 let uProj:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=fun C=>
   RCN042.coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)
 let vProj:∀C:RCN264.RegularComponent Omega G T H,
     Coordinate Omega (RCN002.CoordinateField Omega C.1):=fun C=>Sum.inr {
   embedding:=RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.GN C)
   finite:=D.allFinite C
   separable:=D.allSeparable C}
 let gCaps:=LQ p G lam mu nu hGsupport
 let tCaps:=LQ q T lam mu nu hTsupport
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let sZ:={C:RCN264.RegularComponent Omega G T H//
   Transcendental Omega (coordinate Omega C.1 2)}
 have hinjZ:Function.Injective (fun C:sZ=>C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htZ:∀C:sZ,
     Transcendental Omega
       (RCN093.flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (zOrder_p19 0))):=by
   intro C
   simpa [zOrder_p19,Equiv.swap_apply_def,lam,mu,nu] using C.2
 have hembZ (C:sZ):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder_p19 0))) (htZ C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (coordinate Omega C.1.1 2) C.2:=
   RCN116.elementEmbedding_congr (htZ C) C.2
     (by simp [zOrder_p19,Equiv.swap_apply_def,lam,mu,nu])
 have hgenZ:∀C:sZ,
     letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
       (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder_p19 0))) (htZ C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder_p19 2)),
         RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder_p19 1))}:
         Set (RCN002.CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembZ C]
   simpa [zOrder_p19,Equiv.swap_apply_def,lam,mu,nu] using
     BKE Omega C.1.1 lam mu nu C.2
 have hfamilyZ:=RG
   (K:=Omega) (Q:=fun C:sZ=>C.1.1) hinjZ lam mu nu zOrder_p19
   htZ hgenZ G T hG
   (fun C=>EN Omega G T H C.1)
   (fun C=>GV Omega G T H C.1)
   hproper
   (MV D.lam D.mu G hSderiv).2
   p.all q.all (p.yz+p.all) (q.yz+q.all)
   (flagMixed p q unitZFlag) hTne
   (by simpa only [gCaps] using gCaps.zOuter)
   (by simpa only [tCaps] using tCaps.zOuter)
   (by simpa only [gCaps] using gCaps.zTotal)
   (by simpa only [tCaps] using tCaps.zTotal)
   (RCN121.z_flag_trapezoid_budget p q)
 have hsumZ:
     (∑ C:RCN264.RegularComponent Omega G T H,
       RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (zProj C))≤
       flagMixed p q unitZFlag:=by
   have hsplit:=RCN042.sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RCN264.RegularComponent Omega G T H=>RCN002.CoordinateField Omega C.1)
     (x:=fun C=>coordinate Omega C.1 2) hZ
   change (∑ C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
       (RCN042.coordinateOfGate (coordinate Omega C.1 2) (hZ C)))≤_
   rw [hsplit]
   calc
     (∑ C:sZ,
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
         (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
           (coordinate Omega C.1.1 2) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1)))=
         ∑ C:sZ,
           (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
             (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
               (RCN093.flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (zOrder_p19 0))) (htZ C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembZ C]
     _≤_:=hfamilyZ.2
 let sU:={C:RCN264.RegularComponent Omega G T H//
   Transcendental Omega (affineU Omega C.1 D.lam)}
 have hinjU:Function.Injective (fun C:sU=>C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htU:∀C:sU,
     Transcendental Omega
       (RCN093.flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (uOrder_p19 0))):=by
   intro C
   simpa [uOrder_p19,lam,mu,nu] using C.2
 have hembU (C:sU):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder_p19 0))) (htU C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (affineU Omega C.1.1 D.lam) C.2:=
   RCN116.elementEmbedding_congr (htU C) C.2
     (by simp [uOrder_p19,lam,mu,nu])
 have hgenU:∀C:sU,
     letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
       (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
         (RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder_p19 0))) (htU C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder_p19 2)),
         RCN093.flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder_p19 1))}:
         Set (RCN002.CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembU C]
   simpa [uOrder_p19,lam,mu,nu] using
     BUX Omega C.1.1 lam mu nu C.2
 have hfamilyU:=RG
   (K:=Omega) (Q:=fun C:sU=>C.1.1) hinjU lam mu nu uOrder_p19
   htU hgenU G T hG
   (fun C=>EN Omega G T H C.1)
   (fun C=>GV Omega G T H C.1)
   hproper
   (MV D.lam D.mu G hSderiv).1
   p.all q.all (p.zOnly+p.yz+p.all)
   (q.zOnly+q.yz+q.all) (flagMixed p q unitYZFlag) hTne
   (by simpa only [gCaps] using gCaps.uOuter)
   (by simpa only [tCaps] using tCaps.uOuter)
   (by simpa only [gCaps] using gCaps.uTotal)
   (by simpa only [tCaps] using tCaps.uTotal)
   (RCN121.u_flag_trapezoid_budget p q)
 have hsumU:
     (∑ C:RCN264.RegularComponent Omega G T H,
       RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (uProj C))≤
       flagMixed p q unitYZFlag:=by
   have hsplit:=RCN042.sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RCN264.RegularComponent Omega G T H=>RCN002.CoordinateField Omega C.1)
     (x:=fun C=>affineU Omega C.1 D.lam) D.uGate
   change (∑ C:RCN264.RegularComponent Omega G T H,
     RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1)
       (RCN042.coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)))≤_
   rw [hsplit]
   calc
     (∑ C:sU,
       (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
         (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
           (affineU Omega C.1.1 D.lam) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1)))=
         ∑ C:sU,
           (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1):=
             (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1.1)
               (RCN093.flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (uOrder_p19 0))) (htU C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembU C]
     _≤_:=hfamilyU.2
 let htV:∀C:RCN264.RegularComponent Omega G T H,
     Transcendental Omega
       (RCN093.flagEvaluation Omega C.1 lam mu nu
         (MvPolynomial.X (vOrder_p19 0))):=by
   intro C
   simpa [vOrder_p19,Equiv.swap_apply_def,lam,mu,nu] using
     D.GN C
 have hembV (C:RCN264.RegularComponent Omega G T H):
     RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
         (RCN093.flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder_p19 0))) (htV C)=
       RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam))
           (D.GN C):=
   RCN116.elementEmbedding_congr (htV C) (D.GN C)
     (by simp [vOrder_p19,Equiv.swap_apply_def,lam,mu,nu])
 have hgenV:∀C:RCN264.RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
       (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
         (RCN093.flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder_p19 0))) (htV C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({RCN093.flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder_p19 2)),
         RCN093.flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder_p19 1))}:
         Set (RCN002.CoordinateField Omega C.1))=⊤:=by
   intro C
   rw [hembV C]
   simpa [vOrder_p19,Equiv.swap_apply_def,lam,mu,nu] using
     BTS Omega C.1 lam mu nu (D.GN C)
 have hinjV:Function.Injective
     (fun C:RCN264.RegularComponent Omega G T H=>C.1):=by
   intro C E hCE
   exact Subtype.ext hCE
 have hfamilyV:=RG
   (K:=Omega) (Q:=fun C:RCN264.RegularComponent Omega G T H=>C.1)
   hinjV lam mu nu vOrder_p19 htV hgenV G T hG
   (fun C=>EN Omega G T H C)
   (fun C=>GV Omega G T H C)
   hproper
   (XD D.lam D.mu G D.directional)
   (p.yz+p.all) (q.yz+q.all)
   (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
   (flagMixed p q unitAllFlag) hTne
   (by simpa only [gCaps] using gCaps.vOuter)
   (by simpa only [tCaps] using tCaps.vOuter)
   (by simpa only [gCaps] using gCaps.vTotal)
   (by simpa only [tCaps] using tCaps.vTotal)
   (RCN121.v_flag_trapezoid_budget p q)
 have hsumV:
     (∑ C:RCN264.RegularComponent Omega G T H,
       RCN344.coordinateDegree Omega (RCN002.CoordinateField Omega C.1) (vProj C))≤
       flagMixed p q unitAllFlag:=by
   calc
     _=∑ C:RCN264.RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
             (affineV Omega C.1 D.mu (D.mu*D.lam))
               (D.GN C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rfl
     _=∑ C:RCN264.RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega C.1):=
           (RCN022.elementEmbedding Omega (RCN002.CoordinateField Omega C.1)
             (RCN093.flagEvaluation Omega C.1 lam mu nu
               (MvPolynomial.X (vOrder_p19 0))) (htV C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (RCN002.CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembV C]
     _≤_:=hfamilyV.2
 have hvValue (C:RCN264.RegularComponent Omega G T H):
     RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1) (vProj C)=
       affineV Omega C.1 D.mu (D.mu*D.lam):=by
   dsimp only [vProj,RCN344.coordinateValue,RCN344.SeparableCoordinate.value,Sum.elim_inr]
   exact RCN022.elementEmbedding_variable Omega (RCN002.CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.GN C)
 refine {
   zProjection:=zProj
   yzProjection:=uProj
   NV:=vProj
   zValue:=?_
   ACE:=?_
   zPole_eq:=?_
   yzPole_eq:=?_
   allPole_eq:=?_
   ARJ:=hsumZ
   ALE:=hsumU
   AQB:=hsumV}
 · intro C
   exact RCN042.coordinateOfGate_value _ _
 · intro C
   rw [hvValue C]
   exact D.GN C
 · intro C v
   rw [UC]
   change _=RCN187.poleOrder v.val _
   simp only [zProj]
   exact congrArg (RCN187.poleOrder v.val) (RCN042.coordinateOfGate_value _ _).symm
 · intro C v
   rw [QD]
   change _=RCN187.poleOrder v.val _
   rw [RCN042.coordinateOfGate_value]
   rw [←D.uValue C]
   exact (D.uPole C v).symm
 · intro C v
   rw [SF]
   change _=RCN187.poleOrder v.val _
   rw [hvValue C,←D.allValue C]
   exact (D.allPole C v).symm
end
end RCN040
end SubmissionLower
end ProximityPrize
end PackedLegacy_A2
section PackedLegacy_E7
namespace ProximityPrize
namespace SubmissionLower
namespace RCN265
open scoped Classical
open RCN002 RCN136 RCN243 RCN264 RCN267 RCN344 RCN341 RCN042 RCN037 RCN039 RCN046 RCN142 RCN093 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {K:Type} [Field K]
theorem AAO
   (phi:Polynomial K→+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Omega)
   (hdiv:G∣surfaceMap phi F)
   (C:RCN264.RegularComponent Omega G T (CR phi F)):
   Transcendental Omega (coordinate Omega C.1 0)∨
     Transcendental Omega (coordinate Omega C.1 2):=by
 let H:=CR phi F
 have hGmem:G∈C.1:=EN Omega G T H C
 have hFmem:surfaceMap phi F∈C.1:=by
   obtain ⟨Q,hQ⟩:=hdiv
   rw [hQ]
   exact C.1.mul_mem_right Q hGmem
 have hFRnot:MvPolynomial.pderiv (1:Fin 3) (surfaceMap phi F)∉C.1:=by
   rw [RCN267.surfaceMap_pderiv_R]
   exact _Q6 Omega G T H C
 exact RCN265.y_or_z_transcendental_of_regular_polynomial C.1 (surfaceMap phi F)
   hFmem hFRnot (PU Omega G T H C)
section RefinedAdaptiveFamily
variable {G T H:MvPolynomial (Fin 3) Omega}
structure YQ
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 family:EE base p q
 lam:Omega
 yzValue:∀C:RCN264.RegularComponent Omega G T H,
   RCN344.coordinateValue Omega (RCN002.CoordinateField Omega C.1)
       (family.yzProjection C)=affineU Omega C.1 lam
theorem YQ.one_le_zCost_add_yzCost
   {base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1}
   {p q:FlagDegree}
   (P:YQ base p q)
   (phi:Polynomial K→+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (hH:H=CR phi F)
   (hdiv:G∣surfaceMap phi F)
   (C:RCN264.RegularComponent Omega G T H):
   1≤P.family.toFE.zCost C+
     P.family.toFE.yzCost C:=by
 subst H
 have hYZ:=AAO phi F G T hdiv C
 by_cases hZ:Transcendental Omega (coordinate Omega C.1 2)
 · have hzpos:1≤P.family.toFE.zCost C:=
     P.family.one_le_toPrimeFlagBudgetFamily_zCost C hZ
   omega
 · have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=
     not_not.mp hZ
   have hY:Transcendental Omega (coordinate Omega C.1 0):=by
     rcases hYZ with hY | hZ'
     · exact hY
     · exact (hZ hZ').elim
   have hU:Transcendental Omega (affineU Omega C.1 P.lam):=by
     exact RCN142.transcendental_add_smul_of_transcendental_isAlgebraic
       Omega C.1 (coordinate Omega C.1 0) (coordinate Omega C.1 2)
         P.lam hY hZalg
   have hyzpos:1≤P.family.toFE.yzCost C:=by
     apply RCN042.one_le_coordinateDegree_of_transcendental_value
     rw [P.yzValue C]
     exact hU
   omega
end RefinedAdaptiveFamily
end
end RCN265
end SubmissionLower
end ProximityPrize
end PackedLegacy_E7
section PackedLegacy_DQ
namespace ProximityPrize
namespace SubmissionLower
namespace RCN041
open scoped Classical
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN093 RCN037 RCN038 RCN040 RCN046 RCN265 RCN095
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def BJW
   (p q:FlagDegree)
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hactive:∀C:RCN264.RegularComponent Omega G T H,
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀C:RCN264.RegularComponent Omega G T H,
     RCN037.LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:JO base hactive hSderiv)
   (hG:Irreducible G) (hproper:¬G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   YQ base p q where
 family:=ALJ p q base hactive hZ
   hSderiv D hG hproper hGsupport hTsupport
 lam:=D.lam
 yzValue:=by
   intro C
   exact RCN042.coordinateOfGate_value (affineU Omega C.1 D.lam) (D.uGate C)
theorem AEJ
   (p q:FlagDegree)
   (base:∀C:RCN264.RegularComponent Omega G T H,
     RCN341.SeparableLiteralCoordinate C.1)
   (hactive:∀C:RCN264.RegularComponent Omega G T H,
     D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (RCN002.CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀C:RCN264.RegularComponent Omega G T H,
     RCN037.LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (YQ base p q):=by
 obtain ⟨D⟩:=AFF base hactive hSderiv
 exact ⟨BJW p q base hactive hZ
   hSderiv D hG hproper hGsupport hTsupport⟩
end
end RCN041
end SubmissionLower
end ProximityPrize
end PackedLegacy_DQ
section PackedLegacy_O6
namespace ProximityPrize
namespace SubmissionLower
namespace RCN277
open scoped Classical
open RCN002 RCN005 RCN003 RCN009 RCN001 RCN072 RCN264 RCN136 RCN243 RCN341 RCN265
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
theorem AKM
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime]
   (p:ℕ) [CharP Omega p]
   (G:Poly3 (Omega:=Omega))
   (hG:Irreducible G) (hGmem:G∈P)
   (hdep:0<G.degreeOf (1:Fin 3))
   (hdegree:∀j:Fin 3,G.degreeOf j<p)
   (hY:Transcendental Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   letI:Algebra (RatFunc Omega) (RCN002.CoordinateField Omega P):=
     RCN005.rationalBaseAlgebra Omega P 0 hY
   FiniteDimensional (RatFunc Omega) (RCN002.CoordinateField Omega P)∧
     Algebra.IsSeparable (RatFunc Omega) (RCN002.CoordinateField Omega P):=by
 obtain ⟨c,hHmem⟩:=
   RCN277.exists_coordinate_difference_mem_of_isAlgebraic P 2 hZ
 let H:Poly3 (Omega:=Omega):=
   MvPolynomial.X (2:Fin 3)-MvPolynomial.C c
 have hproper:¬G∣H:=
   RCN277.not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos G hG.ne_zero hdep c
 have hHone:H.degreeOf (1:Fin 3)≤0:=by
   calc
     H.degreeOf (1:Fin 3)≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 1)
           ((MvPolynomial.C c:Poly3).degreeOf 1):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (1:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=0:=by
       rw [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2),
         MvPolynomial.degreeOf_C]
       rfl
 have hHtwo:H.degreeOf (2:Fin 3)≤1:=by
   calc
     H.degreeOf (2:Fin 3)≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 2)
           ((MvPolynomial.C c:Poly3).degreeOf 2):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (2:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=1:=by simp
 have hmixed:RCN001.coordinateMixedDegree Omega G H 0<p:=by
   rw [RCN001.coordinateMixedDegree_zero]
   calc
     H.degreeOf 1*G.degreeOf 2+G.degreeOf 1*H.degreeOf 2≤
         0*G.degreeOf 2+G.degreeOf 1*1:=
       Nat.add_le_add (Nat.mul_le_mul hHone (Nat.le_refl _))
         (Nat.mul_le_mul (Nat.le_refl _) hHtwo)
     _=G.degreeOf 1:=by simp
     _<p:=hdegree 1
 exact RH Omega P 0 hY p G H
   hG hGmem hHmem hproper hdegree hmixed
theorem CAC
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime]
   (p:ℕ) [CharP Omega p]
   (G T:Poly3 (Omega:=Omega))
   (hG:Irreducible G) (hGmem:G∈P) (hTmem:T∈P)
   (hproper:¬G∣T)
   (hdep:0<G.degreeOf (1:Fin 3))
   (hdegree:∀j:Fin 3,G.degreeOf j<p)
   (hmixedZ:RCN001.coordinateMixedDegree Omega G T 2<p)
   (hYZ:Transcendental Omega (coordinate Omega P 0)∨
     Transcendental Omega (coordinate Omega P 2)):
   ∃D:RCN341.SeparableLiteralCoordinate P,
     D.index=0∨D.index=2:=by
 by_cases hZ:Transcendental Omega (coordinate Omega P 2)
 · have hz:=RH
     Omega P 2 hZ p G T hG hGmem hTmem hproper hdegree hmixedZ
   exact ⟨⟨2,hZ,hz.1,hz.2⟩,Or.inr rfl⟩
 · have hY:Transcendental Omega (coordinate Omega P 0):=
     hYZ.resolve_right hZ
   have hZalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hZ
   have hy:=AKM P p G hG hGmem hdep
     hdegree hY hZalg
   exact ⟨⟨0,hY,hy.1,hy.2⟩,Or.inl rfl⟩
theorem AEP
   {K:Type} [Field K]
   (phi:Polynomial K→+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:Poly3 (Omega:=Omega))
   (p:ℕ) [CharP Omega p]
   (hdiv:G∣surfaceMap phi F)
   (hG:Irreducible G) (hproper:¬G∣T)
   (hdep:0<G.degreeOf (1:Fin 3))
   (hdegree:∀j:Fin 3,G.degreeOf j<p)
   (hmixedZ:RCN001.coordinateMixedDegree Omega G T 2<p)
   (C:RCN264.RegularComponent Omega G T (CR phi F)):
   ∃D:RCN341.SeparableLiteralCoordinate C.1,
     D.index=0∨D.index=2:=by
 apply CAC C.1 p G T hG
   (EN Omega G T (CR phi F) C)
   (GV Omega G T (CR phi F) C)
   hproper hdep hdegree hmixedZ
 exact AAO phi F G T hdiv C
end
end RCN277
end SubmissionLower
end ProximityPrize
end PackedLegacy_O6
section PackedLegacy_GN
namespace ProximityPrize
namespace SubmissionLower
namespace RCN314
open scoped Classical
open RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN095 RCN159 RCN156 RCN037 RCN039 RCN341
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K→+*Omega} {Gamma:Finset K} {x:Iota→K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem WD
   {p:FlagDegree} {F:MvPolynomial (Fin 3) Omega}
   (hF:RCN095.PolynomialInFlag p F):
   F.degreeOf 0≤p.yz+p.all∧
     F.degreeOf 1≤p.all∧
     F.degreeOf 2≤p.zOnly+p.yz+p.all:=by
 refine ⟨?_,?_,?_⟩
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (hF e he).1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (Nat.le_add_left (e 2) (e 0+e 1)).trans (by
     simpa only [Nat.add_assoc] using (hF e he).2.2)
end
end RCN314
end SubmissionLower
end ProximityPrize
end PackedLegacy_GN
section PackedLegacy_GO
namespace ProximityPrize
namespace SubmissionLower
namespace RCN315
open scoped Classical
open RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN267 RCN095 RCN159 RCN037 RCN039 RCN046 RCN341 RCN275
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K→+*Omega} {Gamma:Finset K} {x:Iota→K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem EH
   {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
   {support:RCN275.ResidualSupportParameters}
   (S:FH phi Gamma x p e flag d support):
   MvPolynomial.pderiv (1:Fin 3) S.G≠0:=by
 intro hzero
 apply S.BLO
 rw [←RCN267.surfaceMap_pderiv_R]
 obtain ⟨Q,hQ⟩:=S.RR
 refine ⟨MvPolynomial.pderiv (1:Fin 3) Q,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul,hzero,zero_mul,zero_add]
end
end RCN315
end SubmissionLower
end ProximityPrize
end PackedLegacy_GO
section PackedLegacy_B7
namespace ProximityPrize
namespace SubmissionLower
namespace RCN089
open RCN136 RCN313 RCN238 RCN275 RCN095 RCN198 RCN086 RCN262 RCN263
open RCN095 renaming PolynomialInFlag → BI
open RCN262 renaming pderiv_eq_zero_of_wt_lt → BBG
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
theorem AOF
   (phi:Polynomial K→+*Omega) (support:RCN275.ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:RCN275.ResidualSupportData support F)
   (d:ℕ):
   RCN095.PolynomialInFlag (RCN263.reducedResidualAgreementFlag support d)
     (RCN089.reducedGlobalTailCut phi support F d):=by
 exact CWR phi support H d
   (tailSelector d) 0 0 0
end
end RCN089
end SubmissionLower
end ProximityPrize
end PackedLegacy_B7
section PackedLegacy_J5
namespace ProximityPrize
namespace SubmissionLower
namespace RCN090
open scoped Classical BigOperators
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
   (hmixed:(1+(w+1)*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-2)*(w+1))<pchar):
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
 obtain ⟨hTY,hTS,_hTZ⟩:=
   RCN314.WD
     hTflag
 have hTY':Tred.degreeOf 0≤1+(w+1)*(2*(b+s+3)-2):=by
   apply hTY.trans_eq
   exact RCN263.reducedResidualAgreementFlag_ys supp (w+1)
 have hTS':Tred.degreeOf 1≤(2*(s+2)-2)*(w+1):=by
   apply hTS.trans_eq
   rfl
 have hGdegree:∀j:Fin 3,S.G.degreeOf j<pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixedZ:RCN001.coordinateMixedDegree Omega S.G Tred 2<pchar:=by
   rw [RCN001.coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀C:RCN264.RegularComponent Omega S.G Tred H,
     ∃B:RCN341.SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C↦AEP
     phi S.F S.G Tred pchar S.RR S.MW hproperRed
     S.y_dependent hGdegree hmixedZ C
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
 have hZ:∀C:RCN264.RegularComponent Omega S.G Tred H,
     RCN037.LiteralProjectionGate C 2:=by
   intro C htr
   exact RH Omega C.1 2 htr
     pchar S.G Tred S.MW
     (EN Omega S.G Tred H C)
     (GV Omega S.G Tred H C)
     hproperRed hGdegree hmixedZ
 exact ⟨base,hactive,hZ,
   AFF base hactive
     (RCN315.EH S)⟩
end
end RCN090
end SubmissionLower
end ProximityPrize
end PackedLegacy_J5
section PackedLegacy_P7
namespace ProximityPrize
namespace SubmissionLower
namespace RCN330
open scoped Classical
open RCN313 RCN231 RCN136 RCN238 RCN086 RCN055 RCN264 RCN243
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K Ω:Type} [Field K] [Field Ω]
theorem VZ
   (φ:Polynomial K→+*Ω) (F:MvPolynomial (Fin 4) K)
   (selected:K→Polynomial K) (γ:K) (w d:ℕ)
   (hdegree:(selected γ).natDegree≤w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0)
   (hwd:w<d):
   MvPolynomial.aeval (DK φ selected γ)
     (RCN086.globalTailCut φ F d)=0:=by
 rw [RCN086.globalTailCut_eq,map_mul]
 have hzero:MvPolynomial.eval (DK φ selected γ)
     (surfaceMap φ (numerator K F d))=0:=by
   rw [RCN136.eval_surfaceMap]
   have hv:Fin.cases (φ Polynomial.X) (DK φ selected γ)=
       RCN231.polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
         (φ Polynomial.X):=by
     funext i
     fin_cases i<;>rfl
   rw [hv]
   exact RCN231.polynomialPoint_numerator_zero (φ.comp Polynomial.C) F
     (selected γ) γ (φ Polynomial.X) hsolution d
     (hdegree.trans_lt hwd)
 change MvPolynomial.eval (DK φ selected γ)
     (surfaceMap φ (numerator K F d))*_=0
 rw [hzero,zero_mul]
end
end RCN330
end SubmissionLower
end ProximityPrize
end PackedLegacy_P7
section PackedLegacy_B3
namespace ProximityPrize
namespace SubmissionLower
namespace RCN074
open scoped Classical BigOperators
open RCN159 RCN136 RCN238 RCN264 RCN243 RCN086 RCN095 RCN237
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K→+*Omega} {Gamma:Finset K} {x:Iota→K}
 {pchar errors w:ℕ} [CharP Omega pchar]
 {flag tailFlag1 tailFlag2:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
abbrev CM
   (S:FH phi Gamma x pchar errors flag w support):=
 RCN264.RegularComponent Omega S.G (RCN086.globalTailCut phi S.F (w+1))
   (CR phi S.F)
structure BOM
   (S:FH phi Gamma x pchar errors flag w support) where
 budgetFamily:FE
   (G:=S.G) (T:=RCN086.globalTailCut phi S.F (w+1))
   (H:=CR phi S.F) flag tailFlag1
 multiplicity:CM S→ℕ
 cost:CM S→ℕ
 one_le_multiplicity:∀C,1≤multiplicity C
 EHX:errors+1≤tailFlag2.yz
 cost_le:∀C,
   cost C≤multiplicity C*budgetFamily.weightedCost tailFlag2 C
 divisor_le:
   (∑ C,multiplicity C*budgetFamily.weightedCost tailFlag2 C)≤
     flagMixed flag tailFlag1 tailFlag2
 CRK:∀C,
   (RCN264.componentSeeds Omega S.G (RCN086.globalTailCut phi S.F (w+1))
     (CR phi S.F) Gamma
     (DK phi S.selected) C).card≤cost C
 dichotomy:∀C,
   (∃delay,1≤delay∧delay≤multiplicity C∧
     RCN086.globalTailCut phi S.F (w+1+delay)∉C.1)∨
   ((∀delay,RCN086.globalTailCut phi S.F (w+1+delay)∈C.1)∧
     (RCN264.componentSeeds Omega S.G (RCN086.globalTailCut phi S.F (w+1))
       (CR phi S.F) Gamma
       (DK phi S.selected) C).card≤
         (errors+1)*budgetFamily.yzCost C)
end
end RCN074
end SubmissionLower
end ProximityPrize
end PackedLegacy_B3
section PackedLegacy_AM
namespace ProximityPrize
namespace SubmissionLower
namespace RCN338
open scoped Classical BigOperators
open RCN095 RCN264 RCN237 RCN121 RCN337
open RCN095 renaming PolynomialInFlag → BI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
structure EY
   (B:FE
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RCN264.RegularComponent Omega G T H→ℕ) where
 z:(∑ C,multiplicity C*B.zCost C)≤
   flagMixed surfaceFlag firstTailFlag unitZFlag
 yz:(∑ C,multiplicity C*B.yzCost C)≤
   flagMixed surfaceFlag firstTailFlag unitYZFlag
 all:(∑ C,multiplicity C*B.allCost C)≤
   flagMixed surfaceFlag firstTailFlag unitAllFlag
end
end RCN338
end SubmissionLower
end ProximityPrize
end PackedLegacy_AM
section PackedLegacy_EC
namespace ProximityPrize
namespace SubmissionLower
namespace RCN113
open RCN002 RCN011 RCN371 RCN021 RCN125 RCN093
open RCN371 renaming RationalPolynomials → KU
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K:Type) [Field K]
def flagPlaneMap_p19 (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Original K→+*PlaneRing K:=
 (planeMap K order).comp (flagAlgHom_p19 lam mu nu).toRingHom
end
end RCN113
end SubmissionLower
end ProximityPrize
end PackedLegacy_EC
section PackedLegacy_Y9
namespace ProximityPrize
namespace SubmissionLower
namespace RCN106
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN120 RCN102 RCN014 RCN226 RCN225 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
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
include hcomponent in
theorem DQZ
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Function.Injective
     (RCN106.indexedFiberRelation component lam mu nu order ht q hq):=by
 intro a b hab
 have hunder:=congrArg (Ideal.comap (RCN102.fiberLocalizePlane q hq)) hab
 rw [RCN106.indexedFiberRelation_under component lam mu nu order ht q hq a,
   RCN106.indexedFiberRelation_under component lam mu nu order ht q hq b] at hunder
 have heval:=congrArg (Ideal.comap (planeMap Omega order)) hunder
 rw [RCN021.relationKernel_contract,RCN021.relationKernel_contract] at heval
 have hprime:=congrArg (Ideal.comap (flagAlgHom_p19 lam mu nu).toRingHom) heval
 rw [AEE,AEE] at hprime
 have hcomp:component a.1=component b.1:=Subtype.ext hprime
 exact Subtype.ext (hcomponent hcomp)
include hcomponent hfinite hgen in
theorem AYL
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Pairwise fun a b:RCN106.IndexedFactorFiber component lam mu nu order ht q=>
     IsCoprime (RCN106.indexedFiberRelation component lam mu nu order ht q hq a)
       (RCN106.indexedFiberRelation component lam mu nu order ht q hq b):=by
 intro a b hab
 apply Ideal.isCoprime_iff_sup_eq.mpr
 exact (RCN106.indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
   q hq a).coprime_of_ne
     (RCN106.indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
       q hq b)
     (fun heq=>hab (DQZ
       component hcomponent lam mu nu order ht q hq heq))
end
end RCN106
end SubmissionLower
end ProximityPrize
end PackedLegacy_Y9
section PackedLegacy_C8
namespace ProximityPrize
namespace SubmissionLower
namespace RCN193
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN120
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K→ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
@[simp] theorem planeResidueEquiv_mk
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (RCN022.elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (RCN022.elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤)
   (x:PlaneRing K):
   RCN193.planeResidueEquiv K L order e ht hfinite hgen
       (Ideal.Quotient.mk (RCN021.relationKernel K L order e ht) x)=
     Ideal.Quotient.mk (RCN191.localizedRelation K L order e ht hfinite)
       (RCN191.localizePlane K L order e ht hfinite x):=rfl
end
end RCN193
end SubmissionLower
end ProximityPrize
end PackedLegacy_C8
section PackedLegacy_M2
namespace ProximityPrize
namespace SubmissionLower
namespace RCN196
open scoped Classical BigOperators
open Module
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R M ι:Type*}
 [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
theorem GIY
   (a:ι→R) (ha:∀i,a i≠0):
   Ring.ord R (∏ i,a i)=∑ i,Ring.ord R (a i):=by
 classical
 let s:Finset ι:=Finset.univ
 change Ring.ord R (∏ i∈s,a i)=∑ i∈s,Ring.ord R (a i)
 induction s using Finset.induction_on with
 | empty=>simp
 | @insert i s hi ih=>
     rw [Finset.prod_insert hi,Finset.sum_insert hi,
       Ring.ord_mul' (R:=R)
         (mem_nonZeroDivisors_iff_ne_zero.mpr (ha i)),ih]
theorem EUH
   (b:Basis ι R M) (f:M→ₗ[R] M)
   (hinj:Function.Injective f):
   Module.length R (M ⧸ LinearMap.range f)=Ring.ord R (LinearMap.det f):=by
 classical
 let N:Submodule R M:=LinearMap.range f
 let hrank:Module.finrank R N=Module.finrank R M:=
   f.finrank_range_of_inj hinj
 let a:ι→R:=N.smithNormalFormCoeffs b hrank
 have ha:∀i,a i≠0:=fun i=>N.smithNormalFormCoeffs_ne_zero b hrank i
 have hdecomp:Module.length R (M ⧸ N)=
     ∑ i,Module.length R (R ⧸ Ideal.span ({a i}:Set R)):=by
   rw [(N.quotientEquivPiSpan b hrank).length_eq,
     Module.length_pi_of_fintype R]
 have hprod:Ring.ord R (∏ i,a i)=∑ i,Ring.ord R (a i):=
   GIY a ha
 have hassoc:Associated (LinearMap.det f) (∏ i,a i):=by
   simpa only [N,hrank,a] using RCN196.associated_det_prod_smithRange b f hinj
 change Module.length R (M ⧸ N)=_
 calc
   Module.length R (M ⧸ N)=
       ∑ i,Module.length R (R ⧸ Ideal.span ({a i}:Set R)):=hdecomp
   _=∑ i,Ring.ord R (a i):=rfl
   _=Ring.ord R (∏ i,a i):=hprod.symm
   _=Ring.ord R (LinearMap.det f):=
     (Ring.ord_eq_of_associated hassoc).symm
section TwoModules
variable {N:Type*} [AddCommGroup N] [Module R N]
theorem DJE
   (bM:Basis ι R M) (bN:Basis ι R N)
   (f:M→ₗ[R] N) (hinj:Function.Injective f):
   Module.length R (N ⧸ LinearMap.range f)=
     Ring.ord R (LinearMap.toMatrix bM bN f).det:=by
 classical
 let e:N ≃ₗ[R] M:=bN.equiv bM (Equiv.refl ι)
 let g:N→ₗ[R] N:=f.comp e.toLinearMap
 have hginj:Function.Injective g:=hinj.comp e.injective
 have hrange:LinearMap.range g=LinearMap.range f:=by
   change LinearMap.range (f.comp e.toLinearMap)=LinearMap.range f
   rw [LinearMap.range_comp_of_range_eq_top f e.range]
 have hmatrix:LinearMap.toMatrix bN bN g=
     LinearMap.toMatrix bM bN f:=by
   change LinearMap.toMatrix bN bN (f.comp e.toLinearMap)=_
   rw [LinearMap.toMatrix_comp bN bM bN,
     LinearMap.toMatrix_basis_equiv,Matrix.mul_one]
 calc
   Module.length R (N ⧸ LinearMap.range f)=
       Module.length R (N ⧸ LinearMap.range g):=by rw [hrange]
   _=Ring.ord R (LinearMap.det g):=EUH bN g hginj
   _=Ring.ord R (LinearMap.toMatrix bN bN g).det:=by
     rw [LinearMap.det_toMatrix]
   _=Ring.ord R (LinearMap.toMatrix bM bN f).det:=by rw [hmatrix]
theorem AZE
   {J:Type*} [Fintype J]
   (bM:Basis ι R M) (bN:Basis ι R N)
   (f:M→ₗ[R] N) (hinj:Function.Injective f)
   (pieces:J→Type*)
   [∀j,AddCommGroup (pieces j)] [∀j,Module R (pieces j)]
   (multiplicity:J→ℕ)
   (hlength:∀j,(multiplicity j:ℕ∞)≤Module.length R (pieces j))
   (project:(N ⧸ LinearMap.range f)→ₗ[R] (∀j,pieces j))
   (hsurj:Function.Surjective project):
   ((∑ j,multiplicity j:ℕ):ℕ∞)≤
     Ring.ord R (LinearMap.toMatrix bM bN f).det:=by
 rw [←DJE bM bN f hinj]
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞)=
       ∑ j,(multiplicity j:ℕ∞):=by simp
   _≤ ∑ j,Module.length R (pieces j):=
     Finset.sum_le_sum (fun j _=>hlength j)
   _=Module.length R (∀j,pieces j):=
     (Module.length_pi_of_fintype R pieces).symm
   _≤Module.length R (N ⧸ LinearMap.range f):=
     Module.length_le_of_surjective project hsurj
end TwoModules
end
end RCN196
end SubmissionLower
end ProximityPrize
end PackedLegacy_M2
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
noncomputable def BJB
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface tail:PlaneRing Omega)
   [hSurfacePrime:(Ideal.span {RCN107.indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   (hbarne:∀a,RCN106.indexedFiberRelationBar component lam mu nu order ht
     q hq surface a≠⊥)
   (multiplicity:RCN106.IndexedFactorFiber component lam mu nu order ht q→ℕ)
   (htail:∀a,RCN107.indexedFiberTail q hq tail∈
     Ideal.span {RCN107.indexedFiberSurface q hq surface} ⊔
       RCN106.indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   [hlocal:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (RCN102.FiberCoefficient q hq) (Localization.AtPrime
       (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀a:RCN106.IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (RCN102.FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]:
   RCN307.PrimaryPiecesCertificate (RCN107.indexedFiberSurface q hq surface)
     (RCN107.indexedFiberTail q hq tail) (fun a=>multiplicity a*
       Module.finrank (IsLocalRing.ResidueField (RCN102.FiberCoefficient q hq))
         (IsLocalRing.ResidueField (Localization.AtPrime
           (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface a)))):=by
 exact RCN236.primaryPiecesCertificateOfMembershipWeighted
   (RCN107.indexedFiberSurface q hq surface) (RCN107.indexedFiberTail q hq tail)
   (RCN106.indexedFiberRelation component lam mu nu order ht q hq)
   (RCN106.indexedFiberRelationBar component lam mu nu order ht q hq surface)
   (fun _=>rfl) hbarne multiplicity htail
   (AYL component hcomponent lam mu nu order
     ht hfinite hgen q hq)
end
end RCN107
end SubmissionLower
end ProximityPrize
end PackedLegacy_C3
end Compact_PackedLegacy
end
