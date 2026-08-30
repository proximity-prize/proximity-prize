import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.W3
import ProximityPrize.SubmissionLower.W8
import ProximityPrize.SubmissionLower.CL
import ProximityPrize.SubmissionLower.AQ
namespace ProximityPrize.SubmissionLower.FixedCurveNormSum
open scoped BigOperators Classical nonZeroDivisors
open IsDedekindDomain NormValuationTransport
noncomputable section
variable (K L:Type*) [Field K] [Field L]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
abbrev FiniteNormalization:=FunctionField.ringOfIntegers K L
instance finiteNormalization_finite:
   Module.Finite (Polynomial K) (FiniteNormalization K L):=
 IsIntegralClosure.finite (Polynomial K) (RatFunc K) L (FiniteNormalization K L)
instance finiteNormalization_torsionFree:
   Module.IsTorsionFree (Polynomial K) (FiniteNormalization K L):=by
 letI:Module.IsTorsionFree (Polynomial K) L:=
   Module.IsTorsionFree.trans_faithfulSMul (Polynomial K) (RatFunc K) L
 exact IsIntegralClosure.isTorsionFree (Polynomial K) L
abbrev InfinityBase:=InfinityValuationRing.InfinityRing K
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 InfinityValuationRing.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=integralClosure (InfinityBase K) L
instance infiniteNormalization_finite:
   Module.Finite (InfinityBase K) (InfiniteNormalization K L):=
 IsIntegralClosure.finite (InfinityBase K) (RatFunc K) L (InfiniteNormalization K L)
instance infiniteNormalization_torsionFree:
   Module.IsTorsionFree (InfinityBase K) (InfiniteNormalization K L):=by
 letI:Module.IsTorsionFree (InfinityBase K) L:=
   Module.IsTorsionFree.trans_faithfulSMul (InfinityBase K) (RatFunc K) L
 exact IsIntegralClosure.isTorsionFree (InfinityBase K) L
instance infiniteNormalization_isDedekindDomain:
   IsDedekindDomain (InfiniteNormalization K L):=
 integralClosure.isDedekindDomain (InfinityBase K) (RatFunc K) L
instance infiniteNormalization_isFractionRing:
   IsFractionRing (InfiniteNormalization K L) L:=
 integralClosure.isFractionRing_of_finite_extension (RatFunc K) L
def infinityPlace:HeightOneSpectrum (InfinityBase K):=
 IsDiscreteValuationRing.maximalIdeal (InfinityBase K)
def infinityContribution (x:L):ℤ:=
 ∑ P∈(IsDedekindDomain.primesOverFinset
     (infinityPlace K).asIdeal (InfiniteNormalization K L)).attach,
   (P.1.inertiaDeg (InfinityBase K):ℤ)*
     fieldOrder (InfiniteNormalization K L) L
       (placeAbove (InfinityBase K) (InfiniteNormalization K L) (infinityPlace K) P) x
theorem infinityContribution_eq_normOrder (x:L) (hx:x≠0):
   infinityContribution K L x=
     RatFuncProductFormula.infinityOrder K (Algebra.norm (RatFunc K) x):=by
 have h:=fieldOrder_norm (InfinityBase K) (InfiniteNormalization K L)
   (RatFunc K) L (infinityPlace K) x hx
 change-((infinityPlace K).valuation (RatFunc K)
     (Algebra.norm (RatFunc K) x)).log=infinityContribution K L x at h
 rw [infinityPlace,InfinityValuationRing.infinity_valuation_eq] at h
 exact h.symm
theorem asFraction_eq_canonical (x:RatFunc K):
   RatFuncProductFormula.asFraction K x=
     (FractionRing.algEquiv (Polynomial K) (RatFunc K)).symm x:=by
 letI:Subsingleton
     ((RatFunc K) →ₐ[Polynomial K] FractionRing (Polynomial K)):=
   IsLocalization.algHom_subsingleton (nonZeroDivisors (Polynomial K))
 have h:=Subsingleton.elim
   (RatFunc.toFractionRingAlgEquiv K (Polynomial K)).toAlgHom
   (FractionRing.algEquiv (Polynomial K) (RatFunc K)).symm.toAlgHom
 exact DFunLike.congr_fun h x
theorem finiteOrder_eq_specifiedOrder
   (p:Polynomial K) (hp:Irreducible p) (x:RatFunc K):
   RatFuncProductFormula.finiteOrder K p hp x=
     fieldOrder (Polynomial K) (RatFunc K) (RatFuncProductFormula.primePlace K p hp) x:=by
 rw [RatFuncProductFormula.finiteOrder,asFraction_eq_canonical K]
 exact (fieldOrder_transport (Polynomial K) (RatFunc K)
   (RatFuncProductFormula.primePlace K p hp) x).symm
theorem finitePrimeContribution_eq_normOrder
   (p:Polynomial K) (hp:Irreducible p) (x:L) (hx:x≠0):
   (∑ P∈(IsDedekindDomain.primesOverFinset
       (RatFuncProductFormula.primePlace K p hp).asIdeal (FiniteNormalization K L)).attach,
     (P.1.inertiaDeg (Polynomial K):ℤ)*
       fieldOrder (FiniteNormalization K L) L
         (placeAbove (Polynomial K) (FiniteNormalization K L)
           (RatFuncProductFormula.primePlace K p hp) P) x)=
     RatFuncProductFormula.finiteOrder K p hp (Algebra.norm (RatFunc K) x):=by
 have h:=fieldOrder_norm (Polynomial K) (FiniteNormalization K L) (RatFunc K) L
   (RatFuncProductFormula.primePlace K p hp) x hx
 rw [←finiteOrder_eq_specifiedOrder K p hp] at h
 exact h.symm
def finiteContribution (s:Finset (Polynomial K))
   (hs:∀ p∈s,Irreducible p∧p.Monic) (x:L):ℤ:=
 ∑ p∈s.attach,(p.1.natDegree:ℤ)*
   ∑ P∈(IsDedekindDomain.primesOverFinset
       (RatFuncProductFormula.primePlace K p.1 (hs p.1 p.2).1).asIdeal
       (FiniteNormalization K L)).attach,
     (P.1.inertiaDeg (Polynomial K):ℤ)*
       fieldOrder (FiniteNormalization K L) L
         (placeAbove (Polynomial K) (FiniteNormalization K L)
           (RatFuncProductFormula.primePlace K p.1 (hs p.1 p.2).1) P) x
theorem finiteContribution_eq_normOrders
   (s:Finset (Polynomial K)) (hs:∀ p∈s,Irreducible p∧p.Monic)
   (x:L) (hx:x≠0):
   finiteContribution K L s hs x=
     ∑ p∈s.attach,(p.1.natDegree:ℤ)*
       RatFuncProductFormula.finiteOrder K p.1 (hs p.1 p.2).1
         (Algebra.norm (RatFunc K) x):=by
 unfold finiteContribution
 apply Finset.sum_congr rfl
 intro p _
 rw [finitePrimeContribution_eq_normOrder K L p.1 (hs p.1 p.2).1 x hx]
theorem balanced_fiber_sum
   (s:Finset (Polynomial K)) (hs:∀ p∈s,Irreducible p∧p.Monic)
   (x:L) (hx:x≠0)
   (hnum:(UniqueFactorizationMonoid.normalizedFactors
     (Algebra.norm (RatFunc K) x).num).toFinset ⊆ s)
   (hden:(UniqueFactorizationMonoid.normalizedFactors
     (Algebra.norm (RatFunc K) x).denom).toFinset ⊆ s):
   finiteContribution K L s hs x+infinityContribution K L x=0:=by
 have hnorm:Algebra.norm (RatFunc K) x≠0:=Algebra.norm_ne_zero_iff.mpr hx
 rw [finiteContribution_eq_normOrders K L s hs x hx,
   infinityContribution_eq_normOrder K L x hx,
   RatFuncProductFormula.weighted_finite_order_sum K _ hnorm s hs hnum hden,
   RatFuncProductFormula.infinityOrder_eq_neg_intDegree K _ hnorm,
   add_neg_cancel]
theorem finite_orders_support_finite (x:L) (hx:x≠0):
   Function.HasFiniteSupport
     (fun w:HeightOneSpectrum (FiniteNormalization K L)↦
       fieldOrder (FiniteNormalization K L) L w x):=by
 obtain ⟨a,b,hb,rfl⟩:=
   IsFractionRing.div_surjective (A:=FiniteNormalization K L) x
 have hbzero:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hb
 have hazero:a≠0:=by
   intro ha
   apply hx
   simp [ha]
 have hspanA:(Ideal.span {a}:Ideal (FiniteNormalization K L))≠0:=by
   simpa using hazero
 have hspanB:(Ideal.span {b}:Ideal (FiniteNormalization K L))≠0:=by
   simpa using hbzero
 have hA:{w:HeightOneSpectrum (FiniteNormalization K L) |
     w.asIdeal∣Ideal.span {a}}.Finite:=Ideal.finite_factors hspanA
 have hB:{w:HeightOneSpectrum (FiniteNormalization K L) |
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
def finiteOrderSupport (x:L) (hx:x≠0):
   Finset (HeightOneSpectrum (FiniteNormalization K L)):=
 (finite_orders_support_finite K L x hx).toFinset
theorem mem_finiteOrderSupport (x:L) (hx:x≠0)
   (w:HeightOneSpectrum (FiniteNormalization K L)):
   w∈finiteOrderSupport K L x hx ↔
     fieldOrder (FiniteNormalization K L) L w x≠0:=by
 simp [finiteOrderSupport]
def baseRepresentative (w:HeightOneSpectrum (FiniteNormalization K L)):Polynomial K:=
 (RatFuncProductFormula.exists_monic_primePlace K
   (HeightOneSpectrum.under (Polynomial K) w)).choose
theorem baseRepresentative_spec (w:HeightOneSpectrum (FiniteNormalization K L)):
   ∃ hp:Irreducible (baseRepresentative K L w),
     (baseRepresentative K L w).Monic∧
       RatFuncProductFormula.primePlace K (baseRepresentative K L w) hp=
         HeightOneSpectrum.under (Polynomial K) w:=
 (RatFuncProductFormula.exists_monic_primePlace K
   (HeightOneSpectrum.under (Polynomial K) w)).choose_spec
def basePrimesFor (x:L) (hx:x≠0):Finset (Polynomial K):=
 (finiteOrderSupport K L x hx).image (baseRepresentative K L) ∪
   RatFuncProductFormula.factorSupport K (Algebra.norm (RatFunc K) x)
theorem basePrimesFor_primes (x:L) (hx:x≠0)
   (p:Polynomial K) (hp:p∈basePrimesFor K L x hx):Irreducible p∧p.Monic:=by
 rcases Finset.mem_union.mp hp with hleft | hright
 · obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hleft
   obtain ⟨hp,hm,_⟩:=baseRepresentative_spec K L w
   exact ⟨hp,hm⟩
 · exact RatFuncProductFormula.factorSupport_primes K _
     (Algebra.norm_ne_zero_iff.mpr hx) p hright
theorem basePrimesFor_covers (x:L) (hx:x≠0)
   (w:HeightOneSpectrum (FiniteNormalization K L))
   (hw:fieldOrder (FiniteNormalization K L) L w x≠0):
   ∃ p∈basePrimesFor K L x hx,∃ hp:Irreducible p,
     w.asIdeal∈IsDedekindDomain.primesOverFinset
       (RatFuncProductFormula.primePlace K p hp).asIdeal (FiniteNormalization K L):=by
 obtain ⟨hp,hm,hplace⟩:=baseRepresentative_spec K L w
 refine ⟨baseRepresentative K L w,
   Finset.mem_union_left _ (Finset.mem_image.mpr
     ⟨w,(mem_finiteOrderSupport K L x hx w).mpr hw,rfl⟩),hp,?_⟩
 rw [hplace]
 letI:w.asIdeal.LiesOver (HeightOneSpectrum.under (Polynomial K) w).asIdeal:=by
   change w.asIdeal.LiesOver (w.asIdeal.under (Polynomial K))
   infer_instance
 exact (IsDedekindDomain.mem_primesOverFinset_iff
   (HeightOneSpectrum.under (Polynomial K) w).ne_bot (FiniteNormalization K L)).mpr
     ⟨w.isPrime,inferInstance⟩
theorem projective_curve_order_sum (x:L) (hx:x≠0):
   finiteContribution K L (basePrimesFor K L x hx)
     (basePrimesFor_primes K L x hx) x+infinityContribution K L x=0:=by
 apply balanced_fiber_sum K L (basePrimesFor K L x hx)
   (basePrimesFor_primes K L x hx) x hx
 · intro p hp
   exact Finset.mem_union_right _ (Finset.mem_union_left _ hp)
 · intro p hp
   exact Finset.mem_union_right _ (Finset.mem_union_right _ hp)
end
end ProximityPrize.SubmissionLower.FixedCurveNormSum
