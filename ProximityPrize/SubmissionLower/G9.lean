import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.X4
import ProximityPrize.SubmissionLower.X5
namespace ProximityPrize.SubmissionLower.ActualCurveProjectionBounds
open ActualCurveCoordinateField ActualCurveRationalProjection
 TrivariateRationalCollection ActualPlaneCoordinateKernel
 ActualPlaneCoordinateCaps ActualPlanePositiveOrder ActualPlaneCoordinateDegree
noncomputable section
variable (K:Type) [Field K]
theorem rationalBaseAlgebra_congr (P:Ideal (Original K)) [P.IsPrime]
   (i j:Fin 3) (hij:i=j)
   (hi:Transcendental K (coordinate K P i))
   (hj:Transcendental K (coordinate K P j)):
   rationalBaseAlgebra K P i hi=rationalBaseAlgebra K P j hj:=by
 subst j
 rfl
private def singleSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)) (B:ℕ):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
   Module.finrank (RatFunc K) (CoordinateField K P) ≤ B
private def fieldsSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
private def familySummary {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem plane_budget_le_original (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
     (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H) ≤
       originalMixedDegree K order G H:=
 Nat.add_le_add
   (Nat.mul_le_mul (planeMap_natDegree_le K order H) (planeMap_degreeX_le K order G))
   (Nat.mul_le_mul (planeMap_natDegree_le K order G) (planeMap_degreeX_le K order H))
section Single
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
variable (ht:Transcendental K (coordinate K P (order 0)))
theorem original_finite_separable_finrank_bound
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤ originalMixedDegree K order G H:=by
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
   exists_positive_characteristic_order K order P G H p hG hGmem ht h1 h2 hmixed
 have ht':Transcendental K (coordinate K P (order' 0)):=by
   simpa only [hbase] using ht
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order' 0) ht'
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
       Module.finrank (RatFunc K) (CoordinateField K P) ≤ originalMixedDegree K order' G H:=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order' 0) ht'
   obtain ⟨hfd,hsep,hbound⟩:=actual_finite_separable_finrank_bound
     K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
   exact ⟨hfd,hsep,hbound.trans (plane_budget_le_original K order' G H)⟩
 change singleSummary K P (rationalBaseAlgebra K P (order' 0) ht')
   (originalMixedDegree K order' G H) at hresult
 rw [rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht,hbudget] at hresult
 exact hresult
end Single
section Family
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
variable (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem original_finite_separable_sum_finrank_bound
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       originalMixedDegree K order G H:=by
 classical
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
     exists_positive_characteristic_order K order (P i₀) G H p
       hG (hGmem i₀) (ht i₀) h1 h2 hmixed
   have ht':∀ i,Transcendental K (coordinate K (P i) (order' 0)):=by
     intro i
     simpa only [hbase] using ht i
   have hresult:
       letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
         fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
       (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
         Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
         (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
           originalMixedDegree K order' G H:=by
     letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
       fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
     obtain ⟨hfields,hbound⟩:=actual_finite_separable_sum_finrank_bound
       K order' P ht' hinj p G H hG hGmem hHmem hproper hpos houter hres
     exact ⟨hfields,hbound.trans (plane_budget_le_original K order' G H)⟩
   have halg:(fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
       (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
     funext i
     exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0) hbase (ht' i) (ht i)
   change familySummary K P (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
     (originalMixedDegree K order' G H) at hresult
   rw [halg,hbudget] at hresult
   exact hresult
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end Family
theorem all_transcendental_coordinates_finite_separable
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:∀ j k:Fin 3,j≠k →
     H.degreeOf j*G.degreeOf k+G.degreeOf j*H.degreeOf k < p):
   ∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 intro i hi
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hneq:order 1≠order 2:=by
   intro h
   have heq:=order.injective h
   exact (by decide:(1:Fin 3)≠2) heq
 have hbudget:originalMixedDegree K order G H < p:=
   hmixed (order 1) (order 2) hneq
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   have h:=original_finite_separable_finrank_bound K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hbudget
   exact ⟨h.1,h.2.1⟩
 change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
 rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
end
end ProximityPrize.SubmissionLower.ActualCurveProjectionBounds
