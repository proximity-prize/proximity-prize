import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AV
import ProximityPrize.SubmissionLower.AY
namespace ProximityPrize.SubmissionLower.RCN003
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
 RCN004 RCN007 RCN001
open RCN012
noncomputable section
variable (K:Type) [Field K]
def JointOrderCertificate (order:Fin 3 ≃ Fin 3)
   (G H:Original K) (p:ℕ):Prop:=
 ∃ order':Fin 3 ≃ Fin 3,
   order' 0=order 0∧
   originalMixedDegree K order' G H=originalMixedDegree K order G H∧
   0 < (planeMap K order' G).natDegree∧
   (planeMap K order' G).natDegree < p∧
   (Polynomial.resultant (planeMap K order' G)
     (planeMap K order' H)).natDegree < p
theorem jointOrderCertificate_of_projection_data
   (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
   (G T:Original K) (p n mCap totalG totalT cap gOuter tInner:ℕ)
   (hG:Irreducible G) (hGmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0)))
   (hTne:T≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hTouter:(planeMap K order T).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hTsupport:∀ d∈(rationalMap K order T).support,
     d 0+d 1 ≤ totalT)
   (hGswapOuter:(planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
   (hTswapInner:Polynomial.Bivariate.degreeX
     (planeMap K (swapOtherOrder order) T) ≤ tInner)
   (hnp:n < p) (hgOuterP:gOuter < p)
   (hcapP:cap < p) (hswapP:gOuter*tInner < p)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalT-m*n ≤ cap):
   JointOrderCertificate K order G T p:=by
 obtain ⟨order',_hor,hbase,hmixed,hpos,houter,hres⟩:=
   exists_positive_joint_characteristic_order K order P G T p n mCap
     totalG totalT cap gOuter tInner hG hGmem ht hTne hGouter hTouter
     hGsupport hTsupport hGswapOuter hTswapInner hnp hgOuterP hcapP
     hswapP hbudget
 exact ⟨order',hbase,hmixed,hpos,houter,hres⟩
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
private def familySummary {I:Type} [Fintype I]
   (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem finite_separable_finrank_bound_of_joint_certificate
   (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
   (ht:Transcendental K (coordinate K P (order 0)))
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P)
   (hproper:¬ G∣H)
   (hcertificate:JointOrderCertificate K order G H p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤
       originalMixedDegree K order G H:=by
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=hcertificate
 have ht':Transcendental K (coordinate K P (order' 0)):=by
   simpa only [hbase] using ht
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P (order' 0) ht'
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
       Module.finrank (RatFunc K) (CoordinateField K P) ≤
         originalMixedDegree K order' G H:=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P (order' 0) ht'
   obtain ⟨hfd,hsep,hbound⟩:=actual_finite_separable_finrank_bound
     K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
   exact ⟨hfd,hsep,hbound.trans (plane_budget_le_original K order' G H)⟩
 change singleSummary K P (rationalBaseAlgebra K P (order' 0) ht')
   (originalMixedDegree K order' G H) at hresult
 rw [rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht,
   hbudget] at hresult
 exact hresult
theorem finite_separable_sum_finrank_bound_of_joint_certificate
   (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
   (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p]
   (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hcertificate:JointOrderCertificate K order G H p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       originalMixedDegree K order G H:=by
 classical
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=hcertificate
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
 have halg:
     (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
       (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
   funext i
   exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0)
     hbase (ht' i) (ht i)
 change familySummary K P
   (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
     (originalMixedDegree K order' G H) at hresult
 rw [halg,hbudget] at hresult
 exact hresult
theorem sum_actualCoordinateDegree_le_of_joint_certificate
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (order:Fin 3 ≃ Fin 3)
   (hinj:Function.Injective P) (p:ℕ) [CharP K p]
   (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hcertificate:JointOrderCertificate K order G H p):
   (∑ i,actualCoordinateDegree K (P i) (order 0)) ≤
     originalMixedDegree K order G H:=by
 classical
 let s:Set I:={i | Transcendental K (coordinate K (P i) (order 0))}
 let D:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (CoordinateField K (P i)):=
     rationalBaseAlgebra K (P i) (order 0) i.2
   Module.finrank (RatFunc K) (CoordinateField K (P i))
 have hinj':Function.Injective (fun i:s => P i):=by
   intro i j h
   apply Subtype.ext
   exact hinj h
 have hbound:(∑ i:s,D i) ≤ originalMixedDegree K order G H:=by
   have h:=finite_separable_sum_finrank_bound_of_joint_certificate
     K order (fun i:s => P i) (fun i => i.2) hinj' p G H hG
     (fun i => hGmem i) (fun i => hHmem i) hproper hcertificate
   exact h.2
 calc
   _=∑ i:s,D i:=by
     apply Finset.sum_congr_set s
       (fun i => actualCoordinateDegree K (P i) (order 0)) D
     · intro i hi
       exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
     · intro i hi
       change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
       exact dif_neg hi
   _ ≤ _:=hbound
theorem finite_separable_at_of_original_coordinate_gate
   (P:Ideal (Original K)) [P.IsPrime] (i:Fin 3)
   (hi:Transcendental K (coordinate K P i))
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P)
   (hproper:¬ G∣H) (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:coordinateMixedDegree K G H i < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P (order 0) ht
   have h:=original_finite_separable_finrank_bound K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hmixed
   exact ⟨h.1,h.2.1⟩
 change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
 change fieldsSummary K P (rationalBaseAlgebra K P i hi)
 rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
theorem projectionsFiniteSeparable_of_joint_R
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p]
   (G H:Original K) (hG:Irreducible G)
   (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree K G H 0 < p)
   (hmixedZ:coordinateMixedDegree K G H 2 < p)
   (hjoint:JointOrderCertificate K (Equiv.swap 0 1) G H p):
   ProjectionsFiniteSeparable K P:=by
 intro i hi
 by_cases hiR:i=(1:Fin 3)
 · subst i
   have ht:Transcendental K
       (coordinate K P ((Equiv.swap (0:Fin 3) 1) 0)):=by
     have hbase:(Equiv.swap (0:Fin 3) 1) 0=(1:Fin 3):=by decide
     rw [hbase]
     exact hi
   have h:=finite_separable_finrank_bound_of_joint_certificate K
     (Equiv.swap (0:Fin 3) 1) P ht p G H hG hGmem hHmem hproper hjoint
   exact ⟨h.1,h.2.1⟩
 · have hother:i=(0:Fin 3)∨i=(2:Fin 3):=by
     fin_cases i <;> simp_all
   rcases hother with rfl | rfl
   · exact finite_separable_at_of_original_coordinate_gate K P 0 hi p G H
       hG hGmem hHmem hproper hdegree hmixedY
   · exact finite_separable_at_of_original_coordinate_gate K P 2 hi p G H
       hG hGmem hHmem hproper hdegree hmixedZ
theorem projectionsFiniteSeparable_of_joint_R_provider
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p]
   (G H:Original K) (hG:Irreducible G)
   (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree K G H 0 < p)
   (hmixedZ:coordinateMixedDegree K G H 2 < p)
   (hjoint:Transcendental K (coordinate K P 1) →
     JointOrderCertificate K (Equiv.swap 0 1) G H p):
   ProjectionsFiniteSeparable K P:=by
 intro i hi
 by_cases hiR:i=(1:Fin 3)
 · subst i
   exact projectionsFiniteSeparable_of_joint_R K P p G H hG hGmem hHmem
     hproper hdegree hmixedY hmixedZ (hjoint hi) 1 hi
 · have hother:i=(0:Fin 3)∨i=(2:Fin 3):=by
     fin_cases i <;> simp_all
   rcases hother with rfl | rfl
   · exact finite_separable_at_of_original_coordinate_gate K P 0 hi p G H
       hG hGmem hHmem hproper hdegree hmixedY
   · exact finite_separable_at_of_original_coordinate_gate K P 2 hi p G H
       hG hGmem hHmem hproper hdegree hmixedZ
theorem sum_actualCoordinateDegree_at_R_le_of_joint_certificate
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hjoint:JointOrderCertificate K (Equiv.swap 0 1) G H p):
   (∑ i,actualCoordinateDegree K (P i) 1) ≤
     coordinateMixedDegree K G H 1:=by
 simpa only [coordinateMixedDegree,Equiv.swap_apply_left] using
   (sum_actualCoordinateDegree_le_of_joint_certificate K P
     (Equiv.swap (0:Fin 3) 1) hinj p G H hG hGmem hHmem hproper hjoint)
theorem sum_actualCoordinateDegree_at_R_le_of_joint_provider
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hjoint:∀ i,Transcendental K (coordinate K (P i) 1) →
     JointOrderCertificate K (Equiv.swap 0 1) G H p):
   (∑ i,actualCoordinateDegree K (P i) 1) ≤
     coordinateMixedDegree K G H 1:=by
 classical
 let s:Set I:={i | Transcendental K (coordinate K (P i) 1)}
 let D:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (CoordinateField K (P i)):=
     rationalBaseAlgebra K (P i) 1 i.2
   Module.finrank (RatFunc K) (CoordinateField K (P i))
 have hrewrite:(∑ i,actualCoordinateDegree K (P i) 1)=∑ i:s,D i:=by
   apply Finset.sum_congr_set s
     (fun i => actualCoordinateDegree K (P i) 1) D
   · intro i hi
     exact actualCoordinateDegree_of_transcendental K (P i) 1 hi
   · intro i hi
     change ¬ Transcendental K (coordinate K (P i) 1) at hi
     exact dif_neg hi
 rw [hrewrite]
 by_cases hs:Nonempty s
 · let i₀:s:=Classical.choice hs
   have hcert:=hjoint i₀ i₀.2
   have hinj':Function.Injective (fun i:s => P i):=by
     intro i j h
     apply Subtype.ext
     exact hinj h
   have hbound:=finite_separable_sum_finrank_bound_of_joint_certificate K
     (Equiv.swap (0:Fin 3) 1) (fun i:s => P i)
     (fun i => by
       have hbase:(Equiv.swap (0:Fin 3) 1) 0=(1:Fin 3):=by decide
       rw [hbase]
       exact i.2)
     hinj' p G H hG (fun i => hGmem i) (fun i => hHmem i)
     hproper hcert
   have hbound':=hbound.2
   change (∑ i:s,D i) ≤
     originalMixedDegree K (Equiv.swap (0:Fin 3) 1) G H at hbound'
   simpa only [coordinateMixedDegree,Equiv.swap_apply_left] using hbound'
 · letI:IsEmpty s:=⟨fun i => hs ⟨i⟩⟩
   simp
theorem sum_actualCoordinateDegree_at_le_of_joint_R
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H) (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree K G H 0 < p)
   (hmixedZ:coordinateMixedDegree K G H 2 < p)
   (hjoint:JointOrderCertificate K (Equiv.swap 0 1) G H p):
   ∀ j,(∑ i,actualCoordinateDegree K (P i) j) ≤
     coordinateMixedDegree K G H j:=by
 intro j
 fin_cases j
 · exact sum_actualCoordinateDegree_at_le K P hinj 0 p G H hG hGmem hHmem
     hproper hdegree hmixedY
 · exact sum_actualCoordinateDegree_at_R_le_of_joint_certificate K P hinj p
     G H hG hGmem hHmem hproper hjoint
 · exact sum_actualCoordinateDegree_at_le K P hinj 2 p G H hG hGmem hHmem
     hproper hdegree hmixedZ
theorem sum_actualCoordinateDegree_at_le_of_joint_R_provider
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H) (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree K G H 0 < p)
   (hmixedZ:coordinateMixedDegree K G H 2 < p)
   (hjoint:∀ i,Transcendental K (coordinate K (P i) 1) →
     JointOrderCertificate K (Equiv.swap 0 1) G H p):
   ∀ j,(∑ i,actualCoordinateDegree K (P i) j) ≤
     coordinateMixedDegree K G H j:=by
 intro j
 fin_cases j
 · exact sum_actualCoordinateDegree_at_le K P hinj 0 p G H hG hGmem hHmem
     hproper hdegree hmixedY
 · exact sum_actualCoordinateDegree_at_R_le_of_joint_provider K P hinj p
     G H hG hGmem hHmem hproper hjoint
 · exact sum_actualCoordinateDegree_at_le K P hinj 2 p G H hG hGmem hHmem
     hproper hdegree hmixedZ
end
end ProximityPrize.SubmissionLower.RCN003
