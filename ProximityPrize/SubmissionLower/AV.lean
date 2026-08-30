import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.G9
import ProximityPrize.SubmissionLower.M
namespace ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum
open ActualCurveCoordinateField ActualCurveRationalProjection
 TrivariateRationalCollection ActualCurveZeroCount ActualPlanePositiveOrder
 ActualCurveProjectionBounds
noncomputable section
variable (K:Type) [Field K]
section Family
variable {I:Type} [Fintype I] (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem sum_actualCoordinateDegree_le_original
   (order:Fin 3 ≃ Fin 3) (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   (∑ i,actualCoordinateDegree K (P i) (order 0)) ≤ originalMixedDegree K order G H:=by
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
   have h:=original_finite_separable_sum_finrank_bound K order (fun i:s => P i)
     (fun i => i.2) hinj' p G H hG (fun i => hGmem i) (fun i => hHmem i)
     hproper h1 h2 hmixed
   exact h.2
 calc
   _=∑ i:s,D i:=by
     apply Finset.sum_congr_set s (fun i => actualCoordinateDegree K (P i) (order 0)) D
     · intro i hi
       exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
     · intro i hi
       change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
       exact dif_neg hi
   _ ≤ _:=hbound
theorem weighted_sum_actualCoordinateDegree_le (weight bound:Fin 3 → ℕ)
   (hbound:∀ j,(∑ i,actualCoordinateDegree K (P i) j) ≤ bound j):
   (∑ i,∑ j,weight j*actualCoordinateDegree K (P i) j) ≤
     ∑ j,weight j*bound j:=by
 rw [Finset.sum_comm]
 apply Finset.sum_le_sum
 intro j _
 rw [←Finset.mul_sum]
 exact Nat.mul_le_mul_left (weight j) (hbound j)
end Family
def coordinateMixedDegree (G H:Original K) (i:Fin 3):ℕ:=
 originalMixedDegree K (Equiv.swap 0 i) G H
@[simp] theorem coordinateMixedDegree_zero (G H:Original K):
   coordinateMixedDegree K G H 0=
     H.degreeOf 1*G.degreeOf 2+G.degreeOf 1*H.degreeOf 2:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def]
@[simp] theorem coordinateMixedDegree_one (G H:Original K):
   coordinateMixedDegree K G H 1=
     H.degreeOf 0*G.degreeOf 2+G.degreeOf 0*H.degreeOf 2:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def]
@[simp] theorem coordinateMixedDegree_two (G H:Original K):
   coordinateMixedDegree K G H 2=
     H.degreeOf 0*G.degreeOf 1+G.degreeOf 0*H.degreeOf 1:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def] <;> ring
theorem sum_actualCoordinateDegree_at_le
   {I:Type} [Fintype I] (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (hinj:Function.Injective P) (j:Fin 3) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H) (hdegree:∀ k:Fin 3,G.degreeOf k < p)
   (hmixed:coordinateMixedDegree K G H j < p):
   (∑ i,actualCoordinateDegree K (P i) j) ≤ coordinateMixedDegree K G H j:=by
 have h:=sum_actualCoordinateDegree_le_original K P (Equiv.swap 0 j) hinj p G H
   hG hGmem hHmem hproper (hdegree ((Equiv.swap 0 j) 1))
     (hdegree ((Equiv.swap 0 j) 2)) hmixed
 simpa only [coordinateMixedDegree,Equiv.swap_apply_left] using h
theorem projectionsFiniteSeparable_of_original_gates
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:∀ j k:Fin 3,j≠k →
     H.degreeOf j*G.degreeOf k+G.degreeOf j*H.degreeOf k < p):
   ProjectionsFiniteSeparable K P:=
 all_transcendental_coordinates_finite_separable K P p G H
   hG hGmem hHmem hproper hdegree hmixed
end
end ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum
