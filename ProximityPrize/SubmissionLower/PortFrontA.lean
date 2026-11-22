import ProximityPrize.SubmissionLower.PortBase
set_option autoImplicit true
section
set_option maxRecDepth 12000
namespace P0_4
noncomputable section
open Polynomial P0
private theorem threeUAt_eq (q : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    threeUAt q a β = K1_8.threeUAt q a β := by
  delta threeUAt K1_8.threeUAt P0.liftX K1.liftX P0.seed K1.seed P0.twist K1.twist P0.p K1.p
    P0.Bivar K1.Bivar P0.K K1.K
  rfl
private theorem relationOnAt_eq (q : ℕ) (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOnAt q u S U V W = K1_8.relationOnAt q u S U V W := by
  delta relationOnAt K1_8.relationOnAt P0.node K1.node P0.Words K1.Words P0.I K1.I
    P0.Bivar K1.Bivar P0.K K1.K
  rfl
private theorem columnRankAt_eq (q : ℕ) (U V : Bivar) :
    columnRankAt q U V = K1_8.columnRankAt q U V := by
  delta columnRankAt K1_8.columnRankAt P0.seed K1.seed P0.extendSeed K1.extendSeed
    P0.Bivar K1.Bivar P0.Frac K1.Frac P0.K K1.K
  rfl
open private K1_8.threeUAt_native from ProximityPrize.SubmissionLower.Fast068
private theorem native_threeU :
    threeUAt P0.p = (P0.threeU : K[X] → (Fin 2 → K[X]) → Bivar) := by
  unfold threeUAt P0.threeU
  rfl
theorem threeU_eq (a : K[X]) (β : Fin 2 → K[X]) :
    P0.threeU a β = K1.threeU a β := by
  calc
    P0.threeU a β = threeUAt P0.p a β := congrFun (congrFun native_threeU.symm a) β
    _ = K1_8.threeUAt P0.p a β := threeUAt_eq P0.p a β
    _ = K1_8.threeUAt K1.p a β := congrArg (fun q => K1_8.threeUAt q a β) (show P0.p = K1.p from rfl)
    _ = K1.threeU a β := congrFun (congrFun K1_8.threeUAt_native a) β
theorem relationOn_eq (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOn u S U V W = K1_8.relationOnAt K1.p u S U V W := by
  calc
    _ = relationOnAt P0.p u S U V W := by delta P0.relationOn relationOnAt; rfl
    _ = K1_8.relationOnAt P0.p u S U V W := relationOnAt_eq P0.p u S U V W
    _ = K1_8.relationOnAt K1.p u S U V W :=
      congrArg (fun q => K1_8.relationOnAt q u S U V W) (show P0.p = K1.p from rfl)
theorem columnRank_eq (U V : Bivar) : columnRank U V = K1.columnRank U V := by
  calc
    _ = columnRankAt P0.p U V := by delta P0.columnRank columnRankAt; rfl
    _ = K1_8.columnRankAt P0.p U V := columnRankAt_eq P0.p U V
    _ = K1_8.columnRankAt K1.p U V := congrArg (fun q => K1_8.columnRankAt q U V) (show P0.p = K1.p from rfl)
    _ = _ := by delta K1_8.columnRankAt K1.columnRank; rfl
end
end P0_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P0_4
noncomputable section
open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective extendSeedHom AmplitudeDirection)
open private transfer_at from ProximityPrize.SubmissionLower.Fast068
open private threeU_height threeV_height common_multiplier multiplier_degree_zero
  seed_scalar_coeff descend_scalar proportional_amplitudes rescale_threeU from ProximityPrize.SubmissionLower.Fast068
private theorem sameDirection_eq (U V P Q : Bivar) :
    sameDirection U V P Q = K1.sameDirection U V P Q := by
  delta P0.sameDirection K1.sameDirection
  rfl
private theorem threeV_eq (b : K[X]) (α : Fin 2 → K[X]) :
    threeV b α = K1.threeV b α := by
  delta P0.threeV K1.threeV P0.liftX K1.liftX P0.seed K1.seed
  rfl
end
end P0_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace P0_5
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k amplitudeDegree)
open K1_9 (K I node twist pencil fold pencil_degree
  seedCoeff crossValue CoefficientIdentities sixNorm_mul sixNorm_ne_zero)
open private seedCoeff_degree from ProximityPrize.SubmissionLower.Fast068
abbrev heightBound : ℕ := 32781
structure PolarData (u : Words) where
  a : K[X]
  b : K[X]
  A : Fin 2 → K[X]
  Q : K → K → K[X]
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  b_bound : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  Q_degree : ∀ r s, (Q r s).degree < (k + heightBound : ℕ)
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)
private theorem pow_eq_twist (z : K) : z ^ P0.p = twist z :=
  (frobenius_def P0.p z).symm
private theorem threeUAt_native : threeUAt P0.p = P0.threeU := by
  unfold threeUAt P0.threeU
  rfl
private theorem relationOnAt_native : relationOnAt P0.p = P0.relationOn := by
  unfold relationOnAt P0.relationOn
  rfl
private theorem coefficientsAt (q : ℕ) (hq : 1 < q) (hσ : ∀ z : K, z ^ q = twist z)
    (u : Words) (deleted : Finset I) (a b : K[X]) (A B : Fin 2 → K[X])
    (output : P0.Bivar) (hp : A = B)
    (hn : relationOnAt q u deleted (threeUAt q a B) (P0.threeV b A) output)
    (i : I) (hi : i ∉ deleted) :
    (seedCoeff output 0).eval (node i) = crossValue u a b A i 0 0 ∧
    (seedCoeff output 1).eval (node i) = crossValue u a b A i 0 1 ∧
    (seedCoeff output q).eval (node i) = crossValue u a b A i 1 0 ∧
    (seedCoeff output (q + 1)).eval (node i) = crossValue u a b A i 1 1 := by
  subst B
  exact K1_9.coefficients_at_node u a b A i q hq hσ output (threeUAt q a A)
    (K1_9.eval_first a A i q) (hn i hi).symm
end
end P0_5
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P0_7
open P0 Finset
open K1_11 (V J)
private def countRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (s + 1 - i) * (t + 1 - j)
private def gradeRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (i + j) * ((s + 1 - i) * (t + 1 - j))
private def count (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), countRow B s t i
private def grade (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), gradeRow B s t i
private def contactRow (m s t i : ℕ) : ℕ :=
  ∑ j ∈ range (m - i), (m - i - j) * (s + 1 - i) * (t + 1 - j)
private theorem V_affine (D w B s t : ℕ) (hB : w * B ≤ D + 1) :
    V D w B s t + w * grade B s t = (D + 1) * count B s t := by
  unfold V count grade countRow gradeRow
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hij : i + j ≤ B := by
    simp only [mem_range] at hi hj
    omega
  have hw := (Nat.mul_le_mul_left w hij).trans hB
  calc
    _ = ((D + 1 - w * (i + j)) + w * (i + j)) * ((s + 1 - i) * (t + 1 - j)) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hw]
private theorem rational_fee (E M exceptionFee limit a b : ℕ) (hb : 0 < b)
    (h : exceptionFee * b^2 + 5 * E * (a*M)^2 ≤ limit * b^2) :
    (exceptionFee : ℚ) + 5 * ((E : ℚ) * (((a : ℚ) / b) * M)^2) ≤ limit := by
  have hb' : 0 < (b : ℚ) := by exact_mod_cast hb
  have h' : (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 ≤
      (limit : ℚ) * (b : ℚ)^2 := by exact_mod_cast h
  refine le_of_mul_le_mul_right ?_ (pow_pos hb' 2)
  calc
    _ = (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 := by
      field_simp
    _ ≤ _ := h'
end P0_7
end
