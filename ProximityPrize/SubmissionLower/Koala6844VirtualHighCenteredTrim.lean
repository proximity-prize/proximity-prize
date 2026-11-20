import ProximityPrize.SubmissionLower.Koala6844VirtualCRTCoordinates
import ProximityPrize.SubmissionLower.Koala6844VirtualHighAxes
import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantBridge


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
open Koala6831Intrinsic Koala6844Normalization Koala6844VirtualCRT RCN313
open Polynomial

noncomputable section

set_option maxHeartbeats 2500000

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

structure CenteredTrimCarrier (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (first plain : ℕ) where
  V : Carrier K
  W : Carrier K
  invariant : InvariantTrim V W first plain
  divisor_caps : V.degreeOf 1 ≤ 0 ∧ V.degreeOf 2 ≤ 0 ∧ V.degreeOf 3 ≤ 0
  trim_caps : W.degreeOf 1 ≤ 1 ∧ W.degreeOf 2 ≤ 10000 ∧ W.degreeOf 3 ≤ 10000
  scale : K → K
  reduced : K → Polynomial K
  scale_ne : ∀ g ∈ data.seeds, scale g ≠ 0
  denom_spec : ∀ g ∈ data.seeds,
    graphSpecialize (data.normalized g) g (σ g) invariant.denominator = C (scale g)
  divisor_spec : ∀ g : K, graphSpecialize (data.normalized g) g (σ g) V = data.d0 * data.d1
  trim_spec : ∀ g ∈ data.seeds,
    graphSpecialize (data.normalized g) g (σ g) W =
      C (scale g) * graphSpecialize (data.normalized g) g (σ g) V * reduced g
  reduced_degree : ∀ g ∈ data.seeds, (reduced g).natDegree ≤ first

theorem exists_centered_trim_carrier
    (data : CenteredVirtualData x nodes σ w agreement errors excess) (first plain : ℕ)
    (hD : data.d0.natDegree ≤ 10000)
    (hfirst : w-(data.d0.natDegree+affineDegree data.A0) ≤ first)
    (hplain : first+2*data.d0.natDegree ≤ plain) :
    Nonempty (CenteredTrimCarrier data first plain) := by
  obtain ⟨Δ₀, Δ₁, N₀, B₀, N₁, B₁, hΔ₀, hΔ₁, hB₀, hB₁, lift⟩ := centered_cleared_crt data
  let D := data.d0 * data.d1
  let V := atAxis 0 D
  let S := axesProduct 1 Δ₀ Δ₁
  let theta : Carrier K :=
    (∑ i, axesProduct (B₀ i) (N₀ i) Δ₁) + (∑ i, axesProduct (B₁ i) Δ₀ (N₁ i))
  let W := S * MvPolynomial.X 1 - theta
  let scale (g : K) := Δ₀.eval g * Δ₁.eval (σ g)
  let reduced (g : K) := data.normalized g / D
  have hDdegree : D.natDegree = 2*data.d0.natDegree := by
    dsimp only [D]
    rw [Polynomial.natDegree_mul data.d0_ne data.d1_ne, data.degree_content]
    omega
  have hΔ₀' := hΔ₀.trans hD
  have hΔ₁' := hΔ₁.trans (data.degree_content.trans_le hD)
  have hV : V.degreeOf 1 ≤ 0 ∧ V.degreeOf 2 ≤ 0 ∧ V.degreeOf 3 ≤ 0 := by
    exact ⟨atAxis_degree 0 1 D, atAxis_degree 0 2 D, atAxis_degree 0 3 D⟩
  have vX : V.degreeOf 0 ≤ 2*data.d0.natDegree :=
    (show V.degreeOf 0 ≤ D.natDegree from atAxis_degree 0 0 D).trans_eq hDdegree
  have sDegree (j : Fin 4) : S.degreeOf j ≤ ![0,0,10000,10000] j := by
    have h := axesProduct_degree (1 : Polynomial K) Δ₀ Δ₁ j
    exact h.trans (by fin_cases j <;> simp [hΔ₀', hΔ₁'])
  have thetaDegree (j : Fin 4) : theta.degreeOf j ≤ ![2*data.d0.natDegree,0,10000,10000] j := by
    have haxis (A B C : Polynomial K) (hA : A.natDegree ≤ 2*data.d0.natDegree)
        (hB : B.natDegree ≤ 10000) (hC : C.natDegree ≤ 10000) :
        (axesProduct A B C).degreeOf j ≤ ![2*data.d0.natDegree,0,10000,10000] j := by
      apply (axesProduct_degree A B C j).trans
      fin_cases j
      · exact hA
      · exact le_rfl
      · exact hB
      · exact hC
    unfold theta
    apply degree_add_bound j
    · apply (MvPolynomial.degreeOf_sum_le j _ _).trans
      apply Finset.sup_le
      intro i _
      exact haxis _ _ _ ((Polynomial.natDegree_le_natDegree (hB₀ i).2.le).trans_eq hDdegree)
        ((hB₀ i).1.trans hD) hΔ₁'
    · apply (MvPolynomial.degreeOf_sum_le j _ _).trans
      apply Finset.sup_le
      intro i _
      exact haxis _ _ _ ((Polynomial.natDegree_le_natDegree (hB₁ i).2.le).trans_eq hDdegree)
        hΔ₀' ((hB₁ i).1.trans (data.degree_content.trans_le hD))
  have wDegree : W.degreeOf 1 ≤ 1 ∧ W.degreeOf 2 ≤ 10000 ∧ W.degreeOf 3 ≤ 10000 := by
    have bound (j : Fin 4) (d : ℕ)
        (hS : S.degreeOf j + (MvPolynomial.X (1 : Fin 4) : Carrier K).degreeOf j ≤ d)
        (ht : theta.degreeOf j ≤ d) : W.degreeOf j ≤ d := by
      apply degree_sub_bound j
      · exact (MvPolynomial.degreeOf_mul_le j _ _).trans hS
      · exact ht
    refine ⟨bound 1 1 ?_ ((show theta.degreeOf 1 ≤ 0 from thetaDegree 1).trans (by omega)),
      bound 2 10000 ?_ (thetaDegree 2), bound 3 10000 ?_ (thetaDegree 3)⟩
    all_goals
      simp only [MvPolynomial.degreeOf_X]
    · exact Nat.add_le_add_right (sDegree 1) _
    · simpa using sDegree 2
    · simpa using sDegree 3
  let H : InvariantTrim V W first plain :=
    { denominator := S, remainder := theta, divisorDegree := 2*data.d0.natDegree,
      shape := rfl, denominator_X := sDegree 0, denominator_Y := sDegree 1,
      divisor_Y := hV.1, remainder_Y := thetaDegree 1,
      divisor_X := vX, remainder_X := thetaDegree 0, enlargedDegree := hplain }
  have hscale (g : K) (hg : g ∈ data.seeds) : scale g ≠ 0 :=
    mul_ne_zero (lift g hg).1 (lift g hg).2.1
  have hS (g : K) : graphSpecialize (data.normalized g) g (σ g) S = C (scale g) := by
    change graphSpecialize (data.normalized g) g (σ g) (axesProduct 1 Δ₀ Δ₁) = _
    rw [graphSpecialize_axesProduct, mul_one]
  have hV' (g : K) : graphSpecialize (data.normalized g) g (σ g) V = D := by
    change graphSpecialize (data.normalized g) g (σ g) (atAxis 0 D) = D
    rw [graphSpecialize_atAxis]
    exact Polynomial.eval₂_C_X
  refine ⟨{
    V := V
    W := W
    invariant := H
    divisor_caps := hV
    trim_caps := wDegree
    scale := scale
    reduced := reduced
    scale_ne := hscale
    denom_spec := fun g _ => hS g
    divisor_spec := hV'
    trim_spec := ?_
    reduced_degree := ?_ }⟩
  · intro g hg
    have htheta : graphSpecialize (data.normalized g) g (σ g) theta =
        C (scale g) * (data.normalized g % D) := by
      simp only [theta, map_add, map_sum, graphSpecialize_axesProduct]
      have eq := (lift g hg).2.2.symm
      simpa only [Polynomial.smul_eq_C_mul, scale, D, mul_comm] using eq
    have yEval : graphSpecialize (data.normalized g) g (σ g)
        (MvPolynomial.X 1) = data.normalized g := by simp [graphSpecialize]
    change graphSpecialize (data.normalized g) g (σ g) (S * MvPolynomial.X 1 - theta) =
      C (scale g) * graphSpecialize (data.normalized g) g (σ g) V * reduced g
    rw [map_sub, map_mul, hS, yEval, htheta, hV']
    have split := (centered_trim data g hg).1
    change data.normalized g = data.normalized g % D + D * reduced g at split
    conv_lhs => lhs; rhs; rw [split]
    ring
  · intro g hg
    exact (centered_trim data g hg).2.2.2.2.trans hfirst

theorem exists_uniform_centered_trim_carrier
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {agreement errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ 131071 agreement errors excess)
    (hD : data.d0.natDegree ≤ 10000)
    (high : 6681 ≤ data.d0.natDegree + affineDegree data.A0) :
    Nonempty (CenteredTrimCarrier data 124396 144396) :=
  exists_centered_trim_carrier data 124396 144396 hD (by omega) (by omega)

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
