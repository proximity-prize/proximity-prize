import ProximityPrize.SubmissionLower.R6970Height2313Rescue
import ProximityPrize.SubmissionLower.Z6969Pack0427

set_option Elab.async false
set_option autoImplicit true

namespace Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2 (ODECaps mass)
open P1_7_4 (ODEGuard)
open _root_.Lower6960.Far6969RescueGeometry (Model Family)
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)
open Research6970.Height2313.Lower6960.Prefix6969Rates (fixedFee fixed_count)
open scoped Classical BigOperators

noncomputable section

private abbrev rateLambda := Band.lambda .near
private abbrev rateMu := Band.mu .near

def rankBase (plan : Plan) : ℚ :=
  4 * rateLambda * rankB plan * rankJ plan - 2 * rateLambda * (rankJ plan : ℚ)^2 +
    rateMu * rankJ plan + (rankB plan : ℚ)^2 + 1

def rankTransfer (plan : Plan) : ℚ :=
  4 * rateLambda * rankB plan - 2 * rateLambda * rankJ plan

private theorem rank_chord {L μ B₀ J₀ B J s : ℚ}
    (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hs : 0 ≤ s)
    (hb : B+s ≤ B₀) (hj : J+s ≤ J₀) (hbox : J₀ ≤ B₀) :
    4*L*B*J - 2*L*J^2 + μ*J + B^2 + 1 + (4*L*B₀-2*L*J₀)*s ≤
      4*L*B₀*J₀ - 2*L*J₀^2 + μ*J₀ + B₀^2 + 1 := by
  have h1 := mul_nonneg (mul_nonneg (show 0 ≤ 4*L by positivity) hJ)
    (show 0 ≤ B₀-s-B by linarith only [hb])
  have h2 := mul_nonneg (mul_nonneg (show 0 ≤ 2*L by positivity)
    (show 0 ≤ J₀-s-J by linarith only [hj]))
    (show 0 ≤ 2*(B₀-s)-(J₀-s)-J by linarith only [hbox,hj])
  have h3 := mul_nonneg (mul_nonneg (show 0 ≤ 2*L by positivity) hs)
    (show 0 ≤ J₀-s by linarith only [hJ,hj])
  have h4 := mul_nonneg hμ (show 0 ≤ J₀-J by linarith only [hj,hs])
  have h5 := mul_nonneg (show 0 ≤ B₀-B by linarith only [hb,hs])
    (show 0 ≤ B₀+B by linarith only [hb,hs,hB])
  nlinarith only [h1,h2,h3,h4,h5]

variable {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}

theorem rank_count_transfer (R : Run F Crt G plan) (hi : M.overhead.toNat ≤ 2313)
    (box : rankJ plan ≤ rankB plan) (small : rankB plan < p) :
    ((rankMarks R).card : ℚ) + rankTransfer plan * (mass R.initial.parents 1 : ℚ) ≤
      rankBase plan := by
  let S := R.initial.rankExit
  let s := mass R.initial.parents 1
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  have merged (k : Fin 4) : mass S k + mass R.initial.parents k ≤ plan.initialCap k := by
    have eq : mass (S ∪ R.initial.parents) k = mass S k + mass R.initial.parents k :=
      sum_union R.initial.disjoint
    rw [← eq]
    exact R.initial.fits k
  have mixed : s ≤ mass R.initial.parents 2 :=
    _root_.Research6969.MixedSectionCredit.mass_le _ (fun I h => (R.initial.parent_geom I h).1)
  have hBm : B ≤ mass S 2 + 2 := max_le (by omega) (by omega)
  have hJm : J ≤ mass S 1 + 1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B+s ≤ rankB plan := by
    unfold rankB
    have h := merged 2
    omega
  have hJ : J+s ≤ rankJ plan := by
    unfold rankJ
    have h := merged 1
    omega
  have hJB : J ≤ B := max_le (by omega) (min_le_right _ _)
  obtain ⟨E, caps, roots⟩ := R.initial.rank_ode
  have degree : E.natDegree ≤ B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1, (le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  have guard : ODEGuard B J := ⟨le_max_left _ _, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _),
    hJB, ((Nat.le_add_right B s).trans hB).trans_lt small⟩
  have count : (rankMarks R).card ≤ fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ hγ => roots γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
  have hL : 0 ≤ rateLambda := by decide +kernel
  have hμ : 0 ≤ rateMu := by decide +kernel
  have lin := HighCore82268JointRank.fixed_fee_linear rateLambda rateMu 1 (J : ℚ)
    hL hμ (by norm_num) le_rfl hJB (le_refl B) (le_refl J)
  have fee : (fixedFee B J : ℚ) ≤ 4*rateLambda*B*J - 2*rateLambda*(J : ℚ)^2 + rateMu*J + (B : ℚ)^2 + 1 := by
    change ((Band.fixedFee .near B J : ℕ) : ℚ) ≤ _
    rw [Band.fixedFee_eq .near B J]
    unfold P1_7_4_3.mix
    dsimp only at lin
    linarith only [lin]
  have bound := rank_chord (B₀ := (rankB plan : ℚ)) (J₀ := (rankJ plan : ℚ)) hL hμ (Nat.cast_nonneg B) (Nat.cast_nonneg J) (Nat.cast_nonneg s)
    (by exact_mod_cast hB) (by exact_mod_cast hJ) (by exact_mod_cast box)
  unfold rankTransfer rankBase
  exact (add_le_add ((Nat.cast_le.mpr count).trans fee) le_rfl).trans bound

end
end Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice
