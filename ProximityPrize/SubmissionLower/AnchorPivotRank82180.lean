import ProximityPrize.SubmissionLower.AnchorPivotFactors82180

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

namespace AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder orderCutoff bandCount bandSpace_finite finrank_bandSpace)
open MvPolynomial
open scoped BigOperators

abbrev Factor := Fin 8 × ℕ

structure Row where
  tag : ℕ
  index : ℕ
  ord : ℕ
  e : E
  factors : List Factor
  deriving DecidableEq




theorem independent {V ι : Type} [AddCommGroup V] [Module Geom V] [Fintype ι]
    (f : V →ₗ[Geom] Polynomial Geom) (v : ι → V) (tag : ι → ℕ) (inj : Function.Injective tag)
    (hdeg : ∀ i, (f (v i)).degree = (tag i : ℕ)) : LinearIndependent Geom v := by
  classical
  refine (Fintype.linearIndependent_iff (v := v)).mpr ?_
  intro w hw j
  by_contra hj
  let a := Finset.univ.filter fun i => w i ≠ 0
  obtain ⟨i,hi,hiMax⟩ := a.exists_max_image tag
    ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  have hwi := (Finset.mem_filter.mp hi).2
  let t := (Polynomial.lcoeff Geom (tag i)).comp f
  have hz := congrArg t hw
  simp only [map_sum,map_smul,map_zero] at hz
  rw [Finset.sum_eq_single i] at hz
  · change w i * (f (v i)).coeff (tag i) = 0 at hz
    have hn : f (v i) ≠ 0 := fun h => by simpa [h] using hdeg i
    have hd := Polynomial.natDegree_eq_of_degree_eq_some (hdeg i)
    rw [← hd,Polynomial.coeff_natDegree] at hz
    exact (mul_ne_zero hwi (Polynomial.leadingCoeff_ne_zero.mpr hn)) hz
  · intro b _ hbi
    by_cases hb : w b = 0
    · simp [hb]
    · have lt : tag b < tag i := lt_of_le_of_ne
        (hiMax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)) (fun e => hbi (inj e))
      change w b * (f (v b)).coeff (tag i) = 0
      rw [Polynomial.coeff_eq_zero_of_degree_lt (by rw [hdeg]; exact WithBot.coe_lt_coe.mpr lt),mul_zero]
  · simp


end AnchorPivot82180
