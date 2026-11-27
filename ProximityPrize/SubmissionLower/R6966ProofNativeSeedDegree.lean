import ProximityPrize.SubmissionLower.Z6969Pack0096
import ProximityPrize.SubmissionLower.Fast069

set_option Elab.async false

namespace Research6966.NativeSeedDegree
open Polynomial Finset
open K1_14 (FX Seeds Equation)
open K1_14_2 (Ambient toJet generic SeedField)
open K1_14_2_2 (Active sectionDegree mass)
open K1_14_3 (ProjectedProduct Surface)
open K1_14_2_3_2 (genericSeedLineMap genericSeedLine_degree)
open NativeSeedSlice (B Lift z back backBase scalar parameters send)
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

def seed : Seeds →+* B[X] :=
  MvPolynomial.eval₂Hom (C.comp MvPolynomial.C)
    ![(C (MvPolynomial.X 2)-C (MvPolynomial.X 0)*Polynomial.X (R:=B) : B[X]),Polynomial.X (R:=B)]
def native : Equation →+* B[X] := eval₂RingHom seed (C (MvPolynomial.X 3))
def forward : Lift →+* B[X] := MvPolynomial.eval₂Hom native ![C (MvPolynomial.X 0),C (MvPolynomial.X 1)]

theorem inverse (f:B[X]) : forward (back f)=f := by
  have eq : forward.comp back=RingHom.id _ := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [forward,back,backBase,scalar,native,seed]
      · intro i
        fin_cases i <;> simp [forward,back,backBase,parameters,z,native,seed]
    · simp [forward,back,z,native,seed]
  exact DFunLike.congr_fun eq f

private def spec (v:FX) : B →+* SeedField :=
  MvPolynomial.eval₂Hom (algebraMap FX SeedField)
    ![generic 0,0,generic 1,algebraMap FX SeedField v]

private theorem line (v:FX) (H:Equation) :
    (native H).map (spec v)=genericSeedLineMap (H.eval (MvPolynomial.C v)) := by
  have eq : (mapRingHom (spec v)).comp native=
      genericSeedLineMap.comp (evalRingHom (MvPolynomial.C v)) := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [native,seed,spec]
      · intro i
        fin_cases i <;> simp [native,seed,spec]
    · simp [native,spec]
  exact DFunLike.congr_fun eq H

private def column (H:Equation) (m:Fin 2→₀ℕ) : FX[X] :=
  ∑ j∈H.support, monomial j ((H.coeff j).coeff m)

private theorem column_coeff (H:Equation) (m:Fin 2→₀ℕ) (i:ℕ) :
    (column H m).coeff i=(H.coeff i).coeff m := by
  classical
  by_cases hi:i∈H.support
  · simp [column,finsetSum_coeff,coeff_monomial,Finsupp.single_apply,hi]
  · have hz:H.coeff i=0:=by simpa using hi
    simp [column,finsetSum_coeff,coeff_monomial,Finsupp.single_apply,hi,hz]

private theorem column_eval (H:Equation) (m:Fin 2→₀ℕ) (v:FX) :
    (column H m).eval v=(H.eval (MvPolynomial.C v)).coeff m := by
  rw [column,eval_finsetSum]
  conv_rhs => rw [eval_eq_sum,Polynomial.sum]
  rw [MvPolynomial.coeff_sum]
  apply sum_congr rfl
  intro i _
  rw [eval_monomial,←map_pow,mul_comm (H.coeff i),MvPolynomial.coeff_C_mul,mul_comm]

theorem coeff_degree (H:Equation) (i:ℕ) : (H.coeff i).totalDegree≤(native H).natDegree := by
  classical
  letI : Infinite FX := Infinite.of_injective (algebraMap (Polynomial K1_14.L) FX)
    (IsFractionRing.injective (Polynomial K1_14.L) FX)
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro m hm
  have cn:column H m≠0:=by
    intro eq
    have hz:=column_coeff H m i
    rw [eq,coeff_zero] at hz
    exact (MvPolynomial.mem_support_iff.mp hm) hz.symm
  obtain ⟨v,hv⟩ : ∃ v:FX,(column H m).eval v≠0 := by
    by_contra! all
    exact cn (Polynomial.funext (by intro x; simpa using all x))
  have mem:m∈(H.eval (MvPolynomial.C v)).support :=
    MvPolynomial.mem_support_iff.mpr ((column_eval H m v) ▸ hv)
  have ne:H.eval (MvPolynomial.C v)≠0:=by intro eq;simpa [eq] using mem
  apply (MvPolynomial.le_totalDegree mem).trans
  rw [←genericSeedLine_degree _ ne,←line]
  exact natDegree_map_le


/-- Seed mass of the squarefree projection on any subset of the terminal
parents. The annihilator's numerator survives clearing on the generic
ordinate section, including when a particular localized ring is zero. -/
theorem projected_seed {parents:Finset Surface} {H:Equation} (proj:ProjectedProduct parents H)
    (sources:Finset (Ideal Ambient)) (active:∀ J∈sources,Active J)
    (origins:∀ q∈parents,∃ J∈sources,q.asIdeal=J.comap toJet) (i:ℕ) :
    (H.coeff i).totalDegree≤mass sources 1 := by
  classical
  obtain ⟨D,dn,deg,mult⟩:=NativeSeedSlice.common_relation proj sources active origins
  have div := map_dvd forward mult
  rw [inverse] at div
  have eq:forward (MvPolynomial.C H)=native H:=by simp [forward]
  rw [eq] at div
  exact (coeff_degree H i).trans ((natDegree_le_of_dvd div dn).trans deg)

end
end Research6966.NativeSeedDegree
