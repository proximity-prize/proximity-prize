import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingProjectionDegree6676Research
namespace ProximityPrize.SubmissionLower.ContactDerivativeRegularity6719Research
open ContactMovingProjectionDegree6676Research
noncomputable section
set_option autoImplicit false
variable {K E:Type} [Field K] [Field E]
local notation "Poly" => MvPolynomial (Fin 3) K
theorem derivative_eq_mem_span (F H:Poly)
    (h:H=MvPolynomial.pderiv (1:Fin 3) F):
    H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly):=by
  rw [h]
  exact Ideal.subset_span (by simp)
theorem pderiv_mem_span_of_mul (F U Q:Poly) (hQ:Q=F*U):
    MvPolynomial.pderiv (1:Fin 3) Q∈
      Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly):=by
  apply Ideal.mem_span_pair.mpr
  refine ⟨MvPolynomial.pderiv (1:Fin 3) U,U,?_⟩
  rw [hQ,MvPolynomial.pderiv_mul]
  ring
theorem pderiv_mem_span_of_dvd (F Q:Poly) (hFQ:F∣Q):
    MvPolynomial.pderiv (1:Fin 3) Q∈
      Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly):=by
  obtain ⟨U,hU⟩:=hFQ
  exact pderiv_mem_span_of_mul F U Q hU
theorem map_derivative_span (φ:K →+*E) (F H:Poly)
    (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly)):
    MvPolynomial.map φ H∈Ideal.span
      ({MvPolynomial.map φ F,
        MvPolynomial.pderiv (1:Fin 3) (MvPolynomial.map φ F)}:
          Set (MvPolynomial (Fin 3) E)):=by
  obtain ⟨A,B,hAB⟩:=Ideal.mem_span_pair.mp h
  apply Ideal.mem_span_pair.mpr
  refine ⟨MvPolynomial.map φ A,MvPolynomial.map φ B,?_⟩
  rw [MvPolynomial.pderiv_map]
  simpa only [map_add,map_mul] using congrArg (MvPolynomial.map φ) hAB
theorem scalar_derivative_span [Algebra K E] (F H:Poly)
    (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly)):
    scalarPolynomialMap K E H∈Ideal.span
      ({scalarPolynomialMap K E F,
        MvPolynomial.pderiv (1:Fin 3) (scalarPolynomialMap K E F)}:
          Set (MvPolynomial (Fin 3) E)):=
  map_derivative_span (algebraMap K E) F H h
theorem map_pderiv_ne_zero_of_mem_span (ev:Poly →+*E) (F H:Poly)
    (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
    (hF:ev F=0) (hH:ev H≠0):
    ev (MvPolynomial.pderiv (1:Fin 3) F)≠0:=by
  intro hD
  obtain ⟨A,B,hAB⟩:=Ideal.mem_span_pair.mp h
  apply hH
  rw [←hAB,map_add,map_mul,map_mul,hF,hD]
  ring
end
end ProximityPrize.SubmissionLower.ContactDerivativeRegularity6719Research
