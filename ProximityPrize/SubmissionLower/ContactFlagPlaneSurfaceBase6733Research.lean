import ProximityPrize.SubmissionLower.ContactFlagPlaneFiberBase6733Research
namespace ProximityPrize.SubmissionLower.ContactFlagPlaneFiberSurface6733Research
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open ArbitraryPlaneEvaluationFamilyResearch ContactRegularComponentCover
open ContactFlagTriangularProjectionResearch ContactFlagAffineFamilyDegree6543Research
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
theorem transformedSurface_irreducible
    (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
    (hG:Irreducible G)
    (C:RegularComponent Omega G T H)
    (htC:Transcendental Omega
      (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
    Irreducible (planeMap Omega order (flagAlgHom lam mu nu G)):=by
  let e:=flagEvaluation Omega C.1 lam mu nu
  have hroot:e (flagAlgHom lam mu nu G)=0:=by
    rw [flagEvaluation_flag]
    change G∈RingHom.ker (coordinateEvaluation Omega C.1).toRingHom
    rw [coordinateEvaluation_ker]
    exact regularComponent_G_mem Omega G T H C
  exact planeMap_irreducible_of_evaluation Omega (CoordinateField Omega C.1)
    order e (flagAlgHom lam mu nu G)
      ((flag_irreducible_iff lam mu nu G).mpr hG) hroot htC
theorem transformedSurface_not_dvd_tail
    (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
    (hG:Irreducible G) (hproper:¬ G∣T)
    (C:RegularComponent Omega G T H)
    (htC:Transcendental Omega
      (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
    ¬ planeMap Omega order (flagAlgHom lam mu nu G)∣
      planeMap Omega order (flagAlgHom lam mu nu T):=by
  let e:=flagEvaluation Omega C.1 lam mu nu
  have hroot:e (flagAlgHom lam mu nu G)=0:=by
    rw [flagEvaluation_flag]
    change G∈RingHom.ker (coordinateEvaluation Omega C.1).toRingHom
    rw [coordinateEvaluation_ker]
    exact regularComponent_G_mem Omega G T H C
  intro hdiv
  have hflagDvd:=(planeMap_dvd_iff_of_evaluation Omega
    (CoordinateField Omega C.1) order e
      (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
      ((flag_irreducible_iff lam mu nu G).mpr hG) hroot htC).mp hdiv
  exact hproper ((flag_dvd_iff lam mu nu G T).mp hflagDvd)
end
end ProximityPrize.SubmissionLower.ContactFlagPlaneFiberSurface6733Research
