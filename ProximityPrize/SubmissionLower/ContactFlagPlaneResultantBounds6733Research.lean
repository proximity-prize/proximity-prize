import ProximityPrize.SubmissionLower.ContactFlagPlaneSurfaceBase6733Research
import ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps6543Research
import ProximityPrize.SubmissionLower.ContactFlagSymbolicTrapezoidResearch
namespace ProximityPrize.SubmissionLower.ContactFlagPlaneResultantBounds6733Research
open ContactFlagBezout6543Research ContactFlagTriangularProjectionResearch
open ContactFlagAffineFamilyDegree6543Research ContactFlagTrapezoidCaps6543Research
open ContactFlagSymbolicTrapezoidResearch ContactFlagPlaneFiberSurface6733Research
open ActualPlaneJointProjection ActualPlaneCoordinateKernel
open ContactRegularComponentCover
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
local instance:DecidableEq (RatFunc Omega):=Classical.decEq _
variable {G T H:MvPolynomial (Fin 3) Omega}
def flagPlaneResultant (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
    (G T:MvPolynomial (Fin 3) Omega):Polynomial (RatFunc Omega):=
  let P:=planeMap Omega order (flagAlgHom lam mu nu G)
  let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
  Polynomial.resultant P Q P.natDegree Q.natDegree
theorem flagPlaneResultant_ne
    (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
    (hG:Irreducible G) (hproper:¬ G∣T)
    (C:RegularComponent Omega G T H)
    (ht:Transcendental Omega
      (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hpositive:0 < (planeMap Omega order (flagAlgHom lam mu nu G)).natDegree):
    flagPlaneResultant lam mu nu order G T≠0:=by
  exact PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
    (planeMap Omega order (flagAlgHom lam mu nu G))
    (planeMap Omega order (flagAlgHom lam mu nu T))
    (transformedSurface_irreducible lam mu nu order hG C ht) hpositive
    (transformedSurface_not_dvd_tail lam mu nu order hG hproper C ht)
theorem flagPlaneResultant_z_degree_le
    (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
    (hGsupport:G.support ⊆ flagSupport surfaceFlag)
    (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
    (flagPlaneResultant lam mu nu zOrder G T).natDegree ≤
      flagMixed surfaceFlag tailFlag unitZFlag:=by
  let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
  let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
  change (Polynomial.resultant
    (planeMap Omega zOrder (flagAlgHom lam mu nu G))
    (planeMap Omega zOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
  exact planeMap_trapezoid_resultant_natDegree_le Omega zOrder
    (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
    surfaceFlag.all tailFlag.all (surfaceFlag.yz+surfaceFlag.all)
    (tailFlag.yz+tailFlag.all) (flagMixed surfaceFlag tailFlag unitZFlag)
    (flag_ne_zero lam mu nu hTne) gCaps.zOuter tCaps.zOuter
    gCaps.zTotal tCaps.zTotal (z_flag_trapezoid_budget surfaceFlag tailFlag)
theorem flagPlaneResultant_u_degree_le
    (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
    (hGsupport:G.support ⊆ flagSupport surfaceFlag)
    (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
    (flagPlaneResultant lam mu nu uOrder G T).natDegree ≤
      flagMixed surfaceFlag tailFlag unitYZFlag:=by
  let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
  let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
  change (Polynomial.resultant
    (planeMap Omega uOrder (flagAlgHom lam mu nu G))
    (planeMap Omega uOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
  exact planeMap_trapezoid_resultant_natDegree_le Omega uOrder
    (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
    surfaceFlag.all tailFlag.all
    (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
    (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
    (flagMixed surfaceFlag tailFlag unitYZFlag)
    (flag_ne_zero lam mu nu hTne) gCaps.uOuter tCaps.uOuter
    gCaps.uTotal tCaps.uTotal (u_flag_trapezoid_budget surfaceFlag tailFlag)
theorem flagPlaneResultant_v_degree_le
    (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
    (hGsupport:G.support ⊆ flagSupport surfaceFlag)
    (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
    (flagPlaneResultant lam mu nu vOrder G T).natDegree ≤
      flagMixed surfaceFlag tailFlag unitAllFlag:=by
  let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
  let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
  change (Polynomial.resultant
    (planeMap Omega vOrder (flagAlgHom lam mu nu G))
    (planeMap Omega vOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
  exact planeMap_trapezoid_resultant_natDegree_le Omega vOrder
    (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
    (surfaceFlag.yz+surfaceFlag.all) (tailFlag.yz+tailFlag.all)
    (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
    (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
    (flagMixed surfaceFlag tailFlag unitAllFlag)
    (flag_ne_zero lam mu nu hTne) gCaps.vOuter tCaps.vOuter
    gCaps.vTotal tCaps.vTotal (v_flag_trapezoid_budget surfaceFlag tailFlag)
end
end ProximityPrize.SubmissionLower.ContactFlagPlaneResultantBounds6733Research
