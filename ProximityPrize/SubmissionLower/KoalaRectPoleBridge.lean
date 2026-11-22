import ProximityPrize.SubmissionLower.KoalaRectSource
import ProximityPrize.SubmissionLower.KoalaRectPole

set_option autoImplicit false

namespace KoalaRect

open K1 (I)
open K1_14 (L Shape)
open K1_14_1 (CRTLift PoleData)
open P1_7_1 (groupedPoleMoment poleRows)

theorem rectPole_bound {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (hs : s.B < K1.p) (W : ℕ)
    (U : Fin 2 → ℕ) :
    Module.finrank L (rectContacted h word s W U) ≤
      2*h * poleRows s * area U + h * (U 0 + U 1 + 2) * groupedPoleMoment s.B s.J +
        Module.finrank L (rectComplete Crt word s W U) :=
  KoalaRectPole.pole_bound hpos hchar Crt word s hs W U (seedSupport U) (fun _ hp => hp)

#print axioms rectPole_bound

end KoalaRect
