import ProximityPrize.SubmissionLower.Rect52RegularAssembly
import ProximityPrize.SubmissionLower.Rect51Proper

namespace Rect52Regular

theorem properCount : ProperCounter :=
  Rect51Proper.count

open Polynomial
open P1 (I K p)
open High52 (AnchorModel AnchoredFamily degreeAt)
open K1_14 (L Equation atMark)
open Rect51Tangent (Axes)

theorem count_roots_rect_actual
    {u : P1.Words} {del : Finset I} {Γ : Finset K} {lo hi h : ℕ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hw : Window M lo hi h)
    (hshift : M.shift ∉ Γ) {H : L[X]} (hH : Chart h M F H) {f : Equation}
    (hf : High52.Reduced f) (he : 4 ≤ f.natDegree)
    {v : Axes} (hv : Rect51Tangent.SeedBound f v)
    (hsep : High52.singularDegree f.natDegree (seedSum v) < p)
    (hflat : f.natDegree * degreeAt hi + seedSum v < p)
    (T : Finset K) (hT : T ⊆ Γ)
    (roots : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) :
    T.card ≤ wholeFee lo hi f.natDegree v :=
  count_roots_rect properCount M F hw hshift hH hf he hv hsep hflat T hT roots

#print axioms count_roots_rect_actual

#print axioms properCount
end Rect52Regular
