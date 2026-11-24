import ProximityPrize.SubmissionLower.HighCore82258Family
import ProximityPrize.SubmissionLower.UpperBranch4

set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 2000000

namespace HighCore82258PrefixHelpers
noncomputable section

open Polynomial
open P1 (K I node p)
open HighCore82258 (AnchorModel AnchoredFamily)
open K1_14 (Shape Jet Seeds jetAt seedEmbedding graphEval)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing ODE fixedAt)
open K1_14_2_2 (Active RowCaps CutCover sectionDegree weight dot joinCuts joinCuts_cost
  sum_dot emptyCut mass CurveGeometry ODECaps)
open K1_14_2_2_3 K1_14_2_2_7
open K1_14_2_3 (SeedSlice seedImage seedLength)
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (totalCap topCap)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq)
open K1_14_2_2_7 (seed_value_eq)
open K1_14_2_3 (on_seed seed_graph_count)
open scoped BigOperators Classical
open Finset

def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)


def curveMarks {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ) (C : CutCover) :
    Finset K := C.curves.biUnion fun I => Γ.filter (OnParent F I)

theorem section_bound {w : I → K} {T : Finset K} {s : K → (Polynomial K)} {d a v : ℕ}
    (hw : HighCore82258.FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc



end
end HighCore82258PrefixHelpers
