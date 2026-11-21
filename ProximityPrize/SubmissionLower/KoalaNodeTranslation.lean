import ProximityPrize.SubmissionLower.KoalaStableNode
import Mathlib.Algebra.Polynomial.Taylor

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SplitCut.StableNode
noncomputable section
open Polynomial

/-- Translate the abscissa to the node and the ordinate to its word value. -/
def translate {R : Type*} [CommRing R] (x w : R) (G : Polynomial R[X]) : Polynomial R[X] :=
  taylor (C x) (G.map (taylorAlgHom w).toRingHom)

theorem map_translate {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (x w : R) (G : Polynomial R[X]) :
    (translate x w G).map (mapRingHom φ) = translate (φ x) (φ w) (G.map (mapRingHom φ)) := by
  unfold translate
  rw [map_taylor, coe_mapRingHom, map_C, map_map, map_map]
  congr 1
  apply congrArg (fun h : R[X] →+* A[X] => G.map h)
  apply RingHom.ext
  intro P
  change (taylor w P).map φ = taylor (φ w) (P.map φ)
  exact map_taylor _ _ _

theorem translate_ne_zero {R : Type*} [CommRing R] (x w : R) {G : Polynomial R[X]}
    (hG : G ≠ 0) : translate x w G ≠ 0 := by
  unfold translate
  intro hz
  have h := (taylorEquiv (C x)).injective (hz.trans (map_zero (taylorEquiv (C x))).symm)
  exact hG ((map_injective _ (taylorEquiv w).injective) (h.trans (Polynomial.map_zero _).symm))

theorem substitute_translate {A : Type*} [CommRing A] (x w : A) (G : Polynomial A[X]) (S : A[X]) :
    substitute (taylor x S - C w) (translate x w G) = taylor x (substitute S G) := by
  let L := eval₂RingHom C (taylor x S - C w)
  let M := eval₂RingHom C S
  let τ := (taylorAlgHom x).toRingHom
  have hmap : L.comp (taylorAlgHom w).toRingHom = τ.comp M := by
    apply RingHom.ext
    intro Q
    change (taylor w Q).comp (taylor x S - C w) = taylor x (Q.comp S)
    rw [taylor_apply w, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel,
      taylor_apply x, taylor_apply x, comp_assoc]
  change (translate x w G).eval₂ L (Polynomial.X : A[X]) = τ (G.eval₂ M (Polynomial.X : A[X]))
  rw [translate, taylor_apply, eval₂_comp, eval₂_add, eval₂_X, eval₂_C, eval₂_map, hmap, hom_eval₂]
  change G.eval₂ _ (Polynomial.X + (C x : A[X]).eval₂ C (taylor x S-C w)) =
    G.eval₂ _ (taylor x Polynomial.X)
  rw [eval₂_C, taylor_X]

/-- If an exact reconstructed polynomial is a generic root, then a single
    translated coefficient cuts the hits at each nonpersistent node. -/
theorem translated_coefficient {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    (φ : R →+* A) (G : Polynomial R[X]) (S : A[X]) (x w : R)
    (hG : G.map (mapRingHom φ) ≠ 0) (hroot : substitute S (G.map (mapRingHom φ)) = 0)
    (hfail : S.eval (φ x) ≠ φ w) :
    ∃ i j : ℕ, φ (((translate x w G).coeff i).coeff j) ≠ 0 ∧
      ∀ {E : Type*} [CommRing E] (ψ : A →+* E), ψ (S.eval (φ x)) = ψ (φ w) →
        ψ (φ (((translate x w G).coeff i).coeff j)) = 0 := by
  let s := taylor (φ x) S - C (φ w)
  have hs : s.eval 0 = S.eval (φ x) - φ w := by simp [s, taylor_eval]
  have hz : substitute s ((translate x w G).map (mapRingHom φ)) = 0 := by
    rw [map_translate, substitute_translate, hroot, map_zero]
  obtain ⟨i,j,hij,hj⟩ := separating_coefficient φ (translate x w G) s
    (by rw [map_translate]; exact translate_ne_zero _ _ hG) hz
    (by rw [hs]; exact sub_ne_zero.mpr hfail)
  exact ⟨i,j,hij,fun ψ h => hj ψ (by rw [hs, map_sub, h, sub_self])⟩

end
end SplitCut.StableNode

#print axioms SplitCut.StableNode.translated_coefficient
