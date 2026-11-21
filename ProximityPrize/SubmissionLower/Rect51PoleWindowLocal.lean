import ProximityPrize.SubmissionLower.Rect51PoleWindow

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Rect51PoleWindow
noncomputable section

open Polynomial Matrix
open K1_14 (Shape)
open K1_14_1 (otherBlock jetConstant)
open K1_14_1_7 K1_14_1_7_2
open P1_7_1 (poleRows groupedPoleMoment columnCount)
open P1_7_1_1
open scoped BigOperators Polynomial

/-- The grouped CRT tests preserve a rectangular window in the inactive seed. -/
theorem local_tests (F : Type) [Field F] (s : Shape) (u : Fin 2 → ℕ)
    (H : F[X]) (lift : (SeedFrac F)[X])
    (α : F) (side : Fin 2) (a b c : F)
    (hH : H.eval α = 0) (hb : b ≠ 0)
    (hz : lift.eval (algebraMap F (SeedFrac F) α) = residue side a b c) :
    ∃ d : Fin (poleRows s) → ℕ, (∑ r, d r) ≤ groupedPoleMoment s.B s.J ∧
      ∃ tests : Fin (poleRows s) → TrueSource F →ₗ[F] Seed F,
        (∀ r P, RectShaped s u P → Window u (d r) side (tests r P)) ∧
        ∀ P, RectShaped s u P → (∀ r, tests r P = 0) →
          (jetConstant ((Polynomial.X (R := SeedFrac F) -
            Polynomial.C (algebraMap F (SeedFrac F) α)) ^ (s.B+s.J)) :
            JetPolys (SeedFrac F)) ∣ forward H lift P := by
  classical
  have hRows (t : Offset s) :=
    P1_7_1_1_2.proof F (Pivot s t) (Column s t) _ _ (bounded_pole_minors F s t a b c hb)
  choose Q L d hL hdeg hsum using hRows
  let tests (t : Offset s) (r : Pivot s t) := polynomialTest α side (Q t r)
  let e := rowIndex s
  refine ⟨fun k => d (e k).1 (e k).2, rowIndex_sum s d hsum,
    fun k => tests (e k).1 (e k).2, ?_, ?_⟩
  · intro k P hP
    exact polynomial_window α side _ (hdeg _ _) hP
  · intro P hP hzero
    have ht (t : Offset s) (r : Pivot s t) : tests t r P = 0 := by
      let testAt (k : Σ t : Offset s, Pivot s t) := tests k.1 k.2 P
      have hk : testAt (e (e.symm ⟨t, r⟩)) = 0 := hzero (e.symm ⟨t, r⟩)
      rw [e.apply_symm_apply] at hk
      exact hk
    let z := residue side a b c
    have hslots := P1_7_1_1_1.proof F s α z
      (fun t q => pascal_spans (SeedFrac F) (firstJet s t)
        (columnCount s.B s.J t.val q.val) (outputLength s t q)) P hP.1
      (fun t => polynomialTests_to_poleMatrix t α side a b c P (Q t) (L t) (hL t) (ht t))
    have hd := K1_14_1_7_2_2.proof F s (localSlots s α z P) hslots
    rw [← K1_14_1_7_2_1.proof F s α z P hP.1] at hd
    exact transfer_dvd H lift α z (s.B+s.J) P hH hz
      (linear_pole_dvd α z (s.B+s.J) P hd)

theorem slots_card (u : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) :
    Fintype.card (Slots u d side) = (u 0 + 1) * (u 1 + 1) + (u (otherBlock side) + 1) * d := by
  simp only [Slots, Fintype.card_prod, Fintype.card_fin]
  fin_cases side <;> simp [otherBlock] <;> ring

end
end Rect51PoleWindow
