import ProximityPrize.SubmissionLower.High70ConditionalPoles

set_option autoImplicit true
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false

namespace Effective70Poles
noncomputable section

open Polynomial
open P1 (K I node twist p)
open FrontCore82706 (AnchorModel AnchoredFamily)
open K1_14 (L FX liftPoly seedEmbedding)
open P1_7_7 (poleProduct)
open private commonChart common_recovers from ProximityPrize.SubmissionLower.UpperBranch7
open K1_14_1 (PoleData MarkResidues nodeL)
open scoped Polynomial

open private SizedChart sized_chart chart_poles
  from ProximityPrize.SubmissionLower.High70ConditionalPoles

abbrev Chart {u del Γ} (n : ℕ) (M : AnchorModel u del) (F : AnchoredFamily M Γ) (H : L[X]) :=
  SizedChart n M F H

theorem exists_chart {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (n : ℕ) (hn : n ≤ M.E.natDegree) : ∃ H, Chart n M F H :=
  sized_chart M F n hn

theorem poles {u del Γ n} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (H : L[X]) (hH : Chart n M F H) :
    ∃ D : PoleData n,
      K1_14_1.poleProduct D = H * H.map (frobenius L p) ∧
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) :=
  chart_poles M F H hH

theorem pole_data {u del n} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {H : L[X]} (h : Chart n M F H) :
    (poleProduct H).Monic ∧ (poleProduct H).natDegree = 2 * n ∧
    (poleProduct H).eval (algebraMap L[X] FX Polynomial.X) ≠ 0 ∧
    ∀ j : I, (poleProduct H).eval (seedEmbedding (node j)) ≠ 0 := by
  obtain ⟨hm, hd, _, hm', hd', _, _, hn, _, _, _⟩ := h
  let B := H * H.map (frobenius L p)
  let incl := algebraMap L[X] FX
  have hb : B.Monic := hm.mul hm'
  have hdeg : B.natDegree = 2 * n := by
    rw [show B = H * H.map (frobenius L p) from rfl,
      Polynomial.natDegree_mul hm.ne_zero hm'.ne_zero, hd, hd']
    omega
  refine ⟨hb.map _, (hb.natDegree_map _).trans hdeg, ?_, ?_⟩
  · have heval : (poleProduct H).eval (incl Polynomial.X) = incl B := by
      rw [poleProduct, Polynomial.eval_map]
      change B.eval₂ (incl.comp Polynomial.C) (incl Polynomial.X) = incl B
      rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
    rw [heval]
    exact (map_ne_zero_iff incl (IsFractionRing.injective L[X] FX)).mpr hb.ne_zero
  · intro j
    let x := algebraMap K L (node j)
    have heval : (poleProduct H).eval (seedEmbedding (node j)) = incl (Polynomial.C (B.eval x)) := by
      rw [poleProduct, Polynomial.eval_map]
      change B.eval₂ (incl.comp Polynomial.C) ((incl.comp Polynomial.C) x) = _
      rw [Polynomial.eval₂_hom]
      rfl
    have hval : B.eval x ≠ 0 := by
      rw [show B = H * H.map (frobenius L p) from rfl, Polynomial.eval_mul]
      exact mul_ne_zero (hn j).1 (hn j).2
    rw [heval]
    exact (map_ne_zero_iff incl (IsFractionRing.injective L[X] FX)).mpr
      ((map_ne_zero_iff _ Polynomial.C_injective).mpr hval)
theorem crt_chart {u del n} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) (hw : 0 < n) (hH : Chart n M F H) :
    ∃ C : P1_7_7.CRTChart n, ∀ γ ∈ Γ,
      C.Recovers (poleProduct H) (M.label γ) (F.scalar γ) := by
  obtain ⟨D, hD, _, hmarks⟩ := chart_poles M F H hH
  obtain ⟨B, hd, hn⟩ := P1_7_7_1.bounded_crt D
  refine ⟨commonChart hw B hd hn, ?_⟩
  intro γ hγ
  rw [P1_7_7.poleProduct, ← hD]
  exact common_recovers hw B hd hn (hmarks γ hγ)


#print axioms exists_chart
#print axioms crt_chart
end
end Effective70Poles
