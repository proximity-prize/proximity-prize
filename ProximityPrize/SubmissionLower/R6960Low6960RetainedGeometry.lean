import ProximityPrize.SubmissionLower.R6960Low6960SharedBentCaps
import ProximityPrize.SubmissionLower.R6960Low6960SharedTally

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

namespace Low6960RetainedCut
noncomputable section

open P3 (K I)
open K1_13 (Row Shape InBox shape mixed32 chart)
open Low6960Prices (Messages tiltedFits tiltedSurface taylorLength)
open Low6960GeometryCut (CutInput MixedBound)
open Low6960GeometryCut (chargedPrice assemble_charge continued_bound)
open Low6960ActiveCycle (mixed)
open scoped Polynomial BigOperators

/-- The accepted physical charge with an arbitrary mixed surface budget. -/
def cutPrice (x : Shape) (l scale surface : ℕ) := chargedPrice x l scale surface

def fourSurface (p q : Shape) :=
  mixed32 p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)

variable {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem smaller_tilted (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q : Shape) (hQ : InBox (shape Q) q) (hq : Low48BentLattice.Chamber (q,0))
    (hguard : tiltedFits (shape f)) :
    Γ.card ≤ cutPrice (shape f) l (60*32) (tiltedSurface (shape f).chamber q) := by
  let p := (shape f).chamber
  have hp := K1_13_7_1.shape_chamber f
  have ht : 1 ≤ p.t := input.small.2.1
  have hCh := Low6960SharedBentCaps.caps_chamber (p := p) hp.1 ht hguard.1 hq
  apply assemble_charge Low6960GeometryCut_1.proof continued_bound hm input (by decide : 0 < 60*32)
  apply Low6960ActiveCycle.mixed (R := Low48BentCycle.rawFamily (Low6960SharedBentCaps.caps p q))
    (B := Low48BentCycle.capFamily (Low6960SharedBentCaps.caps p q)) input Low6960SharedBentCaps.ordinary_doubled
  · exact Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩
  · exact Low48BentCycle.old_section hQ
  · exact Low6960SharedBentCaps.chart q ht
  · exact Low6960SharedBentCaps.ordinary_budget hCh

theorem smaller_four (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q : Shape) (hQ : InBox (shape Q) q) (hq : K1_13_6_2_3.ChamberBox q) :
    Γ.card ≤ cutPrice (shape f) l 32 (fourSurface (shape f).chamber q) := by
  classical
  let D : Low6960SharedTally.Data Γ s f Q l Set.univ := Low6960SharedTally.build Set.univ
  have h := Low6960SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q Q l input.small input.proper q hq hQ (fun _ => l)
    D.branches D.points (D.four input) (fun b _ => ⟨b.base,b.high⟩)
  have hh := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp h
  have hn : 32*l*(∑ b∈D.branches, b.weight*(D.points b).card) ≤ fourSurface (shape f).chamber q := by
    apply (Nat.cast_le (α := ℚ)).mp
    simp only [fourSurface,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat]
    simpa only [Nat.cast_mul,← Finset.mul_sum,mul_comm (32:ℚ),mul_assoc,mul_left_comm] using hh
  apply assemble_charge Low6960GeometryCut_1.proof continued_bound hm input (by decide : 0 < 32)
  obtain ⟨C,B,hcurve,hpos,hcover,hcost⟩ := D.pieces input
  refine ⟨C,B,hcurve,hpos,?_,(Nat.mul_le_mul_left (32*l) hcost).trans hn⟩
  intro γ hγ hmixed
  obtain ⟨b,hb⟩ := Low6960GeometryCut_2.branch_of_mixed hmixed
  exact hcover γ hγ ⟨b,Set.mem_univ _,hb⟩

#print axioms smaller_tilted
#print axioms smaller_four

end
end Low6960RetainedCut
