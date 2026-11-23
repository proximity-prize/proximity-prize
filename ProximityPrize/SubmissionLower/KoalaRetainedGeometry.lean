import ProximityPrize.SubmissionLower.Shared50BentCaps
import ProximityPrize.SubmissionLower.Shared50Tally

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

namespace KoalaRetainedCut
noncomputable section

open P3 (K I)
open K1_13 (Row Shape InBox shape mixed32 chart)
open Final50Price (Messages tiltedFits tiltedSurface taylorLength)
open Final50GeometryCut (CutInput MixedBound)
open private chargedPrice assemble_charge continued_bound from ProximityPrize.SubmissionLower.Final50GeometryCut
open private Final50ActiveCycle.mixed from ProximityPrize.SubmissionLower.Final50ActiveCycleMixed
open scoped Polynomial BigOperators

/-- The accepted physical charge with an arbitrary mixed surface budget. -/
def cutPrice (x:Shape) (l scale surface:ℕ):=chargedPrice x l scale surface

def fourSurface (p q : Shape) :=
  mixed32 p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)

variable {w:I→K} {Γ:Finset K} {s:K→K[X]} {f Q:Row 4} {l:ℕ}

theorem smaller_tilted (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q:Shape) (hQ:InBox (shape Q) q) (hq:Low48BentLattice.Chamber (q,0))
    (hguard:tiltedFits (shape f)) :
    Γ.card≤cutPrice (shape f) l (60*32) (tiltedSurface (shape f).chamber q):=by
  let p:=(shape f).chamber
  have hp:=K1_13_7_1.shape_chamber f
  have ht:1≤p.t:=input.small.2.1
  have hCh:=Shared50BentCaps.caps_chamber (p:=p) hp.1 ht hguard.1 hq
  apply assemble_charge Final50GeometryCut_1.proof continued_bound hm input (by decide:0 < 60*32)
  apply Final50ActiveCycle.mixed (R := Low48BentCycle.rawFamily (Shared50BentCaps.caps p q))
    (B:=Low48BentCycle.capFamily (Shared50BentCaps.caps p q)) input Shared50BentCaps.ordinary_doubled
  · exact Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩
  · exact Low48BentCycle.old_section hQ
  · exact Shared50BentCaps.chart q ht
  · exact Shared50BentCaps.ordinary_budget hCh

theorem smaller_four (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q:Shape) (hQ:InBox (shape Q) q) (hq:K1_13_6_2_3.ChamberBox q) :
    Γ.card≤cutPrice (shape f) l 32 (fourSurface (shape f).chamber q):=by
  classical
  let D:Shared50Tally.Data Γ s f Q l Set.univ:=Shared50Tally.build Set.univ
  have h := Shared50CycleFour.bound_with_cut K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q Q l input.small input.proper q hq hQ (fun _ => l)
    D.branches D.points (D.four input) (fun b _ => ⟨b.base,b.high⟩)
  have hh:=(le_div_iff₀ (by norm_num:(0:ℚ)<32)).mp h
  have hn : 32*l*(∑ b∈D.branches, b.weight*(D.points b).card) ≤ fourSurface (shape f).chamber q := by
    apply (Nat.cast_le (α:=ℚ)).mp
    simp only [fourSurface,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat]
    simpa only [Nat.cast_mul,← Finset.mul_sum,mul_comm (32:ℚ),mul_assoc,mul_left_comm] using hh
  apply assemble_charge Final50GeometryCut_1.proof continued_bound hm input (by decide:0 < 32)
  obtain ⟨C,B,hcurve,hpos,hcover,hcost⟩:=D.pieces input
  refine ⟨C,B,hcurve,hpos,?_,(Nat.mul_le_mul_left (32*l) hcost).trans hn⟩
  intro γ hγ hmixed
  obtain ⟨b,hb⟩:=Final50GeometryCut_2.branch_of_mixed hmixed
  exact hcover γ hγ ⟨b,Set.mem_univ _,hb⟩

#print axioms smaller_tilted
#print axioms smaller_four

end
end KoalaRetainedCut
