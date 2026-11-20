import ProximityPrize.SubmissionLower.Koala6844ReceiptsExactBand

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open RCN095 LocatorFactorAggregate
set_option autoImplicit false

private theorem secondGate_mono (f g : Flag) (hf : f.ordered) (hg : g.ordered)
    (hr : 0 < f.r) (hfg : f.cumulativeLE g)
    (ha : bandCovers secondAdaptiveFlag f secondAdaptiveGap = true) :
    geometricGate flowWidth (bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap) g.toFlagDegree := by
  have hBelow : Below f.toFlagDegree g.toFlagDegree := by
    unfold Below
    rw [Flag.toFlagDegree_middle f hf,Flag.toFlagDegree_middle g hg,
      Flag.toFlagDegree_total f hf,Flag.toFlagDegree_total g hg]
    exact hfg
  exact geometricGate_mono flowWidth _ hBelow hr ((bandCovers_iff_geometric _ _ _ hf).mp ha)

inductive TerminalSlopeTape (r : Nat) : Nat → Type
  | stop {y : Nat} (active : bandCovers secondAdaptiveFlag ⟨r,y,y⟩ secondAdaptiveGap = true) :
      TerminalSlopeTape r y
  | row {y : Nat} (t : Nat) (ordered : y ≤ t)
      (active : bandCovers secondAdaptiveFlag ⟨r,y,t+1⟩ secondAdaptiveGap = true)
      (rest : TerminalSlopeTape r (y+1)) : TerminalSlopeTape r y

def TerminalSlopeTape.flags {r y : Nat} : TerminalSlopeTape r y → List Flag
  | .stop _ => []
  | .row t _ _ rest => ⟨r,y,t⟩ :: rest.flags

theorem TerminalSlopeTape.covers {r y : Nat} (tape : TerminalSlopeTape r y) (f : Flag)
    (hr : 0 < r) (hry : r ≤ y) (hf : f.ordered) (hfr : f.r = r) (hy : y ≤ f.y)
    (hfail : ¬geometricGate flowWidth (bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap) f.toFlagDegree) :
    ∃ e ∈ tape.flags, f.cumulativeLE e := by
  induction tape with
  | @stop y hstop =>
    exact False.elim (hfail (secondGate_mono ⟨r,y,y⟩ f ⟨hry,le_rfl⟩ hf hr
      ⟨hfr.ge,hy,hy.trans hf.2⟩ hstop))
  | @row y t hyt hstep rest ih =>
    by_cases heq : y = f.y
    · have ht : f.t ≤ t := by
        by_contra hn
        exact hfail (secondGate_mono ⟨r,y,t+1⟩ f ⟨hry,hyt.trans (Nat.le_succ t)⟩ hf hr
          ⟨hfr.ge,hy,by change t+1 ≤ f.t; omega⟩ hstep)
      exact ⟨⟨r,y,t⟩,List.mem_cons.mpr (.inl rfl),⟨hfr.le,heq.ge,ht⟩⟩
    · obtain ⟨g,hg,hfg⟩ := ih (by omega) (by omega)
      exact ⟨g,List.mem_cons.mpr (.inr hg),hfg⟩

structure TerminalCoveredSlope where
  slope : Nat
  tape : TerminalSlopeTape slope slope

def coveredTerminalFlags (schedules : List TerminalCoveredSlope) : List Flag :=
  schedules.flatMap fun s => s.tape.flags

theorem terminalCoverage_of_tapes (schedules : List TerminalCoveredSlope)
    (hslopes : schedules.map TerminalCoveredSlope.slope = (List.range afterRooms.r).map (·+1))
    (table : List CertifiedEndpoint) (hflags : table.map CertifiedEndpoint.flag = coveredTerminalFlags schedules)
    (f : Flag) (hr : 0 < f.r) (hf : f.ordered) (hroom : f.cumulativeLE afterRooms)
    (hfail : ¬geometricGate flowWidth (bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap) f.toFlagDegree) :
    ∃ e ∈ table, f.cumulativeLE e.flag := by
  have hz : f.r∈schedules.map TerminalCoveredSlope.slope := by
    rw [hslopes]
    refine List.mem_map.mpr ⟨f.r-1,List.mem_range.mpr (by have h := hroom.1; omega),?_⟩
    omega
  obtain ⟨s,hs,hrEq⟩ := List.mem_map.mp hz
  obtain ⟨g,hg,hfg⟩ := s.tape.covers f (by omega) le_rfl hf hrEq.symm (by simpa [hrEq] using hf.1) hfail
  have hm : g∈table.map CertifiedEndpoint.flag := by
    rw [hflags]
    exact List.mem_flatMap.mpr ⟨s,hs,hg⟩
  obtain ⟨e,he,heq⟩ := List.mem_map.mp hm
  exact ⟨e,he,by simpa only [heq] using hfg⟩

end ProximityPrize.SubmissionLower.Koala6844Receipts
