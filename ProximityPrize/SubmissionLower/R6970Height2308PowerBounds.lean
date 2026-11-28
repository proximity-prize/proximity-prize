import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970SpreadWide6970

set_option autoImplicit true
set_option Elab.async false

namespace Research6970.Height2313.Research6969.BandPowerBounds

open Research6970.Height2313.Research6969
open _root_.Research6969 Research6966
open _root_.Lower6960.Far6969RescueGeometry (word)
open Finset Polynomial
open K1_14 (Equation)
open K1_14_3 (Parent SeedField)
open scoped Classical

noncomputable abbrev surfaces {i} (s : _root_.Research6970.Height2313.Research6969.HighPackets.State i) := _root_.Research6970.Height2313.Research6969.NormalGeometry.allParents s
abbrev ctrl {i} (s : _root_.Research6970.Height2313.Research6969.HighPackets.State i) (n : ℕ) :=
  s.ControlAt n

private theorem populated {i} (s : _root_.Research6970.Height2313.Research6969.HighPackets.State i) : (surfaces s).Nonempty := by
  by_contra empty
  have dvd := NativeOrdinateMass.divides_of_member (D:=1) s.product
    (fun q h => False.elim (empty ⟨q,h⟩))
  have zero := Polynomial.natDegree_le_of_dvd dvd (one_ne_zero : (1:Equation)≠0)
  rw [Polynomial.natDegree_one] at zero
  have big := s.high
  omega

private theorem geom {i} (s : _root_.Research6970.Height2313.Research6969.HighPackets.State i) (q) (hq:q∈surfaces s) : Parent q :=
  (mem_union.mp hq).elim (fun a => (s.pair.mainGeo q a).1) (fun a => (s.pair.rescueGeo q a).1)

private theorem passes {i} (s : _root_.Research6970.Height2313.Research6969.HighPackets.State i) (q) (hq:q∈surfaces s) :
    TerminalBanks.Pass s.crt (word s.model) 179730 SpreadCatalogue.shape q :=
  (mem_union.mp hq).elim (fun a => (s.pair.mainGeo q a).2.1) (fun a => (s.pair.rescueGeo q a).2.1)

private theorem same_graph {i} (s : _root_.Research6970.Height2313.Research6969.HighPackets.State i) {c : ℕ}
    (gap : 2*c < s.f.natDegree) {G : Pade.Row SeedField} (gp : G.primitive)
    (strong : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep))
      (Pade.Native.sheets (surfaces s)) c) (weak : ctrl s c) :
    ∃ t : Pade.Native.Sep, t ≠ 0 ∧ s.graph.map (algebraMap SeedField Pade.Native.Sep) =
      (G.map (algebraMap SeedField Pade.Native.Sep)).scale t := by
  classical
  obtain ⟨f', T, v, project, size, on⟩ := Pade.Native.projected_sheets
    (surfaces s) (populated s) (geom s)
  have eq : s.f.natDegree = T.card := (NearTerminal.same_degree s.product project).trans size.symm
  let emb : SeedField →+* Pade.Native.Sep := algebraMap _ _
  exact Pade.unique_control (Pade.Native.sheets (surfaces s)) T.card c
    (by omega) ⟨T,v,rfl,on⟩ ((Pade.Row.primitive_map emb).mpr gp)
    ((Pade.Row.primitive_map emb).mpr s.gp) strong weak

theorem degree24 {i} (s : _root_.Research6970.Height2313.Research6969.HighPackets.State i)
    (large : 24 ≤ s.f.natDegree) (weak : ctrl s 9) : s.graph.graphDegree ≤ 5 := by
  obtain ⟨G, gp, cap, strong⟩ := _root_.Research6969.SpreadWide6970.classify24
    (by have age := s.lower; omega) s.higher s.crt (word s.model) (surfaces s) (populated s) (geom s) (passes s) s.product large
  obtain ⟨t, nz, same⟩ := same_graph s (by omega) gp strong weak
  have degree := congrArg (fun g : Pade.Row Pade.Native.Sep => g.graphDegree) same
  rw [Pade.Row.degree_map, Pade.Row.degree_scale _ nz, Pade.Row.degree_map] at degree
  exact degree.trans_le cap

end Research6970.Height2313.Research6969.BandPowerBounds
