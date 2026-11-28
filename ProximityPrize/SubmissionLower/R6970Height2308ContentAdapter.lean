import ProximityPrize.SubmissionLower.R6970SpreadWide6970
import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore

set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Research6970.Height2313.Research6969


open Finset Polynomial Lower6960 Research6966
open _root_.Research6969
open Far6969RescueGeometry (word)
open K1_14 (Equation)
open K1_14_3 (Parent SeedField)
open scoped Classical

noncomputable abbrev surfaces {i} (s : _root_.Research6970.Height2313.Research6969.HighPackets.State i) := _root_.Research6970.Height2313.Research6969.NormalGeometry.allParents s

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

private theorem NormalRoute.wideWithContent {i r} (c : ℕ) (room : c ≤ r.content)
    (law : ∀ (s : HighPackets.State i), NormalRoute.Applies s r → s.ControlAt c)
    (proved : NormalRoute.Done i {r with content := c}) :
    NormalRoute.Done i r := by
  intro s h
  have bound := room.trans (h.2.2.1.symm.trans_le (NormalGeometry.content_le_stock s))
  let next := s.withContent c bound (law s h)
  exact proved next ⟨h.1,h.2.1,rfl,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

private theorem PairRoute.wideWithContent {i w} (c : ℕ) (room : c ≤ w.region.content)
    (law : ∀ (s : HighPackets.State i), PairRoute.Applies s w → s.ControlAt c)
    (proved : PairRoute.Done i {w with region := {w.region with content := c}}) :
    PairRoute.Done i w := by
  intro s h
  have bound := room.trans (h.root.2.2.1.symm.trans_le (NormalGeometry.content_le_stock s))
  let next := s.withContent c bound (law s h)
  obtain ⟨lo,hi,_,degree,low,high⟩ := h.root
  exact proved next ⟨⟨lo,hi,rfl,degree,low,high⟩,h.al,h.ah,h.wl,h.wh⟩


private theorem wide_nine_at {i c} (s : HighPackets.State i)
    (large : 22 ≤ s.f.natDegree) (room : 9 ≤ c) (gap : 2*c < s.f.natDegree)
    (weak : s.ControlAt c) : s.ControlAt 9 := by
  have lower : 2308 ≤ s.model.overhead.toNat := by
    have bound := s.lower
    omega
  exact _root_.Research6969.SpreadWide6970.tighten_nine22 lower s.higher s.crt (word s.model)
    (surfaces s) (populated s) (geom s) (passes s) s.product large s.gp room gap weak

theorem PairRoute.withNineBelow {i w} (grade : 22 ≤ w.region.gradeLo)
    (room : 9 ≤ w.region.content) (gap : 2*w.region.content < w.region.gradeLo)
    (proved : PairRoute.Done i {w with region := {w.region with content := 9}}) :
    PairRoute.Done i w :=
  PairRoute.wideWithContent 9 room (fun s h =>
    wide_nine_at s (grade.trans h.root.1) room (gap.trans_le h.root.1)
      (h.root.2.2.1 ▸ NormalGeometry.control s)) proved

theorem NormalRoute.withNineBelow {i r} (grade : 22 ≤ r.gradeLo)
    (room : 9 ≤ r.content) (gap : 2*r.content < r.gradeLo)
    (proved : NormalRoute.Done i {r with content := 9}) : NormalRoute.Done i r :=
  NormalRoute.wideWithContent 9 room (fun s h =>
    wide_nine_at s (grade.trans h.1) room (gap.trans_le h.1)
      (h.2.2.1 ▸ NormalGeometry.control s)) proved

end Research6970.Height2313.Research6969
