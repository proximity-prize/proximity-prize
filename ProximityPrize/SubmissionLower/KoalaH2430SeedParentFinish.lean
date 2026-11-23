import ProximityPrize.SubmissionLower.KoalaH2430Adapter
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open FrontCore82258 (effectiveHeight)

namespace KoalaH2430

open HighCore82258 HighCore82258_3
open K1_14 (Banks)
open K1_14_1 (PoleData CRTLift evaluated)
open KoalaH2430Receipt (prefixFee2430)

private theorem transport_terminal {n : ℕ} (hn : n = 2430)
    {word : P1.I → K1_14.L} (D : PoleData n) (crt : CRTLift D)
    (parents : Finset K1_14_3.Surface)
    (ht : ∀ q ∈ parents, BankPass (evaluated crt word)
      KoalaH2430Terminal.terminal.shape q) :
    ∃ D' : PoleData 2430, ∃ crt' : CRTLift D',
      ∀ q ∈ parents, ∀ P ∈ evaluated crt' word KoalaH2430Terminal.terminal.shape
        (KoalaH2430Terminal.terminal.shape.m * agreement - 1), P ∈ q.asIdeal := by
  subst n
  exact ⟨D, crt, ht⟩

private theorem prefixFee_le_zero (e : ℕ) : prefixFee2430 e ≤ prefixFee2430 0 := by
  by_cases h16 : e = 16
  · simp [prefixFee2430, h16]
  · by_cases h17 : e = 17 <;> simp [prefixFee2430, h16, h17]

/-- The singleton schedule supplies only the band, terminal shape, and integer bill.
The actual covered parents and terminal vanishing come from the same CRT source. -/
theorem prefix_geometry_of_seed_parent (b : Band)
    (hband : InBand b (2430 : ℤ))
    (hshape : (terminal b).shape = KoalaH2430Terminal.terminal.shape)
    (hbill : ∀ e, seedParentPrefix b e + 1 ≤ prefixFee2430 e)
    (hsource : CRTSourceExists) (hprefix : SeedParentC3) : PrefixTerminalGeometry := by
  classical
  intro u del Γ M F hh hs
  have hw : InBand b (effectiveHeight M) := by simpa only [hh] using hband
  obtain ⟨H,hH⟩ := FrontCore82258.adjacent_chart M F
  obtain ⟨C⟩ := hsource b u del M Γ F hw hs H hH
  let rows := C.rows
  have src : Source b M F rows := C.source
  obtain ⟨pairs⟩ := buffered_pairs b M F hw src
  obtain ⟨I⟩ := hprefix b u del M Γ F hw hs H hH
    (fun _ => persistent_curve M F hw) rows src pairs
  let Q := I.inventory
  let keep := Γ \ Q.books.union
  have hk : keep ⊆ Γ := Finset.sdiff_subset
  have hpaid : (Γ \ keep).card + 1 ≤ prefixFee2430 I.equation.natDegree := by
    apply (Nat.add_le_add_right (Finset.card_le_card ?_) 1).trans
      ((Nat.add_le_add_right I.card_books 1).trans (hbill _))
    intro γ hγ
    obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp hγ
    exact Classical.byContradiction fun hm => hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have hcover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, MarkOn M F q γ := fun γ hγ =>
    (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  by_cases hn : Q.parents.Nonempty
  · have hp : ∀ q ∈ Q.parents, BankPass rows KoalaH2430Terminal.terminal.shape q := by
      intro q hq
      rw [← hshape]
      exact Q.terminal_pass q hq
    obtain ⟨D,crt,hjet⟩ := transport_terminal (by simp [hh]) C.poles C.crt Q.parents hp
    exact Or.inr ⟨⟨Q.parents, hn, I.equation, I.projected hn, keep, hk, hcover,
      Q.geometric, D, crt, hjet, hpaid⟩⟩
  · have he : keep = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun ⟨γ,hγ⟩ => by
      obtain ⟨q,hq,_⟩ := hcover γ hγ
      exact hn ⟨q,hq⟩
    have paid_all : Γ.card + 1 ≤ prefixFee2430 I.equation.natDegree := by
      simpa [he] using hpaid
    exact Or.inl (paid_all.trans (prefixFee_le_zero _))

#print axioms prefix_geometry_of_seed_parent
end KoalaH2430
