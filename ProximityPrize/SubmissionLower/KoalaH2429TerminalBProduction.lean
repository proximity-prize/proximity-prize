import ProximityPrize.SubmissionLower.HighCore82258BankProof
import ProximityPrize.SubmissionLower.HighCore82258Ledger
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace KoalaH2429TerminalB
noncomputable section

open HighCore82258 HighCore82258_3
open K1_14 (Banks Equation L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_3 (Parent ProjectedProduct Surface)
open FrontCore82258 (effectiveHeight)
open scoped Polynomial

def prefixFee : ℕ := 121295101706637002

/-- The live marks and projected equation of the independently charged B inventory. -/
structure RetainedTrace {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) where
  parents : Finset Surface
  parents_nonempty : parents.Nonempty
  equation : Equation
  projected : ProjectedProduct parents equation
  marks : Finset K1.K
  marks_sub : marks ⊆ Γ
  covers : ∀ γ ∈ marks, ∃ q ∈ parents, MarkOn M F q γ
  geometric : ∀ q ∈ parents, Parent q
  poles : PoleData 2429
  crt : CRTLift poles
  terminal_pass : ∀ q ∈ parents, ∀ P ∈ evaluated crt (crtWord M)
    terminal.shape (terminal.shape.m * agreement - 1), P ∈ q.asIdeal
  prefix_paid : (Γ \ marks).card + 1 ≤ prefixFee

private theorem prefix_budget (e : ℕ) : seedParentPrefix .h2429B e + 1 ≤ prefixFee := by
  change seedParentPrefix .h2429B 0 + 1 ≤ prefixFee
  decide +kernel

theorem transport_terminal {n : ℕ} {s : K1_14.Shape} (hn : n = 2429)
    {word : P1.I → L} (D : PoleData n) (crt : CRTLift D)
    (parents : Finset Surface)
    (ht : ∀ q ∈ parents, HighCore82258.BankPass (evaluated crt word) s q) :
    ∃ D' : PoleData 2429, ∃ crt' : CRTLift D',
      ∀ q ∈ parents, ∀ P ∈ evaluated crt' word s
        (s.m * agreement - 1), P ∈ q.asIdeal := by
  subst n
  exact ⟨D, crt, ht⟩

theorem retained {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hh : effectiveHeight M = 2429) (hs : M.shift ∉ Γ) :
    Γ.card + 1 ≤ prefixFee ∨ Nonempty (RetainedTrace M F) := by
  classical
  have hw : InBand .h2429B (effectiveHeight M) := by
    rw [hh]
    exact ⟨le_rfl, le_rfl⟩
  obtain ⟨H,hH⟩ := FrontCore82258.adjacent_chart M F
  obtain ⟨C⟩ := HighCore82258BankProof.interpolation_sources_for_crt .h2429B u del M Γ F hw hs H hH
  let rows := C.rows
  have src : Source .h2429B M F rows := C.source
  obtain ⟨pairs⟩ := buffered_pairs .h2429B M F hw src
  have hprefix := of_children_seed_parent HighCore82258_3_1.proof
    HighCore82258_3_2.proof HighCore82258.schedule HighCore82258.graded_ledger
  obtain ⟨I⟩ := hprefix .h2429B u del M Γ F hw hs H hH
    (fun _ => persistent_curve M F hw) rows src pairs
  let Q := I.inventory
  let keep := Γ \ Q.books.union
  have hk : keep ⊆ Γ := Finset.sdiff_subset
  have hpaid : (Γ \ keep).card + 1 ≤ prefixFee := by
    apply (Nat.add_le_add_right (Finset.card_le_card ?_) 1).trans
      ((Nat.add_le_add_right I.card_books 1).trans (prefix_budget _))
    intro γ hγ
    obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp hγ
    exact Classical.byContradiction fun hm => hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have hcover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, MarkOn M F q γ := fun γ hγ =>
    (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  by_cases hn : Q.parents.Nonempty
  · have hp : ∀ q ∈ Q.parents, HighCore82258.BankPass rows terminal.shape q := Q.terminal_pass
    obtain ⟨D,crt,hjet⟩ := transport_terminal (by simp [hh]) C.poles C.crt Q.parents hp
    exact Or.inr ⟨⟨Q.parents, hn, I.equation, I.projected hn, keep, hk, hcover,
      Q.geometric, D, crt, hjet, hpaid⟩⟩
  · have he : keep = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun ⟨γ,hγ⟩ => by
      obtain ⟨q,hq,_⟩ := hcover γ hγ
      exact hn ⟨q,hq⟩
    exact Or.inl (by simpa [he] using hpaid)

end
end KoalaH2429TerminalB
