import ProximityPrize.SubmissionLower.Peer653NativePrefixPrefixGeometry
import ProximityPrize.SubmissionLower.Peer653NativePrefixLedger
import ProximityPrize.SubmissionLower.Peer653High53BankProof
import ProximityPrize.SubmissionLower.Peer653KoalaTwoCutProof

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Peer653JointCash
noncomputable section
open High53Model (AnchorModel AnchoredFamily)
open K1_14 (Equation Banks atMark)
open P1 (K)
open Polynomial

private abbrev nativeBand : Peer653NativePrefix.Band := .h2390
private abbrev peerBand : Peer653High53.Band := .h2367

private theorem native_listed {t : P1_7.Bank} (ht : Peer653NativePrefix.Listed nativeBand t) :
    Peer653High53.Listed peerBand t := ht

private theorem native_source {u del} {M : AnchorModel u del}
    {Γ : Finset K} {F : AnchoredFamily M Γ} {rows : Banks}
    (src : Peer653High53.Source peerBand M F rows) :
    Peer653NativePrefix.Source nativeBand M F rows where
  nested := fun t ht t' ht' => src.nested t (native_listed ht) t' (native_listed ht')
  necessary := fun t ht => src.necessary t (native_listed ht)
  shape := fun t ht => src.shape t (native_listed ht)
  leading := fun t ht => src.leading t (native_listed ht)
  shift := fun t ht => src.shift t (native_listed ht)
  floor_bound := fun t ht => src.floor_bound t (native_listed ht)

private def peer_pair {h : ℕ} {rows : Banks} {s : P1_7.Stage}
    (P : Peer653NativePrefix.BufferedPair h rows s) : Peer653High53.BufferedPair h rows s :=
  ⟨P.free, P.moving, P.free_ne, P.moving_ne, P.free_mem, P.moving_mem, P.no_moving⟩

private def peer_pairs {h : ℕ} {rows : Banks}
    (P : Peer653NativePrefix.Pairs nativeBand h rows) : Peer653High53.Pairs peerBand h rows :=
  fun s hs => peer_pair (P s hs)

private theorem paid_cash {u del} {M : AnchorModel u del} {Γ : Finset K}
    {F : AnchoredFamily M Γ} {rows : Banks}
    {P : Peer653NativePrefix.Pairs nativeBand M.overhead.toNat rows}
    (Q : Peer653NativePrefix.PrefixInventory nativeBand M F P) :
    Q.books.card ≤ (Peer653High53.fees peerBand).loss :=
  ((Nat.le_add_right _ _).trans Q.paid).trans (by decide)

private def peer_inventory {u del} {M : AnchorModel u del} {Γ : Finset K}
    {F : AnchoredFamily M Γ} {rows : Banks}
    {P : Peer653NativePrefix.Pairs nativeBand M.overhead.toNat rows}
    (Q : Peer653NativePrefix.PrefixInventory nativeBand M F P) :
    Peer653High53.PrefixInventory peerBand M F (peer_pairs P) where
  books := {
    loss := Q.books
    point := ∅
    lowSeed := ∅
    lowJet := ∅
    fixedODE := ∅
    content := ∅
    loss_le := paid_cash Q
    point_le := by simp
    lowSeed_le := by simp
    lowJet_le := by simp
    fixedODE_le := by simp
    content_le := by simp }
  parents := Q.parents
  geometric := Q.geometric
  stage_pass := fun q hq s hs => Q.stage_pass q hq s hs
  terminal_pass := Q.terminal_pass
  covers := by
    intro γ hγ
    rcases Q.covers γ hγ with h | h
    · left
      simpa [Peer653High53.PrefixBooks.union] using h
    · exact Or.inr h

theorem ordinary_of_retained (hRetained : Peer653High53.RetainedCountAt peerBand)
    {u del} (M : AnchorModel u del) {Γ : Finset K} (F : AnchoredFamily M Γ)
    (lo : (2390 : ℤ) ≤ M.overhead) (hi : M.overhead ≤ 2526) :
    Γ.card ≤ 272512621865658327 := by
  classical
  have hn : Peer653NativePrefix.InBand nativeBand M.overhead := ⟨lo, hi⟩
  have hp : Peer653High53.InBand peerBand M.overhead := ⟨lo, hi⟩
  let regular := Γ.erase M.shift
  have hsub : regular ⊆ Γ := Finset.erase_subset _ _
  have hshift : M.shift ∉ regular := Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar, fun γ hγ => F.mark γ (hsub hγ), F.distinct.mono hsub⟩
  obtain ⟨H, hH⟩ := High53Model.adjacent_chart M G
  obtain ⟨C⟩ := Peer653High53BankProof.interpolation_sources_for_crt
    peerBand u del M regular G hp hshift H hH
  have src := native_source C.source
  obtain ⟨P⟩ := Peer653NativePrefix.buffered_pairs nativeBand M G hn src
  obtain ⟨Q⟩ := Peer653NativePrefix_3.of_children Peer653NativePrefix_3_1.proof
    Peer653NativePrefix_3_2.proof Peer653NativePrefix.schedule Peer653NativePrefix.loss_ledger
    nativeBand u del M regular G hn hshift H hH
    (fun _ => Peer653NativePrefix.persistent_curve M G hn) _ src P
  let keep := regular \ Q.books
  have hk : keep ⊆ regular := Finset.sdiff_subset
  have hpaid : (regular \ keep).card ≤ (Peer653High53.fees peerBand).loss := by
    apply (Finset.card_le_card ?_).trans (paid_cash Q)
    intro γ hγ
    obtain ⟨hreg, hnkeep⟩ := Finset.mem_sdiff.mp hγ
    by_contra h
    exact hnkeep (Finset.mem_sdiff.mpr ⟨hreg,h⟩)
  have cover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, Peer653NativePrefix.MarkOn M G q γ :=
    fun γ hγ => (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  have hkept : keep.card ≤ Peer653High53.retainedCap peerBand := by
    by_cases hm : keep.Nonempty
    · obtain ⟨γ,hγ⟩ := hm
      obtain ⟨q,hq,_⟩ := cover γ hγ
      obtain ⟨f,hf⟩ := K1_14_3_7.proof Q.parents ⟨q,hq⟩ Q.geometric
      have hred : Peer653High53.Reduced f := ⟨hf.positive, hf.primitive, hf.separable⟩
      apply hRetained u del M regular G hp hshift H hH C (peer_pairs P)
        (peer_inventory Q) f hred hf keep hk
      intro η hη
      obtain ⟨q',hq',hon⟩ := cover η hη
      have hz := RingHom.mem_ker.mp (hon (hf.vanishes q' hq'))
      simpa only [coe_eval₂RingHom, eval₂_C, atMark] using hz
    · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
  have hpart := Finset.card_sdiff_add_card_eq_card hk
  have herase : Γ.card - 1 ≤ regular.card := Finset.pred_card_le_card_erase
  have cash : (Peer653High53.fees peerBand).loss + Peer653High53.retainedCap peerBand + 1 ≤
      272512621865658327 := by decide
  omega

theorem ordinary {u del} (M : AnchorModel u del) {Γ : Finset K} (F : AnchoredFamily M Γ)
    (lo : (2390 : ℤ) ≤ M.overhead) (hi : M.overhead ≤ 2526) :
    Γ.card ≤ 272512621865658327 :=
  ordinary_of_retained
    (KoalaRect.retained_of_price (Peer653High53BankProof.terminal_ok peerBand)
      (KoalaTwoSectionPrice.rect_price SplitCut.TwoCut.two_cut_count)) M F lo hi

#print axioms ordinary
end
end Peer653JointCash
