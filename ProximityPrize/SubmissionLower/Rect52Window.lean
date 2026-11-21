import ProximityPrize.SubmissionLower.Rect51Rank

import ProximityPrize.SubmissionLower.Rect52Prefix
import ProximityPrize.SubmissionLower.Rect52TerminalProof
import ProximityPrize.SubmissionLower.Rect52RegularResolved
import ProximityPrize.SubmissionLower.Rect52WindowPrice

/-! The rectangular high interval at 69.52. The rectangular Taylor method adapts the
public kaankolcu note f9161583-1b70-4048-8a65-bae6ee236fe4. -/
set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Rect52Window

open P1 (K I)
open High52Model (AnchorModel AnchoredFamily)
open K1_14 (Equation atMark)
open K1_14_1 (evaluated)
open Polynomial
open private flatten from ProximityPrize.SubmissionLower.Fast069
open private exponent_le from ProximityPrize.SubmissionLower.Rect51Rank

private theorem seed_bound (f : Equation) :
    Rect51Tangent.SeedBound f (fun i => Rect51Rank.coordDegree f (some i)) := by
  intro j i
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hm' := MvPolynomial.mem_support_iff.mp hm
  have hc := MvPolynomial.optionEquivLeft_coeff_coeff K1_14.FX (flatten f) j m
  rw [show MvPolynomial.optionEquivLeft K1_14.FX (Fin 2) (flatten f) = f from
    AlgEquiv.apply_symm_apply _ _] at hc
  have hmf : Finsupp.optionElim j m ∈ (flatten f).support :=
    MvPolynomial.mem_support_iff.mpr (hc ▸ hm')
  simpa only [Finsupp.optionElim_apply_some] using exponent_le f (some i) hmf

theorem ordinary {u : P1.Words} {del : Finset I} (M : AnchorModel u del)
    {Γ : Finset K} (F : AnchoredFamily M Γ)
    (hlo : (2391 : ℤ) ≤ M.overhead) (hhi : M.overhead ≤ 2451) :
    Γ.card ≤ 272512621865658327 := by
  classical
  have band : Rect52Prefix.InBand .h2391 M.overhead := ⟨hlo,hhi⟩
  let regular := Γ.erase M.shift
  have hreg : regular ⊆ Γ := Finset.erase_subset _ _
  have hshift : M.shift ∉ regular := Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar, fun γ hγ => F.mark γ (hreg hγ), F.distinct.mono hreg⟩
  suffices hc : regular.card ≤ 100178949002651624 + Rect52WindowPrice.retained by
    have herase : Γ.card - 1 ≤ regular.card := Finset.pred_card_le_card_erase
    change regular.card ≤ 100178949002651624 + 170000000000000000 at hc
    omega
  obtain ⟨H,hH⟩ := High52Model.adjacent_chart M G
  obtain ⟨D,Crt,_,src,pairs,⟨Q⟩⟩ := Rect52Prefix.prefix_at M G band hshift H hH
    (Rect52Prefix.persistent_curve M G band)
  let keep := regular \ Q.books
  have hk : keep ⊆ regular := Finset.sdiff_subset
  have hpaid : (regular \ keep).card ≤ 100178949002651624 := by
    apply (Finset.card_le_card ?_).trans (Rect52Prefix.paid_bound Q)
    intro γ hγ
    obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have cover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, Rect52Prefix.MarkOn M G q γ :=
    fun γ hγ => (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  suffices hkept : keep.card ≤ Rect52WindowPrice.retained by
    have hpart := Finset.card_sdiff_add_card_eq_card hk
    omega
  by_cases hm : keep.Nonempty
  · obtain ⟨γ,hγ⟩ := hm
    obtain ⟨q,hq,_⟩ := cover γ hγ
    obtain ⟨f,hf⟩ := K1_14_3_7.proof Q.parents ⟨q,hq⟩ Q.geometric
    have hred : High52.Reduced f := ⟨hf.positive, hf.primitive, hf.separable⟩
    have hn : f ≠ 0 := by
      intro hz
      have hp := hf.positive
      simp [hz] at hp
    obtain ⟨hl,hu⟩ := Rect52Prefix.window_nat band
    have hw : Rect52Regular.Window M 2391 2451 M.overhead.toNat :=
      ⟨by omega,hl,hu,by decide,le_rfl⟩
    have hH' : Rect52Regular.Chart M.overhead.toNat M G H := ⟨hH.1,hH.2⟩
    have ⟨hdeg,hcap⟩ :=
      Rect52TerminalProof.prefix_bounds Crt src band Q.geometric Q.terminal_pass hf hn
    have roots : ∀ η ∈ keep, atMark f (M.label η) (G.scalar η) = 0 := by
      intro η hη
      obtain ⟨q',hq',hon⟩ := cover η hη
      have hz := RingHom.mem_ker.mp (hon (hf.vanishes q' hq'))
      simpa only [coe_eval₂RingHom, eval₂_C, atMark] using hz
    have hv : Rect52Regular.seedSum (fun i => Rect51Rank.coordDegree f (some i)) ≤
        Rect52WindowPrice.seedCap f.natDegree := by
      exact hcap f.natDegree hf.positive le_rfl
    obtain ⟨hsep,hflat⟩ := Rect52WindowPrice.guards hf.positive hdeg hv
    by_cases he : 4 ≤ f.natDegree
    · exact (Rect52Regular.count_roots_rect_actual M G hw hshift hH' hred he
        (seed_bound f) hsep hflat keep hk roots).trans
          (Rect52WindowPrice.rect_retained he hdeg hv)
    · have hs := (Rect52WindowPrice.guards hf.positive hdeg
        (le_refl (Rect52WindowPrice.seedCap f.natDegree)))
      have hb := fun j => (Rect52Regular.seed_bound (seed_bound f) j).trans hv
      exact (Rect52Regular.count_roots_triangular M G hw hshift hH' hred hb hs.1 hs.2
        keep hk roots).trans (Rect52WindowPrice.stock_retained hf.positive (by omega))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hm]

#print axioms ordinary
end Rect52Window
