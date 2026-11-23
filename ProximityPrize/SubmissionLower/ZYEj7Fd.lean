import ProximityPrize.SubmissionLower.Z77J3Nc
import ProximityPrize.SubmissionLower.ZQIEUqa
set_option Elab.async false
open _root_ renaming Module.finrank→lz,q7IA62d.cutoff→aU,q7IA62d.profile→cy,q7IA62d.source→c9
set_option autoImplicit true
namespace q7IA62d
noncomputable section
open Finset Polynomial
open P5 (I p)
open P5_7_2 (fO jX row NodeUnits)

open cu (L)
open DP (jF zG ad0)
open jA (jK ko bC)
open NR (TT)
open private bXt bCP from ProximityPrize.SubmissionLower.DG
def c1 :Prop :=
  ∀ (b:fO) (e :Bool) (h:ℕ),h≤(row b).declaredHi →
    let t:=cy b e
    let V:=Aw h t (aU t)
    Module.Finite L V ∧
      required b e+contactDebit t+eMG h t≤lz L V
def c2 :Prop :=
  ∀ (b:fO) (e :Bool) (h:ℕ) (x v :L),
    let t:=cy b e
    TT (Aw h t (aU t)) (ays t x v)≤(t.shape.U+1)*t.avF
def c3:Prop :=
  ∀ (b:fO) (e :Bool) (h:ℕ),0<h→h≤(row b).declaredHi →
    ∀ (D:jF h) (Crt:zG D),
      let t:=cy b e
      TT (Aw h t (aU t)) (btN Crt t)≤eMG h t
def c5:Prop :=
  ∀ (b:fO) (e :Bool) (h:ℕ),0<h→h≤(row b).declaredHi →
    ∀ (D:jF h),NodeUnits D → ∀ (Crt:zG D) (word:I→L),
      let t:=cy b e
      ∀ W a,W+(3*h)*a≤ aU t → ∀ P∈c9 Crt word t W,
        Yd D a P∈c9 Crt word t (W+(3*h)*a)
def c6:Prop :=
  ∀ (b:fO) (h:ℕ),0<h→h≤(row b).declaredHi →
    ∀ (D:jF h),NodeUnits D → ∀ (Crt:zG D) (word:I→L) (f :ko),
      0<f.degreeOf (some 2) →
      let t:=cy b true
      (∀ W≤ aU t,∀ P∈c9 Crt word t W,
        f^(1+(aU t-W)/(3*h))∣bC P) →
      lz L (c9 Crt word t (aU t))≤layerCeiling (row b).declaredHi t
private theorem source_rank (h1 :c1) (h2 :c2) (h3:c3)
    (b:fO) (e :Bool) {h:ℕ} (hh:0<h) (hd:h≤(row b).declaredHi)
    {D:jF h} (Crt:zG D) (word:I→L) :
    required b e≤lz L (c9 Crt word (cy b e) (aU (cy b e))) := by
  let t:=cy b e
  let V:=Aw h t (aU t)
  have hb:=(h1 b e h hd).2
  let:Module.Finite L V:=(h1 b e h hd).1
  let U:I→Submodule L jK:= fun i=>ays t (ad0 i) (word i)
  have hU:TT V (amm t word)≤ contactDebit t:= by
    have hlocal (i:I) (_:i∈(univ :Finset I)) :
        TT V (U i)≤(t.shape.U+1)*t.avF:=h2 b e h _ _
    have H :=bCP V (univ :Finset I) U _ hlocal
    have hcard: (univ :Finset I).card = 262144 :=Fintype.card_fin (2^18)
    rw [Finset.inf_univ_eq_iInf,hcard] at H
    exact H
  have hC:TT V (btN Crt t)≤eMG h t:=h3 b e h hh hd D Crt
  have hp:=(bXt V (amm t word) (btN Crt t)).trans (Nat.add_le_add hU hC)
  change required b e+contactDebit t+eMG h t≤lz L V at hb
  change lz L V-Module.finrank L (c9 Crt word t (aU t))≤_ at hp
  change required b e≤lz L (c9 Crt word t (aU t))
  omega
private theorem band_bounds (b:fO) :
  0<(jX b).lo∧(jX b).hi≤(row b).declaredHi∧(cy b true).shape.U<p:= by
 fin_cases b <;> decide
private theorem choose_nonzero (S:Submodule L jK) (hS:1≤lz L S) :
  ∃ P∈S,P≠0:= by
 obtain ⟨rs,hi⟩:=exists_linearIndependent_of_le_finrank (R:=L) (M := ↥S) hS
 exact ⟨(rs 0).val,(rs 0).property,fun hz=>hi.ne_zero 0 (Subtype.ext hz)⟩
end
end q7IA62d
