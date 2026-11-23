import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
import ProximityPrize.SubmissionLower.R6960Low6960WidthAffine

set_option Elab.async false
set_option maxRecDepth 2400
namespace Low6960Rectangle
open K1_13 (Shape InBox)
open Low6960RetainedCut (cutPrice contractedPrice)
open Low6960Prices (tiltedSurface tiltedFits)
open Low6960Allocation (Band MassCell start order allowance weight_mono order_mono)

/-- A tilted-surface price certificate for a width interval of one index and degree. -/
def PaidTilted {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) : Prop :=
  0<l ∧ l≤order cells ⟨b,j,0⟩ ∧ 1≤t ∧ 3*t+3≤j ∧ j+1≤b ∧
    cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) ≤
      allowance k ((start k).t+t) b j t

instance {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    Decidable (PaidTilted cells t b j B l) := inferInstanceAs (Decidable (_ ∧ _))

theorem tilted {k : Band} {cells : List (MassCell k)} {a : Shape} {b j B t l : ℕ}
    (h : PaidTilted cells t b j B l) (hb : b≤a.b) (hB : a.b≤B)
    (hj : a.j=j) (ht : a.t=t) :
    ∃ l, 0<l ∧ l≤order cells a ∧ contractedPrice a (start k) l 165≤
      allowance k ((start k).t+a.t) a.b a.j a.t := by
  obtain ⟨lp,lo,ht',hj',hw,fee⟩ := h
  cases a with
  | mk a d z =>
    change d=j at hj
    change z=t at ht
    subst d z
    have geom : tiltedFits ⟨a,j,t⟩ := ⟨hj',hw.trans hb⟩
    have hprice : contractedPrice ⟨a,j,t⟩ (start k) l 165 ≤
        cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) := by
      unfold contractedPrice
      dsimp only
      rw [ite_eq_left geom]
      exact min_le_right _ _
    have ha : 3*t≤j := by omega
    have mono := Low6960WidthAffine.tilted_width_mono (hullOf k l) (hw.trans hb) hB ht' hj'
    have hcut : cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) ≤
        cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) := by
      have box : InBox ⟨a,j,t⟩ ⟨B,j,t⟩ := ⟨hB,le_rfl,le_rfl⟩
      rw [cut_eq,cut_eq]
      exact charge_mono box ha ha l 1920 mono
    exact ⟨l,lp,lo.trans (order_mono cells hb le_rfl), hprice.trans
      (hcut.trans (fee.trans (Nat.div_le_div_right
        (Nat.mul_le_mul_left _ (weight_mono k hb le_rfl le_rfl)))))⟩

#print axioms tilted
end Low6960Rectangle
