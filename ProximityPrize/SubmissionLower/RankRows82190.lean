import ProximityPrize.SubmissionLower.AnchorPivotRank82180
import ProximityPrize.SubmissionLower.AnchorNinth82190
import ProximityPrize.SubmissionLower.AnchorBlock82190

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

namespace RankRows82190
open AnchorPivot82180 (Data Sound E encode mon sound_monomial monoData sound_one)
open AnchorPivot82190 (allData allPoly all_ok)
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder orderCutoff bandCount bandSpace_finite finrank_bandSpace)
open AnchorBlock82190 (blockAt)
open MvPolynomial
open scoped BigOperators

abbrev Factor := Fin 9 × ℕ
def measure : List Factor → Data
  | [] => Data.unit
  | (i,k)::xs => ((allData i).times k).plus (measure xs)
noncomputable def product : List Factor → Form
  | [] => 1
  | (i,k)::xs => allPoly i^k * product xs
theorem product_ok (xs : List Factor) : Sound (measure xs) (product xs) := by
  induction xs with
  | nil => exact sound_one
  | cons t ts ih => exact ((all_ok t.1).pow t.2).mul ih

structure Row where
  tag : ℕ
  index : ℕ
  ord : ℕ
  e : E
  factors : List Factor
  deriving DecidableEq
def Row.bounds (r : Row) := (monoData r.e).plus (measure r.factors)
noncomputable def Row.form (r : Row) := mon r.e * product r.factors
theorem Row.sound (r : Row) : Sound r.bounds r.form :=
  (sound_monomial r.e).mul (product_ok r.factors)
def Row.good (r : Row) (d : ℕ) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 48 ∧ x.top ≤ 12 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)

def accept (s : ℕ) (g : ℤ) (r : Row) : Bool :=
  decide (-g ≤ (r.index : ℤ) ∧ (orderCutoff s g).toNat ≤ r.ord)

private theorem band_mono {d a b : ℕ} {l h l' h' : ℤ} (hl : l' ≤ l) (hh : h ≤ h') (ht : a ≤ b) :
    bandSpace d l h a ≤ bandSpace d l' h' b := by
  intro p hp
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro e he
  obtain ⟨hd,hlo,hhi,hf⟩ := (MvPolynomial.mem_restrictSupport_iff Geom).mp hp he
  exact ⟨hd,hl.trans hlo,hhi.trans hh,hf.trans ht⟩

private theorem row_kernel (d s : ℕ) (g : ℤ) (r : Row) (hv : r.good d = true)
    (ha : accept s g r = true) :
    ∃ w : LinearMap.ker (blockAt d s g), ((w.val : Form) = r.form) ∧
      (encode (w.val : Form)).degree = (r.tag : ℕ) := by
  obtain ⟨hd,hl,hh,ht,ho,hk⟩ := of_decide_eq_true hv
  obtain ⟨hl',ho'⟩ := of_decide_eq_true ha
  have hb := r.sound.band
  rw [hd] at hb
  let w : bandSpace d (-g) 48 12 := ⟨r.form,
    band_mono (hl'.trans (Int.ofNat_le.mpr hl)) (by exact_mod_cast hh) ht hb⟩
  have hw : w ∈ LinearMap.ker (blockAt d s g) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ (ho'.trans ho) r.sound.contact
  exact ⟨⟨w,hw⟩,rfl,r.sound.degree.trans (congrArg (fun n : ℕ => (n : WithBot ℕ)) hk)⟩

open private independent from ProximityPrize.SubmissionLower.AnchorPivotRank82180

theorem count_bound (rows : List Row) (d s : ℕ) (g : ℤ)
    (good : ∀ r ∈ rows, r.good d = true)
    (sorted : rows.Pairwise fun a b => a.tag < b.tag) :
    Module.finrank Geom (LinearMap.range (blockAt d s g)) + (rows.filter (accept s g)).length ≤
      bandCount d (-g) 48 12 := by
  classical
  let use := rows.filter (accept s g)
  have memb (i : Fin use.length) : use.get i ∈ rows ∧ accept s g (use.get i) = true :=
    List.mem_filter.mp (List.get_mem use i)
  have hsort : use.Pairwise (fun a b => a.tag < b.tag) := sorted.sublist (List.filter_sublist ..)
  have hmono : StrictMono (fun i : Fin use.length => (use.get i).tag) :=
    fun _ _ h => hsort.rel_get_of_lt h
  have h (i : Fin use.length) := row_kernel d s g (use.get i) (good _ (memb i).1) (memb i).2
  let w (i : Fin use.length) := Classical.choose (h i)
  let embed : LinearMap.ker (blockAt d s g) →ₗ[Geom] Polynomial Geom :=
    encode.toLinearMap.comp ((bandSpace d (-g) 48 12).subtype.comp (LinearMap.ker (blockAt d s g)).subtype)
  have hw := independent embed w _ hmono.injective (fun i => (Classical.choose_spec (h i)).2)
  letI : Module.Finite Geom (bandSpace d (-g) 48 12) := bandSpace_finite _ _ _ _
  have hc := hw.fintype_card_le_finrank
  have hd := (blockAt d s g).finrank_range_add_finrank_ker
  rw [finrank_bandSpace] at hd
  simpa only [Fintype.card_fin] using
    ((Nat.add_le_add_left hc (Module.finrank Geom (LinearMap.range (blockAt d s g)))).trans_eq hd)

end RankRows82190
