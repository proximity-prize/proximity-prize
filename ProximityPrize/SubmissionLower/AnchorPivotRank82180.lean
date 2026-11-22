import ProximityPrize.SubmissionLower.AnchorPivotFactors82180

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

namespace AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder orderCutoff bandCount bandSpace_finite finrank_bandSpace)
open SoundnessAnchor (blockAt)
open MvPolynomial
open scoped BigOperators

abbrev Factor := Fin 8 × ℕ
def measure : List Factor → Data
  | [] => Data.unit
  | (i,k)::xs => ((basisData i).times k).plus (measure xs)
noncomputable def product : List Factor → Form
  | [] => 1
  | (i,k)::xs => basisPoly i^k * product xs
theorem product_ok (xs : List Factor) : Sound (measure xs) (product xs) := by
  induction xs with
  | nil => exact sound_one
  | cons t ts ih => exact ((basis_ok t.1).pow t.2).mul ih

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
def Row.good (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = 48 ∧ r.index ≤ x.lo ∧ x.hi ≤ 48 ∧ x.top ≤ 10 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)

def accept (s : ℕ) (g : ℤ) (r : Row) : Bool :=
  decide (-g ≤ (r.index : ℤ) ∧ (orderCutoff s g).toNat ≤ r.ord)

private theorem band_mono {d a b : ℕ} {l h l' h' : ℤ} (hl : l' ≤ l) (hh : h ≤ h') (ht : a ≤ b) :
    bandSpace d l h a ≤ bandSpace d l' h' b := by
  intro p hp
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro e he
  obtain ⟨hd,hlo,hhi,hf⟩ := (MvPolynomial.mem_restrictSupport_iff Geom).mp hp he
  exact ⟨hd,hl.trans hlo,hhi.trans hh,hf.trans ht⟩

private theorem row_kernel (s : ℕ) (g : ℤ) (r : Row) (hv : r.good = true)
    (ha : accept s g r = true) :
    ∃ w : LinearMap.ker (blockAt 48 s g), ((w.val : Form) = r.form) ∧
      (encode (w.val : Form)).degree = (r.tag : ℕ) := by
  obtain ⟨hd,hl,hh,ht,ho,hk⟩ := of_decide_eq_true hv
  obtain ⟨hl',ho'⟩ := of_decide_eq_true ha
  have hb := r.sound.band
  rw [hd] at hb
  let w : bandSpace 48 (-g) 48 10 := ⟨r.form,
    band_mono (hl'.trans (Int.ofNat_le.mpr hl)) (by exact_mod_cast hh) ht hb⟩
  have hw : w ∈ LinearMap.ker (blockAt 48 s g) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ (ho'.trans ho) r.sound.contact
  exact ⟨⟨w,hw⟩,rfl,r.sound.degree.trans (congrArg (fun n : ℕ => (n : WithBot ℕ)) hk)⟩

private theorem independent {V ι : Type} [AddCommGroup V] [Module Geom V] [Fintype ι]
    (f : V →ₗ[Geom] Polynomial Geom) (v : ι → V) (tag : ι → ℕ) (inj : Function.Injective tag)
    (hdeg : ∀ i, (f (v i)).degree = (tag i : ℕ)) : LinearIndependent Geom v := by
  classical
  refine (Fintype.linearIndependent_iff (v := v)).mpr ?_
  intro w hw j
  by_contra hj
  let a := Finset.univ.filter fun i => w i ≠ 0
  obtain ⟨i,hi,hiMax⟩ := a.exists_max_image tag
    ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  have hwi := (Finset.mem_filter.mp hi).2
  let t := (Polynomial.lcoeff Geom (tag i)).comp f
  have hz := congrArg t hw
  simp only [map_sum,map_smul,map_zero] at hz
  rw [Finset.sum_eq_single i] at hz
  · change w i * (f (v i)).coeff (tag i) = 0 at hz
    have hn : f (v i) ≠ 0 := fun h => by simpa [h] using hdeg i
    have hd := Polynomial.natDegree_eq_of_degree_eq_some (hdeg i)
    rw [← hd,Polynomial.coeff_natDegree] at hz
    exact (mul_ne_zero hwi (Polynomial.leadingCoeff_ne_zero.mpr hn)) hz
  · intro b _ hbi
    by_cases hb : w b = 0
    · simp [hb]
    · have lt : tag b < tag i := lt_of_le_of_ne
        (hiMax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)) (fun e => hbi (inj e))
      change w b * (f (v b)).coeff (tag i) = 0
      rw [Polynomial.coeff_eq_zero_of_degree_lt (by rw [hdeg]; exact WithBot.coe_lt_coe.mpr lt),mul_zero]
  · simp

theorem count_bound (rows : List Row) (s : ℕ) (g : ℤ)
    (good : ∀ r ∈ rows, r.good = true)
    (sorted : rows.Pairwise fun a b => a.tag < b.tag) :
    Module.finrank Geom (LinearMap.range (blockAt 48 s g)) + (rows.filter (accept s g)).length ≤
      bandCount 48 (-g) 48 10 := by
  classical
  let use := rows.filter (accept s g)
  have memb (i : Fin use.length) : use.get i ∈ rows ∧ accept s g (use.get i) = true :=
    List.mem_filter.mp (List.get_mem use i)
  have hsort : use.Pairwise (fun a b => a.tag < b.tag) := sorted.sublist (List.filter_sublist ..)
  have hmono : StrictMono (fun i : Fin use.length => (use.get i).tag) :=
    fun _ _ h => hsort.rel_get_of_lt h
  have h (i : Fin use.length) := row_kernel s g (use.get i) (good _ (memb i).1) (memb i).2
  let w (i : Fin use.length) := Classical.choose (h i)
  let embed : LinearMap.ker (blockAt 48 s g) →ₗ[Geom] Polynomial Geom :=
    encode.toLinearMap.comp ((bandSpace 48 (-g) 48 10).subtype.comp (LinearMap.ker (blockAt 48 s g)).subtype)
  have hw := independent embed w _ hmono.injective (fun i => (Classical.choose_spec (h i)).2)
  letI : Module.Finite Geom (bandSpace 48 (-g) 48 10) := bandSpace_finite _ _ _ _
  have hc := hw.fintype_card_le_finrank
  have hd := (blockAt 48 s g).finrank_range_add_finrank_ker
  rw [finrank_bandSpace] at hd
  simpa only [Fintype.card_fin] using
    ((Nat.add_le_add_left hc (Module.finrank Geom (LinearMap.range (blockAt 48 s g)))).trans_eq hd)

#print axioms count_bound
end AnchorPivot82180
