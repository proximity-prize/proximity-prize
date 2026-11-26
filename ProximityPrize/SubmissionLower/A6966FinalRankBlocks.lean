import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import ProximityPrize.SubmissionLower.AnchorNinth82190
import ProximityPrize.SubmissionLower.DdZQtCuFa
import ProximityPrize.SubmissionLower.DdZW31ykd
import ProximityPrize.SubmissionLower.DdZdwiBha
import ProximityPrize.SubmissionLower.Fast076

section Merged6967_A6966FinalRankBlocks
set_option Elab.async false




set_option Elab.async false

-- merged module A6966AnchorBlock
section Merged_A6966AnchorBlock
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace A6966AnchorBlock
open K1_13 K1_13_1_1 MvPolynomial
open SoundnessAnchor (Powers)
noncomputable section




end
end A6966AnchorBlock

end Merged_A6966AnchorBlock

-- merged module A6966Rows
section Merged_A6966Rows

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

namespace A6966Rows
open AnchorPivot82180 (Data Sound E encode mon sound_monomial monoData sound_one)
open AnchorPivot82190 (allData allPoly all_ok)
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder orderCutoff bandCount bandSpace_finite finrank_bandSpace)
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


theorem band_mono {d a b : ℕ} {l h l' h' : ℤ} (hl : l' ≤ l) (hh : h ≤ h') (ht : a ≤ b) :
    bandSpace d l h a ≤ bandSpace d l' h' b := by
  intro p hp
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro e he
  obtain ⟨hd,hlo,hhi,hf⟩ := (MvPolynomial.mem_restrictSupport_iff Geom).mp hp he
  exact ⟨hd,hl.trans hlo,hhi.trans hh,hf.trans ht⟩


open AnchorPivot82180 (independent)


end A6966Rows

end Merged_A6966Rows

-- merged module A6966FinalRankCore
section Merged_A6966FinalRankCore

namespace A6966FinalRankCore
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace bandCount backShift targetOrder bandSpace_finite finrank_bandSpace)
open AnchorPivot82180 (encode)
open MvPolynomial
open scoped BigOperators
open A6966Rows (band_mono)
open AnchorPivot82180 (independent)

abbrev Row := A6966Rows.Row

def orderCutoff (s : ℕ) (g : ℤ) : ℤ := 106 - (s : ℤ) - g

private def accept (s : ℕ) (g : ℤ) (r : Row) : Bool :=
  decide (-g ≤ (r.index : ℤ) ∧ (orderCutoff s g).toNat ≤ r.ord)

noncomputable def blockAt (d s : ℕ) (g : ℤ) : bandSpace d (-g) 58 15 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _

def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 58 ∧ x.top ≤ 15 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)

def gradeFee (s : ℕ) (rows : List Row) : ℕ :=
  (rows.map (fun r => 106 + r.index - (s + r.ord))).sum

def covers (d : ℕ) (rows : List Row) : Prop :=
  ∀ i : Fin 59, bandCount d (i.val : ℤ) 58 15 ≤
    (rows.filter (fun r => decide (i.val ≤ r.index))).length

private theorem row_kernel (d s : ℕ) (g : ℤ) (r : Row) (hv : good d r = true)
    (ha : accept s g r = true) :
    ∃ w : LinearMap.ker (blockAt d s g), ((w.val : Form) = r.form) ∧
      (encode (w.val : Form)).degree = (r.tag : ℕ) := by
  obtain ⟨hd,hl,hh,ht,ho,hk⟩ := of_decide_eq_true hv
  obtain ⟨hl',ho'⟩ := of_decide_eq_true ha
  have hb := r.sound.band
  rw [hd] at hb
  let w : bandSpace d (-g) 58 15 := ⟨r.form,
    band_mono (hl'.trans (Int.ofNat_le.mpr hl)) (by exact_mod_cast hh) ht hb⟩
  have hw : w ∈ LinearMap.ker (blockAt d s g) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ (ho'.trans ho) r.sound.contact
  exact ⟨⟨w,hw⟩,rfl,r.sound.degree.trans (congrArg (fun n : ℕ => (n : WithBot ℕ)) hk)⟩



theorem count_bound (rows : List Row) (d s : ℕ) (g : ℤ)
    (good : ∀ r ∈ rows, good d r = true)
    (sorted : rows.Pairwise fun a b => a.tag < b.tag) :
    Module.finrank Geom (LinearMap.range (blockAt d s g)) + (rows.filter (accept s g)).length ≤
      bandCount d (-g) 58 15 := by
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
    encode.toLinearMap.comp ((bandSpace d (-g) 58 15).subtype.comp (LinearMap.ker (blockAt d s g)).subtype)
  have hw := independent embed w _ hmono.injective (fun i => (Classical.choose_spec (h i)).2)
  let : Module.Finite Geom (bandSpace d (-g) 58 15) := bandSpace_finite _ _ _ _
  have hc := hw.fintype_card_le_finrank
  have hd := (blockAt d s g).finrank_range_add_finrank_ker
  rw [finrank_bandSpace] at hd
  simpa only [Fintype.card_fin] using
    ((Nat.add_le_add_left hc (Module.finrank Geom (LinearMap.range (blockAt d s g)))).trans_eq hd)


private def charge (s : ℕ) (g : ℤ) (r : Row) : ℕ :=
  if -g ≤ (r.index : ℤ) ∧ r.ord < (orderCutoff s g).toNat then 1 else 0

private theorem filter_split (s : ℕ) (g : ℤ) (rows : List Row) :
    (rows.filter (fun r => decide (-g ≤ (r.index : ℤ)))).length =
      (rows.filter (accept s g)).length + (rows.map (charge s g)).sum := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    by_cases hi : -g ≤ (r.index : ℤ) <;> by_cases ho : (orderCutoff s g).toNat ≤ r.ord <;>
      simp [hi,ho,accept,charge,lt_iff_not_ge,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem coverage_at {d : ℕ} {rows : List Row} (hc : covers d rows)
    (g : ℤ) (hg : -58 ≤ g) :
    bandCount d (-g) 58 15 ≤ (rows.filter (fun r => decide (-g ≤ (r.index : ℤ)))).length := by
  let i : Fin 59 := ⟨(-g).toNat,by omega⟩
  have hn (c f : ℕ) : max (0 : ℤ) (-g - 2*c - 3*f) =
      max 0 ((i.val : ℤ) - 2*c - 3*f) := by dsimp [i]; omega
  have hh : bandCount d (-g) 58 15 = bandCount d (i.val : ℤ) 58 15 := by
    simp only [bandCount,hn]
  have he (r : Row) : (-g ≤ (r.index : ℤ)) ↔ (i.val ≤ r.index) := by dsimp [i]; omega
  simp_rw [hh,he]
  exact hc i

private theorem charge_offsets (s : ℕ) (r : Row) :
    (∑ i : Fin 164, charge s ((i.val : ℤ) - 58) r) ≤ 106 + r.index - (s + r.ord) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => charge s ((i : ℤ) - 58) r)]
  unfold charge
  rw [Finset.sum_boole]
  have hs : (Finset.range 164).filter (fun i : ℕ => -((i : ℤ) - 58) ≤ r.index ∧
      r.ord < (orderCutoff s ((i : ℤ) - 58)).toNat) ⊆
      Finset.Ico (58 - r.index) (164 - (s + r.ord)) := by
    intro i hi
    obtain ⟨_,a,b⟩ := Finset.mem_filter.mp hi
    unfold orderCutoff at b
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have h := Finset.card_le_card hs
  rw [Nat.card_Ico] at h
  exact h.trans (by omega)

private theorem list_charge_offsets (s : ℕ) (rows : List Row) :
    (∑ i : Fin 164, (rows.map (charge s ((i.val : ℤ) - 58))).sum) ≤ gradeFee s rows := by
  induction rows with
  | nil => simp [gradeFee]
  | cons r rows ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
    exact Nat.add_le_add (charge_offsets s r) ih

/-- Sum the individual rank charges once per pivot across all offsets of one grade. -/
theorem grade_bound (s d : ℕ) (rows : List Row) (hg : ∀ r ∈ rows, good d r = true)
    (hs : rows.Pairwise fun a b => a.tag < b.tag) (hc : covers d rows) :
    (∑ i : Fin 164, Module.finrank Geom (LinearMap.range (blockAt d s ((i.val : ℤ) - 58)))) ≤
      gradeFee s rows := by
  apply le_trans (Finset.sum_le_sum (g := fun i : Fin 164 =>
    (rows.map (charge s ((i.val : ℤ) - 58))).sum) ?_) (list_charge_offsets s rows)
  intro i _
  let g := (i.val : ℤ) - 58
  have h := count_bound rows d s g hg hs
  have u := coverage_at hc g (by dsimp [g]; omega)
  rw [filter_split s g rows] at u
  change Module.finrank Geom (LinearMap.range (blockAt d s g)) ≤ (rows.map (charge s g)).sum
  omega

#print axioms grade_bound

end A6966FinalRankCore

end Merged_A6966FinalRankCore

-- merged module A6966FinalRankBlocks
section Merged_A6966FinalRankBlocks

/- Use the homogeneous-block decomposition in K1_13_1_1 with the
   homogenizing degree supplied by the anchor cap. -/
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace A6966FinalRankBlocks
noncomputable section
open K1_13 K1_13_1_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open A6966FinalAnchorSpace
open scoped BigOperators
open K1_13_1_1 (liftJets liftJets_X lift_value liftImage liftPower liftVar lift_order lift_value_order project_monomial jet_index_formula value_hom source_monomial_expr form_monomial_expr merge merge_single)

private abbrev Local := LocalPolynomial Geom 3
private abbrev T : Local := MvPolynomial.X (localT 3)
private def offset (i : Fin 164) : ℤ := (i : ℕ) - (58 : ℤ)

private abbrev selectedBlock (s : ℕ) (g : ℤ) :=
  A6966FinalRankCore.blockAt (cap s) s g

private def postprocess (s : ℕ) (g : ℤ) : Form →ₗ[Geom] Local :=
  (projectLowContact 164).comp
    ((LinearMap.mulLeft Geom (T ^ (g + 58).toNat *
      (liftJets valueForm) ^ (s - cap s))).comp liftJets.toLinearMap)
private theorem postprocess_truncate (s : ℕ) (g : ℤ) (hg : -58 ≤ g) {P : Form}
    (hP : P.IsWeightedHomogeneous (fun _ => (1 : ℕ)) (cap s)) :
    postprocess s g (weightedTruncation targetOrder (A6966FinalRankCore.orderCutoff s g).toNat P) =
      postprocess s g P := by
  let d := cap s
  let cutoff := (A6966FinalRankCore.orderCutoff s g).toNat
  let H := filterSupport (fun e : Fin 4 →₀ ℕ => ¬ e.weight targetOrder < cutoff) P
  have hsplit : weightedTruncation targetOrder cutoff P + H = P :=
    filterSupport_add_filterSupport_not _ _
  have hH : H ∈ restrictWeightedOrder (fun j => 1 + targetOrder j) (d + cutoff) := by
    refine mem_restrictWeightedOrder.mpr fun e he => ?_
    have hc := mem_support_iff.mp he
    change (filterSupport _ P).coeff e ≠ 0 at hc
    rw [coeff_filterSupport] at hc
    by_cases hl : e.weight targetOrder < cutoff
    · simp [hl] at hc
    · have hd := hP (d := e) (by simpa [hl] using hc)
      rw [← Finsupp.degree_eq_weight_one] at hd
      have hw : e.weight (fun j => 1 + targetOrder j) = e.degree + e.weight targetOrder := by
        rw [Finsupp.degree_eq_sum, Finsupp.weight_eq_sum, Finsupp.weight_eq_sum,
          ← Finset.sum_add_distrib]
        simp [Nat.mul_add]
      rw [hw, hd]
      exact Nat.add_le_add_left (Nat.le_of_not_lt hl) d
  have ht : (T ^ (g + 58).toNat) ∈
      restrictWeightedOrder (localContactWeight 3) ((g + 58).toNat * 1) :=
    pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ _ (localContactWeight_T 3).ge) _
  have hf := pow_mem_restrictWeightedOrder lift_value_order (s - d)
  have hh := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder ht hf)
    (bind₁_mem_restrictWeightedOrder lift_order hH)
  have hc : 164 ≤ ((g + 58).toNat * 1 + (s-d) * 1) + (d + cutoff) := by
    have hd : d ≤ s := cap_le_grade s
    dsimp [cutoff, A6966FinalRankCore.orderCutoff]
    omega
  have hz : postprocess s g H = 0 :=
    (weightedTruncation_eq_zero_iff _ _ _).mpr (restrictWeightedOrder_anti _ hc hh)
  calc
    postprocess s g (weightedTruncation targetOrder cutoff P) =
        postprocess s g (weightedTruncation targetOrder cutoff P + H) := by rw [map_add, hz, add_zero]
    _ = postprocess s g P := by rw [hsplit]
private def trimmed (u : JetVariable 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  u.some - Finsupp.single 0 (u.some.degree - cap u.some.degree)
private theorem trimmed_other (u : JetVariable 3 →₀ ℕ) (j : Fin 4) (h : j ≠ 0) :
    trimmed u j = u (some j) := by
  simp [trimmed, Ne.symm h]
private theorem trimmed_id (u : JetVariable 3 →₀ ℕ) :
    (trimmed u).weight jetIndex = u.some.weight jetIndex := by
  rw [jet_index_formula, jet_index_formula]
  rw [trimmed_other u 1 (by decide), trimmed_other u 2 (by decide), trimmed_other u 3 (by decide)]
  simp
private theorem trimmed_value_and_degree (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) :
    trimmed u 0 + (u.some.degree - cap u.some.degree) = u (some 0) ∧
      (trimmed u).degree = cap u.some.degree := by
  have htotal : u.some.degree = u (some 0) + u (some 1) + u (some 2) + u (some 3) := by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have hj : u (some 1) + u (some 2) + u (some 3) ≤ 58 := by
    have hi := hu.2.1
    change u.some.weight jetIndex ≤ 58 at hi
    rw [jet_index_formula] at hi
    simp only [Finsupp.some_apply] at hi
    omega
  have hcap := cap_of_grade hj (by omega) hu.2.2.2.1
  have htrim : trimmed u 0 =
      u (some 0) - (u.some.degree - cap u.some.degree) := by
    simp [trimmed]
  have hnew : (trimmed u).degree =
      trimmed u 0 + u (some 1) + u (some 2) + u (some 3) := by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_four, trimmed_other u 1 (by decide),
      trimmed_other u 2 (by decide), trimmed_other u 3 (by decide)]
  have hle := cap_le_grade u.some.degree
  omega
private theorem trimmed_mem_band (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) :
    BandExponent (cap u.some.degree) (-((u none : ℤ) - u.some.weight jetIndex))
      58 15 (trimmed u) := by
  refine ⟨(trimmed_value_and_degree u hu).2, ?_, ?_, ?_⟩
  · rw [trimmed_id]
    omega
  · rw [trimmed_id]
    exact_mod_cast hu.2.1
  · rw [trimmed_other u 3 (by decide)]
    exact hu.2.2.1
private theorem backShift_hom (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) (a : Geom) :
    (backShift (monomial (trimmed u) a)).IsWeightedHomogeneous
      (fun _ => (1 : ℕ)) (cap u.some.degree) := by
  have h := isWeightedHomogeneous_monomial (fun _ : Fin 4 => (1 : ℕ)) (trimmed u) a
    (m := cap u.some.degree)
    (by rw [← Finsupp.degree_eq_weight_one, (trimmed_value_and_degree u hu).2])
  apply h.bind₁
  intro j
  split_ifs
  · exact value_hom
  · exact isWeightedHomogeneous_X _ _ _
private theorem shifted_substitution (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) (a : Geom) :
    T ^ 58 * unscaledLocalSubstitution 3 0 0 (monomial u a) =
      T ^ (((u none : ℤ) - u.some.weight jetIndex) + 58).toNat *
        (liftJets valueForm) ^ (u.some.degree - cap u.some.degree) *
        liftJets (backShift (monomial (trimmed u) a)) := by
  have hi := hu.2.1
  change u.some.weight jetIndex ≤ 58 at hi
  let r := (((u none : ℤ) - u.some.weight jetIndex) + 58).toNat
  have ht : r + u.some.weight jetIndex = u none + 58 := by dsimp [r]; omega
  rw [jet_index_formula] at ht
  simp only [Finsupp.some_apply] at ht
  have hv := (trimmed_value_and_degree u hu).1
  have h1 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 1)) =
      MvPolynomial.X (localY (0 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 0
  have h2 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 2)) =
      MvPolynomial.X (localY (1 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 1
  have h3 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 3)) =
      MvPolynomial.X (localY (2 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 2
  have b0 : backShift (MvPolynomial.X 0) = valueForm := by simp [backShift]
  have b (j : Fin 4) (hj : j ≠ 0) : backShift (MvPolynomial.X j) = MvPolynomial.X j := by
    simp [backShift, hj]
  rw [source_monomial_expr, form_monomial_expr]
  simp only [map_mul, map_pow, algHom_C, algebraMap_eq, unscaledLocalSubstitution_X, map_zero,
    zero_add, ← lift_value, h1, h2, h3, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide),
    trimmed_other u 1 (by decide), trimmed_other u 2 (by decide), trimmed_other u 3 (by decide),
    liftJets_X]
  have hpow : T ^ r * T ^ u (some 1) * (T ^ 2) ^ u (some 2) * (T ^ 3) ^ u (some 3) =
      T ^ (u none + 58) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ = T ^ (u none + 58) * MvPolynomial.C a * liftJets valueForm ^ u (some 0) *
        MvPolynomial.X (localY (0 : Fin 3)) ^ u (some 1) *
        MvPolynomial.X (localY (1 : Fin 3)) ^ u (some 2) *
        MvPolynomial.X (localY (2 : Fin 3)) ^ u (some 3) := by rw [pow_add]; ring
    _ = _ := by
      rw [← hpow, ← hv, pow_add]
      simp [liftImage, liftPower, liftVar, mul_pow]
      ring
private theorem shift_projection (P : Local) :
    T ^ 58 * projectLowContact 106 P = projectLowContact 164 (T ^ 58 * P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      have hmul : T ^ 58 * monomial e a = monomial (Finsupp.single (localT 3) 58 + e) a := by
        rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, one_mul]
      rw [project_monomial, hmul, project_monomial]
      have ho : localContactOrder 3 (Finsupp.single (localT 3) 58 + e) =
          58 + localContactOrder 3 e := by
        simp [localContactOrder, Finsupp.weight_single]
      have hlt : localContactOrder 3 (Finsupp.single (localT 3) 58 + e) < 164 ↔
          localContactOrder 3 e < 106 := by rw [ho]; omega
      by_cases he : localContactOrder 3 e < 106
      · simp [he, hlt.mpr he, hmul]
      · have hnot : ¬ localContactOrder 3 (Finsupp.single (localT 3) 58 + e) < 164 :=
          fun h => he (hlt.mp h)
        simp [he, hnot]
  | add P Q hP hQ => simp only [map_add, mul_add, hP, hQ]
private theorem shifted_constraint_monomial (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u)
    (a : Geom) :
    let s := u.some.degree
    let g := (u none : ℤ) - u.some.weight jetIndex
    T ^ 58 * localConstraintAt 106 0 0 (monomial u a) =
      postprocess s g (selectedBlock s g ⟨monomial (trimmed u) a,
        (monomial_mem_restrictSupport (R := Geom)).mpr (Or.inl (trimmed_mem_band u hu))⟩) := by
  dsimp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [shift_projection, shifted_substitution u hu]
  have hi := hu.2.1
  change u.some.weight jetIndex ≤ 58 at hi
  let s := u.some.degree
  let g : ℤ := (u none : ℤ) - u.some.weight jetIndex
  let P := backShift (monomial (trimmed u) a)
  change postprocess s g P = postprocess s g
    (weightedTruncation targetOrder (A6966FinalRankCore.orderCutoff s g).toNat P)
  exact (postprocess_truncate s g (by dsimp [g]; omega) (backShift_hom u hu a)).symm
private theorem selected_zero (s : ℕ) (g : ℤ) (h : 106 - (s : ℤ) ≤ g) :
    selectedBlock s g = 0 := by
  apply LinearMap.ext
  intro q
  change weightedTruncation targetOrder (A6966FinalRankCore.orderCutoff s g).toNat (backShift q) = 0
  have hcut : (A6966FinalRankCore.orderCutoff s g).toNat = 0 := by unfold A6966FinalRankCore.orderCutoff; omega
  rw [hcut, weightedTruncation_eq_zero_iff, restrictWeightedOrder_zero]
  trivial
private abbrev Block := Fin 143 × Fin 164
private abbrev Image (b : Block) := LinearMap.range (selectedBlock b.1 (offset b.2))
private def assemble : (∀ b : Block, Image b) →ₗ[Geom] Local :=
  merge (fun b => postprocess b.1 (offset b.2))
private theorem postprocess_mem_assemble (b : Block) (s : ℕ) (g : ℤ)
    (hs : (b.1 : ℕ) = s) (hg : offset b.2 = g)
    (q : bandSpace (cap s) (-g) 58 15) :
    postprocess s g (selectedBlock s g q) ∈ LinearMap.range assemble := by
  subst s
  subst g
  let v : Image b := ⟨selectedBlock b.1 (offset b.2) q, LinearMap.mem_range_self _ q⟩
  exact ⟨Pi.single b v, merge_single (fun j : Block => postprocess j.1 (offset j.2)) b v⟩
private theorem shifted_monomial_mem_assemble (u : JetVariable 3 →₀ ℕ)
    (hu : AnchorEligible u) (a : Geom) :
    T ^ 58 * localConstraintAt 106 0 0 (monomial u a) ∈ LinearMap.range assemble := by
  classical
  let s := u.some.degree
  let g : ℤ := (u none : ℤ) - u.some.weight jetIndex
  let q : bandSpace (cap s) (-g) 58 15 :=
    ⟨monomial (trimmed u) a, (monomial_mem_restrictSupport (R := Geom)).mpr (Or.inl (trimmed_mem_band u hu))⟩
  have hmono : T ^ 58 * localConstraintAt 106 0 0 (monomial u a) =
      postprocess s g (selectedBlock s g q) := shifted_constraint_monomial u hu a
  rw [hmono]
  by_cases hg : g < 106
  · have hJ := hu.2.1
    change u.some.weight jetIndex ≤ 58 at hJ
    have hs : s < 143 := by exact Nat.lt_succ_of_le hu.1
    have hr : (g + 58).toNat < 164 := by dsimp [g] at *; omega
    let b : Block := (⟨s, hs⟩, ⟨(g + 58).toNat, hr⟩)
    have ho : offset b.2 = g := by dsimp [b, offset, g]; omega
    exact postprocess_mem_assemble b s g rfl ho q
  · rw [selected_zero s g (by omega), LinearMap.zero_apply, map_zero]
    exact Submodule.zero_mem _
theorem origin_le_blocks :
    Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤
      ∑ s : Fin 143, ∑ r : Fin 164,
        Module.finrank Geom (LinearMap.range (A6966FinalRankCore.blockAt (cap s) s ((r : ℕ) - (58 : ℤ)))) := by
  classical
  let shift := LinearMap.mulLeft Geom (T ^ 58)
  have hshift : Function.Injective shift :=
    fun _ _ h => mul_left_cancel₀ (pow_ne_zero _ (MvPolynomial.X_ne_zero _)) h
  let shifted := shift.comp (anchorLocal 0 0)
  have hdim : Module.finrank Geom (LinearMap.range shifted) =
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
    rw [LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective shift hshift _).finrank_eq.symm
  have hsub : LinearMap.range shifted ≤ LinearMap.range assemble := by
    rintro _ ⟨Q, rfl⟩
    change shift (localConstraintAt 106 0 0 (Q : DifferentialPolynomial Geom 3)) ∈ _
    rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
    exact Submodule.sum_mem _ fun u hu => shifted_monomial_mem_assemble u (Q.property hu) _
  have (b : Block) : Module.Finite Geom (Image b) := by
    have : Module.Finite Geom (bandSpace (cap b.1) (-offset b.2) 58 15) :=
      restrictSupport_finite ((Finsupp.finite_of_degree_le _).subset fun _ he =>
        Nat.le_of_eq he.1)
    infer_instance
  calc
    _ = Module.finrank Geom (LinearMap.range shifted) := hdim.symm
    _ ≤ Module.finrank Geom (LinearMap.range assemble) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank Geom (∀ b : Block, Image b) := LinearMap.finrank_range_le assemble
    _ = _ := by
      rw [Module.finrank_pi_fintype, Fintype.sum_prod_type]
      rfl

#print axioms origin_le_blocks

end
end A6966FinalRankBlocks

end Merged_A6966FinalRankBlocks

end Merged6967_A6966FinalRankBlocks

section Merged6967_Fast077
set_option Elab.async false



set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (σ : Type) [Finite σ] (s : σ → Fin 5) (A C : Finset (σ →₀ ℕ)),
    outside C ⊆ outside A → ∃ p q : Form,
      Represents p (fun t => sliceCount s A t) ∧
      Represents q (fun t => sliceCount s C t) ∧ TopNonnegative (p - q)
def c2 : Prop :=
  ∀ (B : Boxes) (P : Ideal GeoJets5) (t : Grade), (∀ j, 0 < t j) → ∀ N : ℕ,
    gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
      affineHilbertFunction (diagonalIdeal B P t) N
private theorem top_coeff_mono {p q : Form} {a : Grade}
    (hp : p.totalDegree ≤ a.degree) (hq : q.totalDegree ≤ a.degree)
    (h : TopNonnegative (p - q)) : q.coeff a ≤ p.coeff a := by
  have hd : (p - q).totalDegree ≤ a.degree :=
    (totalDegree_sub p q).trans (max_le hp hq)
  exact sub_nonneg.mp (by simpa only [coeff_sub] using h a hd)
theorem of_children (hcounts : c1) (hdiag : c2) :
    K1_13_6_2_4.c1 := by
  intro B _ P I i hi hdim D hbox hreg
  change mixedDegree B (sectionIdeal P D) I ≤ mixedDegree B P (insert i I)
  let P₁ := sectionIdeal P D
  let P₂ := sectionIdeal P (D ^ 2)
  obtain ⟨f, g, hf, hg, hcf, hle₁, hcg, hle₂⟩ := exists_regular_lifts B P i D hbox hreg
  obtain ⟨hhom₁, hex₁⟩ := homogeneous_cut_exact (slot B) (gradedIdeal B P)
    (gradedIdeal_homogeneous B P) i f hf
  obtain ⟨hhom₂, hex₂⟩ := homogeneous_cut_exact (slot B) (gradedIdeal B P₂)
    (gradedIdeal_homogeneous B P₂) i g hg
  rw [hcf] at hex₁
  rw [hcg] at hex₂
  obtain ⟨p, _, hp, _, _⟩ := forms_of_counts hcounts (Generator B) (slot B) (gradedIdeal B P) (gradedIdeal B P)
    (gradedIdeal_homogeneous B P) (gradedIdeal_homogeneous B P) le_rfl
  obtain ⟨q, p₂, hq, hp₂, hpos₂⟩ := forms_of_counts hcounts (Generator B) (slot B)
    (gradedIdeal B P ⊔ Ideal.span {f}) (gradedIdeal B P₂) hhom₁
    (gradedIdeal_homogeneous B P₂) hle₁
  obtain ⟨r, p₁, hr, hp₁, hpos₁⟩ := forms_of_counts hcounts (Generator B) (slot B)
    (gradedIdeal B P₂ ⊔ Ideal.span {g}) (gradedIdeal B P₁) hhom₂
    (gradedIdeal_homogeneous B P₁) hle₂
  have hqeq : q = backwardDiff i p := eq_sub_previous i hq hp hp hex₁
  have hreq : r = p₂ - previous i p₁ := eq_sub_previous i hr hp₂ hp₁ hex₂
  have hreg₂ : IsLeftRegular (Ideal.Quotient.mk P (D ^ 2)) := by
    rw [map_pow]
    exact IsLeftRegular.pow 2 hreg
  have hdp := gradedIdeal_degree_le B P hdim hp (hdiag B P)
  have hdp₁ := gradedIdeal_degree_le B P₁ (dim_le_after_section hreg hdim) hp₁ (hdiag B P₁)
  have hdp₂ := gradedIdeal_degree_le B P₂ (dim_le_after_section hreg₂ hdim) hp₂ (hdiag B P₂)
  have hdq : q.totalDegree ≤ I.card := by
    rw [hqeq]
    exact backwardDiff_degree_le i hdp
  have hdr : r.totalDegree ≤ I.card := by
    rw [hreq]
    exact (totalDegree_sub _ _).trans (max_le hdp₂ (previous_degree_le i hdp₁))
  have hdeg := squarefree_degree I
  have hm₂ := top_coeff_mono (hdq.trans_eq hdeg.symm) (hdp₂.trans_eq hdeg.symm) hpos₂
  have hm₁ := top_coeff_mono (hdr.trans_eq hdeg.symm) (hdp₁.trans_eq hdeg.symm) hpos₁
  rw [hqeq, backwardDiff_coeff_squarefree i hi hdp] at hm₂
  rw [hreq, coeff_sub, previous_coeff i (squarefree I) (hdp₁.trans_eq hdeg.symm)] at hm₁
  have hscaled : 2 * p₁.coeff (squarefree I) ≤ p.coeff (squarefree (insert i I)) := by
    linarith only [hm₁, hm₂]
  rw [mixedDegree_eq B P₁ I hp₁ (hdiag B P₁), mixedDegree_eq B P (insert i I) hp (hdiag B P)]
  rw [Finset.card_insert_of_notMem hi, pow_succ]
  refine (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) I.card)
    (mul_pos (pow_pos (by norm_num : (0 : ℚ) < 2) I.card) (by norm_num))).mpr ?_
  convert mul_le_mul_of_nonneg_right hscaled
    (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) I.card) using 1 <;> ring
end
end K1_13_6_2_4_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1_2
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 K1_13_6_2_4_1 MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private theorem diagonal_add (B : Boxes) (s t : Grade) :
    diagonalExponents B (s + t : Grade) = diagonalExponents B s + diagonalExponents B t := by
  ext m
  constructor
  · rintro ⟨u, hu, rfl⟩
    let v (i : Fin 5) (j : Fin (s i)) := u i (Fin.castAdd (t i) j)
    let w (i : Fin 5) (j : Fin (t i)) := u i (Fin.natAdd (s i) j)
    refine ⟨∑ i, ∑ j, v i j, ⟨v, fun i j => hu i _, rfl⟩,
      ∑ i, ∑ j, w i j, ⟨w, fun i j => hu i _, rfl⟩, ?_⟩
    simp only [v, w, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (Fin.sum_univ_add (u i)).symm)
  · rintro ⟨a, ⟨v, hv, rfl⟩, b, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨fun i => Fin.append (v i) (w i), ?_, ?_⟩
    · intro i
      exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hv i j)
        (fun j => by simpa only [Fin.append_right] using hw i j)
    · change (∑ i, ∑ j, v i j) + (∑ i, ∑ j, w i j) =
          ∑ i, ∑ j : Fin (s i + t i), Fin.append (v i) (w i) j
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa only [Fin.append_left, Fin.append_right] using
        (Fin.sum_univ_add (Fin.append (v i) (w i))).symm
private theorem diagonal_zero (B : Boxes) : diagonalExponents B (0 : Grade) = 0 := by
  ext m
  rw [Set.mem_zero]
  constructor
  · rintro ⟨u, _, rfl⟩
    simp
  · rintro rfl
    exact ⟨fun _ j => j.elim0, fun _ j => j.elim0, by simp⟩
private theorem diagonal_nsmul (B : Boxes) (t : Grade) (n : ℕ) :
    diagonalExponents B (n • t : Grade) = n • diagonalExponents B t := by
  induction n with
  | zero => simpa only [zero_smul] using diagonal_zero B
  | succ n ih => simp only [succ_nsmul, diagonal_add, ih]
private theorem zero_mem_lattice (B : Boxes) (i : Fin 5) : 0 ∈ latticePoints (B i) :=
  allowed_zero _
private theorem zero_mem_diagonal (B : Boxes) (t : Grade) : 0 ∈ diagonalExponents B t :=
  ⟨fun _ _ => 0, fun i _ => zero_mem_lattice B i, by simp⟩
private theorem generator_mem_diagonal {B : Boxes} (v : Generator B) :
    v.2.val ∈ diagonalExponents B (slotWeight (slot B) v) := by
  classical
  let a (i : Fin 5) : Exponent := if i = v.1 then v.2.val else 0
  refine ⟨fun i _ => a i, ?_, ?_⟩
  · intro i _
    by_cases h : i = v.1
    · subst i
      simpa only [a, ite_eq_left rfl] using v.2.property
    · simpa only [a, ite_eq_right h] using zero_mem_lattice B i
  · symm
    calc
      (∑ i, ∑ _j : Fin (slotWeight (slot B) v i), a i) =
          ∑ i, (slotWeight (slot B) v i) • a i :=
        Finset.sum_congr rfl fun i _ => Fin.sum_const _ _
      _ = v.2.val := by
        change (∑ i, (Finsupp.single v.1 (1 : ℕ) i) • a i) = _
        refine (Finset.sum_eq_single v.1 ?_ ?_).trans ?_
        · intro i _ h
          simp [a, h]
        · simp
        · simp [a]
private theorem tagged_monomial (B : Boxes) (d : Generator B →₀ ℕ) (c : GeoField) :
    taggedMap B (monomial d c) =
      monomial (Finsupp.weight (fun v : Generator B => v.2.val) d) c := by
  rw [taggedMap, aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  simp only [monomial_pow, one_pow, ← monomial_sum_one, algebraMap_eq, C_mul_monomial, mul_one]
private theorem tagged_exponent_mem (B : Boxes) (d : Generator B →₀ ℕ) :
    Finsupp.weight (fun v : Generator B => v.2.val) d ∈
      diagonalExponents B (Finsupp.weight (slotWeight (slot B)) d) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using zero_mem_diagonal B (0 : Grade)
  | add a b ha hb => simpa only [map_add, diagonal_add] using Set.add_mem_add ha hb
  | single v n =>
      have hmem : n • v.2.val ∈ n • diagonalExponents B (slotWeight (slot B) v) := by
        induction n with
        | zero => simp
        | succ n ih =>
            simpa only [succ_nsmul] using Set.add_mem_add ih (generator_mem_diagonal v)
      simpa only [Finsupp.weight_single, diagonal_nsmul] using hmem
private theorem tagged_lift {B : Boxes} {g : Grade} {m : Exponent}
    (hm : m ∈ diagonalExponents B g) :
    ∃ a : SlotRing B, a ∈ piece (slot B) g ∧ taggedMap B a = monomial m 1 := by
  classical
  obtain ⟨u, hu, rfl⟩ := hm
  let v (i : Fin 5) (j : Fin (g i)) : Generator B := ⟨i, ⟨u i j, hu i j⟩⟩
  let d : Generator B →₀ ℕ := ∑ i, ∑ j, Finsupp.single (v i j) 1
  have hg : Finsupp.weight (slotWeight (slot B)) d = g := by
    simp only [d, map_sum, Finsupp.weight_single, one_smul, slotWeight, slot, v, Fin.sum_const]
    ext i
    rw [Finsupp.finsetSum_apply]
    simp [unitGrade, Finsupp.single_apply]
  refine ⟨monomial d 1, isWeightedHomogeneous_monomial _ _ _ hg, ?_⟩
  simp only [tagged_monomial, d, map_sum, Finsupp.weight_single, one_smul, v]
private theorem tagged_image (B : Boxes) (g : Grade) :
    (piece (slot B) g).map (taggedMap B).toLinearMap =
      restrictSupport GeoField (diagonalExponents B g) := by
  apply le_antisymm
  · have hpiece : piece (slot B) g =
        restrictSupport GeoField {d | Finsupp.weight (slotWeight (slot B)) d = g} :=
      weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
    rw [Submodule.map_le_iff_le_comap, hpiece, restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨d, hd, rfl⟩
    change taggedMap B (monomial d 1) ∈ restrictSupport GeoField (diagonalExponents B g)
    rw [tagged_monomial, monomial_mem_restrictSupport]
    exact Or.inl ((show Finsupp.weight (slotWeight (slot B)) d = g from hd) ▸
      tagged_exponent_mem B d)
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha, heq⟩ := tagged_lift hm
    exact ⟨a, ha, heq⟩
private theorem monomial_preimage {S : Set Exponent} {n : ℕ} {m : Exponent} (hm : m ∈ n • S) :
    ∃ a : MvPolynomial S GeoField, a.totalDegree ≤ n ∧
      monomialMap GeoField S a = monomial m 1 := by
  induction n generalizing m with
  | zero =>
      rw [zero_smul, Set.mem_zero] at hm
      subst m
      exact ⟨1, by simp, by simp⟩
  | succ n ih =>
      rw [succ_nsmul] at hm
      obtain ⟨b, hb, c, hc, rfl⟩ := hm
      obtain ⟨a, ha, hφ⟩ := ih hb
      refine ⟨a * MvPolynomial.X ⟨c, hc⟩, (totalDegree_mul _ _).trans ?_, ?_⟩
      · simpa only [totalDegree_X] using Nat.add_le_add_right ha 1
      · rw [map_mul, hφ, monomialMap_X, monomial_mul_monomial, one_mul]
theorem affine_image (S : Set Exponent) (h0 : 0 ∈ S) (n : ℕ) :
    (restrictTotalDegree S GeoField n).map (monomialMap GeoField S).toLinearMap =
      restrictSupport GeoField (n • S) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact monomialMap_mem_restrictSupport_nsmul h0 ((mem_restrictTotalDegree S n a).mp ha)
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha, hφ⟩ := monomial_preimage hm
    exact ⟨a, (mem_restrictTotalDegree S n a).mpr ha, hφ⟩
theorem quotient_image_finrank {A : Type*} [CommRing A] [Algebra GeoField A]
    (V : Submodule GeoField A) (I : Ideal A) (P : Ideal GeoJets5) (φ : A →ₐ[GeoField] GeoJets5)
    (hle : I ≤ P.comap φ) (hker : ∀ a ∈ V, φ a ∈ P → a ∈ I) :
    Module.finrank GeoField (V.map (Ideal.Quotient.mkₐ GeoField I).toLinearMap) =
      Module.finrank GeoField ((V.map φ.toLinearMap).map
        (Ideal.Quotient.mkₐ GeoField P).toLinearMap) := by
  let W := V.map (Ideal.Quotient.mkₐ GeoField I).toLinearMap
  let f := Ideal.quotientMapₐ P φ hle
  have hinj : Function.Injective (f.toLinearMap.domRestrict W) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨x, hx⟩ hx0
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    change Ideal.Quotient.mk P (φ a) = 0 at hx0
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker a ha (Ideal.Quotient.eq_zero_iff_mem.mp hx0))
  have hmap : W.map f.toLinearMap =
      (V.map φ.toLinearMap).map (Ideal.Quotient.mkₐ GeoField P).toLinearMap := by
    simp only [W, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap, f,
      Ideal.quotient_map_comp_mkₐ]
  rw [← hmap, ← LinearMap.range_domRestrict W f.toLinearMap]
  exact (LinearEquiv.ofInjective _ hinj).finrank_eq
theorem proof : K1_13_6_2_4_1.c2 := by
  intro B P t _ n
  let S := diagonalExponents B t
  change Module.finrank GeoField
      ((piece (slot B) (n • t)).map (Ideal.Quotient.mkₐ GeoField (gradedIdeal B P)).toLinearMap) =
    Module.finrank GeoField
      ((restrictTotalDegree S GeoField n).map
        (Ideal.Quotient.mkₐ GeoField (diagonalIdeal B P t)).toLinearMap)
  have hle : gradedIdeal B P ≤ P.comap (taggedMap B) :=
    Ideal.toIdeal_homogeneousCore_le (piece (slot B)) _
  have hgraded := quotient_image_finrank (piece (slot B) (n • t)) (gradedIdeal B P) P
    (taggedMap B) hle (fun _ ha => (mem_gradedIdeal_of_grade ha).mpr)
  have haffine := quotient_image_finrank (restrictTotalDegree S GeoField n) (diagonalIdeal B P t) P
    (monomialMap GeoField S) le_rfl (fun _ _ h => h)
  rw [hgraded, haffine, tagged_image B (n • t), affine_image S (zero_mem_diagonal B t) n,
    diagonal_nsmul]
end
end K1_13_6_2_4_1_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1_1
open K1_13_6_2_4_1 MvPolynomial
open scoped BigOperators
private theorem represents_cell_sum {σ : Type} [Fintype σ] (s : σ → Fin 5)
    (b : σ →₀ ℕ) (A : Finset (σ →₀ ℕ)) (hA : ∀ a ∈ A, a ≤ b) :
    Represents (∑ u ∈ cells (b := b) A, cellForm s u) (fun t => sliceCount s A t) := by
  refine ⟨b.degree + 1, fun t ht => ?_⟩
  change eval (fun j => (t j : ℚ)) (∑ u ∈ cells (b := b) A, cellForm s u) =
    (sliceCount s A t : ℚ)
  rw [map_sum, sliceCount_eq_sum s b A hA, Nat.cast_sum]
  exact Finset.sum_congr rfl fun u _ => cellForm_eval s u t (fun j => Nat.lt_of_succ_le (ht j))
theorem proof : K1_13_6_2_4_1.c1 := by
  classical
  intro σ _ s A C h
  let _ := Fintype.ofFinite σ
  let b := (A ∪ C).sup id
  let U := cells (b := b) A
  let V := cells (b := b) C
  refine ⟨∑ u ∈ U, cellForm s u, ∑ u ∈ V, cellForm s u, ?_, ?_, ?_⟩
  · exact represents_cell_sum s b A (fun _ ha => Finset.le_sup (f := id) (Finset.mem_union_left C ha))
  · exact represents_cell_sum s b C (fun _ hc => Finset.le_sup (f := id) (Finset.mem_union_right A hc))
  · rw [← Finset.sum_sdiff (cells_mono (b := b) h) (f := cellForm s), add_sub_cancel_right]
    exact top_sum _ _ (fun u _ => cellForm_top s u)
end K1_13_6_2_4_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_1
noncomputable section
open K1_13_6 K1_13_7_1 K1_13_7_1_1_1 MvPolynomial
open K1_13_6_2_4_1 (Grade Form Represents TopNonnegative gradedHilbert piece slotWeight
  outside sliceCount standard_piece_rank)
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (A : Fin 4 → Set Exponent) (B : Set Exponent), admissible A B →
    ∀ (P : Ideal GeoJets) (t : Grade),
      gradedHilbert (tagSlot A B) (tagIdeal A B P) t =
        hilbertRank A B P (t 4) (fun i => t i.castSucc)
def c2 : Prop :=
  ∀ (σ : Type) [Finite σ] (s : σ → Fin 5) (T : Finset (σ →₀ ℕ)),
    ∃ p : Form, Represents p (fun t => sliceCount s T t) ∧ TopNonnegative p
private theorem graded_footprint (σ : Type) [Finite σ] (s : σ → Fin 5)
    (J : Ideal (MvPolynomial σ GeoField)) (hJ : J.IsHomogeneous (piece s)) :
    ∃ T : Finset (σ →₀ ℕ), ∀ t : Grade, gradedHilbert s J t = sliceCount s T t := by
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨T, hT⟩ := m.exists_finset_standardExponents_iff J
  have hstandard : m.standardExponents J = outside T := Set.ext hT
  refine ⟨T, fun t => ?_⟩
  rw [standard_piece_rank s m J hJ t, hstandard]
  rfl
private theorem form_of_rank (himage : c1) (hcounts : c2)
    {A : Fin 4 → Set Exponent} {B : Set Exponent} (hAB : admissible A B) (P : Ideal GeoJets) :
    ∃ p : Form, Represents p (fun t => (hilbertRank A B P (t 4) (fun i => t i.castSucc) : ℚ)) ∧
      TopNonnegative p := by
  let : ∀ j, Finite (slotSupport A B j) := fun j => by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · unfold slotSupport
      rw [Fin.lastCases_last]
      exact hAB.2.1.to_subtype
    · unfold slotSupport
      rw [Fin.lastCases_castSucc]
      exact (hAB.1 i).1.to_subtype
  let J := tagIdeal A B P
  let s := tagSlot A B
  have hJ : J.IsHomogeneous (piece s) :=
    ((P.comap (tagEval A B)).homogeneousCore (piece s)).isHomogeneous
  obtain ⟨T, hT⟩ := graded_footprint (TaggedVar A B) s J hJ
  obtain ⟨p, ⟨N, hN⟩, hp⟩ := hcounts (TaggedVar A B) s T
  refine ⟨p, ⟨N, fun t ht => ?_⟩, hp⟩
  exact (hN t ht).trans
    (congrArg (fun n : ℕ => (n : ℚ)) ((hT t).symm.trans (himage A B hAB P t)))
private theorem zero_mem_copies {S : Set Exponent} (h : 0 ∈ S) (n : ℕ) : 0 ∈ n • S := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    simpa only [zero_add] using Set.add_mem_add ih h
private theorem finrank_of_contains_one {K R : Type} [Field K] [CommRing R] [Algebra K R]
    (e : R ≃ₐ[K] K) (S : Submodule K R) (h : 1 ∈ S) :
    Module.finrank K S = 1 := by
  have htop : S = ⊤ := by
    apply top_unique
    intro r _
    have hs : (e r) • (1 : R) = r := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv ((e r) • (1 : R)) = (e r) • (e 1) :=
          e.toLinearEquiv.map_smul (e r) 1
        _ = e.toLinearEquiv r := by
          change (e r) • (e 1) = e r
          have he : e (1 : R) = (1 : K) := map_one e
          rw [he, smul_eq_mul, mul_one]
    exact hs ▸ S.smul_mem (e r) h
  calc
    Module.finrank K S = Module.finrank K (⊤ : Submodule K R) :=
      congrArg (fun T : Submodule K R => Module.finrank K T) htop
    _ = Module.finrank K R := finrank_top K R
    _ = Module.finrank K K := e.toLinearEquiv.finrank_eq
    _ = 1 := Module.finrank_self K
private theorem eval_piece_finrank {K : Type} [Field K] (y : Fin 4 → K)
    {T : Set Exponent} (hT : 0 ∈ T) :
    Module.finrank K ((restrictSupport K T).map
      (Ideal.Quotient.mkₐ K (RingHom.ker (eval y))).toLinearMap) = 1 := by
  let f : MvPolynomial (Fin 4) K →ₐ[K] K := aeval y
  have hf : Function.Surjective f := fun c => ⟨C c, by simp [f]⟩
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let q := Ideal.Quotient.mkₐ K (RingHom.ker f.toRingHom)
  have h1 : (1 : MvPolynomial (Fin 4) K) ∈ restrictSupport K T := by
    rw [MvPolynomial.one_def]
    exact (monomial_mem_restrictSupport K).mpr (Or.inl hT)
  have hm : 1 ∈ (restrictSupport K T).map q.toLinearMap :=
    Submodule.mem_map.mpr ⟨1, h1, q.map_one⟩
  exact finrank_of_contains_one e _ hm
private theorem point_hilbert {A : Fin 4 → Set Exponent} {B : Set Exponent} (hAB : admissible A B)
    (y : GeoPoint) (b : ℕ) (w : Grades) : hilbert A B (pointIdeal y) b w = 1 := by
  have hzero {S T : Set Exponent} (hs : 0 ∈ S) (ht : 0 ∈ T) : 0 ∈ S + T := by
    simpa only [zero_add] using Set.add_mem_add hs ht
  have hz : 0 ∈ gradedExponents A B b w :=
    hzero (hzero (hzero (hzero (zero_mem_copies hAB.2.2.1 b)
      (zero_mem_copies (hAB.1 0).2 (w 0)))
      (zero_mem_copies (hAB.1 1).2 (w 1)))
      (zero_mem_copies (hAB.1 2).2 (w 2)))
      (zero_mem_copies (hAB.1 3).2 (w 3))
  unfold hilbert
  rw [eval_piece_finrank y hz, Nat.cast_one]
theorem of_children (himage : c1) (hcounts : c2) : K1_13_7_1_1_1.c1 := by
  classical
  intro A B hAB
  have hex (i : Fin 5) (P : Ideal GeoJets) (hd : affineDim P = 4 - i.val) :
      ∃ d : ℝ, 0 ≤ d ∧ IsMixedDegree A B P i.val d := by
    obtain ⟨p, hp, hpos⟩ := form_of_rank himage hcounts hAB P
    exact mixed_of_polynomial hp i ((polynomial_degree_bound hAB P hp).trans_eq hd) hpos
  let D (i : Fin 5) (P : Ideal GeoJets) : ℝ :=
    if i = 4 ∧ P ∈ Set.range pointIdeal then 1
    else if hd : affineDim P = 4 - i.val then Classical.choose (hex i P hd) else 0
  refine ⟨D, ?_, fun y => ite_eq_left ⟨rfl, ⟨y, rfl⟩⟩⟩
  intro i P _ hd
  by_cases h : i = 4 ∧ P ∈ Set.range pointIdeal
  · have hD : D i P = 1 := ite_eq_left h
    rw [hD]
    obtain ⟨rfl, y, rfl⟩ := h
    refine ⟨zero_le_one, 0, ?_⟩
    have hz : remainingDirections (4 : Fin 5).val = [] := by decide
    intro b w s _ _
    have he : 4 - (4 : Fin 5).val = 0 := by decide
    rw [hz, he]
    change hilbert A B (pointIdeal y) b w = (s : ℝ) ^ (0 : ℕ) * 1
    rw [point_hilbert hAB y b w, pow_zero, mul_one]
  · have hD : D i P = Classical.choose (hex i P hd) := by
      dsimp only [D]
      rw [ite_eq_right h, dite_eq_left hd]
    rw [hD]
    exact Classical.choose_spec (hex i P hd)
end
end K1_13_7_1_1_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_1_1
noncomputable section
open K1_13_6 K1_13_6_2_4_1 K1_13_7_1_1_1 K1_13_7_1_1_1_1 K1_13_7_1_1_1_2
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private theorem slotSupport_eq (A : Fin 4 → Set Exponent) (B : Set Exponent) :
    slotSupport A B = supportIn A B := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [slotSupport, Fin.lastCases_last, supportIn_last]
  · rw [slotSupport, Fin.lastCases_castSucc, supportIn_castSucc]
theorem proof : K1_13_7_1_1_1_1.c1 := by
  intro A B hAB P t
  let rankFor (S : Fin 5 → Set Exponent) : ℕ :=
    let s : ((j : Fin 5) × S j) → Fin 5 := Sigma.fst
    let f : MvPolynomial ((j : Fin 5) × S j) GeoField →ₐ[GeoField] GeoJets :=
      aeval fun v => monomial v.2.val 1
    gradedHilbert s ((P.comap f).homogeneousCore (piece s)).toIdeal t
  have hRank : gradedHilbert (tagSlot A B) (tagIdeal A B P) t =
      gradedHilbert (slot A B) (liftIdeal A B P) t :=
    congrArg rankFor (slotSupport_eq A B)
  rw [hRank]
  have h := K1_13_7_1_1_1_2_2.proof A B hAB P (gridOf t)
  change (gradedHilbert (slot A B) (liftIdeal A B P) (multigrade (gridOf t)) : ℝ) =
    (hilbertRank A B P (t 4) (fun i => t i.castSucc) : ℝ) at h
  rw [multigrade_gridOf] at h
  exact_mod_cast h
end
end K1_13_7_1_1_1_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_1_2
open K1_13_6_2_4_1 K1_13_6_2_4_1_1 MvPolynomial
open scoped BigOperators
theorem proof : K1_13_7_1_1_1_1.c2 := by
  classical
  intro σ _ s T
  let _ := Fintype.ofFinite σ
  let b := T.sup id
  have hb : ∀ a ∈ T, a ≤ b := fun _ ha => Finset.le_sup (f := id) ha
  refine ⟨∑ u ∈ cells (b := b) T, cellForm s u, ?_, ?_⟩
  · refine ⟨b.degree + 1, fun t ht => ?_⟩
    change eval (fun j => (t j : ℚ)) (∑ u ∈ cells (b := b) T, cellForm s u) =
      (sliceCount s T t : ℚ)
    rw [map_sum, sliceCount_eq_sum s b T hb, Nat.cast_sum]
    exact Finset.sum_congr rfl fun u _ => cellForm_eval s u t (fun j => Nat.lt_of_succ_le (ht j))
  · exact top_sum _ _ (fun u _ => cellForm_top s u)
end K1_13_7_1_1_1_1_2
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 K1_13_7_1 MvPolynomial Filter
open K1_13_6_2_3_2_5 (ray_top totalDegree_le_of_ray_degree deltas_top shapeSum_add shapeSum_step)
private def finiteMonomialOrder (σ : Type) [Finite σ] : MonomialOrder σ := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let _ : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact MonomialOrder.degLex
private theorem form_of_cap {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Shape)
    (hs : ∀ i, Chamber (s i)) (J : Ideal GeoJets) (used : List ι) :
    let H := fun a => (supportRank J (capExponents (shapeSum s a)) : ℚ)
    ∃ F : MvPolynomial ι ℚ, (∀ᶠ a in atTop, eval (fun i => (a i : ℚ)) F = H a) ∧
      ∀ᶠ a in atTop, 0 ≤ deltas used H a := by
  classical
  let σ := CapVar s
  let m := finiteMonomialOrder σ
  let I := capIdeal s J
  let slot := capSlot s
  obtain ⟨A, hA⟩ := m.exists_finset_standardExponents_iff I
  have hzero : outside ({0} : Finset (σ →₀ ℕ)) = ∅ := by
    ext e
    simp [outside, zero_le]
  obtain ⟨⟨F, hF⟩, hpos⟩ := K1_13_6_2_3_2_1.proof slot A {0}
    (by rw [hzero]; exact Set.empty_subset _)
  have hcount (a : ι → ℕ) :
      sliceCount slot A a - sliceCount slot {0} a =
        (supportRank J (capExponents (shapeSum s a)) : ℚ) := by
    have hset : m.standardExponents I = outside A := Set.ext hA
    have hstd := standard_rank slot m I (K1_13_6_2_3_2_3.proof s J).1 a
    rw [hset] at hstd
    have he : sliceCount slot A a = hilbert slot I a := hstd.symm
    rw [he, (K1_13_6_2_3_2_3.proof s J).2 a, weak_packing s hs]
    simp [sliceCount, hzero]
  exact ⟨F, by simpa only [hcount] using hF, by simpa only [hcount] using hpos used⟩
private theorem deltas_congr_of_ge {ι : Type} [DecidableEq ι]
    (used : List ι) {F G : (ι → ℕ) → ℚ} {u : ι → ℕ}
    (h : ∀ a ≥ u, F a = G a) (a : ι → ℕ) (ha : u ≤ a) :
    deltas used F a = deltas used G a := by
  induction used generalizing a with
  | nil => exact h a ha
  | cons i rest ih =>
    simp only [deltas, ih a ha, ih (a + step i) (ha.trans fun j => Nat.le_add_right _ _)]
theorem proof : K1_13_7_2_3_1_2.c2 := by
  intro J _ hJ p q hp hq
  let s : Fin 3 → Shape := ![⟨3, 3, 1⟩, p, q]
  let used : List (Fin 3) := [1, 2]
  have hs (i : Fin 3) : Chamber (s i) := by
    fin_cases i
    · change Chamber ⟨3, 3, 1⟩
      exact ⟨by decide, by decide⟩
    · exact hp
    · exact hq
  have hbase : 0 < (s 0).t := by
    change 0 < (1 : ℕ)
    decide
  obtain ⟨F, hF, hpos⟩ := form_of_cap s hs J used
  obtain ⟨u, hu⟩ := eventually_atTop.mp hF
  have hray (v : Fin 3 → ℕ) (hv : 0 < v 0) :=
    weak_ray_compare s J 0 hs hbase F u hu v hv used.length hJ.le
  have hdeg : F.totalDegree ≤ used.length :=
    (totalDegree_le_of_ray_degree F u (dimension J) (fun v hv => (hray v (hv 0)).1)).trans hJ.le
  let G := fun v : Fin 3 → ℕ => eval (fun i => (v i : ℚ)) (homogeneousComponent used.length F)
  have hG (v : Fin 3 → ℕ) (hv : step 0 ≤ v) :
      G v = capCoeff J used.length (shapeSum s v) := by
    have hv₀ : 0 < v 0 :=
      Nat.zero_lt_one.trans_le (by simpa [step] using hv 0)
    exact (ray_top F u v hdeg).symm.trans (hray v hv₀).2
  obtain ⟨a, ha, hau⟩ := (hpos.and (eventually_ge_atTop u)).exists
  have hnon : 0 ≤ deltas used (fun v => capCoeff J used.length (shapeSum s v)) (step 0) := calc
    _ ≤ deltas used (fun v => (supportRank J (capExponents (shapeSum s v)) : ℚ)) a := ha
    _ = deltas used (fun v => eval (fun i => (v i : ℚ)) F) a :=
      (deltas_congr_of_ge used hu a hau).symm
    _ = deltas used G (step 0) := deltas_top used (by decide) F hdeg a (step 0)
    _ = _ := deltas_congr_of_ge used hG (step 0) le_rfl
  have hs₀ : s 0 = ⟨3, 3, 1⟩ := rfl
  have hs₁ : s 1 = p := rfl
  have hs₂ : s 2 = q := rfl
  have hpol : 0 ≤ polarize (capCoeff J 2) [p, q] ⟨3, 3, 1⟩ := by
    simpa only [used, deltas, shapeSum_add, shapeSum_step, hs₀, hs₁, hs₂, polarize,
      List.length_cons, List.length_nil, Nat.reduceAdd] using hnon
  unfold mixedDegree
  exact div_nonneg hpol (by positivity)
end
end K1_13_7_2_3_1_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_10_1_1
noncomputable section
open K1 K1_10 K1_10_1 K1_11 K1_11_2 MvPolynomial
private abbrev lift5 {F : Type*} [Field F] :=
  Polynomial.toMvPolynomial (R := F) (0 : Fin 5)
private def pencil5 {F : Type*} [Field F] (z : Fin 5) (A : Fin 2 → Polynomial F) :
    MvPolynomial (Fin 5) F :=
  lift5 (A 0) + lift5 (A 1) * MvPolynomial.X z
private def output5 {F : Type*} [Field F] (O : Fin 2 → Fin 2 → Polynomial F) :
    MvPolynomial (Fin 5) F :=
  pencil5 3 (fun j => O j 0) + pencil5 3 (fun j => O j 1) * MvPolynomial.X 4
private theorem lift5_view (P : Polynomial K) :
    polynomialView (lift5 P) = Polynomial.C (liftOrdinary P) := by
  have h : (polynomialView (F := K)).toRingHom.comp (lift5 (F := K)).toRingHom =
      Polynomial.C.comp liftOrdinary := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [lift5, liftOrdinary, polynomialView, finSuccEquiv_apply]
    · simp [lift5, liftOrdinary, polynomialView_X]
  exact RingHom.congr_fun h P
private theorem planeRelation_eq (U V : Fin 2 → Polynomial K)
    (O : Fin 2 → Fin 2 → Polynomial K) :
    planeRelation U V O =
      pencil5 4 U * MvPolynomial.X 1 + pencil5 3 V * MvPolynomial.X 2 - output5 O := by
  have h1 : polynomialView (F := K) (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 1) :=
    polynomialView_X 1
  have h2 : polynomialView (F := K) (MvPolynomial.X 2) = Polynomial.X :=
    polynomialView_X 2
  have h3 : polynomialView (F := K) (MvPolynomial.X 3) = Polynomial.C (MvPolynomial.X 2) :=
    polynomialView_X 3
  have h4 : polynomialView (F := K) (MvPolynomial.X 4) = Polynomial.C (MvPolynomial.X 3) :=
    polynomialView_X 4
  apply (polynomialView (F := K)).injective
  simp only [planeRelation_view, pencil5, output5, map_sub, map_add, map_mul,
    lift5_view, h1, h2, h3, h4, denominator, numerator, pencil]
  ring
variable {F : Type*} [Field F]
private theorem lift5_support (P : Polynomial F) (e : Fin 5 →₀ ℕ) :
    e ∈ (lift5 P).support ↔ ∃ n ∈ P.support, e = Finsupp.single 0 n := by
  classical
  let f : Unit → Fin 5 := fun _ => 0
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  change e ∈ (Polynomial.toMvPolynomial (0 : Fin 5) P).support ↔ _
  rw [Polynomial.toMvPolynomial_eq_rename_comp]
  change e ∈ (rename f ((uniqueAlgEquiv F Unit).symm P)).support ↔ _
  rw [support_rename_of_injective hf, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d default, ?_, ?_⟩
    · simpa only [MvPolynomial.mem_support_iff, coeff_uniqueAlgEquiv_symm, Polynomial.mem_support_iff] using hd
    · calc
        Finsupp.mapDomain f d = Finsupp.mapDomain f (Finsupp.single default (d default)) :=
          congrArg (Finsupp.mapDomain f) (Finsupp.unique_single d)
        _ = Finsupp.single 0 (d default) := by rw [Finsupp.mapDomain_single]
  · rintro ⟨n, hn, rfl⟩
    refine ⟨Finsupp.single default n, ?_, ?_⟩
    · simpa only [MvPolynomial.mem_support_iff, coeff_uniqueAlgEquiv_symm, Finsupp.single_eq_same,
        Polynomial.mem_support_iff] using hn
    · rw [Finsupp.mapDomain_single]
private theorem lift5_degree (P : Polynomial F) (i : Fin 5) :
    (lift5 P).degreeOf i = if i = 0 then P.natDegree else 0 := by
  rw [degreeOf_eq_sup]
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    obtain ⟨n, hn, rfl⟩ := (lift5_support P e).mp he
    by_cases hi : i = 0
    · subst i
      simpa using Polynomial.le_natDegree_of_mem_supp n hn
    · simp [hi]
  · by_cases hi : i = 0
    · subst i
      by_cases hz : P = 0
      · simp [hz]
      have he := (lift5_support P (Finsupp.single 0 P.natDegree)).mpr
        ⟨P.natDegree, Polynomial.natDegree_mem_support_of_nonzero hz, rfl⟩
      simpa using Finset.le_sup (f := fun e : Fin 5 →₀ ℕ => e 0) he
    · simp [hi]
private theorem pencil5_disjoint (A : Fin 2 → Polynomial F) {z : Fin 5} (hz : z ≠ 0) :
    Disjoint (lift5 (A 0)).support (lift5 (A 1) * MvPolynomial.X z).support := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  obtain ⟨n, _, rfl⟩ := (lift5_support (A 0) e).mp he
  rw [support_mul_X] at he'
  obtain ⟨d, hd, heq⟩ := Finset.mem_map.mp he'
  obtain ⟨m, _, rfl⟩ := (lift5_support (A 1) d).mp hd
  have h := congrArg (fun a : Fin 5 →₀ ℕ => a z) heq
  simp [Finsupp.add_apply, Ne.symm hz] at h
private theorem pencil5_ne (A : Fin 2 → Polynomial F) {z : Fin 5} (hz : z ≠ 0)
    (hA : ∃ j, A j ≠ 0) : pencil5 z A ≠ 0 := by
  have hn (j : Fin 2) (hj : A j ≠ 0) : lift5 (A j) ≠ 0 := by
    intro h
    exact hj ((Polynomial.toMvPolynomial_injective (0 : Fin 5)) (h.trans (map_zero lift5).symm))
  have hs : (pencil5 z A).support =
      (lift5 (A 0)).support ∪ (lift5 (A 1) * MvPolynomial.X z).support :=
    Finsupp.support_add_eq (pencil5_disjoint A hz)
  apply support_nonempty.mp
  rw [hs]
  obtain ⟨j, hj⟩ := hA
  fin_cases j
  · exact (support_nonempty.mpr (hn 0 hj)).mono Finset.subset_union_left
  · exact (support_nonempty.mpr (mul_ne_zero (hn 1 hj) (X_ne_zero z))).mono Finset.subset_union_right
private theorem pencil5_degree_x (A : Fin 2 → Polynomial F) {z : Fin 5} (hz : z ≠ 0) :
    (pencil5 z A).degreeOf 0 = max (A 0).natDegree (A 1).natDegree := by
  rw [pencil5, ← weightedTotalDegree_piSingle, weighted_add_of_disjoint _ _ _ (pencil5_disjoint A hz),
    weightedTotalDegree_piSingle, weightedTotalDegree_piSingle,
    degreeOf_mul_X_of_ne _ (Ne.symm hz)]
  simp [lift5_degree]
private theorem pencil5_degree_le (A : Fin 2 → Polynomial F) (i z : Fin 5) (d : ℕ)
    (hA : ∀ j, (A j).natDegree ≤ d) :
    (pencil5 z A).degreeOf i ≤ (if i = 0 then d else 0) + (if i = z then 1 else 0) := by
  have h (j : Fin 2) : (lift5 (A j)).degreeOf i ≤ if i = 0 then d else 0 := by
    rw [lift5_degree]
    split <;> simp [hA]
  refine (degreeOf_add_le i _ _).trans (max_le ?_ ?_)
  · exact (h 0).trans (Nat.le_add_right _ _)
  · exact (degreeOf_mul_le i _ _).trans (by rw [degreeOf_X]; exact Nat.add_le_add_right (h 1) _)
private theorem output5_degree_le (O : Fin 2 → Fin 2 → Polynomial F) (i : Fin 5) (d : ℕ)
    (hO : ∀ j l, (O j l).natDegree ≤ d) :
    (output5 O).degreeOf i ≤
      (if i = 0 then d else 0) + (if i = 3 then 1 else 0) + (if i = 4 then 1 else 0) := by
  have h (l : Fin 2) := pencil5_degree_le (fun j => O j l) i 3 d (fun j => hO j l)
  refine (degreeOf_add_le i _ _).trans (max_le ?_ ?_)
  · exact (h 0).trans (Nat.le_add_right _ _)
  · exact (degreeOf_mul_le i _ _).trans (by rw [degreeOf_X]; exact Nat.add_le_add_right (h 1) _)
theorem proof : K1_10_1.c1 := by
  intro u deleted h U V W j
  let A := pencil5 4 U
  let B := pencil5 3 V
  let O := output5 W.output
  have hA : ∀ l, (U l).natDegree ≤ h := by
    intro l
    have hh := W.height_eq
    unfold amplitudeDegree at hh
    fin_cases l
    · change (U 0).natDegree ≤ h
      omega
    · change (U 1).natDegree ≤ h
      omega
  have hB : ∀ l, (V l).natDegree ≤ h := by
    intro l
    have hh := W.height_eq
    unfold amplitudeDegree at hh
    fin_cases l
    · change (V 0).natDegree ≤ h
      omega
    · change (V 1).natDegree ≤ h
      omega
  have hO : ∀ k l, (W.output k l).natDegree ≤ 131071 + h := by
    intro k l
    by_cases hz : W.output k l = 0
    · simp [hz]
    · have hh := W.output_degree k l
      rw [Polynomial.degree_eq_natDegree hz, Nat.cast_lt] at hh
      omega
  have hAd (i : Fin 5) := pencil5_degree_le U i 4 h hA
  have hBd (i : Fin 5) := pencil5_degree_le V i 3 h hB
  have hOd (i : Fin 5) := output5_degree_le W.output i (131071 + h) hO
  have hAm : OmitsMessages A := ⟨by simpa [A] using hAd 1, by simpa [A] using hAd 2⟩
  have hBm : OmitsMessages B := ⟨by simpa [B] using hBd 1, by simpa [B] using hBd 2⟩
  have hOm : OmitsMessages O := ⟨by simpa [O] using hOd 1, by simpa [O] using hOd 2⟩
  have hheight : max (A.degreeOf 0) (B.degreeOf 0) = h := by
    simpa [A, B, pencil5_degree_x _ (by decide : (4 : Fin 5) ≠ 0),
      pencil5_degree_x _ (by decide : (3 : Fin 5) ≠ 0), amplitudeDegree] using W.height_eq
  rw [planeRelation_eq]
  change (A * MvPolynomial.X 1 + B * MvPolynomial.X 2 - O).weightedTotalDegree _ = _
  rw [linear_form_weight _ _ _ _ (pencil5_ne U (by decide) W.U_ne)
    (pencil5_ne V (by decide) W.V_ne) hAm hBm hOm,
    omitted_source_weights _ _ hAm, omitted_source_weights _ _ hBm,
    omitted_source_weights _ _ hOm]
  fin_cases j
  · have hOx : O.degreeOf 0 ≤ 131071 + h := by simpa [O] using hOd 0
    simp [sourceWeights, relationBounds]
    omega
  · simp [sourceWeights, relationBounds]
  · have hAs : A.degreeOf 3 = 0 := by simpa [A] using hAd 3
    have hBs : B.degreeOf 3 ≤ 1 := by simpa [B] using hBd 3
    have hOs : O.degreeOf 3 ≤ 1 := by simpa [O] using hOd 3
    simp [sourceWeights, relationBounds, hAs]
    omega
  · have hAt : A.degreeOf 4 ≤ 1 := by simpa [A] using hAd 4
    have hBt : B.degreeOf 4 = 0 := by simpa [B] using hBd 4
    have hOt : O.degreeOf 4 ≤ 1 := by simpa [O] using hOd 4
    simp [sourceWeights, relationBounds, hBt]
    omega
end
end K1_10_1_1
end
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_2_2
noncomputable section
open MvPolynomial K1_11_2
variable {F : Type*} [Field F]
private def pencil (j : Fin 5) (a b : F) : MvPolynomial (Fin 5) F := C a + MvPolynomial.X j * C b
def nodeValue (x a b c d : F) (U V : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 5) F :=
  parameterNode x U * pencil 3 a b + parameterNode x V * pencil 4 c d
theorem nodeWord_combination (x a b c d : F) (U V : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) :
    nodeWordMap x a b c d (U * MvPolynomial.X 1 + V * MvPolynomial.X 2) = nodeValue x a b c d U V := by
  simp only [map_add, map_mul, nodeWord_omits x a b c d U hU, nodeWord_omits x a b c d V hV]
  simp [nodeWordMap, nodeWordImages, nodeValue, pencil]
theorem seedEval_nodeValue (q : ℕ) (x a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    seedEval q (nodeValue x a b c d U V) =
      (graph q U).eval (Polynomial.C x) * (Polynomial.C a + Polynomial.X * Polynomial.C b) +
      (graph q V).eval (Polynomial.C x) *
        (Polynomial.C c + Polynomial.X ^ q * Polynomial.C d) := by
  simp only [nodeValue, map_add, map_mul, ← eval_graph]
  simp [pencil, seedEval]
theorem parameterNode_nodeValue (x y a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    parameterNode y (nodeValue x a b c d U V) = nodeValue x a b c d U V := by
  have h : (parameterNode y).comp (parameterNode x) = parameterNode x := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [parameterNode]
  simp only [nodeValue, map_add, map_mul, ← AlgHom.comp_apply (parameterNode y) (parameterNode x), h]
  simp [pencil, parameterNode]
private theorem degreeOf_parameterNode_le (j : Fin 5) (x : F) (Q : MvPolynomial (Fin 5) F) :
    (parameterNode x Q).degreeOf j ≤ Q.degreeOf j := by
  rw [← weightedTotalDegree_piSingle j (parameterNode x Q), ← weightedTotalDegree_piSingle j Q]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  rw [weightedTotalDegree_piSingle]
  fin_cases i <;> simp [Pi.single_apply, degreeOf_X, eq_comm]
private theorem degreeOf_parameterNode_eq_zero (j : Fin 5) (x : F) (Q : MvPolynomial (Fin 5) F)
    (h3 : j ≠ 3) (h4 : j ≠ 4) : (parameterNode x Q).degreeOf j = 0 := by
  have h := weightedTotalDegree_aeval_le_of_le (fun _ : Fin 5 => 0) (Pi.single j 1)
    (![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4] : Fin 5 → MvPolynomial (Fin 5) F) Q (by
      intro i
      rw [weightedTotalDegree_piSingle]
      fin_cases i <;> simp [degreeOf_X, h3, h4])
  have hz : Q.weightedTotalDegree (fun _ => (0 : ℕ)) = 0 := by
    simp [weightedTotalDegree, Finsupp.weight_apply]
  rw [weightedTotalDegree_piSingle, hz] at h
  exact Nat.eq_zero_of_le_zero h
private theorem degreeOf_pencil_le (i j : Fin 5) (a b : F) :
    (pencil j a b).degreeOf i ≤ if i = j then 1 else 0 := by
  refine (degreeOf_add_le i _ _).trans (max_le ?_ ?_)
  · simp
  · exact (degreeOf_mul_C_le (MvPolynomial.X j) i b).trans_eq (degreeOf_X i j)
theorem degreeOf_nodeValue_le (j : Fin 5) (x a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    (nodeValue x a b c d U V).degreeOf j ≤
      if j = 3 then sWeight U V else if j = 4 then tWeight U V else 0 := by
  refine (degreeOf_add_le j _ _).trans (max_le ?_ ?_)
  · refine (degreeOf_mul_le j _ _).trans ?_
    have hp := degreeOf_pencil_le j 3 a b
    have hu := degreeOf_parameterNode_le j x U
    by_cases h3 : j = 3
    · subst j
      simp [sWeight] at hp hu ⊢
      omega
    by_cases h4 : j = 4
    · subst j
      simp [tWeight, h3] at hp hu ⊢
      omega
    rw [degreeOf_parameterNode_eq_zero j x U h3 h4]
    simpa [h3, h4] using hp
  · refine (degreeOf_mul_le j _ _).trans ?_
    have hp := degreeOf_pencil_le j 4 c d
    have hv := degreeOf_parameterNode_le j x V
    by_cases h3 : j = 3
    · subst j
      simp [sWeight] at hp hv ⊢
      omega
    by_cases h4 : j = 4
    · subst j
      simp [tWeight, h3] at hp hv ⊢
      omega
    rw [degreeOf_parameterNode_eq_zero j x V h3 h4]
    simpa [h3, h4] using hp
private def liftCoordinate (f : Polynomial F) : MvPolynomial (Fin 5) F :=
  Polynomial.aeval (MvPolynomial.X 0) f
private theorem parameterNode_liftCoordinate (x : F) (f : Polynomial F) :
    parameterNode x (liftCoordinate f) = C (f.eval x) := by
  rw [liftCoordinate, ← Polynomial.aeval_algHom_apply (parameterNode x)]
  simp only [parameterNode, aeval_X, Matrix.cons_val_zero, Polynomial.aeval_def, algebraMap_eq]
  exact Polynomial.eval₂_at_apply _ _
private theorem degreeOf_liftCoordinate (j : Fin 5) (f : Polynomial F) :
    (liftCoordinate f).degreeOf j ≤ f.natDegree * (MvPolynomial.X 0 : MvPolynomial (Fin 5) F).degreeOf j := by
  rw [liftCoordinate, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun n hn => ?_)
  rw [algebraMap_eq]
  exact (degreeOf_C_mul_le _ j _).trans ((degreeOf_pow_le j _ n).trans
    (Nat.mul_le_mul_right _ (Polynomial.le_natDegree_of_mem_supp n hn)))
def interpolant {N : ℕ} (x : Fin N → F) (v : Fin N → MvPolynomial (Fin 5) F) :
    MvPolynomial (Fin 5) F :=
  ∑ i, liftCoordinate (Lagrange.basis Finset.univ x i) * v i
theorem parameterNode_interpolant {N : ℕ} (x : Fin N → F) (hx : Function.Injective x)
    (v : Fin N → MvPolynomial (Fin 5) F) (hv : ∀ i, parameterNode (x i) (v i) = v i)
    (j : Fin N) : parameterNode (x j) (interpolant x v) = v j := by
  rw [interpolant, map_sum]
  simp only [map_mul, parameterNode_liftCoordinate]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [Lagrange.eval_basis_self hx.injOn (Finset.mem_univ j), map_one, one_mul, hv]
  · intro i _ hij
    rw [Lagrange.eval_basis_of_ne hij (Finset.mem_univ j), map_zero, zero_mul]
theorem degreeOf_interpolant_le {N : ℕ} (x : Fin N → F) (hx : Function.Injective x)
    (v : Fin N → MvPolynomial (Fin 5) F) (j : Fin 5) (b : ℕ)
    (hv : ∀ i, (v i).degreeOf j ≤ b) :
    (interpolant x v).degreeOf j ≤ (N - 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 5) F).degreeOf j + b := by
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun i hi => ?_)
  have h := degreeOf_liftCoordinate j (Lagrange.basis Finset.univ x i)
  rw [Lagrange.natDegree_basis hx.injOn hi, Finset.card_univ, Fintype.card_fin] at h
  exact (degreeOf_mul_le j _ _).trans (Nat.add_le_add h (hv i))
end
end K1_11_2_2
end
section
namespace K1_14_3R_1
noncomputable section
open K1 K1_14 K1_14_3 K1_14_2_6_2
private theorem partial_commute (i j : Fin 4) :
    Function.Commute (coordDeriv i) (coordDeriv j) := by
  intro Q
  by_cases hij : i = j
  · subst j
    rfl
  apply MvPolynomial.ext
  intro d
  simp only [coordDeriv, MvPolynomial.coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    ite_eq_right hij, ite_eq_right (Ne.symm hij), add_zero]
  rw [add_right_comm d (Finsupp.single i 1) (Finsupp.single j 1)]
  ring
private theorem reverse_seed_contact {q : Surface} {P : Jet} {k : ℕ}
    {y v : SeedClosure} (hyv : OnSeedFibre q y v) (hk : k < p)
    (h : ∀ a b : ℕ, a + b < k → seedHasse 1 b (seedHasse 0 a P) ∈ q.asIdeal) :
    K1_14_2_6.HasSeedContact (RingHom.ker (K1_14_2_6.genericSeedPoint y v)) P k := by
  let T := K1_14_2.toJet
  let g := K1_14_2_6.genericSeedPoint y v
  have iter0 (r : ℕ) (Q : Jet) : (coordDeriv 0)^[r] (T Q) =
      r.factorial • T (seedHasse 0 r Q) := seed_iter 0 r Q
  have iter1 (r : ℕ) (Q : Jet) : (coordDeriv 1)^[r] (T Q) =
      r.factorial • T (seedHasse 1 r Q) := seed_iter 1 r Q
  have scale (i : Fin 4) (n r : ℕ) (Q : K1_14_2.Ambient) :
      (coordDeriv i)^[r] (n • Q) = n • (coordDeriv i)^[r] Q := by
    have hcomm : Function.Commute (coordDeriv i) (fun A : K1_14_2.Ambient => n • A) :=
      fun A => map_nsmul (MvPolynomial.pderiv (R := FX) i) n A
    exact (hcomm.iterate_left r) Q
  intro a b hab
  have hforward : T (seedHasse 1 b (seedHasse 0 a P)) ∈ RingHom.ker g := by
    change seedHasse 1 b (seedHasse 0 a P) ∈ (RingHom.ker g).comap T
    rw [seed_chart_ker hyv]
    exact h a b hab
  have hcomm := ((partial_commute 0 1).iterate_iterate a b) (T P)
  change (coordDeriv 0)^[a] ((coordDeriv 1)^[b] (T P)) =
    (coordDeriv 1)^[b] ((coordDeriv 0)^[a] (T P)) at hcomm
  have hleft : (coordDeriv 0)^[a] ((coordDeriv 1)^[b] (T P)) =
      b.factorial • a.factorial • T (seedHasse 0 a (seedHasse 1 b P)) := by
    rw [iter1, scale, iter0]
  have hright : (coordDeriv 1)^[b] ((coordDeriv 0)^[a] (T P)) =
      a.factorial • b.factorial • T (seedHasse 1 b (seedHasse 0 a P)) := by
    rw [iter0, scale, iter1]
  have he := congrArg g (hleft.symm.trans (hcomm.trans hright))
  simp only [map_nsmul, RingHom.mem_ker.mp hforward, nsmul_zero] at he
  let : CharP SeedClosure p :=
    charP_of_injective_ringHom (algebraMap K SeedClosure).injective p
  have hp := CharP.char_is_prime_of_two_le K p (by decide)
  have hfac (n : ℕ) (hn : n < p) : (n.factorial : SeedClosure) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hn)
      (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff SeedClosure p _).mp hz))
  simp only [nsmul_eq_mul] at he
  exact RingHom.mem_ker.mpr
    ((mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (hfac b (by omega)))).resolve_left
      (hfac a (by omega)))
theorem proof : K1_14_3R.c1 := by
  intro q P k hq hk hP y v hyv
  let I := RingHom.ker (K1_14_2_6.genericSeedPoint y v)
  have hjet : K1_14_2_6.HasJetContact P y v k :=
    K1_14_2_6_2.proof I (jet_chart hq hyv) P k hk (reverse_seed_contact hyv hk hP) y v rfl
  exact fibre_pow_of_hasse (fibreRow P) y v k hjet
end
end K1_14_3R_1
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3 K1_13_7_1 K1_13_6_2_3_2 K1_13_6_2_3_2_5 Filter
private lemma deltas_sub {ι : Type} [DecidableEq ι] (used : List ι)
    (H G : (ι → ℕ) → ℚ) (a : ι → ℕ) :
    deltas used (fun b => H b - G b) a = deltas used H a - deltas used G a := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih]; ring
private lemma deltas_shift {ι : Type} [DecidableEq ι] (used : List ι)
    (H : (ι → ℕ) → ℚ) (a v : ι → ℕ) :
    deltas used (fun b => H (b + v)) a = deltas used H (a + v) := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih, add_right_comm a (step i) v]
private lemma eventually_shift {ι : Type} {Q : (ι → ℕ) → Prop} (v : ι → ℕ)
    (h : ∀ᶠ a in atTop, Q a) : ∀ᶠ a in atTop, Q (a + v) := by
  obtain ⟨u, hu⟩ := eventually_atTop.mp h
  exact eventually_atTop.mpr ⟨u, fun a ha => hu (a + v) (ha.trans (le_add_of_nonneg_right zero_le))⟩
private lemma spend {ι : Type} [DecidableEq ι] (used : List ι) (v : ι → ℕ)
    (B C G H : (ι → ℕ) → ℚ) (heq : ∀ a, B (a + v) + H a = G (a + v))
    (hpos : ∀ᶠ a in atTop, 0 ≤ deltas used (fun b => B b - C b) a) :
    ∀ᶠ a in atTop, deltas used C (a + v) ≤ deltas used G (a + v) - deltas used H a := by
  have hid : (fun a => B (a + v)) = fun a => G (a + v) - H a := by
    funext a
    linarith [heq a]
  filter_upwards [eventually_shift v hpos] with a ha
  rw [deltas_sub] at ha
  rw [← deltas_shift used B, hid, deltas_sub, deltas_shift] at ha
  linarith
private lemma graded_top {ι σ : Type} [Fintype ι] [DecidableEq ι] (slot : σ → ι) :
    Graded slot (⊤ : Ideal (MvPolynomial σ GeoField)) := by
  intro f hf a
  exact Submodule.mem_top
private lemma hilbert_top {ι σ : Type} [DecidableEq ι] (slot : σ → ι) (a : ι → ℕ) :
    hilbert slot (⊤ : Ideal (MvPolynomial σ GeoField)) a = 0 := by
  have : Subsingleton (MvPolynomial σ GeoField ⧸ (⊤ : Ideal (MvPolynomial σ GeoField))) :=
    (Ideal.Quotient.subsingleton_iff).2 rfl
  simp [hilbert, Module.finrank_eq_zero_of_subsingleton]
theorem hilbert_difference
    {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (I K : Ideal (MvPolynomial σ GeoField))
    (hI : Graded slot I) (hK : Graded slot K) (hle : I ≤ K) :
    let H := fun a => hilbert slot I a - hilbert slot K a
    (∃ P : MvPolynomial ι ℚ, ∀ᶠ a in atTop, MvPolynomial.eval (fun i => (a i : ℚ)) P = H a) ∧
    ∀ used : List ι, ∀ᶠ a in atTop, 0 ≤ deltas used H a := by
  classical
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨A, hA⟩ := m.exists_finset_standardExponents_iff I
  obtain ⟨B, hB⟩ := m.exists_finset_standardExponents_iff K
  have hAB : outside B ⊆ outside A := by
    intro e he
    exact (hA e).mp (fun f hf => (hB e).mpr he f (hle hf))
  have eqI : hilbert slot I = sliceCount slot A := by
    funext a
    rw [standard_rank slot m I hI a]
    simp only [sliceCount, hA, outside, Set.mem_ofPred_eq]
  have eqK : hilbert slot K = sliceCount slot B := by
    funext a
    rw [standard_rank slot m K hK a]
    simp only [sliceCount, hB, outside, Set.mem_ofPred_eq]
  rw [eqI, eqK]
  exact K1_13_6_2_3_2_1.proof slot A B hAB
theorem eventually_deltas_cap_hilbert
    {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (J : Ideal GeoJets)
    (base : ι) (used : List ι) (hsh : ∀ i, Chamber (shapes i))
    (hbase : ChamberBox (shapes base))
    (hn : used.Nodup) (hd : dimension J ≤ used.length) :
    ∀ᶠ a in atTop, deltas used (hilbert (capSlot shapes) (capIdeal shapes J)) a =
      polarize (capCoeff J used.length) (used.map shapes) (shapes base) := by
  let slot := capSlot shapes
  let I := capIdeal shapes J
  have hI := (K1_13_6_2_3_2_3.proof shapes J).1
  have hall := (hilbert_difference slot I ⊤ hI (graded_top slot) le_top).1
  rw [show (fun a => hilbert slot I a - hilbert slot ⊤ a) = hilbert slot I by
    funext a; simp [hilbert_top]] at hall
  obtain ⟨P, hP⟩ := hall
  have hrank : hilbert slot I = fun a => (supportRank J (capExponents (shapeSum shapes a)) : ℚ) := by
    funext a
    rw [(K1_13_6_2_3_2_3.proof shapes J).2 a, product_eq_cap shapes hsh a]
  rw [hrank] at hP ⊢
  obtain ⟨u, hu⟩ := eventually_atTop.mp hP
  let K := fun a => (supportRank J (capExponents (shapeSum shapes a)) : ℚ)
  have hcompare (v : ι → ℕ) (hv : 0 < v base) :=
    ray_degree_and_coefficient shapes hsh J P u v (by
      change 0 < ∑ i, v i * (shapes i).t
      have hle := Finset.single_le_sum (f := fun i => v i * (shapes i).t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ base)
      exact (Nat.mul_pos hv hbase.2.2).trans_le hle) hu _ hd
  have hdeg : P.totalDegree ≤ used.length :=
    totalDegree_le_of_ray_degree P u _ fun v hv => (hcompare v (hv base)).1
  let F := fun v : ι → ℕ =>
    MvPolynomial.eval (fun i => (v i : ℚ)) (MvPolynomial.homogeneousComponent used.length P)
  have hright := deltas_congr_on_upper used F
    (fun v => capCoeff J used.length (shapeSum shapes v)) (step base) fun v hv =>
      (ray_top P u v hdeg).symm.trans (hcompare v (by
        have h : step base base ≤ v base := hv base
        exact Nat.succ_le_iff.mp (by simpa [step] using h))).2
  filter_upwards [eventually_ge_atTop u] with a ha
  change deltas used K a = _
  calc
    _ = deltas used (fun v => MvPolynomial.eval (fun i => (v i : ℚ)) P) a :=
      deltas_congr_on_upper used K _ a fun v hv => (hu v (ha.trans hv)).symm
    _ = deltas used F (step base) := deltas_top used hn P hdeg a (step base)
    _ = _ := by rw [hright, deltas_shapeSum, shapeSum_step]
theorem proof :
    K1_13_7_2_3_1.c1 := by
  classical
  intro J p boxes hp hboxes _ hdim D hD hreg
  let ι := Option (Option (Fin boxes.length))
  let base : ι := none
  let i : ι := some none
  let emb : Fin boxes.length → ι := fun k => some (some k)
  let rest := (List.finRange boxes.length).map emb
  let shapes : ι → Shape
    | none => ⟨3, 3, 1⟩
    | some none => p
    | some (some k) => boxes.get k
  have hsh (k : ι) : Chamber (shapes k) := by
    cases k with
    | none =>
      change Chamber ⟨3, 3, 1⟩
      exact ⟨by decide, by decide⟩
    | some k => cases k with
      | none => exact hp
      | some k => exact hboxes _ (List.get_mem _ _)
  have hbaseBox : ChamberBox (shapes base) := by
    change ChamberBox (⟨3, 3, 1⟩ : Shape)
    exact ⟨by decide, by decide, by decide⟩
  have hi : i ∉ rest := by
    intro h
    obtain ⟨k, _, hk⟩ := List.mem_map.mp h
    change (some (some k) : Option (Option (Fin boxes.length))) = some none at hk
    have hinner : (some k : Option (Fin boxes.length)) = none := Option.some.inj hk
    cases hinner
  have hn : rest.Nodup := (List.nodup_finRange _).map
    (fun _ _ h => Option.some.inj (Option.some.inj h))
  have hn' : (i :: rest).Nodup := List.nodup_cons.mpr ⟨hi, hn⟩
  have hmap : rest.map shapes = boxes := by
    simp [rest, List.map_map, Function.comp_def, emb, shapes]
  have hlen : rest.length = boxes.length := by simp [rest]
  let slot := capSlot shapes
  let I := capIdeal shapes J
  let I₁ := capIdeal shapes (cut J D)
  let I₂ := capIdeal shapes (cut J (D ^ 2))
  have hgraded₂ := (K1_13_6_2_3_2_3.proof shapes (cut J (D ^ 2))).1
  obtain ⟨B, C, hB, hC, hBI, hCI, heqB, heqC⟩ :=
    K1_13_6_2_3_2_6.proof shapes i J D hD hreg (K1_13_6_2_3_2_3.proof shapes J).1 hgraded₂
  have hposB := (hilbert_difference slot B I₂ hB hgraded₂ hBI).2 rest
  have hposC := (hilbert_difference slot C I₁ hC (K1_13_6_2_3_2_3.proof shapes (cut J D)).1 hCI).2 rest
  have hspendB := spend rest (step i) (hilbert slot B) (hilbert slot I₂) (hilbert slot I)
    (hilbert slot I) heqB hposB
  have hspendC := spend rest (step i) (hilbert slot C) (hilbert slot I₁) (hilbert slot I₂)
    (hilbert slot I₁) heqC hposC
  have hd₁ : dimension (cut J D) ≤ rest.length := by
    have hdrop : dimension (cut J D) ≤ dimension J - 1 := cut_dimension hreg
    omega
  have hd₀ : dimension J ≤ (i :: rest).length := by simpa [hlen] using hdim
  have hr₀ := eventually_deltas_cap_hilbert shapes J base (i :: rest) hsh hbaseBox hn' hd₀
  have hr₁ := eventually_deltas_cap_hilbert shapes (cut J D) base rest hsh hbaseBox hn hd₁
  have hfinal : ∀ᶠ _a in (atTop : Filter (ι → ℕ)),
      2 * polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ ≤
        polarize (capCoeff J (p :: boxes).length) (p :: boxes) ⟨3, 3, 1⟩ := by
    filter_upwards [hspendB, hspendC, hr₀, hr₁, eventually_shift (step i) hr₁] with a hb hc h₀ h₁ h₁'
    rw [List.map_cons, hmap, List.length_cons, hlen] at h₀
    rw [hlen, hmap] at h₁ h₁'
    change deltas rest (hilbert slot I) (a + step i) - deltas rest (hilbert slot I) a =
      polarize (capCoeff J (boxes.length + 1)) (p :: boxes) ⟨3, 3, 1⟩ at h₀
    change deltas rest (hilbert slot I₁) a =
      polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ at h₁
    change deltas rest (hilbert slot I₁) (a + step i) =
      polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ at h₁'
    simp only [List.length_cons]
    linarith [hb, hc, h₀, h₁, h₁']
  obtain ⟨_, hfinal⟩ := hfinal.exists
  unfold mixedDegree
  rw [List.length_cons, pow_succ, mul_comm ((2 : ℚ)^boxes.length) 2, ← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).2 (by simpa [mul_comm] using hfinal)
end
end K1_13_7_2_3_1_1
end

end Merged6967_Fast077

section Merged6967_Low48PrimaryPivotRect
set_option Elab.async false






set_option Elab.async false

-- merged module Low48PrimaryPivotRows
section Merged_Low48PrimaryPivotRows

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder)
open AnchorPivot82180 (E mon poly Term sound_monomial)
open AnchorPivot82180 (src0 src3 src6 src7 spec0 spec3 spec6 spec7)
open K1_13_2 K1_13_2_2 MvPolynomial
open scoped BigOperators
open AnchorPivot82180 (independent)
open K1_13_2_2 (active_range_le)

def key (e : E) : ℕ :=
  8177403*e.a + 5451602*e.b + 2725802*e.c + 1651*e.f

noncomputable def encode : Form →ₐ[Geom] Polynomial Geom :=
  aeval (fun i => (Polynomial.X : Polynomial Geom)^(![8177403,5451602,2725802,1651] i : ℕ))

private theorem encode_mon (e : E) : encode (mon e) = Polynomial.X ^ key e := by
  simp [mon, encode, key, ← pow_mul, ← pow_add]

private theorem degree_le (xs : List Term) (v : ℕ)
    (h : xs.all (fun t => decide (key t.2 ≤ v)) = true) :
    (encode (poly xs)).degree ≤ (v : ℕ) := by
  induction xs with
  | nil => simp [poly]
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hp,hr⟩ := h
    rw [poly, map_add, map_zsmul, encode_mon]
    apply Polynomial.degree_add_le_of_degree_le _ (ih hr)
    rw [← Int.cast_smul_eq_zsmul (R := Geom)]
    exact (Polynomial.degree_smul_le _ _).trans ((Polynomial.degree_X_pow_le _).trans
      (WithBot.coe_le_coe.mpr (of_decide_eq_true hp)))

private theorem leading {e : E} {v : ℕ} (xs : List Term) (h : v < key e)
    (ht : xs.all (fun t => decide (key t.2 ≤ v)) = true) :
    (encode (poly ((1,e)::xs))).degree = (key e : ℕ) := by
  rw [poly, one_zsmul, map_add, encode_mon, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact (degree_le xs _ ht).trans_lt (WithBot.coe_lt_coe.mpr h)

private theorem leading0 : (encode (poly src0)).degree = (key ⟨1,0,0,0⟩ : ℕ) := by
  unfold src0
  exact leading _ (v := key ⟨0,1,0,0⟩) (by decide) (by decide)
private theorem leading3 : (encode (poly src3)).degree = (key ⟨1,1,0,0⟩ : ℕ) := by
  unfold src3
  exact leading _ (v := key ⟨1,0,1,0⟩) (by decide) (by decide)
private theorem leading6 : (encode (poly src6)).degree = (key ⟨2,0,1,0⟩ : ℕ) := by
  unfold src6
  exact leading _ (v := key ⟨1,2,0,0⟩) (by decide) (by decide)
private theorem leading7 : (encode (poly src7)).degree = (key ⟨1,3,0,0⟩ : ℕ) := by
  unfold src7
  exact leading _ (v := key ⟨2,1,0,1⟩) (by decide) (by decide)
structure Triple where
  b : ℕ
  c : ℕ
  f : ℕ
  deriving DecidableEq

def Triple.index (p : Triple) := p.b+2*p.c+3*p.f
def Triple.exponent (p : Triple) : E := ⟨1650-p.b-p.c-p.f,p.b,p.c,p.f⟩
def Triple.room (p : Triple) := 1650-p.index
structure Groups where
  fourth : ℕ
  first : ℕ
  second : ℕ

def Groups.width (g : Groups) : ℕ := g.fourth+g.first+g.second
def Groups.gain (g : Groups) : ℕ := 2*g.fourth+g.first+g.second

def Triple.packet (p : Triple) : Groups :=
  let q := min (p.b/3) (min p.room ((p.b+p.c-p.room)/2))
  let singles := min (p.room-q) (p.b+p.c-3*q)
  let first := min (p.b-3*q) singles
  ⟨q,first,singles-first⟩

def Triple.contact (p : Triple) : ℕ := p.c+2*p.f+p.room+p.packet.gain

private theorem packet_valid (p : Triple) :
    p.packet.width ≤ p.room ∧ 3*p.packet.fourth+p.packet.first ≤ p.b ∧
      p.packet.second ≤ p.c := by
  simp only [Triple.packet, Groups.width]
  omega

theorem contact_eq (p : Triple) :
    p.contact = p.c+2*p.f+p.room+
      min (p.b+p.c) (p.room + min (p.b/3) (min p.room ((p.b+p.c-p.room)/2))) := by
  simp only [Triple.contact, Triple.packet, Groups.gain]
  omega

private def linear (p : Triple) := p.room-p.packet.width
private def remainder (p : Triple) : E :=
  let g := p.packet
  ⟨p.exponent.a-(linear p+g.fourth+g.first+2*g.second),
    p.b-(3*g.fourth+g.first),p.c-g.second,p.f⟩

noncomputable def polynomial (p : Triple) : Form :=
  mon (remainder p) * poly src0 ^ linear p *
    poly src3 ^ p.packet.first * poly src6 ^ p.packet.second *
    poly src7 ^ p.packet.fourth

private theorem bot_nsmul (n k : ℕ) :
    k • (n : WithBot ℕ) = ((k*n : ℕ) : WithBot ℕ) := by
  have hn : k • n = k*n := rfl
  exact (WithBot.coe_nsmul n k).symm.trans (congrArg WithBot.some hn)

private theorem bot_add (n k : ℕ) :
    (n : WithBot ℕ) + (k : WithBot ℕ) = ((n+k : ℕ) : WithBot ℕ) := rfl

private theorem row_bounds (p : Triple) (h : p.index ≤ 1650) :
    polynomial p ∈ bandSpace 1650 (p.index : ℤ) 1650 550 ∧
      backShift (polynomial p) ∈ restrictWeightedOrder targetOrder p.contact := by
  obtain ⟨hu,hb,hc⟩ := packet_valid p
  have hs := ((((sound_monomial (remainder p)).mul (spec0.pow (linear p))).mul
    (spec3.pow p.packet.first)).mul (spec6.pow p.packet.second)).mul
    (spec7.pow p.packet.fourth)
  have hp : linear p + p.packet.width = p.room := by unfold linear; omega
  have hTotal : p.exponent.a + p.b + p.c + p.f = 1650 := by
    simp only [Triple.exponent, Triple.index] at *
    omega
  have ha : linear p+p.packet.fourth+p.packet.first+
      2*p.packet.second ≤ p.exponent.a := by
    simp only [Groups.width, Triple.exponent, Triple.room, Triple.index] at *
    omega
  have helpDegree : (remainder p).deg + linear p + p.packet.first*2 + p.packet.second*3 +
      p.packet.fourth*4 = 1650 := by
    simp only [remainder, E.deg]
    omega
  have helpIndex : (remainder p).index + p.packet.first + 2*p.packet.second +
      3*p.packet.fourth = p.index := by
    simp only [remainder, E.index, Triple.index]
    omega
  have helpTop : p.f + p.packet.second+p.packet.fourth ≤ 550 := by
    simp only [Groups.width, Triple.room, Triple.index] at *
    omega
  have helpUpper : (remainder p).index + linear p + 2*p.packet.first +3*p.packet.second +
      4*p.packet.fourth = 1650 := by
    simp only [Groups.width, Triple.room] at hp
    omega
  have helpOrder : (remainder p).c+2*(remainder p).f + linear p +
      p.packet.first*2+p.packet.second*3+p.packet.fourth*3 = p.contact := by
    simp only [remainder, Triple.contact, Groups.gain]
    unfold Groups.width at hp
    omega
  have hd := hs.band
  simp only [AnchorPivot82180.Data.plus, AnchorPivot82180.Data.times,
    AnchorPivot82180.monoData, AnchorPivot82180.data0, AnchorPivot82180.data3,
    AnchorPivot82180.data6, AnchorPivot82180.data7] at hd
  have he (f : Fin 4 →₀ ℕ) (hf : f ∈ (polynomial p).support) :=
    (mem_restrictSupport_iff Geom).mp hd hf
  refine ⟨(mem_restrictSupport_iff Geom).mpr ?_, ?_⟩
  · intro e helem
    obtain ⟨h0,h1,h2,h3⟩ := he e helem
    refine ⟨?_,?_,?_,?_⟩
    · simpa [Nat.mul_comm] using (h0.trans (by omega))
    · omega
    · have := helpUpper
      omega
    · exact h3.trans (by simpa [remainder,Nat.mul_comm] using helpTop)
  · have hContact := hs.contact
    simp only [AnchorPivot82180.Data.plus, AnchorPivot82180.Data.times,
      AnchorPivot82180.monoData, AnchorPivot82180.data0, AnchorPivot82180.data3,
      AnchorPivot82180.data6, AnchorPivot82180.data7] at hContact
    exact restrictWeightedOrder_anti _ (by omega) hContact
private theorem degree_products (A B C D E : Polynomial Geom) (k l m n a b c d e : ℕ)
    (hA : A.degree = (a : WithBot ℕ)) (hB : B.degree = (b : WithBot ℕ))
    (hC : C.degree = (c : WithBot ℕ)) (hD : D.degree = (d : WithBot ℕ))
    (hE : E.degree = (e : WithBot ℕ)) :
    (A*B^k*C^l*D^m*E^n).degree = ((a+k*b+l*c+m*d+n*e : ℕ) : WithBot ℕ) := by
  simp only [Polynomial.degree_mul, Polynomial.degree_pow, hA, hB, hC, hD, hE,
    bot_nsmul, bot_add]

private theorem row_key (p : Triple) (h : p.index ≤ 1650) :
    key (remainder p) + linear p * key ⟨1,0,0,0⟩ +
      p.packet.first * key ⟨1,1,0,0⟩ + p.packet.second * key ⟨2,0,1,0⟩ +
      p.packet.fourth * key ⟨1,3,0,0⟩ = key p.exponent := by
  obtain ⟨hu,hb,hc⟩ := packet_valid p
  have hp : linear p + p.packet.width = p.room := by unfold linear; omega
  have ha : linear p+p.packet.fourth+p.packet.first+2*p.packet.second ≤ p.exponent.a := by
    simp only [Groups.width, Triple.exponent, Triple.room, Triple.index] at *
    omega
  have hA : (remainder p).a + (linear p+p.packet.fourth+p.packet.first+2*p.packet.second) =
      p.exponent.a := Nat.sub_add_cancel ha
  have hB : (remainder p).b + (3*p.packet.fourth+p.packet.first) =
      p.exponent.b := Nat.sub_add_cancel hb
  have hC : (remainder p).c + p.packet.second = p.exponent.c := Nat.sub_add_cancel hc
  have hF : p.exponent.f = (remainder p).f := rfl
  unfold key
  rw [← hA, ← hB, ← hC, hF]
  ring

private theorem deg_remainder (p : Triple) :
    (encode (mon (remainder p))).degree = (key (remainder p) : WithBot ℕ) := by
  rw [encode_mon, Polynomial.degree_X_pow]

private theorem row_degree (p : Triple) (h : p.index ≤ 1650) :
    (encode (polynomial p)).degree = (key p.exponent : ℕ) := by
  rw [polynomial, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
  exact (degree_products _ _ _ _ _ (linear p) p.packet.first p.packet.second p.packet.fourth
    _ _ _ _ _ (deg_remainder p) leading0 leading3 leading6 leading7).trans
      (congrArg (fun n : ℕ => (n : WithBot ℕ)) (row_key p h))

theorem row_sound (p : Triple) (h : p.index ≤ 1650) :
    polynomial p ∈ bandSpace 1650 (p.index : ℤ) 1650 550 ∧
      backShift (polynomial p) ∈ restrictWeightedOrder targetOrder p.contact ∧
      (encode (polynomial p)).degree = (key p.exponent : ℕ) :=
  ⟨(row_bounds p h).1, (row_bounds p h).2, row_degree p h⟩

theorem key_injective (p q : Triple) (hp : p.index ≤ 1650) (hq : q.index ≤ 1650)
    (h : key p.exponent = key q.exponent) : p = q := by
  have hform (r : Triple) (hr : r.index ≤ 1650) :
      key r.exponent = 2725801*(4950-r.index) + 1651*r.f + r.c := by
    simp only [key, Triple.exponent, Triple.index] at *
    omega
  rw [hform p hp,hform q hq] at h
  have hi : p.index=q.index := by unfold Triple.index at *; omega
  rw [hi] at h
  have hcf : p.c=q.c ∧ p.f=q.f := by unfold Triple.index at *; omega
  rcases p with ⟨pb,pc,pf⟩
  rcases q with ⟨qb,qc,qf⟩
  simp only [Triple.index] at hi
  simp only at hcf
  obtain ⟨rfl,rfl⟩ := hcf
  congr
  omega

#print axioms row_sound

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotRows

-- merged module Low48PrimaryPivotCore
section Merged_Low48PrimaryPivotCore

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder)
open AnchorPivot82180 (E mon poly Term sound_monomial)
open AnchorPivot82180 (src0 src3 src6 src7 spec0 spec3 spec6 spec7)
open K1_13_2 K1_13_2_2 MvPolynomial
open scoped BigOperators
open AnchorPivot82180 (independent)
open K1_13_2_2 (active_range_le)

private def ofExp (e : JetExp) : Triple := ⟨e 1,e 2,e 3⟩

private theorem old_jet_index (e : JetExp) :
    e.weight oldWeight = (ofExp e).index := by
  simp [oldWeight, ofExp, Triple.index, Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, mul_comm]

private theorem old_jet_degree (e : JetExp) :
    e.weight gradeWeight = e 0 + e 1 + e 2 + e 3 := by
  simp [gradeWeight, Finsupp.weight_eq_sum, Fin.sum_univ_four]

private theorem source_data {i : BlockIndex} (hs : 1650 ≤ i.1.val)
    {e : JetExp} (he : e ∈ oldColumns (initialFlag i)) :
    (ofExp e).index ≤ 1650 ∧ -(offset i) ≤ ((ofExp e).index : ℤ) ∧
      e 0 + e 1 + e 2 + e 3 = 1650 := by
  obtain ⟨hgrade,hlo,hhi,_⟩ := mem_oldColumns.mp he
  rw [old_jet_index] at hlo hhi
  rw [old_jet_degree] at hgrade
  have hg : (initialFlag i).degree = 1650 := by
    change min (i.1.val : ℤ) 1650 = 1650
    omega
  change ((ofExp e).index : ℤ) ≤ 1650 at hhi
  rw [hg] at hgrade
  push_cast at hgrade
  exact ⟨by omega,hlo,by omega⟩

private theorem triple_injOn {i : BlockIndex} (hs : 1650 ≤ i.1.val) :
    Set.InjOn ofExp (↑(oldColumns (initialFlag i)) : Set JetExp) := by
  intro e he f hf h
  have h1 := congrArg Triple.b h
  have h2 := congrArg Triple.c h
  have h3 := congrArg Triple.f h
  simp only [ofExp] at h1 h2 h3
  have hd : e 0 + e 1 + e 2 + e 3 = 1650 := (source_data hs he).2.2
  have hdf : f 0 + f 1 + f 2 + f 3 = 1650 := (source_data hs hf).2.2
  ext j
  fin_cases j
  · change e 0 = f 0
    omega
  · exact h1
  · exact h2
  · exact h3

private def good (i : BlockIndex) (e : JetExp) : Prop :=
  (initialFlag i).order.toNat ≤ (ofExp e).contact

private instance (i : BlockIndex) (e : JetExp) : Decidable (good i e) := by
  unfold good
  infer_instance

private theorem good_kernel {i : BlockIndex} (hs : 1650 ≤ i.1.val)
    (e : ↑((oldColumns (initialFlag i)).filter (good i))) :
    ∃ w : LinearMap.ker (flagContact (initialFlag i)),
      (encode (w.val : Form)).degree = (key (ofExp e).exponent : ℕ) := by
  obtain ⟨he,hg⟩ := Finset.mem_filter.mp e.property
  let p := ofExp e
  obtain ⟨hi,hl,_⟩ := source_data hs he
  obtain ⟨hBand,hContact,hKey⟩ := row_sound p hi
  have hOld : polynomial p ∈ oldSpace (initialFlag i) := by
    intro e he
    have h := (mem_restrictSupport_iff Geom).mp hBand he
    change K1_13_1_1.BandExponent 1650 p.index 1650 550 e at h
    obtain ⟨hd,hlow,hupp,ht⟩ := h
    refine ⟨?_,hl.trans hlow,hupp,?_⟩
    · have hweight : gradeWeight = (fun _ : Fin 4 => (1 : ℕ)) := rfl
      have hg : (initialFlag i).degree = 1650 := by
        change min (i.1.val : ℤ) 1650 = 1650
        omega
      rw [hweight, ← Finsupp.degree_eq_weight_one, hg]
      exact_mod_cast hd
    · change (e 3 : ℤ) ≤ 550
      exact_mod_cast ht
  let q : oldSpace (initialFlag i) := ⟨polynomial p,hOld⟩
  have hz : q ∈ LinearMap.ker (flagContact (initialFlag i)) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ hg hContact
  exact ⟨⟨q,hz⟩,hKey⟩

private theorem rank_le_bad (i : BlockIndex) (hs : 1650 ≤ i.1.val) :
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤
      ((oldColumns (initialFlag i)).filter (fun e => ¬ good i e)).card := by
  classical
  let S := (oldColumns (initialFlag i)).filter (good i)
  let w : S → LinearMap.ker (flagContact (initialFlag i)) :=
    fun e => Classical.choose (good_kernel hs e)
  let L : LinearMap.ker (flagContact (initialFlag i)) →ₗ[Geom] Polynomial Geom :=
    encode.toLinearMap.comp ((oldSpace (initialFlag i)).subtype.comp (LinearMap.ker _).subtype)
  have keyInj : Function.Injective (fun e : S => key (ofExp e).exponent) := by
    intro p q hkey
    have hp := (Finset.mem_filter.mp p.property).1
    have hq := (Finset.mem_filter.mp q.property).1
    exact Subtype.ext (triple_injOn hs hp hq
      (key_injective _ _ (source_data hs hp).1 (source_data hs hq).1 hkey))
  have hind := independent L w (fun e => key (ofExp e).exponent) keyInj
    (fun e => Classical.choose_spec (good_kernel hs e))
  have hdim := hind.fintype_card_le_finrank
  rw [Fintype.card_coe] at hdim
  have hnull := (flagContact (initialFlag i)).finrank_range_add_finrank_ker
  rw [finrank_oldSpace] at hnull
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := oldColumns (initialFlag i)) (good i)
  have hbound := (K1_13_2_2_1.proof i).trans (Submodule.finrank_mono (active_range_le i))
  change S.card ≤ _ at hdim
  change S.card + _ = _ at hpartition
  omega

abbrev Column := Fin 551 × Fin 826 × Fin 1651

def columnPoint (q : Column) : Triple := ⟨q.2.2.val,q.2.1.val,q.1.val⟩

private def slot (p : Triple) (h : p.index ≤ 1650) : Column :=
  ⟨⟨p.f,by unfold Triple.index at h; omega⟩,
    ⟨p.c,by unfold Triple.index at h; omega⟩,
    ⟨p.b,by unfold Triple.index at h; omega⟩⟩

private theorem slot_inv (p : Triple) (h : p.index ≤ 1650) : columnPoint (slot p h) = p := by
  cases p
  rfl

def pays (i : BlockIndex) (q : Column) : Prop :=
  let p := columnPoint q
  p.index ≤ 1650 ∧ -offset i ≤ (p.index : ℤ) ∧ p.contact < (initialFlag i).order.toNat

instance (i : BlockIndex) (q : Column) : Decidable (pays i q) := by
  unfold pays
  infer_instance

def charge (i : BlockIndex) (q : Column) : ℕ := if pays i q then 1 else 0

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 26000 in
theorem block_le_charge (i : BlockIndex) (hs : 1650 ≤ i.1.val) :
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤ ∑ q, charge i q := by
  classical
  let f : JetExp → Column := fun e =>
    if hp : (ofExp e).index ≤ 1650 then slot (ofExp e) hp else default
  let S : Finset JetExp := (oldColumns (initialFlag i)).filter (fun e => ¬ good i e)
  let T : Finset (Column) := Finset.univ.filter (pays i)
  have hT : (∑ q, charge i q) = T.card := by
    unfold charge T
    rw [Finset.sum_boole]
    rfl
  rw [hT]
  refine (rank_le_bad i hs).trans (Finset.card_le_card_of_injOn (s := S) (t := T) f ?_ ?_)
  · intro e he
    have helem : e ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e) := he
    obtain ⟨hm,hbad⟩ := Finset.mem_filter.mp helem
    obtain ⟨hi,hl,_⟩ := source_data hs hm
    unfold f
    rw [dite_eq_left hi]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    unfold pays
    rw [slot_inv]
    exact ⟨hi,hl,lt_of_not_ge hbad⟩
  · intro e he q hq h
    have hem := (Finset.mem_filter.mp
      (show e ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e) from he)).1
    have hqm := (Finset.mem_filter.mp
      (show q ∈ (oldColumns (initialFlag i)).filter (fun e => ¬ good i e) from hq)).1
    have hei := (source_data hs hem).1
    have hqi := (source_data hs hqm).1
    simp only [f, dite_eq_left hei, dite_eq_left hqi] at h
    have heq := congrArg columnPoint h
    rw [slot_inv,slot_inv] at heq
    exact triple_injOn hs hem hqm heq

#print axioms block_le_charge

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotCore

-- merged module Low48PrimaryPivotRect
section Merged_Low48PrimaryPivotRect

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators

/-- Twice the triangular number of the positive part of an integer. -/
def twiceTri (x : ℤ) : ℤ := max 0 x * (max 0 x + 1)

private theorem tri_step (x : ℤ) : twiceTri (x+1) - twiceTri x = 2 * max 0 (x+1) := by
  by_cases hx : 0 ≤ x
  · simp only [twiceTri, max_eq_right hx, max_eq_right (show 0 ≤ x+1 by omega)]
    ring
  · have h1 : x+1 ≤ 0 := by omega
    simp [twiceTri, max_eq_left h1, max_eq_left (le_of_not_ge hx)]

private theorem sum_ramp (a b k : ℤ) (h : a ≤ b) :
    (∑ l ∈ Ico a b, 2 * max 0 (l-k+1)) = twiceTri (b-k) - twiceTri (a-k) := by
  rw [Int.Ico_eq_finset_map, sum_map]
  let n := (b-a).toNat
  have hn : a+(n : ℤ) = b := by dsimp [n]; omega
  have eq (l : ℕ) :
      2 * max 0 (a+(l : ℤ)-k+1) =
        twiceTri (a+((l+1 : ℕ) : ℤ)-k) - twiceTri (a+(l : ℤ)-k) := by
    push_cast
    rw [show a+((l : ℤ)+1)-k = a+(l : ℤ)-k+1 by ring, tri_step]
  change (∑ l ∈ range n, 2 * max 0 (a+(l : ℤ)-k+1)) = _
  simp_rw [eq]
  rw [sum_range_sub (fun l : ℕ => twiceTri (a+(l : ℤ)-k)) n, hn]
  simp

private theorem cut_card (q0 q1 l k : ℤ) (hq : q0 ≤ q1) :
    (((Ico q0 q1).filter (fun q => k ≤ l-q)).card : ℤ) =
      max 0 (l-k+1-q0) - max 0 (l-k+1-q1) := by
  have eq : (Ico q0 q1).filter (fun q => k ≤ l-q) = Ico q0 (min q1 (l-k+1)) := by
    ext q
    simp only [mem_filter, mem_Ico, lt_min_iff]
    omega
  rw [eq, Int.card_Ico]
  omega

def cutFee (l0 l1 q0 q1 k : ℤ) : ℤ :=
  twiceTri (l1-k-q0) - twiceTri (l0-k-q0) -
    (twiceTri (l1-k-q1) - twiceTri (l0-k-q1))

private theorem sum_cut (l0 l1 q0 q1 k : ℤ) (hl : l0 ≤ l1) (hq : q0 ≤ q1) :
    2 * ↑(((Ico l0 l1).product (Ico q0 q1)).filter (fun x => k ≤ x.1-x.2)).card =
      cutFee l0 l1 q0 q1 k := by
  rw [natCast_card_filter (fun x : ℤ × ℤ => k ≤ x.1-x.2)]
  have hprod :
      (∑ x ∈ (Ico l0 l1).product (Ico q0 q1), if k ≤ x.1-x.2 then (1 : ℤ) else 0) =
        ∑ l ∈ Ico l0 l1, ∑ q ∈ Ico q0 q1, if k ≤ l-q then (1 : ℤ) else 0 :=
    sum_product (Ico l0 l1) (Ico q0 q1) (fun x : ℤ × ℤ => if k ≤ x.1-x.2 then (1 : ℤ) else 0)
  rw [hprod]
  unfold cutFee
  have eq (l : ℤ) :
      (∑ q ∈ Ico q0 q1, (if k ≤ l-q then (1 : ℤ) else 0)) =
        max 0 (l-k+1-q0) - max 0 (l-k+1-q1) := by
    rw [← cut_card q0 q1 l k hq, natCast_card_filter]
  simp_rw [eq, mul_sum, mul_sub]
  rw [sum_sub_distrib]
  have ramp (q : ℤ) : (∑ l ∈ Ico l0 l1, 2 * max 0 (l-k+1-q)) =
      twiceTri (l1-k-q) - twiceTri (l0-k-q) := by
    have h (l : ℤ) : l-k+1-q = l-(k+q)+1 := by ring
    simp_rw [h]
    simpa only [sub_add_eq_sub_sub] using sum_ramp l0 l1 (k+q) hl
  rw [ramp, ramp]

def fee2 (l0 l1 q0 q1 a b : ℤ) : ℤ :=
  cutFee l0 l1 q0 q1 a - cutFee l0 l1 q0 q1 b

theorem band_card (l0 l1 q0 q1 a b : ℤ)
    (hl : l0 ≤ l1) (hq : q0 ≤ q1) (hab : a ≤ b) :
    2 * ↑(((Ico l0 l1).product (Ico q0 q1)).filter
      (fun x => a ≤ x.1-x.2 ∧ x.1-x.2 < b)).card = fee2 l0 l1 q0 q1 a b := by
  let S := (Ico l0 l1).product (Ico q0 q1)
  let A := S.filter (fun x => a ≤ x.1-x.2 ∧ x.1-x.2 < b)
  let B := S.filter (fun x => b ≤ x.1-x.2)
  have disjoint : Disjoint A B := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    have ha := (mem_filter.mp hx).2.2
    have hb := (mem_filter.mp hy).2
    omega
  have union : A ∪ B = S.filter (fun x => a ≤ x.1-x.2) := by
    ext x
    by_cases h : x ∈ S
    · simp only [A, B, mem_union, mem_filter, h, true_and]
      omega
    · simp [A, B, h]
  have hcard : (A.card : ℤ) + B.card = ((S.filter (fun x => a ≤ x.1-x.2)).card : ℤ) := by
    exact_mod_cast ((card_union_of_disjoint disjoint).symm.trans (congrArg card union))
  have hA := sum_cut l0 l1 q0 q1 a hl hq
  have hB := sum_cut l0 l1 q0 q1 b hl hq
  change 2 * (A.card : ℤ) = _
  change 2 * ((S.filter (fun x => a ≤ x.1-x.2)).card : ℤ) = _ at hA
  change 2 * (B.card : ℤ) = _ at hB
  unfold fee2
  omega

def indexLo (w : Window) : ℤ := 1650-w.offsetHi
def indexHi (w : Window) (p : Triple) : ℤ :=
  max (indexLo w) (min (1651-(w.offsetLo : ℤ)) (p.index+1 : ℤ))
def orderHi (w : Window) : ℤ := 4651-w.diagonalLo
def orderLo (w : Window) (p : Triple) : ℤ :=
  min (orderHi w) (max (4650-(w.diagonalHi : ℤ)) (p.contact+1 : ℤ))

def columnFee2 (w : Window) (p : Triple) : ℤ :=
  if p.index ≤ 1650 then
    fee2 (indexLo w) (indexHi w p) (orderLo w p) (orderHi w)
      ((w.gradeLo : ℤ)-3000) ((w.gradeHi : ℤ)-3000)
  else 0

def debit (w : Window) : ℕ :=
  ∑ i : BlockIndex, if w.Contains i then ∑ q : Column, charge i q else 0

private theorem column_le_fee_on (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi)
    (q : Column) (rows : Finset BlockIndex) :
    2 * ↑(∑ i ∈ rows, if w.Contains i then charge i q else 0) ≤
      columnFee2 w (columnPoint q) := by
  let p := columnPoint q
  by_cases hp : p.index ≤ 1650
  · rw [columnFee2, ite_eq_left hp]
    let S := rows.filter (fun i => w.Contains i ∧ pays i q)
    let R := ((Ico (indexLo w) (indexHi w p)).product (Ico (orderLo w p) (orderHi w))).filter
      (fun x => (w.gradeLo : ℤ)-3000 ≤ x.1-x.2 ∧ x.1-x.2 < (w.gradeHi : ℤ)-3000)
    have hsum : (∑ i ∈ rows, if w.Contains i then charge i q else 0) = S.card := by
      calc
        _ = ∑ i ∈ rows, if w.Contains i ∧ pays i q then 1 else 0 := by
          apply sum_congr rfl
          intro i _
          by_cases hw : w.Contains i <;> simp [charge,hw]
        _ = _ := sum_boole _ _
    have hc : S.card ≤ R.card := by
      let f (i : BlockIndex) : ℤ × ℤ := (1650-i.2.val,4650-(i.1.val : ℤ)-i.2.val)
      refine card_le_card_of_injOn f ?_ ?_
      · intro i hi
        change i ∈ rows.filter (fun i => w.Contains i ∧ pays i q) at hi
        have hm : w.Contains i ∧ pays i q :=
          ((Finset.mem_filter (s := rows)
            (p := fun i => w.Contains i ∧ pays i q)).mp hi).2
        obtain ⟨hw,hpays⟩ := hm
        obtain ⟨hgl,hgh,hol,hoh,hdl,hdh⟩ := hw
        have hpos : 0 ≤ (initialFlag i).order := by
          dsimp [pays,p] at hpays
          have h := hpays.2.2
          omega
        obtain ⟨_, hidx, hcontact⟩ := hpays
        change -offset i ≤ (p.index : ℤ) at hidx
        change p.contact < (initialFlag i).order.toNat at hcontact
        change f i ∈ R
        simp only [initialFlag, offset] at hidx hcontact hpos
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · change f i ∈ (Ico (indexLo w) (indexHi w p)) ×ˢ (Ico (orderLo w p) (orderHi w))
          rw [Finset.mem_product]
          simp only [mem_Ico, f, indexLo, indexHi, orderLo, orderHi]
          omega
        · dsimp [f]
          omega
      · intro i _ j _ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        simp only [f] at h1 h2
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have hf := band_card (indexLo w) (indexHi w p) (orderLo w p) (orderHi w)
      ((w.gradeLo : ℤ)-3000) ((w.gradeHi : ℤ)-3000)
      (le_max_left _ _) (min_le_left _ _) (by omega)
    change 2 * (R.card : ℤ) = _ at hf
    rw [hsum, ← hf]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by decide)
  · rw [columnFee2, ite_eq_right hp]
    have hz (i : BlockIndex) : charge i q = 0 := by
      unfold charge pays
      simp [p,hp]
    simp [hz]

private theorem debit_le_fee_on (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi)
    (rows : Finset BlockIndex) (columns : Finset Column) :
    2 * ↑(∑ i ∈ rows, if w.Contains i then ∑ q ∈ columns, charge i q else 0) ≤
      ∑ q ∈ columns, columnFee2 w (columnPoint q) := by
  have h (i : BlockIndex) :
      (if w.Contains i then ∑ q ∈ columns, charge i q else 0) =
        ∑ q ∈ columns, if w.Contains i then charge i q else 0 := by
    split <;> simp [*]
  simp_rw [h]
  rw [sum_comm]
  push_cast
  rw [mul_sum]
  apply sum_le_sum
  intro q _
  have hq := column_le_fee_on w hgrade q rows
  push_cast at hq
  exact hq

theorem debit_le_fee (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi) :
    2 * (debit w : ℤ) ≤ ∑ q : Column, columnFee2 w (columnPoint q) :=
  debit_le_fee_on w hgrade univ univ

#print axioms debit_le_fee
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotRect

end Merged6967_Low48PrimaryPivotRect

section Merged6967_PrimaryTaperRankData
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 40000
set_option maxHeartbeats 0

namespace LambdaTaperFast
open TaperBudget (natOld rankNat natCell cap valuePower sumChunk rowSum sumRange)
open K1_13_2_3_7 (countParts natKernel)
open TaperBudget (removed)

private def target (d j h r : ℕ) (low atH : ℕ × ℕ) : ℕ :=
  if r = 0 then 0 else
  match low, atH, countParts (d-r) (h-3*r), countParts (d-r) (1650-j) with
  | (c,e), (c',e'), (f,g), (k,l) => e+c'+g+k - (c+e'+f+l)

private theorem old_split (a b c e c' e' f g k l : ℕ) :
    (a+e-(b+c)) - (a+e'+f+l-(b+c'+g+k)) =
      min (a+e-(b+c)) (e+c'+g+k-(c+e'+f+l)) := by omega

private theorem target_eq (d j h r : ℕ) :
    natOld d j - natKernel d j h r =
      min (natOld d j) (target d j h r (countParts d (1650-j)) (countParts d h)) := by
  rcases ht : countParts d 1651 with ⟨a,b⟩
  rcases hl : countParts d (1650-j) with ⟨c,e⟩
  by_cases hz : r = 0
  · simp [natOld, natKernel, target, ht, hl, hz]
  · rcases hh : countParts d h with ⟨c',e'⟩
    rcases ha : countParts (d-r) (h-3*r) with ⟨f,g⟩
    rcases hb : countParts (d-r) (1650-j) with ⟨k,l⟩
    simpa only [natOld, natKernel, target, ht, hl, hh, ha, hb, hz, ite_false] using
      old_split a b c e c' e' f g k l

private def rankFast (d q j p : ℕ) (top : ℕ × ℕ) : ℕ :=
  if q+j < 4650 then
    let h := 4650-q-j
    let low := countParts d (1650-j)
    let atH := countParts d h
    let old := top.1 + low.2 - (top.2 + low.1)
    let a := target d j h (removed d q) low atH
    if p = 0 then min old a
    else min (min old a) (old - natKernel (d-p) j h (removed (d-p) q))
  else 0

private theorem rankFast_eq (d q j p : ℕ) :
    rankFast d q j p (countParts d 1651) = rankNat d q j p := by
  by_cases hq : q+j < 4650
  · simp only [rankFast, rankNat, ite_eq_left hq]
    change (if p = 0 then min (natOld d j) (target d j (4650-q-j) (removed d q)
          (countParts d (1650-j)) (countParts d (4650-q-j)))
      else min (min (natOld d j) (target d j (4650-q-j) (removed d q)
          (countParts d (1650-j)) (countParts d (4650-q-j))))
        (natOld d j - natKernel (d-p) j (4650-q-j) (removed (d-p) q))) = _
    rw [← target_eq]
    by_cases hp : p = 0
    · simp [hp]
    · simp only [ite_eq_right hp]
      omega
  · simp [rankFast, rankNat, hq]

private def fastRow (J t : ℕ) : ℕ :=
  let q := 3514+t
  let d := cap q
  let tc := countParts d 1651
  let tb := countParts 1650 1651
  sumRange (fun j => rankFast 1650 q j 0 tb - rankFast d q j (valuePower d q j) tc) J

private theorem fastRow_eq (J t : ℕ) : fastRow J t = rowSum J t := by
  unfold fastRow rowSum
  apply congrArg (fun f : ℕ → ℕ => sumRange f J)
  funext j
  dsimp only [natCell]
  simp only [rankFast_eq]

private theorem fastRows (s n : ℕ) :
    sumChunk (fastRow 600) s n = sumChunk (rowSum 600) s n := by
  simp only [sumChunk, fastRow_eq]


-- Bounded taper simplifications, proved for the 499 × 600 live rectangle.
open K1_13_2_3_7 (natDen)

private def debt (d n : ℕ) : ℕ :=
  if n ≤ d+1 then 0 else natDen (n-d-1) + natDen (n-d-2) + natDen (n-d-3)

private theorem parts_mid (d n : ℕ) (hd : 2 ≤ d) (hn : n ≤ 2*d+3) :
    countParts d n = (natDen n, debt d n) := by
  have hm : n ≤ 3*d+1 := by omega
  have hmin : Nat.min n (3*d+1) = n := Nat.min_eq_left hm
  unfold countParts debt
  simp only [hmin]
  by_cases hs : n ≤ d+1 <;> simp [hs, hn]

private def targetSlim (d j h r low : ℕ) : ℕ :=
  if r = 0 then 0 else natDen h + low - (natDen (h-3*r) + debt (d-r) (1650-j))

private theorem targetSlim_eq (d j h r : ℕ) (hd : 2 ≤ d-r) (hm : 1651 ≤ 2*(d-r)+3)
    (hh : h ≤ d+1) (hr : h-3*r ≤ d-r+1) :
    target d j h r (countParts d (1650-j)) (countParts d h) =
      targetSlim d j h r (debt d (1650-j)) := by
  have hl := parts_mid d (1650-j) (by omega) (by omega)
  have ha := parts_mid d h (by omega) (by omega)
  have hb := parts_mid (d-r) (h-3*r) hd (by omega)
  have hc := parts_mid (d-r) (1650-j) hd (by omega)
  by_cases hz : r = 0
  · simp [target, targetSlim, hz]
  · simp only [target, targetSlim, if_neg hz, hl, ha, hb, hc, debt, if_pos hh, if_pos hr, Nat.add_zero]
    omega

private def rankSmall (d q j p : ℕ) (base : Bool) (oldHi topDebt : ℕ) : ℕ :=
  let h := 4650-q-j
  let loDebt := if base then 0 else debt d (1650-j)
  let old := oldHi + loDebt - (topDebt + natDen (1650-j))
  let cut := min old (targetSlim d j h (removed d q) loDebt)
  if p = 0 then cut else min cut (old - natKernel (q+4*j-3000) j h j)

private theorem rankSmall_eq (d q j p : ℕ) (base : Bool)
    (hd : 1080 ≤ d) (hq : 3514 ≤ q) (hqj : q+j < 4650) (hh : 4650-q-j ≤ d+1)
    (hb : base = true → d = 1650) (hpv : p ≠ 0 → p = valuePower d q j) :
    rankSmall d q j p base (natDen 1651) (debt d 1651) =
      rankFast d q j p (countParts d 1651) := by
  let r := removed d q
  let h := 4650-q-j
  have hr : 2 ≤ d-r := by dsimp [r]; unfold removed; omega
  have hm : 1651 ≤ 2*(d-r)+3 := by dsimp [r]; unfold removed; omega
  have hr' : h-3*r ≤ d-r+1 := by change h ≤ d+1 at hh; omega
  have hSlim := targetSlim_eq d j h r hr hm hh hr'
  have ht := parts_mid d 1651 (by omega) (by omega)
  have hl := parts_mid d (1650-j) (by omega) (by omega)
  have hDebt : (if base then 0 else debt d (1650-j)) = debt d (1650-j) := by
    cases base
    · rfl
    · rw [hb rfl]
      simp [debt, show 1650-j ≤ 1650+1 by omega]
  simp only [rankFast, if_pos hqj]
  change rankSmall d q j p base (natDen 1651) (debt d 1651) =
    (let low := countParts d (1650-j)
     let old := (countParts d 1651).1 + low.2 - ((countParts d 1651).2 + low.1)
     let a := target d j h r low (countParts d h)
     if p = 0 then min old a else min (min old a) (old - natKernel (d-p) j h (removed (d-p) q)))
  dsimp only
  rw [hSlim, ht, hl]
  unfold rankSmall
  rw [hDebt]
  by_cases hp : p = 0
  · simp [hp, r, h]
  · have hp' := hpv hp
    unfold valuePower at hp'
    have he : d-p = q+4*j-3000 := by omega
    have he' : removed (d-p) q = j := by unfold removed; omega
    have he'' : removed (q+4*j-3000) q = j := by unfold removed; omega
    simp [hp, he, he', he'', r, h]

private def compactRow (J t : ℕ) : ℕ :=
  let q := 3514+t
  let d := cap q
  let hi := natDen 1651
  let td := debt d 1651
  sumRange (fun j => rankSmall 1650 q j 0 true hi 0 -
    rankSmall d q j (valuePower d q j) false hi td) J

private theorem exact_cell (t j : ℕ) (ht : t < 499) (hj : j < 600) :
    rankSmall 1650 (3514+t) j 0 true (natDen 1651) 0 -
      rankSmall (cap (3514+t)) (3514+t) j (valuePower (cap (3514+t)) (3514+t) j)
        false (natDen 1651) (debt (cap (3514+t)) 1651) =
    rankFast 1650 (3514+t) j 0 (countParts 1650 1651) -
      rankFast (cap (3514+t)) (3514+t) j (valuePower (cap (3514+t)) (3514+t) j)
        (countParts (cap (3514+t)) 1651) := by
  have hqj : 3514+t+j < 4650 := by omega
  have hc : 1080 ≤ cap (3514+t) := by unfold cap; split <;> omega
  have hh : 4650-(3514+t)-j ≤ cap (3514+t)+1 := by unfold cap; split <;> omega
  have hz : debt 1650 1651 = 0 := rfl
  have hbase := rankSmall_eq 1650 (3514+t) j 0 true (by decide) (by omega) hqj
    (by omega) (fun _ => rfl) (fun hp => False.elim (hp rfl))
  rw [hz] at hbase
  rw [hbase, rankSmall_eq (cap (3514+t)) (3514+t) j (valuePower (cap (3514+t)) (3514+t) j)
    false hc (by omega) hqj hh (by intro hf; cases hf) (fun _ => rfl)]

private theorem sumRange_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, f i = g i) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [h n (Nat.lt_succ_self n), ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))]

private theorem compactRows (s n : ℕ) (h : s+n ≤ 499) :
    sumChunk (compactRow 600) s n = sumChunk (rowSum 600) s n := by
  rw [← fastRows]
  unfold sumChunk
  apply sumRange_congr
  intro i hi
  unfold compactRow fastRow
  apply sumRange_congr
  intro j hj
  exact exact_cell (s+i) j (by omega) hj

-- Cut the exact zero suffix of every live taper row.
private def rowCut (q d : ℕ) : ℕ :=
  max (4650-q-3*removed d q) (1649-(d-removed d q))

private theorem den_mono : Monotone natDen := by
  intro x y h
  cases x with
  | zero => exact Nat.zero_le _
  | succ x =>
    cases y with
    | zero => omega
    | succ y =>
      have hxy : x ≤ y := Nat.le_of_succ_le_succ h
      have h' : 2*x+21 ≤ 2*y+21 := by omega
      simp only [natDen]
      exact Nat.succ_le_succ (Nat.div_le_div_right (Nat.mul_le_mul hxy
        (Nat.add_le_add_right (Nat.mul_le_mul hxy h') 66)))

private abbrev TailGuard (d q s : ℕ) : Prop :=
  removed d q ≠ 0 ∧ 4650-q-s ≤ 3*removed d q ∧ 1650-s ≤ d-removed d q+1 ∧
    debt d 1651 + natDen (1650-s) + natDen (4650-q-s) ≤ natDen 1651

private abbrev RowGuard (t : ℕ) : Prop :=
  let q := 3514+t
  let d := cap q
  let s := rowCut q d
  s ≤ 600 ∧ 3000+d ≤ q+4*s ∧ TailGuard 1650 q s ∧ TailGuard d q s

private theorem rowGuards : (List.range 499).all (fun t => decide (RowGuard t)) = true := by
  decide +kernel

private theorem rowGuard (t : ℕ) (ht : t < 499) : RowGuard t :=
  of_decide_eq_true (List.all_eq_true.mp rowGuards t (List.mem_range.mpr ht))

private theorem rankTail (d q s j : ℕ) (base : Bool) (h : TailGuard d q s) (hs : s ≤ j) :
    rankSmall d q j 0 base (natDen 1651) (debt d 1651) = natDen (4650-q-j) := by
  obtain ⟨hr, hh, hn, hsum⟩ := h
  have hh' : 4650-q-j ≤ 3*removed d q := by omega
  have hn' : 1650-j ≤ d-removed d q+1 := by omega
  have hn0 : 1650-j ≤ d+1 := by omega
  have hm := den_mono (show 1650-j ≤ 1650-s by omega)
  have hm' := den_mono (show 4650-q-j ≤ 4650-q-s by omega)
  have hold : natDen (4650-q-j) ≤ natDen 1651 - (debt d 1651 + natDen (1650-j)) := by omega
  have hl : debt d (1650-j) = 0 := by simp [debt, hn0]
  have hl' : debt (d-removed d q) (1650-j) = 0 := by simp [debt, hn']
  have hb : (if base then 0 else debt d (1650-j)) = 0 := by simp [hl]
  simp only [rankSmall, targetSlim, hb, hr, hl', if_pos rfl, if_neg,
    Nat.sub_eq_zero_of_le hh', show natDen 0 = 0 from rfl, Nat.add_zero, Nat.sub_zero]
  exact min_eq_right hold

private theorem prefix_of_zero_tail {f : ℕ → ℕ} {s n : ℕ} (hs : s ≤ n)
    (hz : ∀ j, s ≤ j → j < n → f j = 0) : sumRange f s = sumRange f n := by
  induction n with
  | zero => rw [show s = 0 by omega]
  | succ n ih =>
    by_cases he : s = n+1
    · rw [he]
    · have hsn : s ≤ n := by omega
      rw [show sumRange f (n+1) = sumRange f n + f n from rfl,
        hz n hsn (Nat.lt_succ_self n), Nat.add_zero]
      exact ih hsn (fun j hj hlt => hz j hj (Nat.lt_succ_of_lt hlt))

private def clippedRow (t : ℕ) : ℕ := compactRow (rowCut (3514+t) (cap (3514+t))) t

private theorem clippedRow_eq (t : ℕ) (ht : t < 499) : clippedRow t = compactRow 600 t := by
  let q := 3514+t
  let d := cap q
  let s := rowCut q d
  obtain ⟨hs, hp, hb, hd⟩ := rowGuard t ht
  unfold clippedRow compactRow
  dsimp only
  apply prefix_of_zero_tail hs
  intro j hj _
  have hp' : valuePower d q j = 0 := by
    show valuePower (cap (3514+t)) (3514+t) j = 0
    unfold valuePower; omega
  have hz : debt 1650 1651 = 0 := rfl
  have hbase := rankTail 1650 q s j true hb hj
  rw [hz] at hbase
  rw [hp', hbase, rankTail d q s j false hd hj, Nat.sub_self]

private theorem clippedRows (s n : ℕ) (h : s+n ≤ 499) :
    sumChunk clippedRow s n = sumChunk (rowSum 600) s n := by
  rw [← compactRows _ _ h]
  unfold sumChunk
  apply sumRange_congr
  intro i hi
  exact clippedRow_eq (s+i) (by omega)

end LambdaTaperFast

namespace TaperBudget

open K1_13 (Geom)
open K1_13_2 (BlockIndex)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

private abbrev row := rowSum 600

private theorem rows0 : sumChunk row 0 8 = 2989340613 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
private theorem rows8 : sumChunk row 8 8 = 3064721710 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
private theorem rows16 : sumChunk row 16 8 = 3141001317 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
private theorem rows24 : sumChunk row 24 8 = 3221706942 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
private theorem rows32 : sumChunk row 32 8 = 3300717247 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
private theorem rows40 : sumChunk row 40 8 = 3381208680 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
private theorem rows48 : sumChunk row 48 8 = 3468350919 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows56 : sumChunk row 56 8 = 3553901216 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows64 : sumChunk row 64 8 = 3641005048 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows72 : sumChunk row 72 8 = 3736730143 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows80 : sumChunk row 80 8 = 3831592054 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows88 : sumChunk row 88 8 = 3927238474 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows96 : sumChunk row 96 8 = 4032675047 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows104 : sumChunk row 104 8 = 4139011739 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows112 : sumChunk row 112 8 = 4244367622 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows120 : sumChunk row 120 8 = 4359842998 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows128 : sumChunk row 128 8 = 4479074534 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows136 : sumChunk row 136 8 = 4594535489 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows144 : sumChunk row 144 8 = 4719447871 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows152 : sumChunk row 152 8 = 4852262991 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows160 : sumChunk row 160 8 = 4977493749 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows168 : sumChunk row 168 8 = 5110525726 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows176 : sumChunk row 176 8 = 5256836096 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows184 : sumChunk row 184 8 = 5390743377 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows192 : sumChunk row 192 8 = 5529753127 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows200 : sumChunk row 200 8 = 5688594654 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows208 : sumChunk row 208 8 = 5829308790 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows216 : sumChunk row 216 8 = 5971489118 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows224 : sumChunk row 224 8 = 6141122417 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows232 : sumChunk row 232 8 = 6286108608 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows240 : sumChunk row 240 8 = 6431540425 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows248 : sumChunk row 248 8 = 6602041516 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows256 : sumChunk row 256 8 = 6751509822 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows264 : sumChunk row 264 8 = 6896640999 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows272 : sumChunk row 272 8 = 7063450232 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows280 : sumChunk row 280 8 = 7213806800 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows288 : sumChunk row 288 8 = 7354364209 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows296 : sumChunk row 296 8 = 7512114721 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows304 : sumChunk row 304 8 = 7658789195 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows312 : sumChunk row 312 8 = 7789842793 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows320 : sumChunk row 320 8 = 7932571009 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows328 : sumChunk row 328 8 = 8070335283 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows336 : sumChunk row 336 8 = 8185948289 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows344 : sumChunk row 344 8 = 8307233701 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows352 : sumChunk row 352 8 = 8429242212 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows360 : sumChunk row 360 8 = 8522803077 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows368 : sumChunk row 368 8 = 8615444240 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows376 : sumChunk row 376 8 = 8713859927 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows384 : sumChunk row 384 8 = 8777670653 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows392 : sumChunk row 392 8 = 8833672402 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows400 : sumChunk row 400 8 = 8899053394 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows408 : sumChunk row 408 8 = 8924421886 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows416 : sumChunk row 416 8 = 8935210038 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows424 : sumChunk row 424 8 = 8956971540 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows432 : sumChunk row 432 8 = 8934265132 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows440 : sumChunk row 440 8 = 8893651408 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows448 : sumChunk row 448 8 = 8853548727 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows456 : sumChunk row 456 8 = 8774993977 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows464 : sumChunk row 464 8 = 8671988451 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows472 : sumChunk row 472 8 = 8559112828 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows480 : sumChunk row 480 8 = 8411849481 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows488 : sumChunk row 488 8 = 8234559803 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel
theorem rows496 : sumChunk row 496 3 = 3036818172 := by
  rw [← LambdaTaperFast.clippedRows _ _ (by decide)]
  decide +kernel

private theorem join (lo n m next full : ℕ) (a b result : ℕ)
    (hLen : n+m = full) (hStart : lo+n = next) (hValue : Nat.add a b = result)
    (ha : sumChunk row lo n = a) (hb : sumChunk row next m = b) :
    sumChunk row lo full = result := by
  rw [← hLen, sumChunk_add row, ha, hStart, hb]
  exact hValue

theorem sum_checked : sumChunk row 0 499 = 396610034658 := by
  have tail496 : sumChunk row 496 3 = 3036818172 :=
    rows496
  have tail488 : sumChunk row 488 11 = 11271377975 :=
    join 488 8 3 496 11 8234559803 3036818172 11271377975 (by decide) (by decide) (by decide) rows488 tail496
  have tail480 : sumChunk row 480 19 = 19683227456 :=
    join 480 8 11 488 19 8411849481 11271377975 19683227456 (by decide) (by decide) (by decide) rows480 tail488
  have tail472 : sumChunk row 472 27 = 28242340284 :=
    join 472 8 19 480 27 8559112828 19683227456 28242340284 (by decide) (by decide) (by decide) rows472 tail480
  have tail464 : sumChunk row 464 35 = 36914328735 :=
    join 464 8 27 472 35 8671988451 28242340284 36914328735 (by decide) (by decide) (by decide) rows464 tail472
  have tail456 : sumChunk row 456 43 = 45689322712 :=
    join 456 8 35 464 43 8774993977 36914328735 45689322712 (by decide) (by decide) (by decide) rows456 tail464
  have tail448 : sumChunk row 448 51 = 54542871439 :=
    join 448 8 43 456 51 8853548727 45689322712 54542871439 (by decide) (by decide) (by decide) rows448 tail456
  have tail440 : sumChunk row 440 59 = 63436522847 :=
    join 440 8 51 448 59 8893651408 54542871439 63436522847 (by decide) (by decide) (by decide) rows440 tail448
  have tail432 : sumChunk row 432 67 = 72370787979 :=
    join 432 8 59 440 67 8934265132 63436522847 72370787979 (by decide) (by decide) (by decide) rows432 tail440
  have tail424 : sumChunk row 424 75 = 81327759519 :=
    join 424 8 67 432 75 8956971540 72370787979 81327759519 (by decide) (by decide) (by decide) rows424 tail432
  have tail416 : sumChunk row 416 83 = 90262969557 :=
    join 416 8 75 424 83 8935210038 81327759519 90262969557 (by decide) (by decide) (by decide) rows416 tail424
  have tail408 : sumChunk row 408 91 = 99187391443 :=
    join 408 8 83 416 91 8924421886 90262969557 99187391443 (by decide) (by decide) (by decide) rows408 tail416
  have tail400 : sumChunk row 400 99 = 108086444837 :=
    join 400 8 91 408 99 8899053394 99187391443 108086444837 (by decide) (by decide) (by decide) rows400 tail408
  have tail392 : sumChunk row 392 107 = 116920117239 :=
    join 392 8 99 400 107 8833672402 108086444837 116920117239 (by decide) (by decide) (by decide) rows392 tail400
  have tail384 : sumChunk row 384 115 = 125697787892 :=
    join 384 8 107 392 115 8777670653 116920117239 125697787892 (by decide) (by decide) (by decide) rows384 tail392
  have tail376 : sumChunk row 376 123 = 134411647819 :=
    join 376 8 115 384 123 8713859927 125697787892 134411647819 (by decide) (by decide) (by decide) rows376 tail384
  have tail368 : sumChunk row 368 131 = 143027092059 :=
    join 368 8 123 376 131 8615444240 134411647819 143027092059 (by decide) (by decide) (by decide) rows368 tail376
  have tail360 : sumChunk row 360 139 = 151549895136 :=
    join 360 8 131 368 139 8522803077 143027092059 151549895136 (by decide) (by decide) (by decide) rows360 tail368
  have tail352 : sumChunk row 352 147 = 159979137348 :=
    join 352 8 139 360 147 8429242212 151549895136 159979137348 (by decide) (by decide) (by decide) rows352 tail360
  have tail344 : sumChunk row 344 155 = 168286371049 :=
    join 344 8 147 352 155 8307233701 159979137348 168286371049 (by decide) (by decide) (by decide) rows344 tail352
  have tail336 : sumChunk row 336 163 = 176472319338 :=
    join 336 8 155 344 163 8185948289 168286371049 176472319338 (by decide) (by decide) (by decide) rows336 tail344
  have tail328 : sumChunk row 328 171 = 184542654621 :=
    join 328 8 163 336 171 8070335283 176472319338 184542654621 (by decide) (by decide) (by decide) rows328 tail336
  have tail320 : sumChunk row 320 179 = 192475225630 :=
    join 320 8 171 328 179 7932571009 184542654621 192475225630 (by decide) (by decide) (by decide) rows320 tail328
  have tail312 : sumChunk row 312 187 = 200265068423 :=
    join 312 8 179 320 187 7789842793 192475225630 200265068423 (by decide) (by decide) (by decide) rows312 tail320
  have tail304 : sumChunk row 304 195 = 207923857618 :=
    join 304 8 187 312 195 7658789195 200265068423 207923857618 (by decide) (by decide) (by decide) rows304 tail312
  have tail296 : sumChunk row 296 203 = 215435972339 :=
    join 296 8 195 304 203 7512114721 207923857618 215435972339 (by decide) (by decide) (by decide) rows296 tail304
  have tail288 : sumChunk row 288 211 = 222790336548 :=
    join 288 8 203 296 211 7354364209 215435972339 222790336548 (by decide) (by decide) (by decide) rows288 tail296
  have tail280 : sumChunk row 280 219 = 230004143348 :=
    join 280 8 211 288 219 7213806800 222790336548 230004143348 (by decide) (by decide) (by decide) rows280 tail288
  have tail272 : sumChunk row 272 227 = 237067593580 :=
    join 272 8 219 280 227 7063450232 230004143348 237067593580 (by decide) (by decide) (by decide) rows272 tail280
  have tail264 : sumChunk row 264 235 = 243964234579 :=
    join 264 8 227 272 235 6896640999 237067593580 243964234579 (by decide) (by decide) (by decide) rows264 tail272
  have tail256 : sumChunk row 256 243 = 250715744401 :=
    join 256 8 235 264 243 6751509822 243964234579 250715744401 (by decide) (by decide) (by decide) rows256 tail264
  have tail248 : sumChunk row 248 251 = 257317785917 :=
    join 248 8 243 256 251 6602041516 250715744401 257317785917 (by decide) (by decide) (by decide) rows248 tail256
  have tail240 : sumChunk row 240 259 = 263749326342 :=
    join 240 8 251 248 259 6431540425 257317785917 263749326342 (by decide) (by decide) (by decide) rows240 tail248
  have tail232 : sumChunk row 232 267 = 270035434950 :=
    join 232 8 259 240 267 6286108608 263749326342 270035434950 (by decide) (by decide) (by decide) rows232 tail240
  have tail224 : sumChunk row 224 275 = 276176557367 :=
    join 224 8 267 232 275 6141122417 270035434950 276176557367 (by decide) (by decide) (by decide) rows224 tail232
  have tail216 : sumChunk row 216 283 = 282148046485 :=
    join 216 8 275 224 283 5971489118 276176557367 282148046485 (by decide) (by decide) (by decide) rows216 tail224
  have tail208 : sumChunk row 208 291 = 287977355275 :=
    join 208 8 283 216 291 5829308790 282148046485 287977355275 (by decide) (by decide) (by decide) rows208 tail216
  have tail200 : sumChunk row 200 299 = 293665949929 :=
    join 200 8 291 208 299 5688594654 287977355275 293665949929 (by decide) (by decide) (by decide) rows200 tail208
  have tail192 : sumChunk row 192 307 = 299195703056 :=
    join 192 8 299 200 307 5529753127 293665949929 299195703056 (by decide) (by decide) (by decide) rows192 tail200
  have tail184 : sumChunk row 184 315 = 304586446433 :=
    join 184 8 307 192 315 5390743377 299195703056 304586446433 (by decide) (by decide) (by decide) rows184 tail192
  have tail176 : sumChunk row 176 323 = 309843282529 :=
    join 176 8 315 184 323 5256836096 304586446433 309843282529 (by decide) (by decide) (by decide) rows176 tail184
  have tail168 : sumChunk row 168 331 = 314953808255 :=
    join 168 8 323 176 331 5110525726 309843282529 314953808255 (by decide) (by decide) (by decide) rows168 tail176
  have tail160 : sumChunk row 160 339 = 319931302004 :=
    join 160 8 331 168 339 4977493749 314953808255 319931302004 (by decide) (by decide) (by decide) rows160 tail168
  have tail152 : sumChunk row 152 347 = 324783564995 :=
    join 152 8 339 160 347 4852262991 319931302004 324783564995 (by decide) (by decide) (by decide) rows152 tail160
  have tail144 : sumChunk row 144 355 = 329503012866 :=
    join 144 8 347 152 355 4719447871 324783564995 329503012866 (by decide) (by decide) (by decide) rows144 tail152
  have tail136 : sumChunk row 136 363 = 334097548355 :=
    join 136 8 355 144 363 4594535489 329503012866 334097548355 (by decide) (by decide) (by decide) rows136 tail144
  have tail128 : sumChunk row 128 371 = 338576622889 :=
    join 128 8 363 136 371 4479074534 334097548355 338576622889 (by decide) (by decide) (by decide) rows128 tail136
  have tail120 : sumChunk row 120 379 = 342936465887 :=
    join 120 8 371 128 379 4359842998 338576622889 342936465887 (by decide) (by decide) (by decide) rows120 tail128
  have tail112 : sumChunk row 112 387 = 347180833509 :=
    join 112 8 379 120 387 4244367622 342936465887 347180833509 (by decide) (by decide) (by decide) rows112 tail120
  have tail104 : sumChunk row 104 395 = 351319845248 :=
    join 104 8 387 112 395 4139011739 347180833509 351319845248 (by decide) (by decide) (by decide) rows104 tail112
  have tail96 : sumChunk row 96 403 = 355352520295 :=
    join 96 8 395 104 403 4032675047 351319845248 355352520295 (by decide) (by decide) (by decide) rows96 tail104
  have tail88 : sumChunk row 88 411 = 359279758769 :=
    join 88 8 403 96 411 3927238474 355352520295 359279758769 (by decide) (by decide) (by decide) rows88 tail96
  have tail80 : sumChunk row 80 419 = 363111350823 :=
    join 80 8 411 88 419 3831592054 359279758769 363111350823 (by decide) (by decide) (by decide) rows80 tail88
  have tail72 : sumChunk row 72 427 = 366848080966 :=
    join 72 8 419 80 427 3736730143 363111350823 366848080966 (by decide) (by decide) (by decide) rows72 tail80
  have tail64 : sumChunk row 64 435 = 370489086014 :=
    join 64 8 427 72 435 3641005048 366848080966 370489086014 (by decide) (by decide) (by decide) rows64 tail72
  have tail56 : sumChunk row 56 443 = 374042987230 :=
    join 56 8 435 64 443 3553901216 370489086014 374042987230 (by decide) (by decide) (by decide) rows56 tail64
  have tail48 : sumChunk row 48 451 = 377511338149 :=
    join 48 8 443 56 451 3468350919 374042987230 377511338149 (by decide) (by decide) (by decide) rows48 tail56
  have tail40 : sumChunk row 40 459 = 380892546829 :=
    join 40 8 451 48 459 3381208680 377511338149 380892546829 (by decide) (by decide) (by decide) rows40 tail48
  have tail32 : sumChunk row 32 467 = 384193264076 :=
    join 32 8 459 40 467 3300717247 380892546829 384193264076 (by decide) (by decide) (by decide) rows32 tail40
  have tail24 : sumChunk row 24 475 = 387414971018 :=
    join 24 8 467 32 475 3221706942 384193264076 387414971018 (by decide) (by decide) (by decide) rows24 tail32
  have tail16 : sumChunk row 16 483 = 390555972335 :=
    join 16 8 475 24 483 3141001317 387414971018 390555972335 (by decide) (by decide) (by decide) rows16 tail24
  have tail8 : sumChunk row 8 491 = 393620694045 :=
    join 8 8 483 16 491 3064721710 390555972335 393620694045 (by decide) (by decide) (by decide) rows8 tail16
  have tail0 : sumChunk row 0 499 = 396610034658 :=
    join 0 8 491 8 499 2989340613 393620694045 396610034658 (by decide) (by decide) (by decide) rows0 tail8
  exact tail0

end TaperBudget

end Merged6967_PrimaryTaperRankData

section Merged6967_Wide50EulerPrimaryBlock
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Wide50EulerPrimary
open K1_13_2 K1_13_2_3
open scoped BigOperators

private def reduceFlag (F : Flag) (a b : ℕ) : Flag :=
  ⟨F.degree - a - b, F.lower - 3*b, F.upper - 3*b,
    F.cap - b, F.order - 2*b⟩

private theorem residual_eq (F : Flag) (a b : ℕ) :
    residualFlag F (Powers.expand ⟨a,b,0⟩) = reduceFlag F a b := by
  simp [residualFlag, reduceFlag, factorFlag, Powers.expand, Fin.sum_univ_succ, sub_sub]
  constructor <;> ring

/-- Two residual factors give a direct arithmetic formula for one compact block. -/
def twoFactorBound (k : ℕ) (i : BlockIndex) (a b : ℕ) : ℕ :=
  let F := TaperNormalize.initialFlag k i
  if F.order ≤ 0 then 0 else
    let active := oldCount (TaperNormalize.activeFlag k i)
    let lower := max 0 (max (kernelLower F) (kernelLower (reduceFlag F a b)))
    (min active (oldCount F - lower)).toNat

theorem twoFactorBound_eq (k : ℕ) (i : BlockIndex) (a b : ℕ) :
    twoFactorBound k i a b = TaperNormalize.bound k i (Powers.expand ⟨a,b,0⟩) := by
  simp only [twoFactorBound, TaperNormalize.bound, residual_eq]
def denN (u : ℕ) : ℕ :=
  let q := u / 6
  let r := u % 6
  1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)

def dd (a b : ℕ) : ℕ := if b ≤ a then denN (a - b) else 0

theorem den_alg (q r : ℕ) (hr : r < 6) :
    (1 + (r:ℤ)*(r+1)/2 + q*(22+7*r+ r*(r-1)/2) + (57+6*r)*(q*(q-1)/2) + 6*q*(q-1)*(q-2) : ℤ) =
    ((1 + r*(r+1)/2 + q*(22+7*r+r*(r-1)/2) + (57+6*r)*(q*(q-1)/2) + 6*q*(q-1)*(q-2) : ℕ):ℤ) := by
  interval_cases r <;> rcases q with _ | _ | _ | q <;> simp <;> omega

theorem denominator_nat (v c : ℕ) : denominator ((v : ℤ) - c) = ((dd v c : ℕ) : ℤ) := by
  unfold dd
  by_cases h : c ≤ v
  · rw [if_pos h]
    have e : (v : ℤ) - c = ((v - c : ℕ) : ℤ) := by omega
    rw [e]
    generalize v - c = u
    unfold denominator denN
    rw [if_neg (by omega)]
    have hq : ((u:ℤ)/6) = ((u/6 : ℕ):ℤ) := by omega
    have hr : ((u:ℤ)%6) = ((u%6 : ℕ):ℤ) := by omega
    simp only [hq, hr]
    exact den_alg (u/6) (u%6) (by omega)
  · rw [if_neg h]
    unfold denominator
    rw [if_pos (by omega)]
    rfl

def cumP (d u : ℕ) : ℤ :=
  let v := min u (3*d)
  ((denN v + dd v (2*d+3) + dd v (2*d+4) + dd v (2*d+5) : ℕ) : ℤ) -
    ((dd v (d+1) + dd v (d+2) + dd v (d+3) + dd v (3*d+6) : ℕ) : ℤ)
def cumI (d u : ℤ) : ℤ := if d < 0 || u < 0 then 0 else cumP d.toNat u.toNat

theorem dd_zero (v : ℕ) : dd v 0 = denN v := by simp [dd]

theorem cumulative_eq (d u : ℤ) : cumulative d u = cumI d u := by
  unfold cumulative cumI
  by_cases h : d < 0 || u < 0
  · simp [h]
  · rw [if_neg h, if_neg h]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h
    obtain ⟨hd, hu⟩ := h
    obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le hd
    obtain ⟨u', rfl⟩ := Int.eq_ofNat_of_zero_le hu
    simp only [Int.toNat_natCast]
    unfold cumP
    have hv : min (u' : ℤ) (3 * (d' : ℤ)) = ((min u' (3*d' ) : ℕ) : ℤ) := by push_cast; rfl
    rw [hv]
    generalize min u' (3*d') = v
    have e0 := denominator_nat v 0
    have e1 := denominator_nat v (d'+1)
    have e2 := denominator_nat v (d'+2)
    have e3 := denominator_nat v (d'+3)
    have e4 := denominator_nat v (2*d'+3)
    have e5 := denominator_nat v (2*d'+4)
    have e6 := denominator_nat v (2*d'+5)
    have e7 := denominator_nat v (3*d'+6)
    push_cast at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
    rw [dd_zero] at e0
    simp only [sub_zero] at e0
    have a1 : (v:ℤ) - d' - 1 = v - (d' + 1) := by ring
    have a2 : (v:ℤ) - d' - 2 = v - (d' + 2) := by ring
    have a3 : (v:ℤ) - d' - 3 = v - (d' + 3) := by ring
    have a4 : (v:ℤ) - 2*d' - 3 = v - (2*d' + 3) := by ring
    have a5 : (v:ℤ) - 2*d' - 4 = v - (2*d' + 4) := by ring
    have a6 : (v:ℤ) - 2*d' - 5 = v - (2*d' + 5) := by ring
    have a7 : (v:ℤ) - 3*d' - 6 = v - (3*d' + 6) := by ring
    rw [a1, a2, a3, a4, a5, a6, a7, e0, e1, e2, e3, e4, e5, e6, e7]
    push_cast
    ring

def cappedCountI (d u cap : ℤ) : ℤ :=
  if cap < 0 then 0 else cumI d u - cumI (d - cap - 1) (u - 3 * (cap + 1))
theorem cappedCount_eq : cappedCount = cappedCountI := by
  funext d u cap
  simp only [cappedCount, cappedCountI, cumulative_eq]
def oldCountI (F : Flag) : ℤ :=
  cappedCountI F.degree F.upper F.cap -
    cappedCountI F.degree (min F.upper (F.lower - 1)) F.cap
theorem oldCount_eq : oldCount = oldCountI := by
  funext F
  simp only [oldCount, oldCountI, cappedCount_eq]
def targetCountI (F : Flag) : ℤ :=
  let balance := F.order - 1 - F.lower + F.degree
  if balance < 0 then 0 else
    let removed := min F.degree (balance / 4) + 1
    cumI F.degree (F.order - 1) - cumI (F.degree - removed) (F.order - 1 - 3 * removed) -
      cumI F.degree (F.lower - 1) + cumI (F.degree - removed) (F.lower - 1)
theorem targetCount_eq : targetCount = targetCountI := by
  funext F
  simp only [targetCount, targetCountI, cumulative_eq]
def kernelLowerI (F : Flag) : ℤ :=
  if F.degree < 0 || F.upper < 0 || F.cap < 0 then 0 else oldCountI F - targetCountI F
theorem kernelLower_eq : kernelLower = kernelLowerI := by
  funext F
  simp only [kernelLower, kernelLowerI, oldCount_eq, targetCount_eq]

def twoFactorBoundI (k : ℕ) (i : BlockIndex) (a b : ℕ) : ℕ :=
  let F := TaperNormalize.initialFlag k i
  if F.order ≤ 0 then 0 else
    let active := oldCountI (TaperNormalize.activeFlag k i)
    let lower := max 0 (max (kernelLowerI F) (kernelLowerI (reduceFlag F a b)))
    (min active (oldCountI F - lower)).toNat

theorem twoFactorBoundI_eq (k : ℕ) (i : BlockIndex) (a b : ℕ) :
    twoFactorBoundI k i a b = twoFactorBound k i a b := by
  simp only [twoFactorBoundI, twoFactorBound, oldCount_eq, kernelLower_eq]

end Wide50EulerPrimary

end Merged6967_Wide50EulerPrimaryBlock
