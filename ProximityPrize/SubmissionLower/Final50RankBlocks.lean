import ProximityPrize.SubmissionLower.RankRows82190
import ProximityPrize.SubmissionLower.Final50AnchorSpace
import ProximityPrize.SubmissionLower.Fast063

-- merged module Final50RankCore
section Merged_Final50RankCore
namespace Final50RankCore
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace bandCount backShift targetOrder bandSpace_finite finrank_bandSpace)
open AnchorPivot82180 (encode)
open MvPolynomial
open scoped BigOperators
open private band_mono from ProximityPrize.SubmissionLower.RankRows82190
open private independent from ProximityPrize.SubmissionLower.AnchorPivotRank82180

abbrev Row := RankRows82190.Row

def orderCutoff (s : ℕ) (g : ℤ) : ℤ := 99 - (s : ℤ) - g

private def accept (s : ℕ) (g : ℤ) (r : Row) : Bool :=
  decide (-g ≤ (r.index : ℤ) ∧ (orderCutoff s g).toNat ≤ r.ord)

noncomputable def blockAt (d s : ℕ) (g : ℤ) : bandSpace d (-g) 55 14 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _

def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 55 ∧ x.top ≤ 14 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)

def gradeFee (s : ℕ) (rows : List Row) : ℕ :=
  (rows.map (fun r => 99 + r.index - (s + r.ord))).sum

def covers (d : ℕ) (rows : List Row) : Prop :=
  ∀ i : Fin 56, bandCount d (i.val : ℤ) 55 14 ≤
    (rows.filter (fun r => decide (i.val ≤ r.index))).length

private theorem row_kernel (d s : ℕ) (g : ℤ) (r : Row) (hv : good d r = true)
    (ha : accept s g r = true) :
    ∃ w : LinearMap.ker (blockAt d s g), ((w.val : Form) = r.form) ∧
      (encode (w.val : Form)).degree = (r.tag : ℕ) := by
  obtain ⟨hd,hl,hh,ht,ho,hk⟩ := of_decide_eq_true hv
  obtain ⟨hl',ho'⟩ := of_decide_eq_true ha
  have hb := r.sound.band
  rw [hd] at hb
  let w : bandSpace d (-g) 55 14 := ⟨r.form,
    band_mono (hl'.trans (Int.ofNat_le.mpr hl)) (by exact_mod_cast hh) ht hb⟩
  have hw : w ∈ LinearMap.ker (blockAt d s g) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ (ho'.trans ho) r.sound.contact
  exact ⟨⟨w,hw⟩,rfl,r.sound.degree.trans (congrArg (fun n : ℕ => (n : WithBot ℕ)) hk)⟩



theorem count_bound (rows : List Row) (d s : ℕ) (g : ℤ)
    (good : ∀ r ∈ rows, good d r = true)
    (sorted : rows.Pairwise fun a b => a.tag < b.tag) :
    Module.finrank Geom (LinearMap.range (blockAt d s g)) + (rows.filter (accept s g)).length ≤
      bandCount d (-g) 55 14 := by
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
    encode.toLinearMap.comp ((bandSpace d (-g) 55 14).subtype.comp (LinearMap.ker (blockAt d s g)).subtype)
  have hw := independent embed w _ hmono.injective (fun i => (Classical.choose_spec (h i)).2)
  let : Module.Finite Geom (bandSpace d (-g) 55 14) := bandSpace_finite _ _ _ _
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
    (g : ℤ) (hg : -55 ≤ g) :
    bandCount d (-g) 55 14 ≤ (rows.filter (fun r => decide (-g ≤ (r.index : ℤ)))).length := by
  let i : Fin 56 := ⟨(-g).toNat,by omega⟩
  have hn (c f : ℕ) : max (0 : ℤ) (-g - 2*c - 3*f) =
      max 0 ((i.val : ℤ) - 2*c - 3*f) := by dsimp [i]; omega
  have hh : bandCount d (-g) 55 14 = bandCount d (i.val : ℤ) 55 14 := by
    simp only [bandCount,hn]
  have he (r : Row) : (-g ≤ (r.index : ℤ)) ↔ (i.val ≤ r.index) := by dsimp [i]; omega
  simp_rw [hh,he]
  exact hc i

private theorem charge_offsets (s : ℕ) (r : Row) :
    (∑ i : Fin 154, charge s ((i.val : ℤ) - 55) r) ≤ 99 + r.index - (s + r.ord) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => charge s ((i : ℤ) - 55) r)]
  unfold charge
  rw [Finset.sum_boole]
  have hs : (Finset.range 154).filter (fun i : ℕ => -((i : ℤ) - 55) ≤ r.index ∧
      r.ord < (orderCutoff s ((i : ℤ) - 55)).toNat) ⊆
      Finset.Ico (55 - r.index) (154 - (s + r.ord)) := by
    intro i hi
    obtain ⟨_,a,b⟩ := Finset.mem_filter.mp hi
    unfold orderCutoff at b
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have h := Finset.card_le_card hs
  rw [Nat.card_Ico] at h
  exact h.trans (by omega)

private theorem list_charge_offsets (s : ℕ) (rows : List Row) :
    (∑ i : Fin 154, (rows.map (charge s ((i.val : ℤ) - 55))).sum) ≤ gradeFee s rows := by
  induction rows with
  | nil => simp [gradeFee]
  | cons r rows ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
    exact Nat.add_le_add (charge_offsets s r) ih

/-- Sum the individual rank charges once per pivot across all offsets of one grade. -/
theorem grade_bound (s d : ℕ) (rows : List Row) (hg : ∀ r ∈ rows, good d r = true)
    (hs : rows.Pairwise fun a b => a.tag < b.tag) (hc : covers d rows) :
    (∑ i : Fin 154, Module.finrank Geom (LinearMap.range (blockAt d s ((i.val : ℤ) - 55)))) ≤
      gradeFee s rows := by
  apply le_trans (Finset.sum_le_sum (g := fun i : Fin 154 =>
    (rows.map (charge s ((i.val : ℤ) - 55))).sum) ?_) (list_charge_offsets s rows)
  intro i _
  let g := (i.val : ℤ) - 55
  have h := count_bound rows d s g hg hs
  have u := coverage_at hc g (by dsimp [g]; omega)
  rw [filter_split s g rows] at u
  change Module.finrank Geom (LinearMap.range (blockAt d s g)) ≤ (rows.map (charge s g)).sum
  omega

#print axioms grade_bound

end Final50RankCore
end Merged_Final50RankCore

/- Use the homogeneous-block decomposition in K1_13_1_1 with the
   homogenizing degree supplied by the anchor cap. -/
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace Final50RankBlocks
noncomputable section
open K1_13 K1_13_1_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Final50AnchorSpace
open scoped BigOperators
open private liftJets liftJets_X lift_value liftImage liftPower liftVar lift_order lift_value_order
  project_monomial jet_index_formula value_hom source_monomial_expr form_monomial_expr merge merge_single
  from ProximityPrize.SubmissionLower.Fast063

private abbrev Local := LocalPolynomial Geom 3
private abbrev T : Local := MvPolynomial.X (localT 3)
private def offset (i : Fin 154) : ℤ := (i : ℕ) - (55 : ℤ)

private abbrev selectedBlock (s : ℕ) (g : ℤ) :=
  Final50RankCore.blockAt (cap s) s g

private def postprocess (s : ℕ) (g : ℤ) : Form →ₗ[Geom] Local :=
  (projectLowContact 154).comp
    ((LinearMap.mulLeft Geom (T ^ (g + 55).toNat *
      (liftJets valueForm) ^ (s - cap s))).comp liftJets.toLinearMap)
private theorem postprocess_truncate (s : ℕ) (g : ℤ) (hg : -55 ≤ g) {P : Form}
    (hP : P.IsWeightedHomogeneous (fun _ => (1 : ℕ)) (cap s)) :
    postprocess s g (weightedTruncation targetOrder (Final50RankCore.orderCutoff s g).toNat P) =
      postprocess s g P := by
  let d := cap s
  let cutoff := (Final50RankCore.orderCutoff s g).toNat
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
  have ht : (T ^ (g + 55).toNat) ∈
      restrictWeightedOrder (localContactWeight 3) ((g + 55).toNat * 1) :=
    pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ _ (localContactWeight_T 3).ge) _
  have hf := pow_mem_restrictWeightedOrder lift_value_order (s - d)
  have hh := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder ht hf)
    (bind₁_mem_restrictWeightedOrder lift_order hH)
  have hc : 154 ≤ ((g + 55).toNat * 1 + (s-d) * 1) + (d + cutoff) := by
    have hd : d ≤ s := cap_le_grade s
    dsimp [cutoff, Final50RankCore.orderCutoff]
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
  have hj : u (some 1) + u (some 2) + u (some 3) ≤ 55 := by
    have hi := hu.2.1
    change u.some.weight jetIndex ≤ 55 at hi
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
      55 14 (trimmed u) := by
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
    T ^ 55 * unscaledLocalSubstitution 3 0 0 (monomial u a) =
      T ^ (((u none : ℤ) - u.some.weight jetIndex) + 55).toNat *
        (liftJets valueForm) ^ (u.some.degree - cap u.some.degree) *
        liftJets (backShift (monomial (trimmed u) a)) := by
  have hi := hu.2.1
  change u.some.weight jetIndex ≤ 55 at hi
  let r := (((u none : ℤ) - u.some.weight jetIndex) + 55).toNat
  have ht : r + u.some.weight jetIndex = u none + 55 := by dsimp [r]; omega
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
      T ^ (u none + 55) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ = T ^ (u none + 55) * MvPolynomial.C a * liftJets valueForm ^ u (some 0) *
        MvPolynomial.X (localY (0 : Fin 3)) ^ u (some 1) *
        MvPolynomial.X (localY (1 : Fin 3)) ^ u (some 2) *
        MvPolynomial.X (localY (2 : Fin 3)) ^ u (some 3) := by rw [pow_add]; ring
    _ = _ := by
      rw [← hpow, ← hv, pow_add]
      simp [liftImage, liftPower, liftVar, mul_pow]
      ring
private theorem shift_projection (P : Local) :
    T ^ 55 * projectLowContact 99 P = projectLowContact 154 (T ^ 55 * P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      have hmul : T ^ 55 * monomial e a = monomial (Finsupp.single (localT 3) 55 + e) a := by
        rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, one_mul]
      rw [project_monomial, hmul, project_monomial]
      have ho : localContactOrder 3 (Finsupp.single (localT 3) 55 + e) =
          55 + localContactOrder 3 e := by
        simp [localContactOrder, Finsupp.weight_single]
      have hlt : localContactOrder 3 (Finsupp.single (localT 3) 55 + e) < 154 ↔
          localContactOrder 3 e < 99 := by rw [ho]; omega
      by_cases he : localContactOrder 3 e < 99
      · simp [he, hlt.mpr he, hmul]
      · have hnot : ¬ localContactOrder 3 (Finsupp.single (localT 3) 55 + e) < 154 :=
          fun h => he (hlt.mp h)
        simp [he, hnot]
  | add P Q hP hQ => simp only [map_add, mul_add, hP, hQ]
private theorem shifted_constraint_monomial (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u)
    (a : Geom) :
    let s := u.some.degree
    let g := (u none : ℤ) - u.some.weight jetIndex
    T ^ 55 * localConstraintAt 99 0 0 (monomial u a) =
      postprocess s g (selectedBlock s g ⟨monomial (trimmed u) a,
        (monomial_mem_restrictSupport (R := Geom)).mpr (Or.inl (trimmed_mem_band u hu))⟩) := by
  dsimp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [shift_projection, shifted_substitution u hu]
  have hi := hu.2.1
  change u.some.weight jetIndex ≤ 55 at hi
  let s := u.some.degree
  let g : ℤ := (u none : ℤ) - u.some.weight jetIndex
  let P := backShift (monomial (trimmed u) a)
  change postprocess s g P = postprocess s g
    (weightedTruncation targetOrder (Final50RankCore.orderCutoff s g).toNat P)
  exact (postprocess_truncate s g (by dsimp [g]; omega) (backShift_hom u hu a)).symm
private theorem selected_zero (s : ℕ) (g : ℤ) (h : 99 - (s : ℤ) ≤ g) :
    selectedBlock s g = 0 := by
  apply LinearMap.ext
  intro q
  change weightedTruncation targetOrder (Final50RankCore.orderCutoff s g).toNat (backShift q) = 0
  have hcut : (Final50RankCore.orderCutoff s g).toNat = 0 := by unfold Final50RankCore.orderCutoff; omega
  rw [hcut, weightedTruncation_eq_zero_iff, restrictWeightedOrder_zero]
  trivial
private abbrev Block := Fin 133 × Fin 154
private abbrev Image (b : Block) := LinearMap.range (selectedBlock b.1 (offset b.2))
private def assemble : (∀ b : Block, Image b) →ₗ[Geom] Local :=
  merge (fun b => postprocess b.1 (offset b.2))
private theorem postprocess_mem_assemble (b : Block) (s : ℕ) (g : ℤ)
    (hs : (b.1 : ℕ) = s) (hg : offset b.2 = g)
    (q : bandSpace (cap s) (-g) 55 14) :
    postprocess s g (selectedBlock s g q) ∈ LinearMap.range assemble := by
  subst s
  subst g
  let v : Image b := ⟨selectedBlock b.1 (offset b.2) q, LinearMap.mem_range_self _ q⟩
  exact ⟨Pi.single b v, merge_single (fun j : Block => postprocess j.1 (offset j.2)) b v⟩
private theorem shifted_monomial_mem_assemble (u : JetVariable 3 →₀ ℕ)
    (hu : AnchorEligible u) (a : Geom) :
    T ^ 55 * localConstraintAt 99 0 0 (monomial u a) ∈ LinearMap.range assemble := by
  classical
  let s := u.some.degree
  let g : ℤ := (u none : ℤ) - u.some.weight jetIndex
  let q : bandSpace (cap s) (-g) 55 14 :=
    ⟨monomial (trimmed u) a, (monomial_mem_restrictSupport (R := Geom)).mpr (Or.inl (trimmed_mem_band u hu))⟩
  have hmono : T ^ 55 * localConstraintAt 99 0 0 (monomial u a) =
      postprocess s g (selectedBlock s g q) := shifted_constraint_monomial u hu a
  rw [hmono]
  by_cases hg : g < 99
  · have hJ := hu.2.1
    change u.some.weight jetIndex ≤ 55 at hJ
    have hs : s < 133 := by exact Nat.lt_succ_of_le hu.1
    have hr : (g + 55).toNat < 154 := by dsimp [g] at *; omega
    let b : Block := (⟨s, hs⟩, ⟨(g + 55).toNat, hr⟩)
    have ho : offset b.2 = g := by dsimp [b, offset, g]; omega
    exact postprocess_mem_assemble b s g rfl ho q
  · rw [selected_zero s g (by omega), LinearMap.zero_apply, map_zero]
    exact Submodule.zero_mem _
theorem origin_le_blocks :
    Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤
      ∑ s : Fin 133, ∑ r : Fin 154,
        Module.finrank Geom (LinearMap.range (Final50RankCore.blockAt (cap s) s ((r : ℕ) - (55 : ℤ)))) := by
  classical
  let shift := LinearMap.mulLeft Geom (T ^ 55)
  have hshift : Function.Injective shift :=
    fun _ _ h => mul_left_cancel₀ (pow_ne_zero _ (MvPolynomial.X_ne_zero _)) h
  let shifted := shift.comp (anchorLocal 0 0)
  have hdim : Module.finrank Geom (LinearMap.range shifted) =
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
    rw [LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective shift hshift _).finrank_eq.symm
  have hsub : LinearMap.range shifted ≤ LinearMap.range assemble := by
    rintro _ ⟨Q, rfl⟩
    change shift (localConstraintAt 99 0 0 (Q : DifferentialPolynomial Geom 3)) ∈ _
    rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
    exact Submodule.sum_mem _ fun u hu => shifted_monomial_mem_assemble u (Q.property hu) _
  have (b : Block) : Module.Finite Geom (Image b) := by
    have : Module.Finite Geom (bandSpace (cap b.1) (-offset b.2) 55 14) :=
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
end Final50RankBlocks