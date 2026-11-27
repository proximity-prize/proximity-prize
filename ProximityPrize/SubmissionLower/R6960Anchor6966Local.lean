import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup58
import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import Mathlib.Algebra.BigOperators.Intervals
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup5
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup10
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup15
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup20
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup25
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup30
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup35
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup40
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup45
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup50
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup55
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup56
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup57
import ProximityPrize.SubmissionLower.A6966FinalRankBlocks
import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false

-- merged module A6966FinalRank
section Merged_A6966FinalRank

-- merged module A6966FinalRankReceiptSum
section Merged_A6966FinalRankReceiptSum

set_option Elab.async false
set_option maxHeartbeats 2000000
namespace A6966FinalRankReceipt
open A6966FinalAnchorSpace (cap cap_le_index)
open Finset
open scoped BigOperators

private theorem triangle_succ (n : ℕ) :
    triangle (n+1) = triangle n + (n+1) := by
  unfold triangle
  have h : (n+1)*(n+1+1) = n*(n+1) + 2*(n+1) := by ring
  rw [h]
  omega

private theorem triangle_diff (x n : ℕ) :
    ∑ j ∈ range n, (x-j) = triangle x - triangle (x-n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases h : x ≤ n
    · have h' : x ≤ n+1 := by omega
      simp [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le h']
    · have hx : x-n = (x-(n+1))+1 := by omega
      have hle : triangle (x-n) ≤ triangle x := by
        apply Nat.div_le_div_right
        exact Nat.mul_le_mul (Nat.sub_le ..) (by omega)
      rw [hx, triangle_succ] at hle
      rw [hx, triangle_succ]
      omega

private def late (d : ℕ) : Finset ℕ :=
  (range (lateHi d - lateLo d)).image (fun s => lateLo d + s)

private def stages (d : ℕ) : Finset ℕ := insert d (late d)

private def inStage (d s : ℕ) : Prop := s = d ∨ lateLo d ≤ s ∧ s < lateHi d
private instance (d s : ℕ) : Decidable (inStage d s) := by unfold inStage; infer_instance

private theorem in_late (d s : ℕ) : s ∈ late d ↔ lateLo d ≤ s ∧ s < lateHi d := by
  unfold late
  rw [mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [mem_range] at hi
    omega
  · intro hs
    exact ⟨s - lateLo d, mem_range.mpr (by omega), by omega⟩

private theorem stage_bounds (d : ℕ) (hd : d < 59) :
    d < lateLo d ∧ lateLo d ≤ lateHi d ∧ lateHi d ≤ 143 := by
  have checks : (List.range 59).all (fun i => decide
      (i < lateLo i ∧ lateLo i ≤ lateHi i ∧ lateHi i ≤ 143)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks d (List.mem_range.mpr hd))

private theorem stages_eq (d : ℕ) (hd : d < 59) :
    (range 143).filter (fun s => cap s = d) = stages d := by
  have checks : (List.range 59).all (fun j =>
      (List.range 143).all (fun s => decide (cap s = j ↔ inStage j s))) = true := by decide +kernel
  ext s
  rw [mem_filter, mem_range, stages, mem_insert, in_late]
  by_cases hs : s < 143
  · have hh := of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp checks d (List.mem_range.mpr hd)) s (List.mem_range.mpr hs))
    simpa only [hs, true_and, inStage] using hh
  · obtain ⟨_, _, hhi⟩ := stage_bounds d hd
    simp [hs]
    omega

private theorem fee_add (s i : ℕ) (r : Row) : fee (s+i) r = fee s r - i := by
  unfold fee
  omega

private theorem sum_stage_fee (d : ℕ) (hd : d < 59) (r : Row) :
    ∑ s ∈ stages d, fee s r = price d r := by
  obtain ⟨hlo, hlen, _⟩ := stage_bounds d hd
  have hmiss : d ∉ late d := fun h => (Nat.not_le_of_gt hlo) ((in_late d d).mp h).1
  have hinj : Set.InjOn (fun s : ℕ => lateLo d+s) (↑(range (lateHi d-lateLo d))) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  rw [stages, sum_insert hmiss, late, sum_image hinj, price]
  simp_rw [fee_add (lateLo d)]
  rw [triangle_diff, ← fee_add, Nat.add_sub_of_le hlen]

private theorem exchange (st : Finset ℕ) (rows : List Row) :
    (∑ s ∈ st, ((rows.map (fee s)).sum)) =
      (rows.map (fun r => ∑ s ∈ st, fee s r)).sum := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem sum_fees (rows : ℕ → List Row) :
    (∑ s : Fin 143, ((rows (cap s)).map (fee s)).sum) =
      ∑ d : Fin 59, ((rows d).map (price d)).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun s => ((rows (cap s)).map (fee s)).sum) 143,
    Fin.sum_univ_eq_sum_range (fun d => ((rows d).map (price d)).sum) 59]
  calc
    _ = ∑ s ∈ range 143, ∑ d ∈ range 59,
          if cap s = d then ((rows d).map (fee s)).sum else 0 := by
        apply sum_congr rfl
        intro s hs
        rw [sum_eq_single (cap s)]
        · simp
        · intro d hd hne
          simp [Ne.symm hne]
        · intro he
          exact (he (mem_range.mpr (Nat.lt_succ_of_le (cap_le_index s)))).elim
    _ = ∑ d ∈ range 59, ((rows d).map (price d)).sum := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d hd
        rw [← sum_filter, stages_eq d (mem_range.mp hd), exchange]
        simp_rw [sum_stage_fee d (mem_range.mp hd)]

end A6966FinalRankReceipt

end Merged_A6966FinalRankReceiptSum

-- merged module A6966FinalRankReceipt
section Merged_A6966FinalRankReceipt

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000

namespace A6966FinalRankReceipt
open scoped BigOperators
open K1_13_1_1 (bandCount)
open A6966FinalAnchorSpace (cap)

def rows : ℕ → List Row
  | 0 => rows0
  | 1 => rows1
  | 2 => rows2
  | 3 => rows3
  | 4 => rows4
  | 5 => rows5
  | 6 => rows6
  | 7 => rows7
  | 8 => rows8
  | 9 => rows9
  | 10 => rows10
  | 11 => rows11
  | 12 => rows12
  | 13 => rows13
  | 14 => rows14
  | 15 => rows15
  | 16 => rows16
  | 17 => rows17
  | 18 => rows18
  | 19 => rows19
  | 20 => rows20
  | 21 => rows21
  | 22 => rows22
  | 23 => rows23
  | 24 => rows24
  | 25 => rows25
  | 26 => rows26
  | 27 => rows27
  | 28 => rows28
  | 29 => rows29
  | 30 => rows30
  | 31 => rows31
  | 32 => rows32
  | 33 => rows33
  | 34 => rows34
  | 35 => rows35
  | 36 => rows36
  | 37 => rows37
  | 38 => rows38
  | 39 => rows39
  | 40 => rows40
  | 41 => rows41
  | 42 => rows42
  | 43 => rows43
  | 44 => rows44
  | 45 => rows45
  | 46 => rows46
  | 47 => rows47
  | 48 => rows48
  | 49 => rows49
  | 50 => rows50
  | 51 => rows51
  | 52 => rows52
  | 53 => rows53
  | 54 => rows54
  | 55 => rows55
  | 56 => rows56
  | 57 => rows57
  | 58 => rows58
  | _ => []

private def expected : ℕ → ℕ
  | 0 => 106
  | 1 => 420
  | 2 => 1040
  | 3 => 2060
  | 4 => 3570
  | 5 => 5656
  | 6 => 8400
  | 7 => 11880
  | 8 => 16170
  | 9 => 21340
  | 10 => 27456
  | 11 => 34580
  | 12 => 42770
  | 13 => 52080
  | 14 => 62560
  | 15 => 74256
  | 16 => 87120
  | 17 => 101104
  | 18 => 116160
  | 19 => 132240
  | 20 => 149296
  | 21 => 167280
  | 22 => 186060
  | 23 => 205259
  | 24 => 224516
  | 25 => 243486
  | 26 => 261840
  | 27 => 279265
  | 28 => 295464
  | 29 => 310156
  | 30 => 323228
  | 31 => 334725
  | 32 => 344766
  | 33 => 353393
  | 34 => 360720
  | 35 => 366786
  | 36 => 371700
  | 37 => 375774
  | 38 => 378837
  | 39 => 381154
  | 40 => 382595
  | 41 => 383382
  | 42 => 383422
  | 43 => 382898
  | 44 => 381750
  | 45 => 380124
  | 46 => 377989
  | 47 => 375458
  | 48 => 372525
  | 49 => 369276
  | 50 => 365724
  | 51 => 361932
  | 52 => 357929
  | 53 => 353760
  | 54 => 349467
  | 55 => 345079
  | 56 => 340647
  | 57 => 336190
  | 58 => 8924726
  | _ => 0

theorem rows_good (d : Fin 59) : ∀ r ∈ rows d, good d r = true := by
  fin_cases d
  · exact good0
  · exact good1
  · exact good2
  · exact good3
  · exact good4
  · exact good5
  · exact good6
  · exact good7
  · exact good8
  · exact good9
  · exact good10
  · exact good11
  · exact good12
  · exact good13
  · exact good14
  · exact good15
  · exact good16
  · exact good17
  · exact good18
  · exact good19
  · exact good20
  · exact good21
  · exact good22
  · exact good23
  · exact good24
  · exact good25
  · exact good26
  · exact good27
  · exact good28
  · exact good29
  · exact good30
  · exact good31
  · exact good32
  · exact good33
  · exact good34
  · exact good35
  · exact good36
  · exact good37
  · exact good38
  · exact good39
  · exact good40
  · exact good41
  · exact good42
  · exact good43
  · exact good44
  · exact good45
  · exact good46
  · exact good47
  · exact good48
  · exact good49
  · exact good50
  · exact good51
  · exact good52
  · exact good53
  · exact good54
  · exact good55
  · exact good56
  · exact good57
  · exact good58
theorem rows_sorted (d : Fin 59) : (rows d).Pairwise (fun a b => a.tag < b.tag) := by
  fin_cases d
  · exact sorted0
  · exact sorted1
  · exact sorted2
  · exact sorted3
  · exact sorted4
  · exact sorted5
  · exact sorted6
  · exact sorted7
  · exact sorted8
  · exact sorted9
  · exact sorted10
  · exact sorted11
  · exact sorted12
  · exact sorted13
  · exact sorted14
  · exact sorted15
  · exact sorted16
  · exact sorted17
  · exact sorted18
  · exact sorted19
  · exact sorted20
  · exact sorted21
  · exact sorted22
  · exact sorted23
  · exact sorted24
  · exact sorted25
  · exact sorted26
  · exact sorted27
  · exact sorted28
  · exact sorted29
  · exact sorted30
  · exact sorted31
  · exact sorted32
  · exact sorted33
  · exact sorted34
  · exact sorted35
  · exact sorted36
  · exact sorted37
  · exact sorted38
  · exact sorted39
  · exact sorted40
  · exact sorted41
  · exact sorted42
  · exact sorted43
  · exact sorted44
  · exact sorted45
  · exact sorted46
  · exact sorted47
  · exact sorted48
  · exact sorted49
  · exact sorted50
  · exact sorted51
  · exact sorted52
  · exact sorted53
  · exact sorted54
  · exact sorted55
  · exact sorted56
  · exact sorted57
  · exact sorted58
theorem rows_cover (d i : Fin 59) :
    bandCount d (i.val : ℤ) 58 15 ≤ ((rows d).filter (fun r => decide (i.val ≤ r.index))).length := by
  fin_cases d
  · exact mass0 i
  · exact mass1 i
  · exact mass2 i
  · exact mass3 i
  · exact mass4 i
  · exact mass5 i
  · exact mass6 i
  · exact mass7 i
  · exact mass8 i
  · exact mass9 i
  · exact mass10 i
  · exact mass11 i
  · exact mass12 i
  · exact mass13 i
  · exact mass14 i
  · exact mass15 i
  · exact mass16 i
  · exact mass17 i
  · exact mass18 i
  · exact mass19 i
  · exact mass20 i
  · exact mass21 i
  · exact mass22 i
  · exact mass23 i
  · exact mass24 i
  · exact mass25 i
  · exact mass26 i
  · exact mass27 i
  · exact mass28 i
  · exact mass29 i
  · exact mass30 i
  · exact mass31 i
  · exact mass32 i
  · exact mass33 i
  · exact mass34 i
  · exact mass35 i
  · exact mass36 i
  · exact mass37 i
  · exact mass38 i
  · exact mass39 i
  · exact mass40 i
  · exact mass41 i
  · exact mass42 i
  · exact mass43 i
  · exact mass44 i
  · exact mass45 i
  · exact mass46 i
  · exact mass47 i
  · exact mass48 i
  · exact mass49 i
  · exact mass50 i
  · exact mass51 i
  · exact mass52 i
  · exact mass53 i
  · exact mass54 i
  · exact mass55 i
  · exact mass56 i
  · exact mass57 i
  · exact mass58 i

private theorem rows_price (d : Fin 59) :
    ((rows d).map (price d)).sum = expected d := by
  fin_cases d
  · exact total0
  · exact total1
  · exact total2
  · exact total3
  · exact total4
  · exact total5
  · exact total6
  · exact total7
  · exact total8
  · exact total9
  · exact total10
  · exact total11
  · exact total12
  · exact total13
  · exact total14
  · exact total15
  · exact total16
  · exact total17
  · exact total18
  · exact total19
  · exact total20
  · exact total21
  · exact total22
  · exact total23
  · exact total24
  · exact total25
  · exact total26
  · exact total27
  · exact total28
  · exact total29
  · exact total30
  · exact total31
  · exact total32
  · exact total33
  · exact total34
  · exact total35
  · exact total36
  · exact total37
  · exact total38
  · exact total39
  · exact total40
  · exact total41
  · exact total42
  · exact total43
  · exact total44
  · exact total45
  · exact total46
  · exact total47
  · exact total48
  · exact total49
  · exact total50
  · exact total51
  · exact total52
  · exact total53
  · exact total54
  · exact total55
  · exact total56
  · exact total57
  · exact total58


theorem total_fees :
    (∑ s : Fin 143, ((rows (cap s)).map (fee s)).sum) = 22239546 := by
  rw [sum_fees]
  simp_rw [rows_price]
  rw [Fin.sum_univ_eq_sum_range expected 59]
  decide +kernel


end A6966FinalRankReceipt

end Merged_A6966FinalRankReceipt

-- merged module A6966FinalRank
section Merged_A6966FinalRank

namespace A6966FinalRank
open K1_13 (Geom InBox Row shape extend atJet)
open K1 (I K node)
open A6966FinalAnchorSpace (cap anchorLocal)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 22239546 := by
  apply A6966FinalRankBlocks.origin_le_blocks.trans
  calc
    _ ≤ ∑ s : Fin 143, A6966FinalRankCore.gradeFee s (A6966FinalRankReceipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d : Fin 59 := ⟨cap s,Nat.lt_succ_of_le (A6966FinalAnchorSpace.cap_le_index s)⟩
      exact A6966FinalRankCore.grade_bound s d (A6966FinalRankReceipt.rows d)
        (A6966FinalRankReceipt.rows_good d) (A6966FinalRankReceipt.rows_sorted d) (A6966FinalRankReceipt.rows_cover d)
    _ = _ := A6966FinalRankReceipt.total_fees

end A6966FinalRank

end Merged_A6966FinalRank

end Merged_A6966FinalRank

-- merged module R6960Anchor6966Local
section Merged_R6960Anchor6966Local

-- merged module A6966LowBaseSpace
section Merged_A6966LowBaseSpace
set_option Elab.async false
set_option maxHeartbeats 2000000

end Merged_A6966LowBaseSpace

-- merged module A6966LowBaseDimension
section Merged_A6966LowBaseDimension
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

end Merged_A6966LowBaseDimension

-- merged module A6966LowBase
section Merged_A6966LowBase
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace A6966LowBase
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
/-- Bound the sum of the total and differentiated degrees at each monomial. -/
def ActiveFits (P : Row 4) (n : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ n
end
end A6966LowBase

end Merged_A6966LowBase

-- merged module R6960Anchor6966Local
section Merged_R6960Anchor6966Local

set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

namespace Anchor6966Local
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open A6966FinalAnchorSpace (gradeLimit gradeLimit_antitone cap_of_grade cap_active AnchorEligible anchorLocal anchorSpace)
open scoped BigOperators
open K1_13_1 (atJet_unflatten)
open K1_13_1_1 (exponent_le_of_mem_translation_monomial)

def WideEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 142 ∧ u.some.weight (fun i => i.val) ≤ 58 ∧ u (some 3) ≤ 15 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133400) ≤ 106 * 179769 - 1 + 58

def wideSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | WideEligible u}

def wideLocal (x y : Geom) : wideSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 106 x y).domRestrict _

section
open MvPolynomial

private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 106)
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu : 106 ≤ u none) :
    localConstraintAt 106 0 0 (monomial u a) = 0 := by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3) = monomial u a := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul, Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 106 0 0 _).mpr
  intro e he
  rw [map_mul, map_pow, unscaledLocalSubstitution, bind₁_X_right]
  simp only [unscaledLocalImage, MvPolynomial.C_0, zero_add, MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none ≤ e (localT 3) → False
  omega
private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 106 0 0 (truncateX Q) = localConstraintAt 106 0 0 Q := by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 106 then monomial u (Q.coeff u) else 0 := by
    ext v
    rw [truncateX, coeff_filterSupport]
    by_cases h : u = v
    · subst v
      by_cases hx : u none < 106 <;> simp [hx]
    · by_cases hx : u none < 106 <;> simp [hx, MvPolynomial.coeff_monomial, h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero, origin_monomial_zero _ _ (by omega)]

private theorem centered {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : WideEligible u) (hx : v none < 106) :
    AnchorEligible v := by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hi : v.some.weight (fun i => i.val) ≤ u.some.weight (fun i => i.val) := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right j.val (h (some j))
  obtain ⟨hdeg,hidx,ht,htail,_⟩ := hu
  have hsum := add_le_add (add_le_add (h (some 1)) (h (some 2))) (h (some 3))
  refine ⟨hd.trans hdeg,hi.trans hidx,(h _).trans ht,hd.trans (htail.trans (gradeLimit_antitone hsum)),?_⟩
  have hw := Finsupp.weight_le_weight
    (w := fun j : Fin 4 => 133484 - j.val) (w' := fun _ => 133484)
    (fun j => Nat.sub_le _ _) v.some
  have he : v.some.weight (fun _ => 133484) = 133484 * v.some.degree := by
    simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
      Finset.mul_sum, Nat.mul_comm]
  rw [he] at hw
  have hweight : differentialWeight (d := 3) 133484 =
      fun j => j.elim 1 (fun i => 133484 - i.val) := by
    funext j
    cases j <;> rfl
  rw [← Finsupp.optionElim_some v, hweight, Finsupp.weight_optionElim, one_mul]
  calc
    _ ≤ 105 + 133484 * 142 :=
      Nat.add_le_add (Nat.le_of_lt_succ hx)
        (hw.trans (Nat.mul_le_mul_left _ (hd.trans hdeg)))
    _ ≤ _ := by decide
private theorem centered_in_space (x y : Geom) (Q : wideSpace) :
    truncateX (globalPointTranslation x y (Q : DifferentialPolynomial Geom 3)) ∈
      anchorSpace := by
  classical
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn := mem_support_iff.mp hv
  rw [truncateX, coeff_filterSupport] at hn
  split at hn
  · exact centered
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (Q.property hu) (by assumption)
  · exact (hn rfl).elim
theorem rank_at_point_le_origin (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
  have hpositive (j : JetVariable 3) : differentialWeight 133484 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133484 - j.val ≠ 0
      omega
  have : Module.Finite Geom anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let f : wideSpace →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict wideSpace
  let tr : wideSpace →ₗ[Geom] anchorSpace := f.codRestrict _ fun Q =>
    centered_in_space x y Q
  have he : wideLocal x y = (anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 106 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 106 0 0 (truncateX (globalPointTranslation x y Q))
    rw [origin_truncateX,localConstraintAt_eq_zero_globalPointTranslation]
  rw [he]
  exact LinearMap.finrank_range_comp_le_left _ _

end

theorem per_position (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤ 22239546 :=
  (rank_at_point_le_origin x y).trans A6966FinalRank.origin_rank

theorem finiteWide : Module.Finite Geom wideSpace := by
  have hpositive (j : JetVariable 3) : differentialWeight 133400 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133400 - j.val ≠ 0
      omega
  exact MvPolynomial.restrictSupport_finite <|
    (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2

theorem shape_bound (Q : wideSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨142, 58, 15⟩ := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, WideEligible (m.optionElim i) := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i, hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.degree_apply, Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 15
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1

theorem active_bound (Q : wideSpace) :
    A6966LowBase.ActiveFits (MvPolynomial.optionEquivRight Geom (Fin 4) Q) 178 := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  intro m hm
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hm)
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have h : WideEligible (m.optionElim i) := hQ (MvPolynomial.mem_support_iff.mpr (by
    rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff]))
  have hd := h.1
  have hl := h.2.2.2.1
  have hw := h.2.1
  simp only [Finsupp.optionElim_apply_some] at hl
  rw [Finsupp.some_optionElim] at hd hw
  have hdeg : m.degree = m 0 + m 1 + m 2 + m 3 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have hweight : m.weight (fun i : Fin 4 => i.val) = m 1 + 2 * m 2 + 3 * m 3 := by
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_four]
    simp [Nat.mul_comm, Nat.add_assoc]
  change m.weight (fun i : Fin 4 => i.val) ≤ 58 at hw
  rw [hweight] at hw
  have hc := cap_of_grade (s := m.degree) (t := m 1 + m 2 + m 3)
    (by omega) (by omega) (by simpa [Finsupp.some_optionElim] using hl)
  have hb := cap_active _ hd
  omega

theorem rawWeight (Q : wideSpace) :
    differentialWeightedDegree 133400 (Q : DifferentialPolynomial Geom 3) ≤
      106 * 179769 - 1 + 58 := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  exact fun m hm => (Q.property hm).2.2.2.2


end
end Anchor6966Local

end Merged_R6960Anchor6966Local

end Merged_R6960Anchor6966Local
